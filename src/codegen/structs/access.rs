// src/codegen/structs/access.rs

use super::helpers::{convert_field_value_id, convert_to_i64_for_storage, get_field_slot_and_type_id};
use crate::codegen::RuntimeFn;
use crate::codegen::context::Cg;
use crate::codegen::types::{
    CompiledValue, box_interface_value_id, module_name_id,
};
use crate::errors::CodegenError;
use crate::frontend::{Expr, FieldAccessExpr, OptionalChainExpr, Symbol};
use crate::sema::types::ConstantValue;
use crate::sema::{LegacyType, PrimitiveType};
use cranelift::prelude::*;

impl Cg<'_, '_, '_> {
    #[tracing::instrument(skip(self, fa), fields(field = %self.ctx.interner.resolve(fa.field)))]
    pub fn field_access(&mut self, fa: &FieldAccessExpr) -> Result<CompiledValue, String> {
        let obj = self.expr(&fa.object)?;

        // Check for module type using arena method
        let module_info = self.ctx.arena.borrow().unwrap_module(obj.type_id).map(|m| m.module_id);
        if let Some(_module_id) = module_info {
            // For module access, we need LegacyType to access constants
            let obj_type = self.to_legacy(obj.type_id);
            let LegacyType::Module(ref module_type) = obj_type else {
                unreachable!("unwrap_module returned Some but to_legacy didn't return Module")
            };
            tracing::trace!(object_type = ?obj_type, "field access on module");
            let field_name = self.ctx.interner.resolve(fa.field);
            let module_path = self
                .ctx
                .analyzed
                .name_table
                .module_path(module_type.module_id);
            let name_id = module_name_id(self.ctx.analyzed, module_type.module_id, field_name);

            // Look up constant value in module
            if let Some(name_id) = name_id
                && let Some(const_val) = module_type.constants.get(&name_id)
            {
                return match const_val {
                    ConstantValue::F64(v) => {
                        let val = self.builder.ins().f64const(*v);
                        Ok(CompiledValue {
                            value: val,
                            ty: types::F64,
                            type_id: self.intern_type(&LegacyType::Primitive(PrimitiveType::F64)),
                        })
                    }
                    ConstantValue::I64(v) => {
                        let val = self.builder.ins().iconst(types::I64, *v);
                        Ok(CompiledValue {
                            value: val,
                            ty: types::I64,
                            type_id: self.intern_type(&LegacyType::Primitive(PrimitiveType::I64)),
                        })
                    }
                    ConstantValue::Bool(v) => {
                        let val = self.builder.ins().iconst(types::I8, if *v { 1 } else { 0 });
                        Ok(CompiledValue {
                            value: val,
                            ty: types::I8,
                            type_id: self.intern_type(&LegacyType::Primitive(PrimitiveType::Bool)),
                        })
                    }
                    ConstantValue::String(s) => self.string_literal(s),
                };
            }

            // Check if it's a function export
            if let Some(name_id) = name_id
                && let Some(export_type) = module_type.exports.get(&name_id)
            {
                if matches!(export_type, LegacyType::Function(_)) {
                    return Err(CodegenError::unsupported_with_context(
                        "function as field value",
                        format!("use {}() to call the function", field_name),
                    )
                    .into());
                }

                return Err(CodegenError::unsupported_with_context(
                    "non-constant module export",
                    format!("{} cannot be accessed at compile time", field_name),
                )
                .into());
            }

            return Err(CodegenError::not_found(
                "module export",
                format!("{}.{}", module_path, field_name),
            )
            .into());
        }

        // Non-module field access - use TypeId-based helpers
        let field_name = self.ctx.interner.resolve(fa.field);
        let (slot, field_type_id) = get_field_slot_and_type_id(obj.type_id, field_name, self.ctx)?;

        let result_raw = self.get_field_cached(obj.value, slot as u32)?;

        let arena = self.ctx.arena.borrow();
        let (result_val, cranelift_ty) = convert_field_value_id(self.builder, result_raw, field_type_id, &arena);
        drop(arena);

        Ok(CompiledValue {
            value: result_val,
            ty: cranelift_ty,
            type_id: field_type_id,
        })
    }

    pub fn optional_chain(&mut self, oc: &OptionalChainExpr) -> Result<CompiledValue, String> {
        let obj = self.expr(&oc.object)?;

        // The object should be an optional type (union with nil)
        // Use arena methods instead of LegacyType pattern matching
        let (_variants, nil_tag, inner_type_id) = {
            let arena = self.ctx.arena.borrow();
            let variants = arena.unwrap_union(obj.type_id).ok_or_else(|| {
                CodegenError::type_mismatch("optional chain", "optional type", "non-optional")
                    .to_string()
            })?;
            let nil_id = arena.nil();
            let nil_tag = variants
                .iter()
                .position(|&v| v == nil_id)
                .unwrap_or(usize::MAX);
            let inner_type_id = arena.unwrap_optional(obj.type_id).ok_or_else(|| {
                CodegenError::type_mismatch(
                    "optional chain",
                    "optional type",
                    "union without inner type",
                )
                .to_string()
            })?;
            (variants.clone(), nil_tag, inner_type_id)
        };

        // Check if object is nil by reading the tag
        let tag = self
            .builder
            .ins()
            .load(types::I8, MemFlags::new(), obj.value, 0);
        let nil_tag_val = self.builder.ins().iconst(types::I8, nil_tag as i64);
        let is_nil = self.builder.ins().icmp(IntCC::Equal, tag, nil_tag_val);

        // Create blocks for branching
        let nil_block = self.builder.create_block();
        let not_nil_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        // Get the field type from the inner type using TypeId-based helper
        let field_name = self.ctx.interner.resolve(oc.field);
        let (slot, field_type_id) = get_field_slot_and_type_id(inner_type_id, field_name, self.ctx)?;

        // Result type is field_type | nil (optional)
        // But if field type is already optional, don't double-wrap
        let (result_type_id, is_field_optional) = {
            let mut arena = self.ctx.arena.borrow_mut();
            let is_optional = arena.is_optional(field_type_id);
            let result_id = if is_optional {
                field_type_id
            } else {
                arena.optional(field_type_id)
            };
            (result_id, is_optional)
        };

        let cranelift_type = {
            let arena = self.ctx.arena.borrow();
            crate::codegen::types::type_id_to_cranelift(result_type_id, &arena, self.ctx.pointer_type)
        };
        self.builder.append_block_param(merge_block, cranelift_type);

        self.builder
            .ins()
            .brif(is_nil, nil_block, &[], not_nil_block, &[]);

        // Nil block: return nil wrapped in the optional type
        // construct_union still needs LegacyType - convert for now
        self.builder.switch_to_block(nil_block);
        self.builder.seal_block(nil_block);
        let nil_val = self.nil_value();
        let result_vole_type = self.to_legacy(result_type_id);
        let nil_union = self.construct_union(nil_val, &result_vole_type)?;
        self.builder
            .ins()
            .jump(merge_block, &[nil_union.value.into()]);

        // Not-nil block: do field access and wrap result in optional
        self.builder.switch_to_block(not_nil_block);
        self.builder.seal_block(not_nil_block);

        // Load the actual object from the union payload (offset 8)
        let inner_cranelift_type = {
            let arena = self.ctx.arena.borrow();
            crate::codegen::types::type_id_to_cranelift(inner_type_id, &arena, self.ctx.pointer_type)
        };
        let inner_obj =
            self.builder
                .ins()
                .load(inner_cranelift_type, MemFlags::new(), obj.value, 8);

        // Get field from the inner object
        let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
        let field_raw = self.call_runtime(RuntimeFn::InstanceGetField, &[inner_obj, slot_val])?;
        let (field_val, field_cranelift_ty) = {
            let arena = self.ctx.arena.borrow();
            convert_field_value_id(self.builder, field_raw, field_type_id, &arena)
        };

        // Wrap the field value in an optional (using construct_union)
        // But if field type is already optional, it's already a union - just use it directly
        let field_compiled = CompiledValue {
            value: field_val,
            ty: field_cranelift_ty,
            type_id: field_type_id,
        };
        let final_value = if is_field_optional {
            // Field is already optional, use as-is
            field_compiled
        } else {
            // Wrap non-optional field in optional
            self.construct_union(field_compiled, &result_vole_type)?
        };
        self.builder
            .ins()
            .jump(merge_block, &[final_value.value.into()]);

        // Merge block
        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);

        let result = self.builder.block_params(merge_block)[0];
        Ok(CompiledValue {
            value: result,
            ty: cranelift_type,
            type_id: result_type_id,
        })
    }

    pub fn field_assign(
        &mut self,
        object: &Expr,
        field: Symbol,
        value_expr: &Expr,
    ) -> Result<CompiledValue, String> {
        let obj = self.expr(object)?;
        let value = self.expr(value_expr)?;

        let field_name = self.ctx.interner.resolve(field);
        // Use TypeId-based helper to avoid LegacyType conversion
        let (slot, field_type_id) = get_field_slot_and_type_id(obj.type_id, field_name, self.ctx)?;
        let value = if self.ctx.arena.borrow().is_interface(field_type_id) {
            box_interface_value_id(self.builder, self.ctx, value, field_type_id)?
        } else {
            value
        };

        let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
        let store_value = convert_to_i64_for_storage(self.builder, &value);

        self.call_runtime_void(
            RuntimeFn::InstanceSetField,
            &[obj.value, slot_val, store_value],
        )?;
        self.field_cache.clear(); // Invalidate cached field reads

        Ok(value)
    }
}
