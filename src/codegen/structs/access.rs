// src/codegen/structs/access.rs

use super::helpers::{
    convert_field_value_id, convert_to_i64_for_storage, get_field_slot_and_type_id,
};
use crate::codegen::RuntimeFn;
use crate::codegen::context::Cg;
use crate::codegen::types::{CompiledValue, box_interface_value_id, module_name_id};
use crate::errors::CodegenError;
use crate::frontend::{Expr, FieldAccessExpr, OptionalChainExpr, Symbol};
use crate::sema::types::ConstantValue;
use cranelift::prelude::*;

impl Cg<'_, '_, '_> {
    #[tracing::instrument(skip(self, fa), fields(field = %self.ctx.interner.resolve(fa.field)))]
    pub fn field_access(&mut self, fa: &FieldAccessExpr) -> Result<CompiledValue, String> {
        let obj = self.expr(&fa.object)?;

        // Check for module type using arena methods (no DisplayType conversion)
        let module_info = {
            let arena = self.ctx.arena.borrow();
            arena.unwrap_module(obj.type_id).map(|m| {
                let exports = m.exports.clone();
                (m.module_id, exports)
            })
        };
        if let Some((module_id, exports)) = module_info {
            tracing::trace!(?module_id, "field access on module");
            let field_name = self.ctx.interner.resolve(fa.field);
            let module_path = self.ctx.analyzed.name_table.module_path(module_id);
            let name_id = module_name_id(self.ctx.analyzed, module_id, field_name);

            // Look up constant value in module metadata
            let const_val = {
                let arena = self.ctx.arena.borrow();
                name_id.and_then(|nid| {
                    arena
                        .module_metadata(module_id)
                        .and_then(|meta| meta.constants.get(&nid).cloned())
                })
            };
            if let Some(const_val) = const_val {
                let arena = self.ctx.arena.borrow();
                return match const_val {
                    ConstantValue::F64(v) => {
                        let val = self.builder.ins().f64const(v);
                        Ok(CompiledValue {
                            value: val,
                            ty: types::F64,
                            type_id: arena.f64(),
                        })
                    }
                    ConstantValue::I64(v) => {
                        let val = self.builder.ins().iconst(types::I64, v);
                        Ok(CompiledValue {
                            value: val,
                            ty: types::I64,
                            type_id: arena.i64(),
                        })
                    }
                    ConstantValue::Bool(v) => {
                        let val = self.builder.ins().iconst(types::I8, if v { 1 } else { 0 });
                        Ok(CompiledValue {
                            value: val,
                            ty: types::I8,
                            type_id: arena.bool(),
                        })
                    }
                    ConstantValue::String(s) => {
                        drop(arena);
                        self.string_literal(&s)
                    }
                };
            }

            // Check if it's an export (function or other)
            let export_type_id = name_id
                .and_then(|nid| exports.iter().find(|(n, _)| *n == nid).map(|(_, tid)| *tid));
            if let Some(export_type_id) = export_type_id {
                let is_function = self.ctx.arena.borrow().is_function(export_type_id);
                if is_function {
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
        let (result_val, cranelift_ty) =
            convert_field_value_id(self.builder, result_raw, field_type_id, &arena);
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
        // Use arena methods instead of DisplayType pattern matching
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
        let (slot, field_type_id) =
            get_field_slot_and_type_id(inner_type_id, field_name, self.ctx)?;

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
            crate::codegen::types::type_id_to_cranelift(
                result_type_id,
                &arena,
                self.ctx.pointer_type,
            )
        };
        self.builder.append_block_param(merge_block, cranelift_type);

        self.builder
            .ins()
            .brif(is_nil, nil_block, &[], not_nil_block, &[]);

        // Nil block: return nil wrapped in the optional type
        self.builder.switch_to_block(nil_block);
        self.builder.seal_block(nil_block);
        let nil_val = self.nil_value();
        let nil_union = self.construct_union_id(nil_val, result_type_id)?;
        self.builder
            .ins()
            .jump(merge_block, &[nil_union.value.into()]);

        // Not-nil block: do field access and wrap result in optional
        self.builder.switch_to_block(not_nil_block);
        self.builder.seal_block(not_nil_block);

        // Load the actual object from the union payload (offset 8)
        let inner_cranelift_type = {
            let arena = self.ctx.arena.borrow();
            crate::codegen::types::type_id_to_cranelift(
                inner_type_id,
                &arena,
                self.ctx.pointer_type,
            )
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

        // Wrap the field value in an optional (using construct_union_id)
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
            self.construct_union_id(field_compiled, result_type_id)?
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
        // Use TypeId-based helper to avoid DisplayType conversion
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
