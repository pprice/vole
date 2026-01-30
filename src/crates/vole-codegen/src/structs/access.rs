// src/codegen/structs/access.rs

use super::helpers::{convert_to_i64_for_storage, get_field_slot_and_type_id_cg};
use crate::RuntimeFn;
use crate::context::Cg;
use crate::errors::CodegenError;
use crate::types::{CompiledValue, module_name_id};
use cranelift::prelude::*;
use vole_frontend::{Expr, FieldAccessExpr, NodeId, OptionalChainExpr, Symbol};
use vole_sema::type_arena::TypeId;
use vole_sema::types::ConstantValue;

impl Cg<'_, '_, '_> {
    #[tracing::instrument(skip(self, fa), fields(field = %self.interner().resolve(fa.field)))]
    pub fn field_access(&mut self, fa: &FieldAccessExpr) -> Result<CompiledValue, String> {
        let obj = self.expr(&fa.object)?;

        let module_info = {
            let arena = self.arena();
            arena.unwrap_module(obj.type_id).map(|m| {
                let exports = m.exports.clone();
                (m.module_id, exports)
            })
        };
        if let Some((module_id, exports)) = module_info {
            tracing::trace!(?module_id, "field access on module");
            let field_name = self.interner().resolve(fa.field);
            let module_path = self.name_table().module_path(module_id).to_string();
            let name_id = module_name_id(self.analyzed(), module_id, field_name);

            // Look up constant value in module metadata
            let const_val = {
                let arena = self.arena();
                name_id.and_then(|nid| {
                    arena
                        .module_metadata(module_id)
                        .and_then(|meta| meta.constants.get(&nid).cloned())
                })
            };
            if let Some(const_val) = const_val {
                let arena = self.arena();
                let f64_id = arena.f64();
                let i64_id = arena.i64();
                let bool_id = arena.bool();
                return match const_val {
                    ConstantValue::F64(v) => {
                        let val = self.builder.ins().f64const(v);
                        Ok(CompiledValue {
                            value: val,
                            ty: types::F64,
                            type_id: f64_id,
                        })
                    }
                    ConstantValue::I64(v) => {
                        let val = self.builder.ins().iconst(types::I64, v);
                        Ok(CompiledValue {
                            value: val,
                            ty: types::I64,
                            type_id: i64_id,
                        })
                    }
                    ConstantValue::Bool(v) => {
                        let val = self.builder.ins().iconst(types::I8, if v { 1 } else { 0 });
                        Ok(CompiledValue {
                            value: val,
                            ty: types::I8,
                            type_id: bool_id,
                        })
                    }
                    ConstantValue::String(s) => self.string_literal(&s),
                };
            }

            // Check if it's an export (function or other)
            let export_type_id = name_id
                .and_then(|nid| exports.iter().find(|(n, _)| *n == nid).map(|(_, tid)| *tid));
            if let Some(export_type_id) = export_type_id {
                let is_function = self.arena().is_function(export_type_id);
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
        let field_name = self.interner().resolve(fa.field);
        let (slot, field_type_id) = get_field_slot_and_type_id_cg(obj.type_id, field_name, self)?;

        // Struct types are stack-allocated: load field directly from pointer + offset
        let is_struct = self.arena().is_struct(obj.type_id);
        if is_struct {
            return self.struct_field_load(obj.value, slot, field_type_id);
        }

        let result_raw = self.get_field_cached(obj.value, slot as u32)?;
        Ok(self.convert_field_value(result_raw, field_type_id))
    }

    pub fn optional_chain(
        &mut self,
        oc: &OptionalChainExpr,
        expr_id: NodeId,
    ) -> Result<CompiledValue, String> {
        let obj = self.expr(&oc.object)?;

        // The object should be an optional type (union with nil)
        let (_variants, nil_tag, inner_type_id) = {
            let arena = self.arena();
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
        let is_nil = self.tag_eq(obj.value, nil_tag as i64);

        // Create blocks for branching
        let nil_block = self.builder.create_block();
        let not_nil_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        // Get the field type from the inner type using TypeId-based helper
        let field_name = self.interner().resolve(oc.field);
        let (slot, field_type_id) = get_field_slot_and_type_id_cg(inner_type_id, field_name, self)?;

        // Get result type from sema (already computed as Optional<T> or T if T is already optional)
        // Sema handles the double-wrapping logic in check_optional_chain_expr
        let result_type_id = self
            .get_expr_type(&expr_id)
            .expect("optional_chain: sema must record type for optional chain expression");
        let is_field_optional = self.arena().is_optional(field_type_id);

        let cranelift_type = {
            let arena = self.arena();
            crate::types::type_id_to_cranelift(result_type_id, arena, self.ptr_type())
        };
        self.builder.append_block_param(merge_block, cranelift_type);

        self.builder
            .ins()
            .brif(is_nil, nil_block, &[], not_nil_block, &[]);

        // Nil block: return nil wrapped in the optional type
        self.switch_and_seal(nil_block);
        let nil_val = self.nil_value();
        let nil_union = self.construct_union_id(nil_val, result_type_id)?;
        self.builder
            .ins()
            .jump(merge_block, &[nil_union.value.into()]);

        // Not-nil block: do field access and wrap result in optional
        self.switch_and_seal(not_nil_block);

        // Load the actual object from the union payload (offset 8)
        let inner_cranelift_type = {
            let arena = self.arena();
            crate::types::type_id_to_cranelift(inner_type_id, arena, self.ptr_type())
        };
        let inner_obj =
            self.builder
                .ins()
                .load(inner_cranelift_type, MemFlags::new(), obj.value, 8);

        // Get field from the inner object
        let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
        let field_raw = self.call_runtime(RuntimeFn::InstanceGetField, &[inner_obj, slot_val])?;
        let field_compiled = self.convert_field_value(field_raw, field_type_id);

        // Wrap the field value in an optional (using construct_union_id)
        // But if field type is already optional, it's already a union - just use it directly
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
        self.switch_and_seal(merge_block);

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

        let field_name = self.interner().resolve(field);
        let (slot, field_type_id) = get_field_slot_and_type_id_cg(obj.type_id, field_name, self)?;

        // Struct types: store directly to pointer + offset
        let is_struct = self.arena().is_struct(obj.type_id);
        if is_struct {
            let offset = (slot as i32) * 8;
            let store_value = convert_to_i64_for_storage(self.builder, &value);
            self.builder
                .ins()
                .store(MemFlags::new(), store_value, obj.value, offset);
            return Ok(value);
        }

        let value = if self.arena().is_interface(field_type_id) {
            self.box_interface_value(value, field_type_id)?
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

    /// Load a field from a struct pointer at the given slot.
    /// Structs are stack-allocated with 8-byte fields at offset slot * 8.
    pub fn struct_field_load(
        &mut self,
        struct_ptr: Value,
        slot: usize,
        field_type_id: TypeId,
    ) -> Result<CompiledValue, String> {
        let offset = (slot as i32) * 8;
        // Load as i64, then convert to proper type
        let raw_value = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), struct_ptr, offset);
        Ok(self.convert_field_value(raw_value, field_type_id))
    }
}
