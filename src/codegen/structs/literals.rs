// src/codegen/structs/literals.rs

use std::collections::HashMap;

use super::helpers::convert_to_i64_for_storage;
use crate::codegen::RuntimeFn;
use crate::codegen::context::Cg;
use crate::codegen::types::{CompiledValue, box_interface_value, type_size};
use crate::errors::CodegenError;
use crate::frontend::{Expr, StructLiteralExpr};
use crate::sema::LegacyType;
use crate::sema::types::NominalType;
use cranelift::prelude::*;

impl Cg<'_, '_, '_> {
    pub fn struct_literal(
        &mut self,
        sl: &StructLiteralExpr,
        expr: &Expr,
    ) -> Result<CompiledValue, String> {
        // Resolve type name to main interner's Symbol for lookup
        // This is needed because module classes register with main interner Symbols,
        // but struct literals in module code use module interner Symbols
        let type_name = self.ctx.interner.resolve(sl.name);
        let lookup_symbol = self
            .ctx
            .analyzed
            .interner
            .lookup(type_name)
            .unwrap_or(sl.name);
        let metadata = self
            .ctx
            .type_metadata
            .get(&lookup_symbol)
            .ok_or_else(|| format!("Unknown type: {}", type_name))?;

        let type_id = metadata.type_id;
        let field_count = metadata.field_slots.len() as u32;
        // Prefer the type from semantic analysis (handles generic instantiation)
        let vole_type = self
            .ctx
            .analyzed
            .query()
            .type_of(expr.id)
            .cloned()
            .unwrap_or_else(|| metadata.vole_type.clone());
        let field_slots = metadata.field_slots.clone();

        let type_id_val = self.builder.ins().iconst(types::I32, type_id as i64);
        let field_count_val = self.builder.ins().iconst(types::I32, field_count as i64);
        let runtime_type = self.builder.ins().iconst(types::I32, 7); // TYPE_INSTANCE

        let instance_ptr = self.call_runtime(
            RuntimeFn::InstanceNew,
            &[type_id_val, field_count_val, runtime_type],
        )?;

        let set_key = self
            .ctx
            .func_registry
            .runtime_key(RuntimeFn::InstanceSetField)
            .ok_or_else(|| "vole_instance_set_field not found".to_string())?;
        let set_func_ref = self.func_ref(set_key)?;

        // Get field types for wrapping optional values
        let field_types: HashMap<String, LegacyType> = match &vole_type {
            LegacyType::Nominal(NominalType::Record(rt)) => {
                let type_def = self.ctx.analyzed.entity_registry.get_type(rt.type_def_id);
                if let Some(generic_info) = &type_def.generic_info {
                    generic_info
                        .field_names
                        .iter()
                        .zip(generic_info.field_types.iter())
                        .map(|(name_id, ty)| {
                            (
                                self.ctx
                                    .analyzed
                                    .name_table
                                    .last_segment_str(*name_id)
                                    .unwrap_or_default(),
                                ty.clone(),
                            )
                        })
                        .collect()
                } else {
                    HashMap::new()
                }
            }
            LegacyType::Nominal(NominalType::Class(ct)) => {
                let type_def = self.ctx.analyzed.entity_registry.get_type(ct.type_def_id);
                if let Some(generic_info) = &type_def.generic_info {
                    generic_info
                        .field_names
                        .iter()
                        .zip(generic_info.field_types.iter())
                        .map(|(name_id, ty)| {
                            (
                                self.ctx
                                    .analyzed
                                    .name_table
                                    .last_segment_str(*name_id)
                                    .unwrap_or_default(),
                                ty.clone(),
                            )
                        })
                        .collect()
                } else {
                    HashMap::new()
                }
            }
            _ => HashMap::new(),
        };

        for init in &sl.fields {
            let init_name = self.ctx.interner.resolve(init.name);
            let slot = *field_slots.get(init_name).ok_or_else(|| {
                format!(
                    "Unknown field: {} in type {}",
                    init_name,
                    self.ctx.interner.resolve(sl.name)
                )
            })?;

            let value = self.expr(&init.value)?;

            // If field type is optional (union) and value type is not a union, wrap it
            // Use heap allocation for unions stored in class/record fields since stack slots
            // don't persist beyond the current function's stack frame
            let final_value = if let Some(field_type) = field_types.get(init_name) {
                if matches!(field_type, LegacyType::Union(_))
                    && !matches!(&value.vole_type, LegacyType::Union(_))
                {
                    self.construct_union_heap(value, field_type)?
                } else if matches!(field_type, LegacyType::Nominal(NominalType::Interface(_))) {
                    box_interface_value(self.builder, self.ctx, value, field_type)?
                } else {
                    value
                }
            } else {
                value
            };

            let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
            let store_value = convert_to_i64_for_storage(self.builder, &final_value);

            self.builder
                .ins()
                .call(set_func_ref, &[instance_ptr, slot_val, store_value]);
        }

        Ok(CompiledValue {
            value: instance_ptr,
            ty: self.ctx.pointer_type,
            vole_type,
        })
    }

    /// Construct a union value on the heap (for storing in class/record fields).
    /// Unlike the stack-based construct_union, this allocates on the heap so the
    /// union persists beyond the current function's stack frame.
    fn construct_union_heap(
        &mut self,
        value: CompiledValue,
        union_type: &LegacyType,
    ) -> Result<CompiledValue, String> {
        let LegacyType::Union(variants) = union_type else {
            return Err(CodegenError::type_mismatch(
                "union construction",
                "union type",
                "non-union",
            )
            .into());
        };

        // If the value is already the same union type, just return it
        if &value.vole_type == union_type {
            return Ok(value);
        }

        // Find the tag for the value type
        let tag = variants
            .iter()
            .position(|v| v == &value.vole_type)
            .ok_or_else(|| {
                CodegenError::type_mismatch(
                    "union variant",
                    format!("one of {:?}", variants),
                    format!("{:?}", value.vole_type),
                )
            })?;

        // Get heap_alloc function ref
        let heap_alloc_key = self
            .ctx
            .func_registry
            .runtime_key(RuntimeFn::HeapAlloc)
            .ok_or_else(|| "heap allocator not registered".to_string())?;
        let heap_alloc_ref = self.func_ref(heap_alloc_key)?;

        // Allocate union storage on the heap
        let union_size = type_size(union_type, self.ctx.pointer_type);
        let size_val = self
            .builder
            .ins()
            .iconst(self.ctx.pointer_type, union_size as i64);
        let alloc_call = self.builder.ins().call(heap_alloc_ref, &[size_val]);
        let heap_ptr = self.builder.inst_results(alloc_call)[0];

        // Store tag at offset 0
        let tag_val = self.builder.ins().iconst(types::I8, tag as i64);
        self.builder
            .ins()
            .store(MemFlags::new(), tag_val, heap_ptr, 0);

        // Store payload at offset 8 (if not nil)
        if value.vole_type != LegacyType::Nil {
            self.builder
                .ins()
                .store(MemFlags::new(), value.value, heap_ptr, 8);
        }

        Ok(CompiledValue {
            value: heap_ptr,
            ty: self.ctx.pointer_type,
            vole_type: union_type.clone(),
        })
    }
}
