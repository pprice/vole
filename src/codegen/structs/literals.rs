// src/codegen/structs/literals.rs

use std::collections::HashMap;

use super::helpers::convert_to_i64_for_storage;
use crate::codegen::context::Cg;
use crate::codegen::types::CompiledValue;
use crate::frontend::{StructLiteralExpr, Symbol};
use crate::sema::Type;
use cranelift::prelude::*;

impl Cg<'_, '_, '_> {
    pub fn struct_literal(&mut self, sl: &StructLiteralExpr) -> Result<CompiledValue, String> {
        let metadata = self
            .ctx
            .type_metadata
            .get(&sl.name)
            .ok_or_else(|| format!("Unknown type: {}", self.ctx.interner.resolve(sl.name)))?;

        let type_id = metadata.type_id;
        let field_count = metadata.field_slots.len() as u32;
        let vole_type = metadata.vole_type.clone();
        let field_slots = metadata.field_slots.clone();

        let type_id_val = self.builder.ins().iconst(types::I32, type_id as i64);
        let field_count_val = self.builder.ins().iconst(types::I32, field_count as i64);
        let runtime_type = self.builder.ins().iconst(types::I32, 7); // TYPE_INSTANCE

        let instance_ptr = self.call_runtime(
            "vole_instance_new",
            &[type_id_val, field_count_val, runtime_type],
        )?;

        let set_func_ref = self.func_ref("vole_instance_set_field")?;

        // Get field types for wrapping optional values
        let field_types: HashMap<Symbol, Type> = match &vole_type {
            Type::Record(rt) => rt.fields.iter().map(|f| (f.name, f.ty.clone())).collect(),
            Type::Class(ct) => ct.fields.iter().map(|f| (f.name, f.ty.clone())).collect(),
            _ => HashMap::new(),
        };

        for init in &sl.fields {
            let slot = *field_slots.get(&init.name).ok_or_else(|| {
                format!(
                    "Unknown field: {} in type {}",
                    self.ctx.interner.resolve(init.name),
                    self.ctx.interner.resolve(sl.name)
                )
            })?;

            let value = self.expr(&init.value)?;

            // If field type is optional (union) and value type is not a union, wrap it
            let final_value = if let Some(field_type) = field_types.get(&init.name) {
                if matches!(field_type, Type::Union(_))
                    && !matches!(&value.vole_type, Type::Union(_))
                {
                    self.construct_union(value, field_type)?
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
}
