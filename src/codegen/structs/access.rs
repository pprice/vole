// src/codegen/structs/access.rs

use super::helpers::{convert_field_value, convert_to_i64_for_storage, get_field_slot_and_type};
use crate::codegen::context::Cg;
use crate::codegen::types::{CompiledValue, type_to_cranelift};
use crate::frontend::{Expr, FieldAccessExpr, OptionalChainExpr, Symbol};
use crate::sema::Type;
use crate::sema::types::ConstantValue;
use cranelift::prelude::*;

impl Cg<'_, '_, '_> {
    pub fn field_access(&mut self, fa: &FieldAccessExpr) -> Result<CompiledValue, String> {
        let obj = self.expr(&fa.object)?;

        // Handle module field access for constants (e.g., math.PI)
        if let Type::Module(ref module_type) = obj.vole_type {
            let field_name = self.ctx.interner.resolve(fa.field);

            // Look up constant value in module
            if let Some(const_val) = module_type.constants.get(field_name) {
                return match const_val {
                    ConstantValue::F64(v) => {
                        let val = self.builder.ins().f64const(*v);
                        Ok(CompiledValue {
                            value: val,
                            ty: types::F64,
                            vole_type: Type::F64,
                        })
                    }
                    ConstantValue::I64(v) => {
                        let val = self.builder.ins().iconst(types::I64, *v);
                        Ok(CompiledValue {
                            value: val,
                            ty: types::I64,
                            vole_type: Type::I64,
                        })
                    }
                    ConstantValue::Bool(v) => {
                        let val = self.builder.ins().iconst(types::I8, if *v { 1 } else { 0 });
                        Ok(CompiledValue {
                            value: val,
                            ty: types::I8,
                            vole_type: Type::Bool,
                        })
                    }
                    ConstantValue::String(s) => self.string_literal(s),
                };
            }

            // Check if it's a function export
            if let Some(export_type) = module_type.exports.get(field_name) {
                if matches!(export_type, Type::Function(_)) {
                    return Err(format!(
                        "Module function {} should be called, not accessed as a field. Use {}() instead.",
                        field_name, field_name
                    ));
                }

                return Err(format!(
                    "Module export {} is not a constant literal and cannot be accessed at compile time",
                    field_name
                ));
            }

            return Err(format!(
                "Module {} has no export named {}",
                module_type.path, field_name
            ));
        }

        let (slot, field_type) = get_field_slot_and_type(&obj.vole_type, fa.field, self.ctx)?;

        let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
        let result_raw = self.call_runtime("vole_instance_get_field", &[obj.value, slot_val])?;

        let (result_val, cranelift_ty) = convert_field_value(self.builder, result_raw, &field_type);

        Ok(CompiledValue {
            value: result_val,
            ty: cranelift_ty,
            vole_type: field_type,
        })
    }

    pub fn optional_chain(&mut self, oc: &OptionalChainExpr) -> Result<CompiledValue, String> {
        let obj = self.expr(&oc.object)?;

        // The object should be an optional type (union with nil)
        let Type::Union(variants) = &obj.vole_type else {
            return Err("Expected optional type for ?.".to_string());
        };

        // Find the nil tag
        let nil_tag = variants
            .iter()
            .position(|v| v == &Type::Nil)
            .unwrap_or(usize::MAX);

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

        // Get the inner (non-nil) type for field access
        let inner_type = obj.vole_type.unwrap_optional().unwrap_or(Type::Error);

        // Get the field type from the inner type
        let (slot, field_type) = get_field_slot_and_type(&inner_type, oc.field, self.ctx)?;

        // Result type is field_type | nil (optional)
        // But if field type is already optional, don't double-wrap
        let result_vole_type = if field_type.is_optional() {
            field_type.clone()
        } else {
            Type::optional(field_type.clone())
        };
        let cranelift_type = type_to_cranelift(&result_vole_type, self.ctx.pointer_type);
        self.builder.append_block_param(merge_block, cranelift_type);

        self.builder
            .ins()
            .brif(is_nil, nil_block, &[], not_nil_block, &[]);

        // Nil block: return nil wrapped in the optional type
        self.builder.switch_to_block(nil_block);
        self.builder.seal_block(nil_block);
        let nil_val = self.nil_value();
        let nil_union = self.construct_union(nil_val, &result_vole_type)?;
        self.builder
            .ins()
            .jump(merge_block, &[nil_union.value.into()]);

        // Not-nil block: do field access and wrap result in optional
        self.builder.switch_to_block(not_nil_block);
        self.builder.seal_block(not_nil_block);

        // Load the actual object from the union payload (offset 8)
        let inner_cranelift_type = type_to_cranelift(&inner_type, self.ctx.pointer_type);
        let inner_obj =
            self.builder
                .ins()
                .load(inner_cranelift_type, MemFlags::new(), obj.value, 8);

        // Get field from the inner object
        let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
        let field_raw = self.call_runtime("vole_instance_get_field", &[inner_obj, slot_val])?;
        let (field_val, field_cranelift_ty) =
            convert_field_value(self.builder, field_raw, &field_type);

        // Wrap the field value in an optional (using construct_union)
        // But if field type is already optional, it's already a union - just use it directly
        let field_compiled = CompiledValue {
            value: field_val,
            ty: field_cranelift_ty,
            vole_type: field_type.clone(),
        };
        let final_value = if field_type.is_optional() {
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
            vole_type: result_vole_type,
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

        let (slot, _field_type) = get_field_slot_and_type(&obj.vole_type, field, self.ctx)?;

        let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
        let store_value = convert_to_i64_for_storage(self.builder, &value);

        self.call_runtime_void(
            "vole_instance_set_field",
            &[obj.value, slot_val, store_value],
        )?;

        Ok(value)
    }
}
