// src/codegen/structs.rs
//
// Struct/class/record operations for code generation.
// This module contains helper functions and impl Cg methods for field access, method lookups.

use cranelift::prelude::*;
use cranelift_module::Module;

use super::context::Cg;
use super::types::{type_to_cranelift, CompileCtx, CompiledValue};
use crate::frontend::{FieldAccessExpr, MethodCallExpr, StructLiteralExpr, Symbol};
use crate::sema::Type;

/// Get field slot and type from a class/record type
pub(crate) fn get_field_slot_and_type(
    vole_type: &Type,
    field: Symbol,
    ctx: &CompileCtx,
) -> Result<(usize, Type), String> {
    match vole_type {
        Type::Class(class_type) => {
            for sf in &class_type.fields {
                if sf.name == field {
                    return Ok((sf.slot, sf.ty.clone()));
                }
            }
            Err(format!(
                "Field {} not found in class",
                ctx.interner.resolve(field)
            ))
        }
        Type::Record(record_type) => {
            for sf in &record_type.fields {
                if sf.name == field {
                    return Ok((sf.slot, sf.ty.clone()));
                }
            }
            Err(format!(
                "Field {} not found in record",
                ctx.interner.resolve(field)
            ))
        }
        _ => Err(format!(
            "Cannot access field {} on non-class/record type {:?}",
            ctx.interner.resolve(field),
            vole_type
        )),
    }
}

/// Get the type name symbol from a class/record type
pub(crate) fn get_type_name_symbol(vole_type: &Type) -> Result<Symbol, String> {
    match vole_type {
        Type::Class(class_type) => Ok(class_type.name),
        Type::Record(record_type) => Ok(record_type.name),
        _ => Err(format!(
            "Cannot get type name from non-class/record type {:?}",
            vole_type
        )),
    }
}

/// Get the return type of a method
pub(crate) fn get_method_return_type(
    vole_type: &Type,
    method: Symbol,
    ctx: &CompileCtx,
) -> Result<Type, String> {
    let type_name = get_type_name_symbol(vole_type)?;
    let metadata = ctx
        .type_metadata
        .get(&type_name)
        .ok_or_else(|| "Type metadata not found".to_string())?;

    // Look up the method return type from metadata
    metadata
        .method_return_types
        .get(&method)
        .cloned()
        .ok_or_else(|| format!("Method {} not found in type", ctx.interner.resolve(method)))
}

/// Convert a raw i64 field value to the appropriate Cranelift type
pub(crate) fn convert_field_value(
    builder: &mut FunctionBuilder,
    raw_value: Value,
    field_type: &Type,
) -> (Value, types::Type) {
    match field_type {
        Type::F64 => {
            let fval = builder
                .ins()
                .bitcast(types::F64, MemFlags::new(), raw_value);
            (fval, types::F64)
        }
        Type::F32 => {
            // Truncate to i32 first, then bitcast
            let i32_val = builder.ins().ireduce(types::I32, raw_value);
            let fval = builder.ins().bitcast(types::F32, MemFlags::new(), i32_val);
            (fval, types::F32)
        }
        Type::Bool => {
            let bval = builder.ins().ireduce(types::I8, raw_value);
            (bval, types::I8)
        }
        Type::I8 | Type::U8 => {
            let val = builder.ins().ireduce(types::I8, raw_value);
            (val, types::I8)
        }
        Type::I16 | Type::U16 => {
            let val = builder.ins().ireduce(types::I16, raw_value);
            (val, types::I16)
        }
        Type::I32 | Type::U32 => {
            let val = builder.ins().ireduce(types::I32, raw_value);
            (val, types::I32)
        }
        Type::String | Type::Array(_) | Type::Class(_) | Type::Record(_) => {
            // Pointers stay as i64
            (raw_value, types::I64)
        }
        _ => (raw_value, types::I64),
    }
}

/// Convert a CompiledValue to i64 for storage in instance fields
pub(crate) fn convert_to_i64_for_storage(
    builder: &mut FunctionBuilder,
    value: &CompiledValue,
) -> Value {
    match value.ty {
        types::F64 => builder
            .ins()
            .bitcast(types::I64, MemFlags::new(), value.value),
        types::F32 => {
            let i32_val = builder
                .ins()
                .bitcast(types::I32, MemFlags::new(), value.value);
            builder.ins().uextend(types::I64, i32_val)
        }
        types::I8 => builder.ins().uextend(types::I64, value.value),
        types::I16 => builder.ins().uextend(types::I64, value.value),
        types::I32 => builder.ins().uextend(types::I64, value.value),
        types::I64 => value.value,
        _ => value.value,
    }
}

impl Cg<'_, '_, '_> {
    /// Compile a struct literal: Point { x: 10, y: 20 }
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

        let new_func_id = self
            .ctx
            .func_ids
            .get("vole_instance_new")
            .ok_or_else(|| "vole_instance_new not found".to_string())?;
        let new_func_ref = self
            .ctx
            .module
            .declare_func_in_func(*new_func_id, self.builder.func);

        let type_id_val = self.builder.ins().iconst(types::I32, type_id as i64);
        let field_count_val = self.builder.ins().iconst(types::I32, field_count as i64);
        let runtime_type = self.builder.ins().iconst(types::I32, 7); // TYPE_INSTANCE

        let call = self.builder.ins().call(
            new_func_ref,
            &[type_id_val, field_count_val, runtime_type],
        );
        let instance_ptr = self.builder.inst_results(call)[0];

        let set_func_id = self
            .ctx
            .func_ids
            .get("vole_instance_set_field")
            .ok_or_else(|| "vole_instance_set_field not found".to_string())?;
        let set_func_ref = self
            .ctx
            .module
            .declare_func_in_func(*set_func_id, self.builder.func);

        for init in &sl.fields {
            let slot = *field_slots.get(&init.name).ok_or_else(|| {
                format!(
                    "Unknown field: {} in type {}",
                    self.ctx.interner.resolve(init.name),
                    self.ctx.interner.resolve(sl.name)
                )
            })?;

            let value = self.expr(&init.value)?;
            let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
            let store_value = convert_to_i64_for_storage(self.builder, &value);

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

    /// Compile field access: point.x
    pub fn field_access(&mut self, fa: &FieldAccessExpr) -> Result<CompiledValue, String> {
        let obj = self.expr(&fa.object)?;
        let (slot, field_type) = get_field_slot_and_type(&obj.vole_type, fa.field, self.ctx)?;

        let get_func_id = self
            .ctx
            .func_ids
            .get("vole_instance_get_field")
            .ok_or_else(|| "vole_instance_get_field not found".to_string())?;
        let get_func_ref = self
            .ctx
            .module
            .declare_func_in_func(*get_func_id, self.builder.func);

        let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
        let call = self.builder.ins().call(get_func_ref, &[obj.value, slot_val]);
        let result_raw = self.builder.inst_results(call)[0];

        let (result_val, cranelift_ty) = convert_field_value(self.builder, result_raw, &field_type);

        Ok(CompiledValue {
            value: result_val,
            ty: cranelift_ty,
            vole_type: field_type,
        })
    }

    /// Compile field assignment: obj.field = value
    pub fn field_assign(
        &mut self,
        object: &crate::frontend::Expr,
        field: Symbol,
        value_expr: &crate::frontend::Expr,
    ) -> Result<CompiledValue, String> {
        let obj = self.expr(object)?;
        let value = self.expr(value_expr)?;

        let (slot, _field_type) = get_field_slot_and_type(&obj.vole_type, field, self.ctx)?;

        let set_func_id = self
            .ctx
            .func_ids
            .get("vole_instance_set_field")
            .ok_or_else(|| "vole_instance_set_field not found".to_string())?;
        let set_func_ref = self
            .ctx
            .module
            .declare_func_in_func(*set_func_id, self.builder.func);

        let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
        let store_value = convert_to_i64_for_storage(self.builder, &value);

        self.builder
            .ins()
            .call(set_func_ref, &[obj.value, slot_val, store_value]);

        Ok(value)
    }

    /// Compile a method call: point.distance()
    pub fn method_call(&mut self, mc: &MethodCallExpr) -> Result<CompiledValue, String> {
        let obj = self.expr(&mc.object)?;
        let method_name_str = self.ctx.interner.resolve(mc.method);

        // Handle built-in methods
        if let Some(result) = self.builtin_method(&obj, method_name_str)? {
            return Ok(result);
        }

        let type_name = get_type_name_symbol(&obj.vole_type)?;
        let type_name_str = self.ctx.interner.resolve(type_name);
        let full_name = format!("{}_{}", type_name_str, method_name_str);

        let method_func_id = self
            .ctx
            .func_ids
            .get(&full_name)
            .ok_or_else(|| format!("Unknown method: {}", full_name))?;
        let method_func_ref = self
            .ctx
            .module
            .declare_func_in_func(*method_func_id, self.builder.func);

        let mut args = vec![obj.value];
        for arg in &mc.args {
            let compiled = self.expr(arg)?;
            args.push(compiled.value);
        }

        let call = self.builder.ins().call(method_func_ref, &args);
        let results = self.builder.inst_results(call);

        let return_type = get_method_return_type(&obj.vole_type, mc.method, self.ctx)?;

        if results.is_empty() {
            Ok(CompiledValue {
                value: self.builder.ins().iconst(types::I64, 0),
                ty: types::I64,
                vole_type: Type::Void,
            })
        } else {
            Ok(CompiledValue {
                value: results[0],
                ty: type_to_cranelift(&return_type, self.ctx.pointer_type),
                vole_type: return_type,
            })
        }
    }

    /// Handle built-in methods for primitive types
    fn builtin_method(
        &mut self,
        obj: &CompiledValue,
        method_name: &str,
    ) -> Result<Option<CompiledValue>, String> {
        match (&obj.vole_type, method_name) {
            (Type::Array(_), "length") => {
                let func_id = self
                    .ctx
                    .func_ids
                    .get("vole_array_len")
                    .ok_or_else(|| "vole_array_len not found".to_string())?;
                let func_ref = self
                    .ctx
                    .module
                    .declare_func_in_func(*func_id, self.builder.func);
                let call = self.builder.ins().call(func_ref, &[obj.value]);
                let result = self.builder.inst_results(call)[0];
                Ok(Some(CompiledValue {
                    value: result,
                    ty: types::I64,
                    vole_type: Type::I64,
                }))
            }
            (Type::String, "length") => {
                let func_id = self
                    .ctx
                    .func_ids
                    .get("vole_string_len")
                    .ok_or_else(|| "vole_string_len not found".to_string())?;
                let func_ref = self
                    .ctx
                    .module
                    .declare_func_in_func(*func_id, self.builder.func);
                let call = self.builder.ins().call(func_ref, &[obj.value]);
                let result = self.builder.inst_results(call)[0];
                Ok(Some(CompiledValue {
                    value: result,
                    ty: types::I64,
                    vole_type: Type::I64,
                }))
            }
            _ => Ok(None),
        }
    }
}
