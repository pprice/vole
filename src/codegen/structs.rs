// src/codegen/structs.rs
//
// Struct/class/record operations for code generation.
// This module contains helper functions and impl Cg methods for field access, method lookups.

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_module::Module;

use super::context::Cg;
use super::types::{CompileCtx, CompiledValue, type_to_cranelift};
use crate::frontend::{
    Expr, FieldAccessExpr, MethodCallExpr, NodeId, OptionalChainExpr, StructLiteralExpr, Symbol,
};
use crate::sema::implement_registry::TypeId;
use crate::sema::resolution::ResolvedMethod;
use crate::sema::types::ConstantValue;
use crate::sema::{FunctionType, Type};

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

    /// Compile field access: point.x or module.constant
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

    /// Compile optional chaining: obj?.field
    /// If obj is nil, returns nil; otherwise returns obj.field wrapped in optional
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

    /// Compile field assignment: obj.field = value
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

    /// Compile a method call: point.distance()
    pub fn method_call(
        &mut self,
        mc: &MethodCallExpr,
        expr_id: NodeId,
    ) -> Result<CompiledValue, String> {
        let obj = self.expr(&mc.object)?;
        let method_name_str = self.ctx.interner.resolve(mc.method);

        // Handle module method calls (e.g., math.sqrt(16.0), math.lerp(...))
        // These go to either external native functions or pure Vole module functions
        if let Type::Module(ref module_type) = obj.vole_type {
            // Get the method resolution
            let resolution = self.ctx.method_resolutions.get(expr_id);
            if let Some(ResolvedMethod::Implemented {
                external_info,
                func_type,
                ..
            }) = resolution
            {
                // Compile arguments (no receiver for module functions)
                let mut args = Vec::new();
                for arg in &mc.args {
                    let compiled = self.expr(arg)?;
                    args.push(compiled.value);
                }

                let return_type = (*func_type.return_type).clone();

                if let Some(ext_info) = external_info {
                    // External FFI function
                    return self.call_external(ext_info, &args, &return_type);
                } else {
                    // Pure Vole function - call by mangled name
                    let mangled_name = format!("{}::{}", module_type.path, method_name_str);
                    let func_id = self
                        .ctx
                        .func_ids
                        .get(&mangled_name)
                        .copied()
                        .ok_or_else(|| format!("Module function {} not found", mangled_name))?;
                    let func_ref = self
                        .ctx
                        .module
                        .declare_func_in_func(func_id, self.builder.func);
                    let call_inst = self.builder.ins().call(func_ref, &args);
                    let results = self.builder.inst_results(call_inst);

                    if results.is_empty() {
                        return Ok(self.void_value());
                    } else {
                        return Ok(self.typed_value(results[0], return_type));
                    }
                }
            } else {
                return Err(format!(
                    "Module method {}::{} has no resolution",
                    module_type.path, method_name_str
                ));
            }
        }

        // Handle built-in methods
        if let Some(result) = self.builtin_method(&obj, method_name_str)? {
            return Ok(result);
        }

        // Handle iterator.map(fn) -> creates a MapIterator
        // Also handle MapIterator.map(fn), FilterIterator.map(fn), TakeIterator.map(fn), SkipIterator.map(fn) for chained maps
        if let Type::Iterator(elem_ty)
        | Type::MapIterator(elem_ty)
        | Type::FilterIterator(elem_ty)
        | Type::TakeIterator(elem_ty)
        | Type::SkipIterator(elem_ty) = &obj.vole_type
            && method_name_str == "map"
        {
            return self.iterator_map(&obj, elem_ty, &mc.args);
        }

        // Handle iterator.filter(fn) -> creates a FilterIterator
        // Also handle MapIterator.filter(fn), FilterIterator.filter(fn), TakeIterator.filter(fn), SkipIterator.filter(fn) for chained filters
        if let Type::Iterator(elem_ty)
        | Type::MapIterator(elem_ty)
        | Type::FilterIterator(elem_ty)
        | Type::TakeIterator(elem_ty)
        | Type::SkipIterator(elem_ty) = &obj.vole_type
            && method_name_str == "filter"
        {
            return self.iterator_filter(&obj, elem_ty, &mc.args);
        }

        // Handle iterator.take(n) -> creates a TakeIterator
        if let Type::Iterator(elem_ty)
        | Type::MapIterator(elem_ty)
        | Type::FilterIterator(elem_ty)
        | Type::TakeIterator(elem_ty)
        | Type::SkipIterator(elem_ty) = &obj.vole_type
            && method_name_str == "take"
        {
            return self.iterator_take(&obj, elem_ty, &mc.args);
        }

        // Handle iterator.skip(n) -> creates a SkipIterator
        if let Type::Iterator(elem_ty)
        | Type::MapIterator(elem_ty)
        | Type::FilterIterator(elem_ty)
        | Type::TakeIterator(elem_ty)
        | Type::SkipIterator(elem_ty) = &obj.vole_type
            && method_name_str == "skip"
        {
            return self.iterator_skip(&obj, elem_ty, &mc.args);
        }

        // Handle iterator.for_each(fn) -> calls function for each element
        if let Type::Iterator(_)
        | Type::MapIterator(_)
        | Type::FilterIterator(_)
        | Type::TakeIterator(_)
        | Type::SkipIterator(_) = &obj.vole_type
            && method_name_str == "for_each"
        {
            return self.iterator_for_each(&obj, &mc.args);
        }

        // Handle iterator.reduce(init, fn) -> reduces iterator to single value
        if let Type::Iterator(_)
        | Type::MapIterator(_)
        | Type::FilterIterator(_)
        | Type::TakeIterator(_)
        | Type::SkipIterator(_) = &obj.vole_type
            && method_name_str == "reduce"
        {
            return self.iterator_reduce(&obj, &mc.args);
        }

        // Look up method resolution to determine naming convention and return type
        // If no resolution exists (e.g., inside default method bodies), fall back to type-based lookup
        let resolution = self.ctx.method_resolutions.get(expr_id);

        // Determine the method function name based on resolution type
        let (full_name, return_type) = if let Some(resolution) = resolution {
            match resolution {
                ResolvedMethod::Direct { func_type } => {
                    // Direct method on class/record: use TypeName_methodName
                    let type_name = get_type_name_symbol(&obj.vole_type)?;
                    let type_name_str = self.ctx.interner.resolve(type_name);
                    let name = format!("{}_{}", type_name_str, method_name_str);
                    (name, (*func_type.return_type).clone())
                }
                ResolvedMethod::Implemented {
                    func_type,
                    is_builtin,
                    external_info,
                    ..
                } => {
                    if *is_builtin {
                        // Built-in methods should have been handled above
                        return Err(format!("Unhandled builtin method: {}", method_name_str));
                    }

                    // Check if this is an external native method
                    if let Some(ext_info) = external_info {
                        // Compile the receiver and arguments
                        let mut args = vec![obj.value];
                        for arg in &mc.args {
                            let compiled = self.expr(arg)?;
                            args.push(compiled.value);
                        }

                        // Call the external native function
                        let return_type = (*func_type.return_type).clone();
                        return self.call_external(ext_info, &args, &return_type);
                    }

                    // Implement block method: use TypeName::methodName
                    let type_id = TypeId::from_type(&obj.vole_type)
                        .ok_or_else(|| format!("Cannot get TypeId for {:?}", obj.vole_type))?;
                    let type_name_str = type_id.type_name(self.ctx.interner);
                    let name = format!("{}::{}", type_name_str, method_name_str);
                    (name, (*func_type.return_type).clone())
                }
                ResolvedMethod::FunctionalInterface { func_type } => {
                    // For functional interfaces, the object holds the function ptr or closure
                    // The actual is_closure status depends on the lambda's compilation,
                    // which we can get from the object's actual type
                    let is_closure = if let Type::Function(ft) = &obj.vole_type {
                        ft.is_closure
                    } else {
                        // If it's not a function type (e.g., still typed as Interface),
                        // fall back to the resolution's flag
                        func_type.is_closure
                    };
                    let actual_func_type = FunctionType {
                        params: func_type.params.clone(),
                        return_type: func_type.return_type.clone(),
                        is_closure,
                    };
                    return self.functional_interface_call(obj.value, actual_func_type, mc);
                }
                ResolvedMethod::DefaultMethod {
                    type_name,
                    func_type,
                    ..
                } => {
                    // Default method from interface, monomorphized for the concrete type
                    // Name format is TypeName_methodName (same as direct methods)
                    let type_name_str = self.ctx.interner.resolve(*type_name);
                    let name = format!("{}_{}", type_name_str, method_name_str);
                    (name, (*func_type.return_type).clone())
                }
            }
        } else {
            // No resolution found - try to resolve directly from object type
            // This handles method calls inside default method bodies where sema
            // doesn't analyze the interface body
            let type_name = get_type_name_symbol(&obj.vole_type)?;
            let type_name_str = self.ctx.interner.resolve(type_name);

            // Look up method return type from type metadata
            let return_type = self
                .ctx
                .type_metadata
                .get(&type_name)
                .and_then(|meta| meta.method_return_types.get(&mc.method).cloned())
                .ok_or_else(|| {
                    format!(
                        "Method {} not found on type {}",
                        method_name_str, type_name_str
                    )
                })?;

            let name = format!("{}_{}", type_name_str, method_name_str);
            (name, return_type)
        };

        let method_func_ref = self.func_ref(&full_name)?;

        let mut args = vec![obj.value];
        for arg in &mc.args {
            let compiled = self.expr(arg)?;
            args.push(compiled.value);
        }

        let call = self.builder.ins().call(method_func_ref, &args);
        let results = self.builder.inst_results(call);

        if results.is_empty() {
            Ok(self.void_value())
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
                let result = self.call_runtime("vole_array_len", &[obj.value])?;
                Ok(Some(self.i64_value(result)))
            }
            (Type::Array(elem_ty), "iter") => {
                let result = self.call_runtime("vole_array_iter", &[obj.value])?;
                Ok(Some(CompiledValue {
                    value: result,
                    ty: self.ctx.pointer_type,
                    vole_type: Type::Iterator(elem_ty.clone()),
                }))
            }
            // Iterator.next() -> T | Done
            (Type::Iterator(elem_ty), "next") => {
                // Create stack slot for output value (8 bytes for i64)
                let out_slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    8,
                    0,
                ));
                let out_ptr = self
                    .builder
                    .ins()
                    .stack_addr(self.ctx.pointer_type, out_slot, 0);

                // Call runtime: has_value = vole_array_iter_next(iter, out_ptr)
                let has_value = self.call_runtime("vole_array_iter_next", &[obj.value, out_ptr])?;

                // Load value from out_slot
                let value = self.builder.ins().stack_load(types::I64, out_slot, 0);

                // Build union result: T | Done
                // Union layout: [tag:1][padding:7][payload:8] = 16 bytes
                // Tag 0 = element type (T), Tag 1 = Done
                let union_type = Type::Union(vec![*elem_ty.clone(), Type::Done]);
                let union_size = 16u32; // tag(1) + padding(7) + payload(8)
                let union_slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    union_size,
                    0,
                ));

                // Determine tag based on has_value:
                // has_value != 0 => tag = 0 (element type)
                // has_value == 0 => tag = 1 (Done)
                let zero = self.builder.ins().iconst(types::I64, 0);
                let is_done = self.builder.ins().icmp(IntCC::Equal, has_value, zero);
                let tag_done = self.builder.ins().iconst(types::I8, 1);
                let tag_value = self.builder.ins().iconst(types::I8, 0);
                let tag = self.builder.ins().select(is_done, tag_done, tag_value);

                // Store tag at offset 0
                self.builder.ins().stack_store(tag, union_slot, 0);

                // Store payload at offset 8 (value if has_value, 0 if done)
                self.builder.ins().stack_store(value, union_slot, 8);

                let union_ptr = self
                    .builder
                    .ins()
                    .stack_addr(self.ctx.pointer_type, union_slot, 0);
                Ok(Some(CompiledValue {
                    value: union_ptr,
                    ty: self.ctx.pointer_type,
                    vole_type: union_type,
                }))
            }
            // Iterator.collect() -> [T]
            (Type::Iterator(elem_ty), "collect") => {
                let result = self.call_runtime("vole_array_iter_collect", &[obj.value])?;
                Ok(Some(CompiledValue {
                    value: result,
                    ty: self.ctx.pointer_type,
                    vole_type: Type::Array(elem_ty.clone()),
                }))
            }
            // MapIterator.next() -> T | Done
            (Type::MapIterator(elem_ty), "next") => {
                // Create stack slot for output value (8 bytes for i64)
                let out_slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    8,
                    0,
                ));
                let out_ptr = self
                    .builder
                    .ins()
                    .stack_addr(self.ctx.pointer_type, out_slot, 0);

                // Call runtime: has_value = vole_map_iter_next(iter, out_ptr)
                let has_value = self.call_runtime("vole_map_iter_next", &[obj.value, out_ptr])?;

                // Load value from out_slot
                let value = self.builder.ins().stack_load(types::I64, out_slot, 0);

                // Build union result: T | Done
                // Union layout: [tag:1][padding:7][payload:8] = 16 bytes
                // Tag 0 = element type (T), Tag 1 = Done
                let union_type = Type::Union(vec![*elem_ty.clone(), Type::Done]);
                let union_size = 16u32; // tag(1) + padding(7) + payload(8)
                let union_slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    union_size,
                    0,
                ));

                // Determine tag based on has_value:
                // has_value != 0 => tag = 0 (element type)
                // has_value == 0 => tag = 1 (Done)
                let zero = self.builder.ins().iconst(types::I64, 0);
                let is_done = self.builder.ins().icmp(IntCC::Equal, has_value, zero);
                let tag_done = self.builder.ins().iconst(types::I8, 1);
                let tag_value = self.builder.ins().iconst(types::I8, 0);
                let tag = self.builder.ins().select(is_done, tag_done, tag_value);

                // Store tag at offset 0
                self.builder.ins().stack_store(tag, union_slot, 0);

                // Store payload at offset 8 (value if has_value, 0 if done)
                self.builder.ins().stack_store(value, union_slot, 8);

                let union_ptr = self
                    .builder
                    .ins()
                    .stack_addr(self.ctx.pointer_type, union_slot, 0);
                Ok(Some(CompiledValue {
                    value: union_ptr,
                    ty: self.ctx.pointer_type,
                    vole_type: union_type,
                }))
            }
            // MapIterator.collect() -> [T]
            (Type::MapIterator(elem_ty), "collect") => {
                let result = self.call_runtime("vole_map_iter_collect", &[obj.value])?;
                Ok(Some(CompiledValue {
                    value: result,
                    ty: self.ctx.pointer_type,
                    vole_type: Type::Array(elem_ty.clone()),
                }))
            }
            // FilterIterator.next() -> T | Done
            (Type::FilterIterator(elem_ty), "next") => {
                // Create stack slot for output value (8 bytes for i64)
                let out_slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    8,
                    0,
                ));
                let out_ptr = self
                    .builder
                    .ins()
                    .stack_addr(self.ctx.pointer_type, out_slot, 0);

                // Call runtime: has_value = vole_filter_iter_next(iter, out_ptr)
                let has_value =
                    self.call_runtime("vole_filter_iter_next", &[obj.value, out_ptr])?;

                // Load value from out_slot
                let value = self.builder.ins().stack_load(types::I64, out_slot, 0);

                // Build union result: T | Done
                // Union layout: [tag:1][padding:7][payload:8] = 16 bytes
                // Tag 0 = element type (T), Tag 1 = Done
                let union_type = Type::Union(vec![*elem_ty.clone(), Type::Done]);
                let union_size = 16u32; // tag(1) + padding(7) + payload(8)
                let union_slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    union_size,
                    0,
                ));

                // Determine tag based on has_value:
                // has_value != 0 => tag = 0 (element type)
                // has_value == 0 => tag = 1 (Done)
                let zero = self.builder.ins().iconst(types::I64, 0);
                let is_done = self.builder.ins().icmp(IntCC::Equal, has_value, zero);
                let tag_done = self.builder.ins().iconst(types::I8, 1);
                let tag_value = self.builder.ins().iconst(types::I8, 0);
                let tag = self.builder.ins().select(is_done, tag_done, tag_value);

                // Store tag at offset 0
                self.builder.ins().stack_store(tag, union_slot, 0);

                // Store payload at offset 8 (value if has_value, 0 if done)
                self.builder.ins().stack_store(value, union_slot, 8);

                let union_ptr = self
                    .builder
                    .ins()
                    .stack_addr(self.ctx.pointer_type, union_slot, 0);
                Ok(Some(CompiledValue {
                    value: union_ptr,
                    ty: self.ctx.pointer_type,
                    vole_type: union_type,
                }))
            }
            // FilterIterator.collect() -> [T]
            (Type::FilterIterator(elem_ty), "collect") => {
                let result = self.call_runtime("vole_filter_iter_collect", &[obj.value])?;
                Ok(Some(CompiledValue {
                    value: result,
                    ty: self.ctx.pointer_type,
                    vole_type: Type::Array(elem_ty.clone()),
                }))
            }
            // TakeIterator.next() -> T | Done
            (Type::TakeIterator(elem_ty), "next") => {
                let out_slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    8,
                    0,
                ));
                let out_ptr = self
                    .builder
                    .ins()
                    .stack_addr(self.ctx.pointer_type, out_slot, 0);

                let has_value = self.call_runtime("vole_take_iter_next", &[obj.value, out_ptr])?;

                let value = self.builder.ins().stack_load(types::I64, out_slot, 0);

                let union_type = Type::Union(vec![*elem_ty.clone(), Type::Done]);
                let union_size = 16u32;
                let union_slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    union_size,
                    0,
                ));

                let zero = self.builder.ins().iconst(types::I64, 0);
                let is_done = self.builder.ins().icmp(IntCC::Equal, has_value, zero);
                let tag_done = self.builder.ins().iconst(types::I8, 1);
                let tag_value = self.builder.ins().iconst(types::I8, 0);
                let tag = self.builder.ins().select(is_done, tag_done, tag_value);

                self.builder.ins().stack_store(tag, union_slot, 0);
                self.builder.ins().stack_store(value, union_slot, 8);

                let union_ptr = self
                    .builder
                    .ins()
                    .stack_addr(self.ctx.pointer_type, union_slot, 0);
                Ok(Some(CompiledValue {
                    value: union_ptr,
                    ty: self.ctx.pointer_type,
                    vole_type: union_type,
                }))
            }
            // TakeIterator.collect() -> [T]
            (Type::TakeIterator(elem_ty), "collect") => {
                let result = self.call_runtime("vole_take_iter_collect", &[obj.value])?;
                Ok(Some(CompiledValue {
                    value: result,
                    ty: self.ctx.pointer_type,
                    vole_type: Type::Array(elem_ty.clone()),
                }))
            }
            // SkipIterator.next() -> T | Done
            (Type::SkipIterator(elem_ty), "next") => {
                let out_slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    8,
                    0,
                ));
                let out_ptr = self
                    .builder
                    .ins()
                    .stack_addr(self.ctx.pointer_type, out_slot, 0);

                let has_value = self.call_runtime("vole_skip_iter_next", &[obj.value, out_ptr])?;

                let value = self.builder.ins().stack_load(types::I64, out_slot, 0);

                let union_type = Type::Union(vec![*elem_ty.clone(), Type::Done]);
                let union_size = 16u32;
                let union_slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    union_size,
                    0,
                ));

                let zero = self.builder.ins().iconst(types::I64, 0);
                let is_done = self.builder.ins().icmp(IntCC::Equal, has_value, zero);
                let tag_done = self.builder.ins().iconst(types::I8, 1);
                let tag_value = self.builder.ins().iconst(types::I8, 0);
                let tag = self.builder.ins().select(is_done, tag_done, tag_value);

                self.builder.ins().stack_store(tag, union_slot, 0);
                self.builder.ins().stack_store(value, union_slot, 8);

                let union_ptr = self
                    .builder
                    .ins()
                    .stack_addr(self.ctx.pointer_type, union_slot, 0);
                Ok(Some(CompiledValue {
                    value: union_ptr,
                    ty: self.ctx.pointer_type,
                    vole_type: union_type,
                }))
            }
            // SkipIterator.collect() -> [T]
            (Type::SkipIterator(elem_ty), "collect") => {
                let result = self.call_runtime("vole_skip_iter_collect", &[obj.value])?;
                Ok(Some(CompiledValue {
                    value: result,
                    ty: self.ctx.pointer_type,
                    vole_type: Type::Array(elem_ty.clone()),
                }))
            }
            // Iterator.count() -> i64 (works on any iterator type)
            (Type::Iterator(_), "count")
            | (Type::MapIterator(_), "count")
            | (Type::FilterIterator(_), "count")
            | (Type::TakeIterator(_), "count")
            | (Type::SkipIterator(_), "count") => {
                let result = self.call_runtime("vole_iter_count", &[obj.value])?;
                Ok(Some(self.i64_value(result)))
            }
            // Iterator.sum() -> i64 (works on numeric iterators)
            (Type::Iterator(_), "sum")
            | (Type::MapIterator(_), "sum")
            | (Type::FilterIterator(_), "sum")
            | (Type::TakeIterator(_), "sum")
            | (Type::SkipIterator(_), "sum") => {
                let result = self.call_runtime("vole_iter_sum", &[obj.value])?;
                Ok(Some(self.i64_value(result)))
            }
            (Type::String, "length") => {
                let result = self.call_runtime("vole_string_len", &[obj.value])?;
                Ok(Some(self.i64_value(result)))
            }
            _ => Ok(None),
        }
    }

    /// Handle Iterator.map(fn) -> creates a MapIterator
    fn iterator_map(
        &mut self,
        iter_obj: &CompiledValue,
        _elem_ty: &Type,
        args: &[Expr],
    ) -> Result<CompiledValue, String> {
        if args.len() != 1 {
            return Err(format!("map expects 1 argument, got {}", args.len()));
        }

        // Compile the transform function (should be a lambda/closure)
        let transform = self.expr(&args[0])?;

        // The transform should be a function
        let (output_type, is_closure) = match &transform.vole_type {
            Type::Function(ft) => ((*ft.return_type).clone(), ft.is_closure),
            _ => {
                return Err(format!(
                    "map argument must be a function, got {:?}",
                    transform.vole_type
                ));
            }
        };

        // If it's a pure function (not a closure), wrap it in a closure structure
        // so the runtime can uniformly call it as a closure
        let closure_ptr = if is_closure {
            transform.value
        } else {
            // Wrap pure function in a closure with 0 captures
            let zero = self.builder.ins().iconst(types::I64, 0);
            self.call_runtime("vole_closure_alloc", &[transform.value, zero])?
        };

        // Call vole_map_iter(source_iter, transform_closure)
        let result = self.call_runtime("vole_map_iter", &[iter_obj.value, closure_ptr])?;

        Ok(CompiledValue {
            value: result,
            ty: self.ctx.pointer_type,
            vole_type: Type::MapIterator(Box::new(output_type)),
        })
    }

    /// Handle Iterator.filter(fn) -> creates a FilterIterator
    fn iterator_filter(
        &mut self,
        iter_obj: &CompiledValue,
        elem_ty: &Type,
        args: &[Expr],
    ) -> Result<CompiledValue, String> {
        if args.len() != 1 {
            return Err(format!("filter expects 1 argument, got {}", args.len()));
        }

        // Compile the predicate function (should be a lambda/closure)
        let predicate = self.expr(&args[0])?;

        // The predicate should be a function returning bool
        let is_closure = match &predicate.vole_type {
            Type::Function(ft) => ft.is_closure,
            _ => {
                return Err(format!(
                    "filter argument must be a function, got {:?}",
                    predicate.vole_type
                ));
            }
        };

        // If it's a pure function (not a closure), wrap it in a closure structure
        // so the runtime can uniformly call it as a closure
        let closure_ptr = if is_closure {
            predicate.value
        } else {
            // Wrap pure function in a closure with 0 captures
            let zero = self.builder.ins().iconst(types::I64, 0);
            self.call_runtime("vole_closure_alloc", &[predicate.value, zero])?
        };

        // Call vole_filter_iter(source_iter, predicate_closure)
        let result = self.call_runtime("vole_filter_iter", &[iter_obj.value, closure_ptr])?;

        // FilterIterator preserves element type
        Ok(CompiledValue {
            value: result,
            ty: self.ctx.pointer_type,
            vole_type: Type::FilterIterator(Box::new(elem_ty.clone())),
        })
    }

    /// Handle Iterator.take(n) -> creates a TakeIterator
    fn iterator_take(
        &mut self,
        iter_obj: &CompiledValue,
        elem_ty: &Type,
        args: &[Expr],
    ) -> Result<CompiledValue, String> {
        if args.len() != 1 {
            return Err(format!("take expects 1 argument, got {}", args.len()));
        }

        // Compile the count argument (should be an integer)
        let count = self.expr(&args[0])?;

        // Call vole_take_iter(source_iter, count)
        let result = self.call_runtime("vole_take_iter", &[iter_obj.value, count.value])?;

        // TakeIterator preserves element type
        Ok(CompiledValue {
            value: result,
            ty: self.ctx.pointer_type,
            vole_type: Type::TakeIterator(Box::new(elem_ty.clone())),
        })
    }

    /// Handle Iterator.skip(n) -> creates a SkipIterator
    fn iterator_skip(
        &mut self,
        iter_obj: &CompiledValue,
        elem_ty: &Type,
        args: &[Expr],
    ) -> Result<CompiledValue, String> {
        if args.len() != 1 {
            return Err(format!("skip expects 1 argument, got {}", args.len()));
        }

        // Compile the count argument (should be an integer)
        let count = self.expr(&args[0])?;

        // Call vole_skip_iter(source_iter, count)
        let result = self.call_runtime("vole_skip_iter", &[iter_obj.value, count.value])?;

        // SkipIterator preserves element type
        Ok(CompiledValue {
            value: result,
            ty: self.ctx.pointer_type,
            vole_type: Type::SkipIterator(Box::new(elem_ty.clone())),
        })
    }

    /// Handle Iterator.for_each(fn) -> calls function for each element, returns void
    fn iterator_for_each(
        &mut self,
        iter_obj: &CompiledValue,
        args: &[Expr],
    ) -> Result<CompiledValue, String> {
        if args.len() != 1 {
            return Err(format!("for_each expects 1 argument, got {}", args.len()));
        }

        // Compile the callback function (should be a lambda/closure)
        let callback = self.expr(&args[0])?;

        // The callback should be a function
        let is_closure = match &callback.vole_type {
            Type::Function(ft) => ft.is_closure,
            _ => {
                return Err(format!(
                    "for_each argument must be a function, got {:?}",
                    callback.vole_type
                ));
            }
        };

        // If it's a pure function (not a closure), wrap it in a closure structure
        // so the runtime can uniformly call it as a closure
        let closure_ptr = if is_closure {
            callback.value
        } else {
            // Wrap pure function in a closure with 0 captures
            let zero = self.builder.ins().iconst(types::I64, 0);
            self.call_runtime("vole_closure_alloc", &[callback.value, zero])?
        };

        // Call vole_iter_for_each(iter, callback_closure)
        self.call_runtime_void("vole_iter_for_each", &[iter_obj.value, closure_ptr])?;

        // for_each returns void
        Ok(self.void_value())
    }

    /// Handle Iterator.reduce(init, fn) -> reduces iterator to single value
    fn iterator_reduce(
        &mut self,
        iter_obj: &CompiledValue,
        args: &[Expr],
    ) -> Result<CompiledValue, String> {
        if args.len() != 2 {
            return Err(format!("reduce expects 2 arguments, got {}", args.len()));
        }

        // Compile the initial value
        let init = self.expr(&args[0])?;

        // Compile the reducer function (should be a lambda/closure)
        let reducer = self.expr(&args[1])?;

        // The reducer should be a function
        let is_closure = match &reducer.vole_type {
            Type::Function(ft) => ft.is_closure,
            _ => {
                return Err(format!(
                    "reduce argument must be a function, got {:?}",
                    reducer.vole_type
                ));
            }
        };

        // If it's a pure function (not a closure), wrap it in a closure structure
        // so the runtime can uniformly call it as a closure
        let closure_ptr = if is_closure {
            reducer.value
        } else {
            // Wrap pure function in a closure with 0 captures
            let zero = self.builder.ins().iconst(types::I64, 0);
            self.call_runtime("vole_closure_alloc", &[reducer.value, zero])?
        };

        // Call vole_iter_reduce(iter, init, reducer_closure)
        let result = self.call_runtime(
            "vole_iter_reduce",
            &[iter_obj.value, init.value, closure_ptr],
        )?;

        // reduce returns the same type as init
        Ok(CompiledValue {
            value: result,
            ty: init.ty,
            vole_type: init.vole_type,
        })
    }

    /// Call a functional interface as a closure or pure function
    fn functional_interface_call(
        &mut self,
        func_ptr_or_closure: Value,
        func_type: FunctionType,
        mc: &MethodCallExpr,
    ) -> Result<CompiledValue, String> {
        // Check if this is actually a closure or a pure function
        // The FunctionType passed in has is_closure set from the analyzer,
        // but we need to handle both cases since the underlying lambda
        // might be pure (no captures) or a closure (has captures).
        //
        // The actual calling convention is determined by whether the
        // lambda had captures, which we track via the FunctionType.
        // Since functional interfaces can hold either, we need to check
        // both cases at runtime... BUT for now, since we're compiling
        // statically, we trust the func_type.is_closure flag.
        //
        // Note: The issue is that functional interfaces always mark is_closure: true
        // in the analyzer, but the actual lambda might be pure. We need to
        // check the object's actual type to determine this.
        //
        // For now, trust that pure functions (is_closure=false) are called directly.
        if func_type.is_closure {
            // It's a closure - extract function pointer and pass closure
            let func_ptr = self.call_runtime("vole_closure_get_func", &[func_ptr_or_closure])?;

            // Build the Cranelift signature for the closure call
            // First param is the closure pointer, then the user params
            let mut sig = self.ctx.module.make_signature();
            sig.params.push(AbiParam::new(self.ctx.pointer_type)); // Closure pointer
            for param_type in &func_type.params {
                sig.params.push(AbiParam::new(type_to_cranelift(
                    param_type,
                    self.ctx.pointer_type,
                )));
            }
            if func_type.return_type.as_ref() != &Type::Void {
                sig.returns.push(AbiParam::new(type_to_cranelift(
                    &func_type.return_type,
                    self.ctx.pointer_type,
                )));
            }

            let sig_ref = self.builder.import_signature(sig);

            // Compile arguments - closure pointer first, then user args
            let mut args = vec![func_ptr_or_closure];
            for arg in &mc.args {
                let compiled = self.expr(arg)?;
                args.push(compiled.value);
            }

            // Perform the indirect call
            let call_inst = self.builder.ins().call_indirect(sig_ref, func_ptr, &args);
            let results = self.builder.inst_results(call_inst);

            if results.is_empty() {
                Ok(self.void_value())
            } else {
                Ok(CompiledValue {
                    value: results[0],
                    ty: type_to_cranelift(&func_type.return_type, self.ctx.pointer_type),
                    vole_type: (*func_type.return_type).clone(),
                })
            }
        } else {
            // It's a pure function - call directly
            let mut sig = self.ctx.module.make_signature();
            for param_type in &func_type.params {
                sig.params.push(AbiParam::new(type_to_cranelift(
                    param_type,
                    self.ctx.pointer_type,
                )));
            }
            if func_type.return_type.as_ref() != &Type::Void {
                sig.returns.push(AbiParam::new(type_to_cranelift(
                    &func_type.return_type,
                    self.ctx.pointer_type,
                )));
            }

            let sig_ref = self.builder.import_signature(sig);

            let mut args = Vec::new();
            for arg in &mc.args {
                let compiled = self.expr(arg)?;
                args.push(compiled.value);
            }

            let call_inst = self
                .builder
                .ins()
                .call_indirect(sig_ref, func_ptr_or_closure, &args);
            let results = self.builder.inst_results(call_inst);

            if results.is_empty() {
                Ok(self.void_value())
            } else {
                Ok(CompiledValue {
                    value: results[0],
                    ty: type_to_cranelift(&func_type.return_type, self.ctx.pointer_type),
                    vole_type: (*func_type.return_type).clone(),
                })
            }
        }
    }
}
