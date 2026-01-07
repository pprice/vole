// src/codegen/structs/methods.rs

use cranelift::prelude::*;
use cranelift_module::Module;

use super::helpers::get_type_name_symbol;
use crate::codegen::RuntimeFn;
use crate::codegen::context::Cg;
use crate::codegen::types::{
    CompiledValue, display_type, method_name_id, module_name_id, type_to_cranelift,
};
use crate::frontend::{Expr, MethodCallExpr, NodeId};
use crate::sema::implement_registry::TypeId;
use crate::sema::resolution::ResolvedMethod;
use crate::sema::{FunctionType, Type};

impl Cg<'_, '_, '_> {
    pub fn method_call(
        &mut self,
        mc: &MethodCallExpr,
        expr_id: NodeId,
    ) -> Result<CompiledValue, String> {
        let display_type = |ty: &Type| display_type(self.ctx.analyzed, self.ctx.interner, ty);
        let display_type_symbol = |sym: crate::frontend::Symbol| {
            self.ctx
                .type_metadata
                .get(&sym)
                .and_then(|meta| match &meta.vole_type {
                    Type::Class(class_type) => Some(class_type.name_id),
                    Type::Record(record_type) => Some(record_type.name_id),
                    _ => None,
                })
                .map(|name_id| {
                    self.ctx
                        .analyzed
                        .name_table
                        .display(name_id, self.ctx.interner)
                })
                .unwrap_or_else(|| self.ctx.interner.resolve(sym).to_string())
        };

        let obj = self.expr(&mc.object)?;
        let method_name_str = self.ctx.interner.resolve(mc.method);

        // Handle module method calls (e.g., math.sqrt(16.0), math.lerp(...))
        // These go to either external native functions or pure Vole module functions
        if let Type::Module(ref module_type) = obj.vole_type {
            let module_path = self
                .ctx
                .analyzed
                .name_table
                .module_path(module_type.module_id);
            let name_id = module_name_id(self.ctx.analyzed, module_type.module_id, method_name_str);
            // Get the method resolution
            let resolution = self.ctx.analyzed.method_resolutions.get(expr_id);
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
                    let name_id = name_id.ok_or_else(|| {
                        format!(
                            "Module method {}::{} not interned",
                            module_path, method_name_str
                        )
                    })?;
                    let func_key = self.ctx.func_registry.intern_name_id(name_id);
                    let func_id = self.ctx.func_registry.func_id(func_key).ok_or_else(|| {
                        format!(
                            "Module function {}::{} not found",
                            module_path, method_name_str
                        )
                    })?;
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
                    module_path, method_name_str
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

        let method_id = method_name_id(self.ctx.analyzed, self.ctx.interner, mc.method)
            .ok_or_else(|| {
                format!(
                    "codegen error: method name not interned (method: {})",
                    method_name_str
                )
            })?;

        // Look up method resolution to determine naming convention and return type
        // If no resolution exists (e.g., inside default method bodies), fall back to type-based lookup
        let resolution = self.ctx.analyzed.method_resolutions.get(expr_id);

        // Determine the method function target based on resolution type
        let (method_info, return_type) = if let Some(resolution) = resolution {
            match resolution {
                ResolvedMethod::Direct { func_type } => {
                    // Direct method on class/record: use TypeName_methodName
                    let type_name = get_type_name_symbol(&obj.vole_type)?;
                    let info = self
                        .ctx
                        .type_metadata
                        .get(&type_name)
                        .and_then(|meta| meta.method_infos.get(&method_id))
                        .cloned()
                        .ok_or_else(|| {
                            format!(
                                "Method {} not found on type {}",
                                method_name_str,
                                display_type_symbol(type_name)
                            )
                        })?;
                    (Some(info), (*func_type.return_type).clone())
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
                    let type_id = TypeId::from_type(&obj.vole_type, &self.ctx.analyzed.type_table);
                    let info = type_id
                        .and_then(|type_id| self.ctx.impl_method_infos.get(&(type_id, method_id)))
                        .cloned();
                    (info, (*func_type.return_type).clone())
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
                    let info = self
                        .ctx
                        .type_metadata
                        .get(type_name)
                        .and_then(|meta| meta.method_infos.get(&method_id))
                        .cloned()
                        .ok_or_else(|| {
                            format!(
                                "Method {} not found on type {}",
                                method_name_str,
                                display_type_symbol(*type_name)
                            )
                        })?;
                    (Some(info), (*func_type.return_type).clone())
                }
            }
        } else {
            // No resolution found - try to resolve directly from object type
            // This handles method calls inside default method bodies where sema
            // doesn't analyze the interface body
            let type_name = get_type_name_symbol(&obj.vole_type)?;

            let info = self
                .ctx
                .type_metadata
                .get(&type_name)
                .and_then(|meta| meta.method_infos.get(&method_id))
                .cloned()
                .ok_or_else(|| {
                    format!(
                        "Method {} not found on type {}",
                        method_name_str,
                        display_type_symbol(type_name)
                    )
                })?;
            let return_type = info.return_type.clone();
            (Some(info), return_type)
        };

        let method_info = method_info.ok_or_else(|| {
            format!(
                "Unknown method {} on {}",
                method_name_str,
                display_type(&obj.vole_type)
            )
        })?;
        let method_func_ref = self.func_ref(method_info.func_key)?;

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

    fn builtin_method(
        &mut self,
        obj: &CompiledValue,
        method_name: &str,
    ) -> Result<Option<CompiledValue>, String> {
        match (&obj.vole_type, method_name) {
            (Type::Array(_), "length") => {
                let result = self.call_runtime(RuntimeFn::ArrayLen, &[obj.value])?;
                Ok(Some(self.i64_value(result)))
            }
            (Type::Array(elem_ty), "iter") => {
                let result = self.call_runtime(RuntimeFn::ArrayIter, &[obj.value])?;
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
                let has_value =
                    self.call_runtime(RuntimeFn::ArrayIterNext, &[obj.value, out_ptr])?;

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
                let result = self.call_runtime(RuntimeFn::ArrayIterCollect, &[obj.value])?;
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
                let has_value = self.call_runtime(RuntimeFn::MapIterNext, &[obj.value, out_ptr])?;

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
                let result = self.call_runtime(RuntimeFn::MapIterCollect, &[obj.value])?;
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
                    self.call_runtime(RuntimeFn::FilterIterNext, &[obj.value, out_ptr])?;

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
                let result = self.call_runtime(RuntimeFn::FilterIterCollect, &[obj.value])?;
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

                let has_value =
                    self.call_runtime(RuntimeFn::TakeIterNext, &[obj.value, out_ptr])?;

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
                let result = self.call_runtime(RuntimeFn::TakeIterCollect, &[obj.value])?;
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

                let has_value =
                    self.call_runtime(RuntimeFn::SkipIterNext, &[obj.value, out_ptr])?;

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
                let result = self.call_runtime(RuntimeFn::SkipIterCollect, &[obj.value])?;
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
                let result = self.call_runtime(RuntimeFn::IterCount, &[obj.value])?;
                Ok(Some(self.i64_value(result)))
            }
            // Iterator.sum() -> i64 (works on numeric iterators)
            (Type::Iterator(_), "sum")
            | (Type::MapIterator(_), "sum")
            | (Type::FilterIterator(_), "sum")
            | (Type::TakeIterator(_), "sum")
            | (Type::SkipIterator(_), "sum") => {
                let result = self.call_runtime(RuntimeFn::IterSum, &[obj.value])?;
                Ok(Some(self.i64_value(result)))
            }
            (Type::String, "length") => {
                let result = self.call_runtime(RuntimeFn::StringLen, &[obj.value])?;
                Ok(Some(self.i64_value(result)))
            }
            _ => Ok(None),
        }
    }

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
            self.call_runtime(RuntimeFn::ClosureAlloc, &[transform.value, zero])?
        };

        // Call vole_map_iter(source_iter, transform_closure)
        let result = self.call_runtime(RuntimeFn::MapIter, &[iter_obj.value, closure_ptr])?;

        Ok(CompiledValue {
            value: result,
            ty: self.ctx.pointer_type,
            vole_type: Type::MapIterator(Box::new(output_type)),
        })
    }

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
            self.call_runtime(RuntimeFn::ClosureAlloc, &[predicate.value, zero])?
        };

        // Call vole_filter_iter(source_iter, predicate_closure)
        let result = self.call_runtime(RuntimeFn::FilterIter, &[iter_obj.value, closure_ptr])?;

        // FilterIterator preserves element type
        Ok(CompiledValue {
            value: result,
            ty: self.ctx.pointer_type,
            vole_type: Type::FilterIterator(Box::new(elem_ty.clone())),
        })
    }

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
        let result = self.call_runtime(RuntimeFn::TakeIter, &[iter_obj.value, count.value])?;

        // TakeIterator preserves element type
        Ok(CompiledValue {
            value: result,
            ty: self.ctx.pointer_type,
            vole_type: Type::TakeIterator(Box::new(elem_ty.clone())),
        })
    }

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
        let result = self.call_runtime(RuntimeFn::SkipIter, &[iter_obj.value, count.value])?;

        // SkipIterator preserves element type
        Ok(CompiledValue {
            value: result,
            ty: self.ctx.pointer_type,
            vole_type: Type::SkipIterator(Box::new(elem_ty.clone())),
        })
    }

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
            self.call_runtime(RuntimeFn::ClosureAlloc, &[callback.value, zero])?
        };

        // Call vole_iter_for_each(iter, callback_closure)
        self.call_runtime_void(RuntimeFn::IterForEach, &[iter_obj.value, closure_ptr])?;

        // for_each returns void
        Ok(self.void_value())
    }

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
            self.call_runtime(RuntimeFn::ClosureAlloc, &[reducer.value, zero])?
        };

        // Call vole_iter_reduce(iter, init, reducer_closure)
        let result = self.call_runtime(
            RuntimeFn::IterReduce,
            &[iter_obj.value, init.value, closure_ptr],
        )?;

        // reduce returns the same type as init
        Ok(CompiledValue {
            value: result,
            ty: init.ty,
            vole_type: init.vole_type,
        })
    }

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
            let func_ptr = self.call_runtime(RuntimeFn::ClosureGetFunc, &[func_ptr_or_closure])?;

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
