// src/codegen/structs/methods.rs

use cranelift::prelude::*;
use cranelift_module::Module;
use smallvec::{SmallVec, smallvec};

use crate::codegen::RuntimeFn;

/// SmallVec for call arguments - most calls have <= 8 args
type ArgVec = SmallVec<[Value; 8]>;
use crate::codegen::context::Cg;
use crate::codegen::interface_vtable::box_interface_value;
use crate::codegen::method_resolution::{
    MethodResolutionInput, MethodTarget, resolve_method_target,
};
use crate::codegen::types::{
    CompiledValue, module_name_id, type_size, type_to_cranelift, value_to_word, word_to_value,
};
use crate::errors::CodegenError;
use crate::frontend::{Expr, ExprKind, MethodCallExpr, NodeId, Symbol};
use crate::identity::NamerLookup;
use crate::identity::{MethodId, NameId, TypeDefId};
use crate::sema::generic::substitute_type;
use crate::sema::resolution::ResolvedMethod;
use crate::sema::{FunctionType, Type};

impl Cg<'_, '_, '_> {
    /// Look up a method NameId using the context's interner (which may be a module interner)
    fn method_name_id(&self, name: Symbol) -> NameId {
        let namer = NamerLookup::new(&self.ctx.analyzed.name_table, self.ctx.interner);
        namer.method(name).unwrap_or_else(|| {
            panic!(
                "method name_id not found for '{}'",
                self.ctx.interner.resolve(name)
            )
        })
    }

    #[tracing::instrument(skip(self, mc), fields(method = %self.ctx.interner.resolve(mc.method)))]
    pub fn method_call(
        &mut self,
        mc: &MethodCallExpr,
        expr_id: NodeId,
    ) -> Result<CompiledValue, String> {
        // Check for static method call FIRST - don't try to compile the receiver
        if let Some(ResolvedMethod::Static {
            type_def_id,
            method_id,
            func_type,
        }) = self
            .ctx
            .analyzed
            .query()
            .method_at_in_module(expr_id, self.ctx.current_module)
        {
            return self.static_method_call(
                *type_def_id,
                *method_id,
                func_type.clone(),
                mc,
                expr_id,
            );
        }

        // Handle range.iter() specially since range expressions can't be compiled to values directly
        if let ExprKind::Range(range) = &mc.object.kind {
            let method_name = self.ctx.interner.resolve(mc.method);
            if method_name == "iter" {
                return self.range_iter(range);
            }
        }

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
            let resolution = self
                .ctx
                .analyzed
                .query()
                .method_at_in_module(expr_id, self.ctx.current_module);
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
                return Err(CodegenError::not_found(
                    "module method",
                    format!("{}::{}", module_path, method_name_str),
                )
                .into());
            }
        }

        // Handle built-in methods
        if let Some(result) = self.builtin_method(&obj, method_name_str)? {
            return Ok(result);
        }

        // Handle RuntimeIterator methods - these call external functions directly
        // without interface boxing or vtable dispatch
        if let Type::RuntimeIterator(elem_ty) = &obj.vole_type {
            return self.runtime_iterator_method(&obj, mc, method_name_str, elem_ty);
        }

        let method_id = self.method_name_id(mc.method);

        // Look up method resolution to determine naming convention and return type
        // If no resolution exists (e.g., inside default method bodies), fall back to type-based lookup
        // In monomorphized context, skip sema resolution because it was computed for the type parameter,
        // not the concrete type. Let resolve_method_target do dynamic resolution based on object_type.
        let resolution = if self.ctx.type_substitutions.is_some() {
            None
        } else {
            self.ctx
                .analyzed
                .query()
                .method_at_in_module(expr_id, self.ctx.current_module)
        };

        tracing::debug!(
            obj_type = ?obj.vole_type,
            method = %method_name_str,
            resolution = ?resolution,
            "method call"
        );

        let target = resolve_method_target(MethodResolutionInput {
            analyzed: self.ctx.analyzed,
            type_metadata: self.ctx.type_metadata,
            impl_method_infos: self.ctx.impl_method_infos,
            method_name_str,
            object_type: &obj.vole_type,
            method_id,
            resolution,
        })?;

        let (method_info, return_type) = match target {
            MethodTarget::FunctionalInterface { func_type } => {
                // Use TypeDefId directly for EntityRegistry-based dispatch
                if let Type::Interface(interface_type) = &obj.vole_type {
                    let method_name_id = self.method_name_id(mc.method);
                    return self.interface_dispatch_call_args_by_type_def_id(
                        &obj,
                        &mc.args,
                        interface_type.type_def_id,
                        method_name_id,
                        func_type,
                    );
                }
                // For functional interfaces, the object holds the function ptr or closure
                // The actual is_closure status depends on the lambda's compilation.
                let is_closure = if let Type::Function(ft) = &obj.vole_type {
                    ft.is_closure
                } else {
                    func_type.is_closure
                };
                let actual_func_type = FunctionType {
                    params: func_type.params.clone(),
                    return_type: Box::new((*func_type.return_type).clone()),
                    is_closure,
                };
                return self.functional_interface_call(obj.value, actual_func_type, mc);
            }
            MethodTarget::External {
                external_info,
                return_type,
            } => {
                let param_types = resolution.map(|resolved| resolved.func_type().params.clone());
                let mut args: ArgVec = smallvec![obj.value];
                if let Some(param_types) = &param_types {
                    for (arg, param_type) in mc.args.iter().zip(param_types.iter()) {
                        let compiled = self.expr(arg)?;
                        let compiled = if matches!(param_type, Type::Interface(_)) {
                            box_interface_value(self.builder, self.ctx, compiled, param_type)?
                        } else {
                            compiled
                        };
                        args.push(compiled.value);
                    }
                } else {
                    for arg in &mc.args {
                        let compiled = self.expr(arg)?;
                        args.push(compiled.value);
                    }
                }
                // Convert Iterator return types to RuntimeIterator for external methods
                let return_type = self.maybe_convert_iterator_return_type(return_type);
                return self.call_external(&external_info, &args, &return_type);
            }
            MethodTarget::InterfaceDispatch {
                interface_type_id,
                method_name_id,
                func_type,
            } => {
                return self.interface_dispatch_call_args_by_type_def_id(
                    &obj,
                    &mc.args,
                    interface_type_id,
                    method_name_id,
                    func_type,
                );
            }
            MethodTarget::StaticMethod { .. } => {
                // Static method calls are handled early in method_call() before resolve_method_target
                // This branch should never be reached
                unreachable!("Static method calls should be handled early in method_call()")
            }
            MethodTarget::Direct {
                method_info,
                return_type,
            }
            | MethodTarget::Implemented {
                method_info,
                return_type,
            }
            | MethodTarget::Default {
                method_info,
                return_type,
            } => (method_info, return_type),
        };

        // Check if this is a monomorphized class method call
        // If so, use the monomorphized method's func_key instead
        let (method_func_ref, is_generic_class) = if let Some(monomorph_key) = self
            .ctx
            .analyzed
            .expression_data
            .get_class_method_generic(expr_id)
        {
            // Look up the monomorphized instance
            if let Some(instance) = self
                .ctx
                .analyzed
                .entity_registry
                .class_method_monomorph_cache
                .get(monomorph_key)
            {
                let func_key = self.ctx.func_registry.intern_name_id(instance.mangled_name);
                // Monomorphized methods have concrete types, no i64 conversion needed
                (self.func_ref(func_key)?, false)
            } else {
                // Fallback to regular method if monomorph not found
                (self.func_ref(method_info.func_key)?, false)
            }
        } else {
            // Not a monomorphized class method, use regular dispatch
            let is_generic_class =
                matches!(&obj.vole_type, Type::Class(c) if !c.type_args.is_empty());
            (self.func_ref(method_info.func_key)?, is_generic_class)
        };

        let param_types = resolution.map(|resolved| resolved.func_type().params.clone());
        let mut args: ArgVec = smallvec![obj.value];
        if let Some(param_types) = &param_types {
            for (arg, param_type) in mc.args.iter().zip(param_types.iter()) {
                let compiled = self.expr(arg)?;
                let compiled = if matches!(param_type, Type::Interface(_)) {
                    box_interface_value(self.builder, self.ctx, compiled, param_type)?
                } else {
                    compiled
                };

                // Generic class methods expect i64 for TypeParam, convert if needed
                let arg_value = if is_generic_class && compiled.ty != types::I64 {
                    value_to_word(
                        self.builder,
                        &compiled,
                        self.ctx.pointer_type,
                        None, // No heap alloc needed for primitive conversions
                    )?
                } else {
                    compiled.value
                };
                args.push(arg_value);
            }
        } else {
            for arg in &mc.args {
                let compiled = self.expr(arg)?;
                // Generic class methods expect i64 for TypeParam, convert if needed
                let arg_value = if is_generic_class && compiled.ty != types::I64 {
                    value_to_word(
                        self.builder,
                        &compiled,
                        self.ctx.pointer_type,
                        None, // No heap alloc needed for primitive conversions
                    )?
                } else {
                    compiled.value
                };
                args.push(arg_value);
            }
        }

        let call = self.builder.ins().call(method_func_ref, &args);
        let results = self.builder.inst_results(call);

        if results.is_empty() {
            Ok(self.void_value())
        } else {
            // Generic methods are compiled with TypeParam -> i64, but we may need
            // a different type (f64, bool, etc). Convert using word_to_value.
            let expected_ty = type_to_cranelift(&return_type, self.ctx.pointer_type);
            let actual_result = results[0];
            let actual_ty = self.builder.func.dfg.value_type(actual_result);

            let result_value = if actual_ty != expected_ty && actual_ty == types::I64 {
                // Method returned i64 (TypeParam) but we expect a different type
                word_to_value(
                    self.builder,
                    actual_result,
                    &return_type,
                    self.ctx.pointer_type,
                )
            } else {
                actual_result
            };

            // For Union return types, the callee returns a pointer to its stack memory
            // which becomes invalid after the call. Copy the union to our own stack.
            let (final_value, final_type) = if matches!(&return_type, Type::Union(_)) {
                let union_size = type_size(&return_type, self.ctx.pointer_type);
                let local_slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    union_size,
                    0,
                ));

                // Copy tag (8 bytes at offset 0) and value (8 bytes at offset 8)
                let tag = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), result_value, 0);
                self.builder.ins().stack_store(tag, local_slot, 0);

                let payload = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), result_value, 8);
                self.builder.ins().stack_store(payload, local_slot, 8);

                let local_ptr = self
                    .builder
                    .ins()
                    .stack_addr(self.ctx.pointer_type, local_slot, 0);
                (local_ptr, expected_ty)
            } else {
                (result_value, expected_ty)
            };

            Ok(CompiledValue {
                value: final_value,
                ty: final_type,
                vole_type: return_type,
            })
        }
    }

    /// Compile range.iter() - creates a range iterator from start..end
    fn range_iter(&mut self, range: &crate::frontend::RangeExpr) -> Result<CompiledValue, String> {
        // Compile start and end expressions
        let start = self.expr(&range.start)?;
        let end_val = self.expr(&range.end)?;

        // For inclusive ranges, add 1 to the end (since our iterator is exclusive-end)
        let end_value = if range.inclusive {
            self.builder.ins().iadd_imm(end_val.value, 1)
        } else {
            end_val.value
        };

        // Call vole_range_iter(start, end) -> RuntimeIterator<i64>
        let result = self.call_runtime(RuntimeFn::RangeIter, &[start.value, end_value])?;

        // Return as RuntimeIterator<i64> - concrete type for builtin iterators
        Ok(CompiledValue {
            value: result,
            ty: self.ctx.pointer_type,
            vole_type: Type::RuntimeIterator(Box::new(Type::I64)),
        })
    }

    pub(crate) fn builtin_method(
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
                // Return RuntimeIterator - a concrete type for builtin iterators
                // This avoids interface boxing while still being compatible with Iterator<T>
                Ok(Some(CompiledValue {
                    value: result,
                    ty: self.ctx.pointer_type,
                    vole_type: Type::RuntimeIterator(elem_ty.clone()),
                }))
            }
            (Type::String, "length") => {
                let result = self.call_runtime(RuntimeFn::StringLen, &[obj.value])?;
                Ok(Some(self.i64_value(result)))
            }
            (Type::String, "iter") => {
                let result = self.call_runtime(RuntimeFn::StringCharsIter, &[obj.value])?;
                Ok(Some(CompiledValue {
                    value: result,
                    ty: self.ctx.pointer_type,
                    vole_type: Type::RuntimeIterator(Box::new(Type::String)),
                }))
            }
            (Type::Range, "iter") => {
                // Load start and end from the range struct (pointer to [start, end])
                let start = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), obj.value, 0);
                let end = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), obj.value, 8);
                let result = self.call_runtime(RuntimeFn::RangeIter, &[start, end])?;
                Ok(Some(CompiledValue {
                    value: result,
                    ty: self.ctx.pointer_type,
                    vole_type: Type::RuntimeIterator(Box::new(Type::I64)),
                }))
            }
            _ => Ok(None),
        }
    }

    /// Handle method calls on RuntimeIterator - calls external Iterator functions directly
    fn runtime_iterator_method(
        &mut self,
        obj: &CompiledValue,
        mc: &MethodCallExpr,
        method_name: &str,
        elem_ty: &Type,
    ) -> Result<CompiledValue, String> {
        // Look up the Iterator interface via Resolver
        let iter_type_id = self
            .ctx
            .resolver()
            .resolve_type_str_or_interface("Iterator", &self.ctx.analyzed.entity_registry)
            .ok_or_else(|| "Iterator interface not found in entity registry".to_string())?;

        let iter_def = self.ctx.analyzed.entity_registry.get_type(iter_type_id);

        // Find the method by name
        let method_id = iter_def
            .methods
            .iter()
            .find(|&&mid| {
                let m = self.ctx.analyzed.entity_registry.get_method(mid);
                self.ctx
                    .analyzed
                    .name_table
                    .last_segment_str(m.name_id)
                    .is_some_and(|n| n == method_name)
            })
            .ok_or_else(|| format!("Method {} not found on Iterator", method_name))?;

        let method = self.ctx.analyzed.entity_registry.get_method(*method_id);

        // Get the external binding for this method
        let external_info = self
            .ctx
            .analyzed
            .entity_registry
            .get_external_binding(*method_id)
            .ok_or_else(|| format!("No external binding for Iterator.{}", method_name))?
            .clone();

        // Substitute the element type for T in the return type
        let substitutions: std::collections::HashMap<NameId, Type> = iter_def
            .type_params
            .iter()
            .map(|param| (*param, elem_ty.clone()))
            .collect();
        let return_type = substitute_type(&method.signature.return_type, &substitutions);

        // Convert Iterator<T> return types to RuntimeIterator(T) since the runtime
        // functions return raw iterator pointers, not boxed interface values
        let return_type = self.convert_iterator_return_type(return_type, iter_type_id);

        // Build args: self (iterator ptr) + method args
        let mut args: ArgVec = smallvec![obj.value];
        for arg in &mc.args {
            let compiled = self.expr(arg)?;
            args.push(compiled.value);
        }

        // Call the external function directly
        self.call_external(&external_info, &args, &return_type)
    }

    /// Convert Iterator<T> return types to RuntimeIterator(T)
    ///
    /// When calling external iterator methods, the runtime returns raw iterator pointers,
    /// not boxed interface values. This function converts Interface/GenericInstance types
    /// for Iterator to RuntimeIterator so that subsequent method calls use direct dispatch.
    fn convert_iterator_return_type(&self, ty: Type, iterator_type_id: TypeDefId) -> Type {
        self.convert_iterator_return_type_by_type_def_id(ty, iterator_type_id)
    }

    /// Convert Iterator<T> return types to RuntimeIterator(T), looking up Iterator interface by name
    pub(crate) fn maybe_convert_iterator_return_type(&self, ty: Type) -> Type {
        // Look up the Iterator interface via Resolver
        let iterator_type_id = self
            .ctx
            .resolver()
            .resolve_type_str_or_interface("Iterator", &self.ctx.analyzed.entity_registry);
        if let Some(iterator_type_id) = iterator_type_id {
            self.convert_iterator_return_type_by_type_def_id(ty, iterator_type_id)
        } else {
            ty
        }
    }

    /// Core implementation of iterator return type conversion
    fn convert_iterator_return_type_by_type_def_id(&self, ty: Type, iterator_type_id: TypeDefId) -> Type {
        match &ty {
            // Handle Iterator<T> stored as Interface
            Type::Interface(iface) if iface.type_def_id == iterator_type_id => {
                if let Some(elem_ty) = iface.type_args.first() {
                    Type::RuntimeIterator(Box::new(elem_ty.clone()))
                } else {
                    ty
                }
            }
            // Not an Iterator type, return as-is
            _ => ty,
        }
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
            let mut args: ArgVec = smallvec![func_ptr_or_closure];
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

    /// Dispatch an interface method call by TypeDefId (EntityRegistry-based)
    pub(crate) fn interface_dispatch_call_args_by_type_def_id(
        &mut self,
        obj: &CompiledValue,
        args: &[Expr],
        interface_type_id: TypeDefId,
        method_name_id: NameId,
        func_type: FunctionType,
    ) -> Result<CompiledValue, String> {
        let slot = crate::codegen::interface_vtable::interface_method_slot_by_type_def_id(
            interface_type_id,
            method_name_id,
            &self.ctx.analyzed.entity_registry,
        )?;
        self.interface_dispatch_call_args_inner(obj, args, slot, func_type)
    }

    fn interface_dispatch_call_args_inner(
        &mut self,
        obj: &CompiledValue,
        args: &[Expr],
        slot: usize,
        func_type: FunctionType,
    ) -> Result<CompiledValue, String> {
        let word_type = self.ctx.pointer_type;
        let word_bytes = word_type.bytes() as i32;

        // Load data pointer from boxed interface (first word)
        // Currently unused but kept for interface dispatch debugging
        let _data_word = self
            .builder
            .ins()
            .load(word_type, MemFlags::new(), obj.value, 0);
        let vtable_ptr = self
            .builder
            .ins()
            .load(word_type, MemFlags::new(), obj.value, word_bytes);
        let func_ptr = self.builder.ins().load(
            word_type,
            MemFlags::new(),
            vtable_ptr,
            (slot as i32) * word_bytes,
        );

        tracing::trace!(slot = slot, "interface vtable dispatch");

        let mut sig = self.ctx.module.make_signature();
        sig.params.push(AbiParam::new(word_type));
        for _ in &func_type.params {
            sig.params.push(AbiParam::new(word_type));
        }
        if func_type.return_type.as_ref() != &Type::Void {
            sig.returns.push(AbiParam::new(word_type));
        }
        let sig_ref = self.builder.import_signature(sig);

        let heap_alloc_ref = {
            let key = self
                .ctx
                .func_registry
                .runtime_key(RuntimeFn::HeapAlloc)
                .ok_or_else(|| "heap allocator not registered".to_string())?;
            self.func_ref(key)?
        };

        // Pass the full boxed interface pointer (not just data_word) so wrappers can
        // access both data and vtable. This is needed for Iterator methods that create
        // UnifiedIterator adapters via vole_interface_iter.
        let mut call_args: ArgVec = smallvec![obj.value];
        for arg in args {
            let compiled = self.expr(arg)?;
            let word = value_to_word(self.builder, &compiled, word_type, Some(heap_alloc_ref))?;
            call_args.push(word);
        }

        let call = self
            .builder
            .ins()
            .call_indirect(sig_ref, func_ptr, &call_args);
        let results = self.builder.inst_results(call);

        if func_type.return_type.as_ref() == &Type::Void {
            return Ok(self.void_value());
        }

        let word = results
            .first()
            .copied()
            .ok_or_else(|| "interface call missing return value".to_string())?;
        let value = word_to_value(self.builder, word, &func_type.return_type, word_type);

        // Convert Iterator return types to RuntimeIterator for interface dispatch
        // since external iterator methods return raw iterator pointers, not boxed interfaces
        let return_type = self.maybe_convert_iterator_return_type((*func_type.return_type).clone());

        Ok(CompiledValue {
            value,
            ty: type_to_cranelift(&return_type, word_type),
            vole_type: return_type,
        })
    }

    /// Handle static method call: TypeName.method(args)
    /// Static methods don't have a receiver, so we don't compile the object expression.
    fn static_method_call(
        &mut self,
        type_def_id: TypeDefId,
        method_id: MethodId,
        func_type: FunctionType,
        mc: &MethodCallExpr,
        expr_id: NodeId,
    ) -> Result<CompiledValue, String> {
        // Get the method's name_id for lookup
        let method_def = self.ctx.analyzed.entity_registry.get_method(method_id);
        let method_name_id = method_def.name_id;

        // Check for monomorphized static method (for generic classes)
        if let Some(mono_key) = self.ctx.analyzed.query().static_method_generic_at(expr_id) {
            // Look up the monomorphized instance
            if let Some(instance) = self
                .ctx
                .analyzed
                .entity_registry
                .static_method_monomorph_cache
                .get(mono_key)
            {
                // Compile arguments with substituted param types
                let mut args = Vec::new();
                for (arg, param_ty) in mc.args.iter().zip(instance.func_type.params.iter()) {
                    let compiled = self.expr(arg)?;
                    // Box interface values if needed
                    let compiled = if matches!(param_ty, Type::Interface(_)) {
                        box_interface_value(self.builder, self.ctx, compiled, param_ty)?
                    } else {
                        compiled
                    };
                    args.push(compiled.value);
                }

                // Get monomorphized function reference and call
                let func_key = self.ctx.func_registry.intern_name_id(instance.mangled_name);
                let func_ref = self.func_ref(func_key)?;
                let call = self.builder.ins().call(func_ref, &args);
                let results = self.builder.inst_results(call);

                let return_type = (*instance.func_type.return_type).clone();
                if results.is_empty() {
                    return Ok(self.void_value());
                } else {
                    return Ok(CompiledValue {
                        value: results[0],
                        ty: type_to_cranelift(&return_type, self.ctx.pointer_type),
                        vole_type: return_type,
                    });
                }
            }
        }

        // Look up the static method info (for non-generic classes)
        let method_info = self
            .ctx
            .static_method_infos
            .get(&(type_def_id, method_name_id))
            .ok_or_else(|| {
                let type_def = self.ctx.analyzed.entity_registry.get_type(type_def_id);
                let type_name = self.ctx.analyzed.name_table.display(type_def.name_id);
                let method_name = self.ctx.analyzed.name_table.display(method_name_id);
                let registered_keys: Vec<_> = self
                    .ctx
                    .static_method_infos
                    .keys()
                    .map(|(tid, mid)| {
                        let t = self.ctx.analyzed.entity_registry.get_type(*tid);
                        let tn = self.ctx.analyzed.name_table.display(t.name_id);
                        let mn = self.ctx.analyzed.name_table.display(*mid);
                        format!("({}, {})", tn, mn)
                    })
                    .collect();
                format!(
                    "Static method not found: {}::{} (type_def_id={:?}, method_name_id={:?}). Registered: {:?}",
                    type_name, method_name, type_def_id, method_name_id, registered_keys
                )
            })?
            .clone();

        // Compile arguments (no receiver for static methods)
        let mut args = Vec::new();
        for (arg, param_ty) in mc.args.iter().zip(func_type.params.iter()) {
            let compiled = self.expr(arg)?;
            // Box interface values if needed
            let compiled = if matches!(param_ty, Type::Interface(_)) {
                box_interface_value(self.builder, self.ctx, compiled, param_ty)?
            } else {
                compiled
            };
            args.push(compiled.value);
        }

        // Get function reference and call
        let func_ref = self.func_ref(method_info.func_key)?;
        let call = self.builder.ins().call(func_ref, &args);
        let results = self.builder.inst_results(call);

        let return_type = (*func_type.return_type).clone();
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
}
