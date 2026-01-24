// src/codegen/structs/methods.rs

use cranelift::prelude::*;
use cranelift_module::Module;
use rustc_hash::FxHashMap;
use smallvec::{SmallVec, smallvec};

use crate::RuntimeFn;

/// SmallVec for call arguments - most calls have <= 8 args
type ArgVec = SmallVec<[Value; 8]>;
use crate::context::Cg;
use crate::errors::CodegenError;
use crate::method_resolution::{MethodResolutionInputId, MethodTarget, resolve_method_target_id};
use crate::types::{
    CompiledValue, module_name_id, type_id_to_cranelift, value_to_word, word_to_value_type_id,
};
use vole_frontend::{Expr, ExprKind, MethodCallExpr, NodeId, Symbol};
use vole_identity::NamerLookup;
use vole_identity::{MethodId, NameId, TypeDefId};
use vole_sema::resolution::ResolvedMethod;
use vole_sema::type_arena::TypeId;

impl Cg<'_, '_, '_> {
    /// Look up a method NameId using the context's interner (which may be a module interner)
    fn method_name_id(&self, name: Symbol) -> NameId {
        let name_table = self.name_table();
        let namer = NamerLookup::new(&name_table, self.interner());
        namer.method(name).unwrap_or_else(|| {
            panic!(
                "method name_id not found for '{}'",
                self.interner().resolve(name)
            )
        })
    }

    #[tracing::instrument(skip(self, mc), fields(method = %self.interner().resolve(mc.method)))]
    pub fn method_call(
        &mut self,
        mc: &MethodCallExpr,
        expr_id: NodeId,
    ) -> Result<CompiledValue, String> {
        // Check for static method call FIRST - don't try to compile the receiver
        // Convert ModuleId to module path string for method_at_in_module
        let current_module_path = self
            .current_module()
            .map(|mid| self.name_table().module_path(mid).to_string());
        if let Some(ResolvedMethod::Static {
            type_def_id,
            method_id,
            func_type_id,
            ..
        }) = self
            .analyzed()
            .query()
            .method_at_in_module(expr_id, current_module_path.as_deref())
        {
            return self.static_method_call(*type_def_id, *method_id, *func_type_id, mc, expr_id);
        }

        // Handle range.iter() specially since range expressions can't be compiled to values directly
        if let ExprKind::Range(range) = &mc.object.kind {
            let method_name = self.interner().resolve(mc.method);
            if method_name == "iter" {
                return self.range_iter(range);
            }
        }

        let obj = self.expr(&mc.object)?;
        let method_name_str = self.interner().resolve(mc.method);

        // Handle module method calls (e.g., math.sqrt(16.0), math.lerp(...))
        // These go to either external native functions or pure Vole module functions
        // Extract module_id before the if-let to avoid holding arena borrow
        let module_id_opt = self.arena().unwrap_module(obj.type_id).map(|m| m.module_id);
        if let Some(module_id) = module_id_opt {
            let module_path = self
                .analyzed()
                .name_table()
                .module_path(module_id)
                .to_string();
            let name_id = module_name_id(self.analyzed(), module_id, method_name_str);
            // Get the method resolution (reuse current_module_path from above)
            let resolution = self
                .analyzed()
                .query()
                .method_at_in_module(expr_id, current_module_path.as_deref());
            if let Some(ResolvedMethod::Implemented {
                external_info,
                func_type_id,
                ..
            }) = resolution
            {
                // Get return type from arena
                let return_type_id = {
                    let arena = self.arena();
                    let (_, ret, _) = arena
                        .unwrap_function(*func_type_id)
                        .expect("module method must have function type");
                    ret
                };

                // Compile arguments (no receiver for module functions)
                let args = self.compile_call_args(&mc.args)?;

                if let Some(ext_info) = external_info {
                    // External FFI function
                    return self.call_external_id(ext_info, &args, return_type_id);
                } else {
                    // Pure Vole function - call by mangled name
                    let name_id = name_id.ok_or_else(|| {
                        format!(
                            "Module method {}::{} not interned",
                            module_path, method_name_str
                        )
                    })?;
                    let func_key = self.funcs().intern_name_id(name_id);
                    let func_id = self.funcs().func_id(func_key).ok_or_else(|| {
                        format!(
                            "Module function {}::{} not found",
                            module_path, method_name_str
                        )
                    })?;
                    let func_ref = self
                        .codegen_ctx
                        .jit_module()
                        .declare_func_in_func(func_id, self.builder.func);
                    let call_inst = self.builder.ins().call(func_ref, &args);
                    return Ok(self.call_result(call_inst, return_type_id));
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
        let runtime_iter_elem = self.arena().unwrap_runtime_iterator(obj.type_id);
        if let Some(elem_type_id) = runtime_iter_elem {
            return self.runtime_iterator_method(&obj, mc, method_name_str, elem_type_id);
        }

        let method_id = self.method_name_id(mc.method);

        // Look up method resolution to determine naming convention and return type
        // If no resolution exists (e.g., inside default method bodies), fall back to type-based lookup
        // In monomorphized context, skip sema resolution because it was computed for the type parameter,
        // not the concrete type. Let resolve_method_target do dynamic resolution based on object_type.
        let resolution = if self.substitutions.is_some() {
            None
        } else {
            self.analyzed()
                .query()
                .method_at_in_module(expr_id, current_module_path.as_deref())
        };

        tracing::debug!(
            obj_type_id = ?obj.type_id,
            method = %method_name_str,
            resolution = ?resolution,
            "method call"
        );

        let target = resolve_method_target_id(MethodResolutionInputId {
            analyzed: self.analyzed(),
            type_metadata: self.type_metadata(),
            impl_method_infos: self.impl_method_infos(),
            method_name_str,
            object_type_id: obj.type_id,
            method_id,
            resolution,
        })?;

        let (method_info, return_type_id) = match target {
            MethodTarget::FunctionalInterface { func_type_id } => {
                // Use TypeDefId directly for EntityRegistry-based dispatch
                let interface_type_def_id =
                    self.arena().unwrap_interface(obj.type_id).map(|(id, _)| id);
                if let Some(interface_type_def_id) = interface_type_def_id {
                    let method_name_id = self.method_name_id(mc.method);
                    return self.interface_dispatch_call_args_by_type_def_id(
                        &obj,
                        &mc.args,
                        interface_type_def_id,
                        method_name_id,
                        func_type_id,
                    );
                }
                // For functional interfaces, the object holds the function ptr or closure
                // The actual is_closure status depends on the lambda's compilation.
                // Get is_closure from the object's type if available, otherwise from func_type_id
                let is_closure = self
                    .arena()
                    .unwrap_function(obj.type_id)
                    .map(|(_, _, is_closure)| is_closure)
                    .or_else(|| {
                        self.arena()
                            .unwrap_function(func_type_id)
                            .map(|(_, _, is_closure)| is_closure)
                    })
                    .unwrap_or(true);
                return self.functional_interface_call(obj.value, func_type_id, is_closure, mc);
            }
            MethodTarget::External {
                external_info,
                return_type,
            } => {
                // Use TypeId-based params for interface boxing check
                let param_type_ids = resolution.and_then(|resolved: &ResolvedMethod| {
                    self.arena()
                        .unwrap_function(resolved.func_type_id())
                        .map(|(params, _, _)| params.clone())
                });
                let mut args: ArgVec = smallvec![obj.value];
                if let Some(param_type_ids) = &param_type_ids {
                    for (arg, &param_type_id) in mc.args.iter().zip(param_type_ids.iter()) {
                        let compiled = self.expr(arg)?;
                        let compiled = self.coerce_to_type(compiled, param_type_id)?;
                        args.push(compiled.value);
                    }
                } else {
                    for arg in &mc.args {
                        let compiled = self.expr(arg)?;
                        args.push(compiled.value);
                    }
                }
                // Convert Iterator return types to RuntimeIterator for external methods
                let return_type_id = self.maybe_convert_iterator_return_type(return_type);
                return self.call_external_id(&external_info, &args, return_type_id);
            }
            MethodTarget::InterfaceDispatch {
                interface_type_id,
                method_name_id,
                func_type_id,
            } => {
                return self.interface_dispatch_call_args_by_type_def_id(
                    &obj,
                    &mc.args,
                    interface_type_id,
                    method_name_id,
                    func_type_id,
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

        // Use sema's cached substituted return type if available (avoids recomputation)
        let return_type_id = self
            .get_substituted_return_type(&expr_id)
            .unwrap_or(return_type_id);

        // Check if this is a monomorphized class method call
        // If so, use the monomorphized method's func_key instead
        let (method_func_ref, is_generic_class) = if let Some(monomorph_key) = self
            .analyzed()
            .expression_data
            .get_class_method_generic(expr_id)
        {
            // Look up the monomorphized instance
            if let Some(instance) = self
                .registry()
                .class_method_monomorph_cache
                .get(monomorph_key)
            {
                let func_key = self.funcs().intern_name_id(instance.mangled_name);
                // Monomorphized methods have concrete types, no i64 conversion needed
                (self.func_ref(func_key)?, false)
            } else {
                // Fallback to regular method if monomorph not found
                (self.func_ref(method_info.func_key)?, false)
            }
        } else {
            // Not a monomorphized class method, use regular dispatch
            let is_generic_class = self
                .arena()
                .unwrap_class(obj.type_id)
                .map(|(_, type_args)| !type_args.is_empty())
                .unwrap_or(false);
            (self.func_ref(method_info.func_key)?, is_generic_class)
        };

        // Use TypeId-based params for interface boxing check
        let param_type_ids = resolution.and_then(|resolved: &ResolvedMethod| {
            self.arena()
                .unwrap_function(resolved.func_type_id())
                .map(|(params, _, _)| params.clone())
        });
        let mut args: ArgVec = smallvec![obj.value];
        if let Some(param_type_ids) = &param_type_ids {
            for (arg, &param_type_id) in mc.args.iter().zip(param_type_ids.iter()) {
                let compiled = self.expr(arg)?;
                // Check if param is interface type using arena
                let is_interface = self.arena().unwrap_interface(param_type_id).is_some();
                let compiled = if is_interface {
                    self.box_interface_value(compiled, param_type_id)?
                } else {
                    compiled
                };

                // Generic class methods expect i64 for TypeParam, convert if needed
                let arg_value = if is_generic_class && compiled.ty != types::I64 {
                    let ptr_type = self.ptr_type();
                    let arena_rc = self.arena_rc().clone();
                    let registry = self.registry();
                    value_to_word(
                        self.builder,
                        &compiled,
                        ptr_type,
                        None, // No heap alloc needed for primitive conversions
                        &arena_rc,
                        registry,
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
                    let ptr_type = self.ptr_type();
                    let arena_rc = self.arena_rc().clone();
                    let registry = self.registry();
                    value_to_word(
                        self.builder,
                        &compiled,
                        ptr_type,
                        None, // No heap alloc needed for primitive conversions
                        &arena_rc,
                        registry,
                    )?
                } else {
                    compiled.value
                };
                args.push(arg_value);
            }
        }

        // Compile default arguments if fewer args provided than expected
        // args includes self, so provided_args = args.len() - 1, expected includes params only
        if let Some(param_type_ids) = &param_type_ids {
            let provided_args = args.len() - 1; // subtract self
            let expected_params = param_type_ids.len();
            if provided_args < expected_params {
                // Get method_id from resolution to look up param_defaults
                if let Some(method_id) = resolution.and_then(|r| r.method_id()) {
                    let default_args = self.compile_method_default_args(
                        method_id,
                        provided_args,
                        &param_type_ids[provided_args..],
                        is_generic_class,
                    )?;
                    args.extend(default_args);
                }
            }
        }

        let call = self.builder.ins().call(method_func_ref, &args);
        let results = self.builder.inst_results(call);

        if results.is_empty() {
            Ok(self.void_value())
        } else {
            // Generic methods are compiled with TypeParam -> i64, but we may need
            // a different type (f64, bool, etc). Convert using word_to_value.
            let expected_ty = self.cranelift_type(return_type_id);
            let actual_result = results[0];
            let actual_ty = self.builder.func.dfg.value_type(actual_result);

            let result_value = if actual_ty != expected_ty && actual_ty == types::I64 {
                // Method returned i64 (TypeParam) but we expect a different type
                let ptr_type = self.ptr_type();
                let registry = self.registry();
                let arena = self.env.analyzed.type_arena();
                let converted = word_to_value_type_id(
                    self.builder,
                    actual_result,
                    return_type_id,
                    ptr_type,
                    registry,
                    &arena,
                );
                drop(arena);
                converted
            } else {
                actual_result
            };

            // For Union return types, the callee returns a pointer to its stack memory
            // which becomes invalid after the call. Copy the union to our own stack.
            let (final_value, final_type) = if self.arena().is_union(return_type_id) {
                let union_size = self.type_size(return_type_id);
                let local_slot = self.alloc_stack(union_size);

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

                let ptr_type = self.ptr_type();
                let local_ptr = self.builder.ins().stack_addr(ptr_type, local_slot, 0);
                (local_ptr, expected_ty)
            } else {
                (result_value, expected_ty)
            };

            Ok(CompiledValue {
                value: final_value,
                ty: final_type,
                type_id: return_type_id,
            })
        }
    }

    /// Compile range.iter() - creates a range iterator from start..end
    fn range_iter(&mut self, range: &vole_frontend::RangeExpr) -> Result<CompiledValue, String> {
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
        let i64_id = self.arena().primitives.i64;
        let iter_type_id = self.update().runtime_iterator(i64_id);
        Ok(CompiledValue {
            value: result,
            ty: self.ptr_type(),
            type_id: iter_type_id,
        })
    }

    pub(crate) fn builtin_method(
        &mut self,
        obj: &CompiledValue,
        method_name: &str,
    ) -> Result<Option<CompiledValue>, String> {
        let arena = self.arena();

        // Array methods
        if let Some(elem_type_id) = arena.unwrap_array(obj.type_id) {
            drop(arena);
            return match method_name {
                "length" => {
                    let result = self.call_runtime(RuntimeFn::ArrayLen, &[obj.value])?;
                    Ok(Some(self.i64_value(result)))
                }
                "iter" => {
                    let result = self.call_runtime(RuntimeFn::ArrayIter, &[obj.value])?;
                    // Return RuntimeIterator - a concrete type for builtin iterators
                    let iter_type_id = self.update().runtime_iterator(elem_type_id);
                    Ok(Some(CompiledValue {
                        value: result,
                        ty: self.ptr_type(),
                        type_id: iter_type_id,
                    }))
                }
                _ => Ok(None),
            };
        }

        // String methods
        if arena.is_string(obj.type_id) {
            drop(arena);
            return match method_name {
                "length" => {
                    let result = self.call_runtime(RuntimeFn::StringLen, &[obj.value])?;
                    Ok(Some(self.i64_value(result)))
                }
                "iter" => {
                    let result = self.call_runtime(RuntimeFn::StringCharsIter, &[obj.value])?;
                    let string_id = self.arena().string();
                    let iter_type_id = self.update().runtime_iterator(string_id);
                    Ok(Some(CompiledValue {
                        value: result,
                        ty: self.ptr_type(),
                        type_id: iter_type_id,
                    }))
                }
                _ => Ok(None),
            };
        }

        // Range methods
        if matches!(
            arena.get(obj.type_id),
            vole_sema::type_arena::SemaType::Range
        ) {
            drop(arena);
            if method_name == "iter" {
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
                let i64_id = self.arena().i64();
                let iter_type_id = self.update().runtime_iterator(i64_id);
                return Ok(Some(CompiledValue {
                    value: result,
                    ty: self.ptr_type(),
                    type_id: iter_type_id,
                }));
            }
            return Ok(None);
        }

        drop(arena);
        Ok(None)
    }

    /// Handle method calls on RuntimeIterator - calls external Iterator functions directly
    fn runtime_iterator_method(
        &mut self,
        obj: &CompiledValue,
        mc: &MethodCallExpr,
        method_name: &str,
        elem_type_id: TypeId,
    ) -> Result<CompiledValue, String> {
        // Look up the Iterator interface
        let iter_type_id = self
            .resolve_type_str_or_interface("Iterator")
            .ok_or_else(|| "Iterator interface not found in entity registry".to_string())?;

        let iter_def = self.query().get_type(iter_type_id);

        // Find the method by name
        let method_id = iter_def
            .methods
            .iter()
            .find(|&&mid| {
                let m = self.query().get_method(mid);
                self.analyzed()
                    .name_table()
                    .last_segment_str(m.name_id)
                    .is_some_and(|n| n == method_name)
            })
            .ok_or_else(|| format!("Method {} not found on Iterator", method_name))?;

        let method = self.query().get_method(*method_id);

        // Get the external binding for this method
        let external_info = *self
            .registry()
            .get_external_binding(*method_id)
            .ok_or_else(|| format!("No external binding for Iterator.{}", method_name))?;

        // Substitute the element type for T in the return type using arena substitute
        let substitutions: FxHashMap<NameId, TypeId> = iter_def
            .type_params
            .iter()
            .map(|param| (*param, elem_type_id))
            .collect();
        let method_return_id = {
            let arena = self.arena();
            let (_, ret, _) = arena
                .unwrap_function(method.signature_id)
                .expect("method signature must be a function type");
            ret
        };
        let return_type_id = self.update().substitute(method_return_id, &substitutions);

        // Convert Iterator<T> return types to RuntimeIterator(T) since the runtime
        // functions return raw iterator pointers, not boxed interface values
        let return_type_id = self.convert_iterator_return_type(return_type_id, iter_type_id);

        // Build args: self (iterator ptr) + method args
        let mut args: ArgVec = smallvec![obj.value];
        for arg in &mc.args {
            let compiled = self.expr(arg)?;
            args.push(compiled.value);
        }

        // Call the external function directly
        self.call_external_id(&external_info, &args, return_type_id)
    }

    /// Convert Iterator<T> return types to RuntimeIterator(T)
    ///
    /// When calling external iterator methods, the runtime returns raw iterator pointers,
    /// not boxed interface values. This function converts Interface/GenericInstance types
    /// for Iterator to RuntimeIterator so that subsequent method calls use direct dispatch.
    fn convert_iterator_return_type(&self, ty: TypeId, iterator_type_id: TypeDefId) -> TypeId {
        self.convert_iterator_return_type_by_type_def_id(ty, iterator_type_id)
    }

    /// Convert Iterator<T> return types to RuntimeIterator(T), looking up Iterator interface by name
    /// Takes and returns TypeId for O(1) equality; converts internally for matching
    pub(crate) fn maybe_convert_iterator_return_type(&self, ty: TypeId) -> TypeId {
        // Look up the Iterator interface
        let iterator_type_id = self.resolve_type_str_or_interface("Iterator");
        if let Some(iterator_type_id) = iterator_type_id {
            self.convert_iterator_return_type_by_type_def_id(ty, iterator_type_id)
        } else {
            ty
        }
    }

    /// Core implementation of iterator return type conversion
    /// Uses arena methods to check for Iterator interface and convert to RuntimeIterator
    fn convert_iterator_return_type_by_type_def_id(
        &self,
        ty: TypeId,
        iterator_type_id: TypeDefId,
    ) -> TypeId {
        let arena = self.arena();
        // Check if this is an Interface type matching Iterator
        if let Some((type_def_id, type_args)) = arena.unwrap_interface(ty)
            && type_def_id == iterator_type_id
            && let Some(&elem_type_id) = type_args.first()
        {
            drop(arena);
            return self.update().runtime_iterator(elem_type_id);
        }
        ty
    }

    fn functional_interface_call(
        &mut self,
        func_ptr_or_closure: Value,
        func_type_id: TypeId,
        is_closure: bool,
        mc: &MethodCallExpr,
    ) -> Result<CompiledValue, String> {
        // Extract function type components from the arena
        let (param_ids, return_type_id) = {
            let arena = self.arena();
            let (params, ret, _) = arena.unwrap_function(func_type_id).ok_or_else(|| {
                "Expected function type for functional interface call".to_string()
            })?;
            (params.clone(), ret)
        };

        // Check if this is actually a closure or a pure function
        // The is_closure flag is determined by the caller based on the actual
        // lambda's compilation, not the interface's generic signature.
        if is_closure {
            // It's a closure - extract function pointer and pass closure
            let func_ptr = self.call_runtime(RuntimeFn::ClosureGetFunc, &[func_ptr_or_closure])?;

            // Build the Cranelift signature for the closure call
            // First param is the closure pointer, then the user params
            let mut sig = self.jit_module().make_signature();
            sig.params.push(AbiParam::new(self.ptr_type())); // Closure pointer
            for param_id in param_ids.iter() {
                sig.params.push(AbiParam::new(type_id_to_cranelift(
                    *param_id,
                    &self.arena(),
                    self.ptr_type(),
                )));
            }
            let is_void_return = self.arena().is_void(return_type_id);
            if !is_void_return {
                sig.returns.push(AbiParam::new(type_id_to_cranelift(
                    return_type_id,
                    &self.arena(),
                    self.ptr_type(),
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
            Ok(self.call_result(call_inst, return_type_id))
        } else {
            // It's a pure function - call directly
            let mut sig = self.jit_module().make_signature();
            for param_id in param_ids.iter() {
                sig.params.push(AbiParam::new(type_id_to_cranelift(
                    *param_id,
                    &self.arena(),
                    self.ptr_type(),
                )));
            }
            let is_void_return = self.arena().is_void(return_type_id);
            if !is_void_return {
                sig.returns.push(AbiParam::new(type_id_to_cranelift(
                    return_type_id,
                    &self.arena(),
                    self.ptr_type(),
                )));
            }

            let sig_ref = self.builder.import_signature(sig);
            let args = self.compile_call_args(&mc.args)?;
            let call_inst = self
                .builder
                .ins()
                .call_indirect(sig_ref, func_ptr_or_closure, &args);
            Ok(self.call_result(call_inst, return_type_id))
        }
    }

    /// Dispatch an interface method call by TypeDefId (EntityRegistry-based)
    pub(crate) fn interface_dispatch_call_args_by_type_def_id(
        &mut self,
        obj: &CompiledValue,
        args: &[Expr],
        interface_type_id: TypeDefId,
        method_name_id: NameId,
        func_type_id: TypeId,
    ) -> Result<CompiledValue, String> {
        let slot = crate::interface_vtable::interface_method_slot_by_type_def_id(
            interface_type_id,
            method_name_id,
            self.registry(),
        )?;
        self.interface_dispatch_call_args_inner(obj, args, slot, func_type_id)
    }

    fn interface_dispatch_call_args_inner(
        &mut self,
        obj: &CompiledValue,
        args: &[Expr],
        slot: usize,
        func_type_id: TypeId,
    ) -> Result<CompiledValue, String> {
        let word_type = self.ptr_type();
        let word_bytes = word_type.bytes() as i32;

        // Unwrap function type to get params and return type
        let (param_count, return_type_id, is_void_return) = {
            let arena = self.arena();
            let (params, ret_id, _is_closure) = arena
                .unwrap_function(func_type_id)
                .ok_or_else(|| "Expected function type for interface dispatch".to_string())?;
            (params.len(), ret_id, arena.is_void(ret_id))
        };

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

        let mut sig = self.jit_module().make_signature();
        sig.params.push(AbiParam::new(word_type));
        for _ in 0..param_count {
            sig.params.push(AbiParam::new(word_type));
        }
        if !is_void_return {
            sig.returns.push(AbiParam::new(word_type));
        }
        let sig_ref = self.builder.import_signature(sig);

        let heap_alloc_ref = self.runtime_func_ref(RuntimeFn::HeapAlloc)?;

        // Pass the full boxed interface pointer (not just data_word) so wrappers can
        // access both data and vtable. This is needed for Iterator methods that create
        // UnifiedIterator adapters via vole_interface_iter.
        let mut call_args: ArgVec = smallvec![obj.value];
        for arg in args {
            let compiled = self.expr(arg)?;
            let arena_rc = self.arena_rc().clone();
            let registry = self.registry();
            let word = value_to_word(
                self.builder,
                &compiled,
                word_type,
                Some(heap_alloc_ref),
                &arena_rc,
                registry,
            )?;
            call_args.push(word);
        }

        let call = self
            .builder
            .ins()
            .call_indirect(sig_ref, func_ptr, &call_args);
        let results = self.builder.inst_results(call);

        if is_void_return {
            return Ok(self.void_value());
        }

        let word = results
            .first()
            .copied()
            .ok_or_else(|| "interface call missing return value".to_string())?;
        let registry = self.registry();
        let arena = self.env.analyzed.type_arena();
        let value = word_to_value_type_id(
            self.builder,
            word,
            return_type_id,
            word_type,
            registry,
            &arena,
        );
        drop(arena);

        // Convert Iterator return types to RuntimeIterator for interface dispatch
        // since external iterator methods return raw iterator pointers, not boxed interfaces
        let return_type_id = self.maybe_convert_iterator_return_type(return_type_id);

        Ok(self.compiled(value, return_type_id))
    }

    /// Handle static method call: TypeName.method(args)
    /// Static methods don't have a receiver, so we don't compile the object expression.
    fn static_method_call(
        &mut self,
        type_def_id: TypeDefId,
        method_id: MethodId,
        func_type_id: TypeId,
        mc: &MethodCallExpr,
        expr_id: NodeId,
    ) -> Result<CompiledValue, String> {
        // Check for float intrinsics (nan, infinity, neg_infinity, epsilon)
        // These are compiled directly to constants, no function call needed.
        if mc.args.is_empty()
            && let Some(result) = self.try_float_intrinsic(type_def_id, mc.method)?
        {
            return Ok(result);
        }

        // Get the method's name_id for lookup
        let method_def = self.query().get_method(method_id);
        let method_name_id = method_def.name_id;

        // Check for monomorphized static method (for generic classes)
        if let Some(mono_key) = self.query().static_method_generic_at(expr_id) {
            // Look up the monomorphized instance
            if let Some(instance) = self.registry().static_method_monomorph_cache.get(mono_key) {
                // Compile arguments with substituted param types (TypeId-based)
                let param_type_ids = &instance.func_type.params_id;
                let mut args = Vec::new();
                for (arg, &param_type_id) in mc.args.iter().zip(param_type_ids.iter()) {
                    let compiled = self.expr(arg)?;
                    let compiled = self.coerce_to_type(compiled, param_type_id)?;
                    args.push(compiled.value);
                }

                // Get monomorphized function reference and call
                let func_key = self.funcs().intern_name_id(instance.mangled_name);
                let func_ref = self.func_ref(func_key)?;
                let call = self.builder.ins().call(func_ref, &args);
                let return_type_id = instance.func_type.return_type_id;
                return Ok(self.call_result(call, return_type_id));
            }
        }

        // Look up the static method info via unified method_func_keys map
        let func_key = *self.method_func_keys()
            .get(&(type_def_id, method_name_id))
            .ok_or_else(|| {
                let type_def = self.query().get_type(type_def_id);
                let name_table = self.name_table();
                let type_name = name_table.display(type_def.name_id);
                let method_name = name_table.display(method_name_id);
                let registered_keys: Vec<_> = self.method_func_keys()
                    .keys()
                    .map(|(tid, mid)| {
                        let t = self.query().get_type(*tid);
                        let tn = name_table.display(t.name_id);
                        let mn = name_table.display(*mid);
                        format!("({}, {})", tn, mn)
                    })
                    .collect();
                format!(
                    "Static method not found: {}::{} (type_def_id={:?}, method_name_id={:?}). Registered: {:?}",
                    type_name, method_name, type_def_id, method_name_id, registered_keys
                )
            })?;

        // Get param types and return type from arena
        let (param_ids, return_type_id) = {
            let arena = self.arena();
            let (params, ret, _) = arena
                .unwrap_function(func_type_id)
                .ok_or_else(|| "Expected function type for static method call".to_string())?;
            (params.clone(), ret)
        };

        // Compile provided arguments (no receiver for static methods)
        let mut args = Vec::new();
        for (arg, param_id) in mc.args.iter().zip(param_ids.iter()) {
            let compiled = self.expr(arg)?;
            let compiled = self.coerce_to_type(compiled, *param_id)?;
            args.push(compiled.value);
        }

        // If there are fewer provided args than expected, compile default expressions
        if args.len() < param_ids.len() {
            let default_args =
                self.compile_static_method_default_args(method_id, args.len(), &param_ids)?;
            args.extend(default_args);
        }

        // Get function reference and call
        let func_ref = self.func_ref(func_key)?;
        let call = self.builder.ins().call(func_ref, &args);
        Ok(self.call_result(call, return_type_id))
    }

    /// Compile default expressions for omitted static method parameters.
    /// Returns compiled values for parameters starting at `start_index`.
    ///
    /// Uses the unified `compile_defaults_from_ptrs` helper.
    fn compile_static_method_default_args(
        &mut self,
        method_id: MethodId,
        start_index: usize,
        param_type_ids: &[TypeId],
    ) -> Result<Vec<Value>, String> {
        // Get raw pointers to default expressions from MethodDef.
        let default_ptrs: Vec<Option<*const Expr>> = {
            let method_def = self.query().registry().get_method(method_id);
            method_def
                .param_defaults
                .iter()
                .map(|opt| opt.as_ref().map(|e| e.as_ref() as *const Expr))
                .collect()
        };

        // Use the unified helper
        self.compile_defaults_from_ptrs(
            &default_ptrs,
            start_index,
            &param_type_ids[start_index..],
            false, // Not a generic class call
        )
    }

    /// Compile default expressions for omitted instance method parameters.
    /// Returns compiled values for parameters starting at `start_index`.
    ///
    /// Uses the unified `compile_defaults_from_ptrs` helper.
    fn compile_method_default_args(
        &mut self,
        method_id: MethodId,
        start_index: usize,
        expected_types: &[TypeId],
        is_generic_class: bool,
    ) -> Result<Vec<Value>, String> {
        // Get raw pointers to default expressions from MethodDef.
        let default_ptrs: Vec<Option<*const Expr>> = {
            let method_def = self.query().registry().get_method(method_id);
            method_def
                .param_defaults
                .iter()
                .map(|opt| opt.as_ref().map(|e| e.as_ref() as *const Expr))
                .collect()
        };

        // Use the unified helper
        self.compile_defaults_from_ptrs(
            &default_ptrs,
            start_index,
            expected_types,
            is_generic_class,
        )
    }

    /// Try to compile a float intrinsic (nan, infinity, neg_infinity, epsilon).
    /// Returns Some(value) if this is a known intrinsic, None otherwise.
    fn try_float_intrinsic(
        &mut self,
        type_def_id: TypeDefId,
        method_sym: Symbol,
    ) -> Result<Option<CompiledValue>, String> {
        // Get type name_id and check if it's f32 or f64
        let type_name_id = self.query().get_type(type_def_id).name_id;
        let name_table = self.name_table();
        let is_f32 = type_name_id == name_table.primitives.f32;
        let is_f64 = type_name_id == name_table.primitives.f64;
        drop(name_table);

        if !is_f32 && !is_f64 {
            return Ok(None);
        }

        // Get method name string
        let method_name = self.interner().resolve(method_sym);

        // Match intrinsic methods
        let value = match method_name {
            "nan" => {
                if is_f32 {
                    let v = self.builder.ins().f32const(f32::NAN);
                    CompiledValue {
                        value: v,
                        ty: types::F32,
                        type_id: TypeId::F32,
                    }
                } else {
                    let v = self.builder.ins().f64const(f64::NAN);
                    CompiledValue {
                        value: v,
                        ty: types::F64,
                        type_id: TypeId::F64,
                    }
                }
            }
            "infinity" => {
                if is_f32 {
                    let v = self.builder.ins().f32const(f32::INFINITY);
                    CompiledValue {
                        value: v,
                        ty: types::F32,
                        type_id: TypeId::F32,
                    }
                } else {
                    let v = self.builder.ins().f64const(f64::INFINITY);
                    CompiledValue {
                        value: v,
                        ty: types::F64,
                        type_id: TypeId::F64,
                    }
                }
            }
            "neg_infinity" => {
                if is_f32 {
                    let v = self.builder.ins().f32const(f32::NEG_INFINITY);
                    CompiledValue {
                        value: v,
                        ty: types::F32,
                        type_id: TypeId::F32,
                    }
                } else {
                    let v = self.builder.ins().f64const(f64::NEG_INFINITY);
                    CompiledValue {
                        value: v,
                        ty: types::F64,
                        type_id: TypeId::F64,
                    }
                }
            }
            "epsilon" => {
                if is_f32 {
                    let v = self.builder.ins().f32const(f32::EPSILON);
                    CompiledValue {
                        value: v,
                        ty: types::F32,
                        type_id: TypeId::F32,
                    }
                } else {
                    let v = self.builder.ins().f64const(f64::EPSILON);
                    CompiledValue {
                        value: v,
                        ty: types::F64,
                        type_id: TypeId::F64,
                    }
                }
            }
            _ => return Ok(None),
        };

        Ok(Some(value))
    }
}
