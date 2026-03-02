// src/codegen/lambda.rs
//
// Lambda/closure compilation support for code generation.

use rustc_hash::FxHashMap;

use cranelift::prelude::*;
use cranelift_module::Module;

use vole_frontend::{Capture, Symbol};
use vole_identity::{TypeId, VirTypeId};
use vole_vir::VirBody;
use vole_vir::expr::VirCapture;

use super::RuntimeKey;
use super::compiler::common::FunctionCompileConfig;
use super::context::Cg;
use super::types::CompiledValue;
use crate::errors::{CodegenError, CodegenResult};

/// Information about a captured variable for lambda compilation
#[derive(Clone, Copy)]
pub(crate) struct CaptureBinding {
    /// Index in the closure's captures array
    pub index: usize,
    /// Vole type of the captured variable (VIR type)
    pub vole_type: VirTypeId,
}

impl CaptureBinding {
    pub fn new(index: usize, vole_type: VirTypeId) -> Self {
        Self { index, vole_type }
    }
}

/// Build capture bindings from a list of captures, variable types, and parent captures
///
/// For transitive captures (nested closures), the type may be in parent_captures
/// rather than in variables.
pub(crate) fn build_capture_bindings(
    captures: &[Capture],
    variables: &FxHashMap<Symbol, (Variable, VirTypeId)>,
    parent_captures: Option<&FxHashMap<Symbol, CaptureBinding>>,
) -> FxHashMap<Symbol, CaptureBinding> {
    let mut bindings = FxHashMap::default();
    for (i, capture) in captures.iter().enumerate() {
        // First check local variables, then parent captures, finally fall back to i64.
        let vir_type_id = variables
            .get(&capture.name)
            .map(|(_, vir_ty)| *vir_ty)
            .or_else(|| parent_captures?.get(&capture.name).map(|b| b.vole_type))
            .unwrap_or(VirTypeId::I64);
        bindings.insert(capture.name, CaptureBinding::new(i, vir_type_id));
    }
    bindings
}

impl Cg<'_, '_, '_> {
    /// Build the Cranelift signature for a lambda function.
    ///
    /// All lambdas use the closure calling convention: the first parameter is
    /// a pointer (the closure pointer), followed by the user-visible parameters.
    fn build_lambda_signature(
        &mut self,
        param_types: &[Type],
        return_type: Type,
        return_vir_ty: VirTypeId,
    ) -> Signature {
        let mut sig = self.jit_module().make_signature();
        sig.params.push(AbiParam::new(self.ptr_type())); // closure ptr
        for &param_ty in param_types {
            sig.params.push(AbiParam::new(param_ty));
        }
        // For fallible returns, use multi-value return (tag: i64, payload: i64)
        // For wide fallible (i128 success), use (tag: i64, low: i64, high: i64)
        if self.vir_query_is_wide_fallible_v(return_vir_ty) {
            sig.returns.push(AbiParam::new(types::I64)); // tag
            sig.returns.push(AbiParam::new(types::I64)); // low
            sig.returns.push(AbiParam::new(types::I64)); // high
        } else if self.vir_query_unwrap_fallible_v(return_vir_ty).is_some() {
            sig.returns.push(AbiParam::new(types::I64)); // tag
            sig.returns.push(AbiParam::new(types::I64)); // payload
        } else {
            sig.returns.push(AbiParam::new(return_type));
        }
        sig
    }

    /// Compile a VIR lambda expression — the VIR-path counterpart to
    /// `compile_closure`.
    ///
    /// Derives param types from the function type `ty` via
    /// `TypeArena::unwrap_function`, compiles the body via the VIR path,
    /// allocates a closure struct, and sets up captures.
    pub fn compile_vir_lambda(
        &mut self,
        param_names: &[Symbol],
        body: &VirBody,
        vir_captures: &[VirCapture],
        vir_ty: VirTypeId,
    ) -> CodegenResult<CompiledValue> {
        let (param_type_ids, return_type_id) = self.unwrap_lambda_func_type(vir_ty)?;

        let captures: Vec<Capture> = vir_captures
            .iter()
            .map(|c| Capture {
                name: c.name,
                is_mutable: false,
                is_mutated: false,
            })
            .collect();

        let func_id = self.declare_vir_lambda_func(
            param_names,
            &param_type_ids,
            return_type_id,
            &captures,
            body,
        )?;

        self.alloc_closure(func_id, vir_ty, &captures)
    }

    /// Unwrap a function type into param types and return type, applying
    /// monomorphization substitutions.
    fn unwrap_lambda_func_type(
        &self,
        func_vir_type_id: VirTypeId,
    ) -> CodegenResult<(Vec<TypeId>, TypeId)> {
        let (sema_params, ret_id) = self
            .vir_query_unwrap_function_sema_v(func_vir_type_id)
            .ok_or_else(|| {
                CodegenError::type_mismatch(
                    "VIR lambda",
                    "function type",
                    format!("{func_vir_type_id:?}"),
                )
            })?;
        let param_ids: Vec<TypeId> = sema_params
            .iter()
            .map(|&p| self.substitute_type(p))
            .collect();
        let ret = self.substitute_type(ret_id);
        Ok((param_ids, ret))
    }

    /// Declare and compile a VIR lambda as a Cranelift function.
    ///
    /// Builds the signature, declares the function, compiles the VIR body,
    /// and defines the function in the JIT module.  Returns the Cranelift
    /// FuncId for use in closure allocation.
    fn declare_vir_lambda_func(
        &mut self,
        param_names: &[Symbol],
        param_type_ids: &[TypeId],
        return_type_id: TypeId,
        captures: &[Capture],
        body: &VirBody,
    ) -> CodegenResult<cranelift_module::FuncId> {
        let lambda_id = self.next_lambda_id();
        let cr_param_types: Vec<Type> = param_type_ids
            .iter()
            .map(|&id| self.cranelift_type(id))
            .collect();
        let return_type = self.cranelift_type(return_type_id);
        let ptr_type = self.ptr_type();

        let return_vir_ty = self.to_vir_type(return_type_id);
        let sig = self.build_lambda_signature(&cr_param_types, return_type, return_vir_ty);

        let func_key = self.funcs().intern_lambda(lambda_id);
        let lambda_name = self.funcs().display(func_key);
        let func_id = self
            .jit_module()
            .declare_function(&lambda_name, cranelift_module::Linkage::Local, &sig)
            .map_err(CodegenError::cranelift)?;
        self.funcs().set_func_id(func_key, func_id);
        self.funcs().set_return_type(func_key, return_type_id);

        // Build capture bindings
        let capture_bindings = if !captures.is_empty() {
            let parent_captures = self.captures.as_ref().map(|c| c.bindings);
            Some(build_capture_bindings(
                captures,
                &self.vars,
                parent_captures,
            ))
        } else {
            None
        };

        let params: Vec<(Symbol, TypeId, Type)> = param_names
            .iter()
            .enumerate()
            .map(|(i, &name)| (name, param_type_ids[i], cr_param_types[i]))
            .collect();

        // Compile the body in a new Cranelift function context.
        let mut lambda_ctx = self.jit_module().make_context();
        lambda_ctx.func.signature = sig;

        {
            use super::compiler::common::compile_function_inner_with_vir;

            let mut builder_ctx = FunctionBuilderContext::new();
            let builder = FunctionBuilder::new(&mut lambda_ctx.func, &mut builder_ctx);

            let config = FunctionCompileConfig::lambda(
                params,
                return_type_id,
                capture_bindings.as_ref(),
                ptr_type,
            );

            compile_function_inner_with_vir(
                builder,
                self.codegen_ctx,
                self.env,
                config,
                body,
                self.current_module(),
                self.substitutions,
            )?;
        }

        self.jit_module()
            .define_function(func_id, &mut lambda_ctx)
            .map_err(CodegenError::cranelift)?;

        Ok(func_id)
    }

    /// Allocate a closure struct and set up captures.
    ///
    /// Given the compiled function's FuncId, allocates a closure struct with
    /// the function pointer and capture slots, then populates the captures.
    fn alloc_closure(
        &mut self,
        func_id: cranelift_module::FuncId,
        func_vir_type_id: VirTypeId,
        captures: &[Capture],
    ) -> CodegenResult<CompiledValue> {
        let ptr_type = self.ptr_type();
        let func_ref = self
            .codegen_ctx
            .module
            .declare_func_in_func(func_id, self.builder.func);
        let func_addr = self.builder.ins().func_addr(ptr_type, func_ref);

        let alloc_ref = self.runtime_func_ref(RuntimeKey::ClosureAlloc)?;
        let num_captures_val = self.iconst_cached(types::I64, captures.len() as i64);
        let alloc_call = self
            .builder
            .ins()
            .call(alloc_ref, &[func_addr, num_captures_val]);
        let closure_ptr = self.builder.inst_results(alloc_call)[0];

        if !captures.is_empty() {
            self.setup_closure_captures(captures, closure_ptr)?;
        }

        Ok(CompiledValue::new(closure_ptr, ptr_type, func_vir_type_id))
    }

    /// Set up the capture values in an allocated closure.
    ///
    /// For each captured variable, this resolves its value (from local variables,
    /// parent captures, or self-capture), heap-allocates storage, copies the value,
    /// and registers the capture with the closure runtime.
    fn setup_closure_captures(
        &mut self,
        captures: &[Capture],
        closure_ptr: Value,
    ) -> CodegenResult<()> {
        let set_capture_ref = self.runtime_func_ref(RuntimeKey::ClosureSetCapture)?;
        let set_kind_ref = self.runtime_func_ref(RuntimeKey::ClosureSetCaptureKind)?;
        let set_size_ref = self.runtime_func_ref(RuntimeKey::ClosureSetCaptureSize)?;
        let heap_alloc_ref = self.runtime_func_ref(RuntimeKey::HeapAlloc)?;
        let rc_inc_ref = self.runtime_func_ref(RuntimeKey::RcInc)?;

        for (i, capture) in captures.iter().enumerate() {
            let (current_value, vole_vir_ty, is_self_capture) =
                self.resolve_capture(capture, closure_ptr)?;

            // Self-captures are weak references (no rc_inc, no rc_dec on drop)
            // to break the reference cycle: closure -> self-capture -> closure.
            let is_rc = !is_self_capture && self.rc_state_v(vole_vir_ty).is_capture();

            // If the capture is RC, increment its refcount (the closure now shares ownership)
            if is_rc {
                self.builder.ins().call(rc_inc_ref, &[current_value]);
            }

            // Prefer VIR-native size lookup; fall back through cv_type_id_from_vir
            // for compat-encoded VirTypeIds that are not yet in the VirTypeTable.
            let size = if vole_vir_ty.is_compat() {
                self.type_size(self.cv_type_id_from_vir(vole_vir_ty))
            } else {
                self.type_size_v(vole_vir_ty)
            };
            let size_val = self.iconst_cached(types::I64, size as i64);

            let alloc_call = self.builder.ins().call(heap_alloc_ref, &[size_val]);
            let heap_ptr = self.builder.inst_results(alloc_call)[0];

            // Structs are stack-allocated pointers -- we must copy the full struct
            // data into the heap allocation (not just store the stack pointer,
            // which would dangle after the creating function returns).
            self.copy_value_to_heap_v(current_value, heap_ptr, vole_vir_ty);

            let index_val = self.iconst_cached(types::I64, i as i64);
            self.builder
                .ins()
                .call(set_capture_ref, &[closure_ptr, index_val, heap_ptr]);

            // Set the capture kind so closure_drop knows which captures need rc_dec
            let kind_val = self.iconst_cached(types::I8, is_rc as i64);
            self.builder
                .ins()
                .call(set_kind_ref, &[closure_ptr, index_val, kind_val]);

            // Store the allocation size so closure_drop can free with correct layout
            let size_i32 = self.iconst_cached(types::I32, size as i64);
            self.builder
                .ins()
                .call(set_size_ref, &[closure_ptr, index_val, size_i32]);
        }

        Ok(())
    }

    /// Resolve a captured variable's value and type.
    ///
    /// Returns (value, vir_type_id, is_self_capture).
    fn resolve_capture(
        &mut self,
        capture: &Capture,
        closure_ptr: Value,
    ) -> CodegenResult<(Value, VirTypeId, bool)> {
        let is_self_capture = Some(capture.name) == self.self_capture;
        let resolve_symbol_text = |sym: Symbol| -> Option<&str> {
            let idx = sym.index() as usize;
            if idx < self.interner().len() {
                return Some(self.interner().resolve(sym));
            }
            if idx < self.analyzed().interner().len() {
                return Some(self.analyzed().interner().resolve(sym));
            }
            None
        };
        let capture_name = resolve_symbol_text(capture.name).map(str::to_string);

        if is_self_capture {
            // Self-capture: use the closure pointer we just created
            let (_, vir_ty) = self.vars.get(&capture.name).ok_or_else(|| {
                CodegenError::not_found("self-captured variable", format!("{:?}", capture.name))
            })?;
            Ok((closure_ptr, *vir_ty, true))
        } else if let Some((var, vir_ty)) = self.vars.get(&capture.name) {
            // Normal capture: load from local variable
            Ok((self.builder.use_var(*var), *vir_ty, false))
        } else if let Some(capture_name) = capture_name.as_deref()
            && let Some((var, vir_ty)) = self.vars.iter().find_map(|(sym, (var, ty))| {
                resolve_symbol_text(*sym)
                    .filter(|name| *name == capture_name)
                    .map(|_| (*var, *ty))
            })
        {
            // Fallback for cross-interner symbol-id mismatches: match by symbol name.
            Ok((self.builder.use_var(var), vir_ty, false))
        } else if let Some(binding) = self.get_capture(&capture.name).copied() {
            // Transitive capture: load from parent closure's captures.
            let captured = self.load_capture(&binding)?;
            Ok((captured.value, binding.vole_type, false))
        } else if let Some(capture_name) = capture_name.as_deref()
            && let Some(binding) = self.captures.as_ref().and_then(|captures| {
                captures.bindings.iter().find_map(|(sym, binding)| {
                    resolve_symbol_text(*sym)
                        .filter(|name| *name == capture_name)
                        .map(|_| *binding)
                })
            })
        {
            // Same fallback for transitive captures when Symbol IDs differ by interner.
            let captured = self.load_capture(&binding)?;
            Ok((captured.value, binding.vole_type, false))
        } else {
            let format_sym = |sym: Symbol| {
                resolve_symbol_text(sym)
                    .map(str::to_string)
                    .unwrap_or_else(|| format!("{sym:?}"))
            };
            let available_vars: Vec<String> =
                self.vars.keys().map(|sym| format_sym(*sym)).collect();
            let parent_captures: Vec<String> = self
                .captures
                .as_ref()
                .map(|caps| caps.bindings.keys().map(|sym| format_sym(*sym)).collect())
                .unwrap_or_default();
            Err(CodegenError::not_found(
                "captured variable",
                format!(
                    "{}; vars={:?}; parent_captures={:?}; self_capture={:?}",
                    capture_name.unwrap_or_else(|| format!("{:?}", capture.name)),
                    available_vars,
                    parent_captures,
                    self.self_capture.map(format_sym)
                ),
            ))
        }
    }

    /// Copy a value into a heap allocation, handling structs with multiple slots.
    ///
    /// Uses VirTypeId to determine struct layout via VirTypeDef.field_types.
    fn copy_value_to_heap_v(&mut self, value: Value, heap_ptr: Value, vir_ty: VirTypeId) {
        if let Some(flat_count) = self.vir_struct_flat_slot_count(vir_ty) {
            for slot in 0..flat_count {
                let offset = (slot as i32) * 8;
                let val = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), value, offset);
                self.builder
                    .ins()
                    .store(MemFlags::new(), val, heap_ptr, offset);
            }
        } else {
            self.builder
                .ins()
                .store(MemFlags::new(), value, heap_ptr, 0);
        }
    }
}
