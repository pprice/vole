// src/codegen/lambda.rs
//
// Lambda/closure compilation support for code generation.

use rustc_hash::FxHashMap;

use cranelift::prelude::*;
use cranelift_module::Module;

use vole_frontend::{Capture, LambdaExpr, NodeId, Symbol};
use vole_sema::type_arena::{TypeArena, TypeId};

use super::RuntimeKey;
use super::compiler::common::{FunctionCompileConfig, compile_function_inner_with_params};
use super::context::Cg;
use super::types::{CompiledValue, is_wide_fallible};
use crate::errors::{CodegenError, CodegenResult};

/// Information about a captured variable for lambda compilation
#[derive(Clone, Copy)]
pub(crate) struct CaptureBinding {
    /// Index in the closure's captures array
    pub index: usize,
    /// Vole type of the captured variable (interned TypeId)
    pub vole_type: TypeId,
}

impl CaptureBinding {
    pub fn new(index: usize, vole_type: TypeId) -> Self {
        Self { index, vole_type }
    }
}

/// Build capture bindings from a list of captures, variable types, and parent captures
///
/// For transitive captures (nested closures), the type may be in parent_captures
/// rather than in variables.
pub(crate) fn build_capture_bindings(
    captures: &[Capture],
    variables: &FxHashMap<Symbol, (Variable, TypeId)>,
    parent_captures: Option<&FxHashMap<Symbol, CaptureBinding>>,
    arena: &TypeArena,
) -> FxHashMap<Symbol, CaptureBinding> {
    let mut bindings = FxHashMap::default();
    let default_type_id = arena.primitives.i64;
    for (i, capture) in captures.iter().enumerate() {
        // First check local variables, then parent captures, finally fall back to i64
        let vole_type_id = variables
            .get(&capture.name)
            .map(|(_, ty)| *ty)
            .or_else(|| parent_captures?.get(&capture.name).map(|b| b.vole_type))
            .unwrap_or(default_type_id);
        bindings.insert(capture.name, CaptureBinding::new(i, vole_type_id));
    }
    bindings
}

impl Cg<'_, '_, '_> {
    /// Get lambda param and return types from sema analysis.
    ///
    /// Returns the function type ID and decomposed param/return types from sema.
    /// Errors if sema did not store the lambda's type (which would be a bug).
    fn get_lambda_types(&self, node_id: NodeId) -> CodegenResult<(TypeId, Vec<TypeId>, TypeId)> {
        let lambda_type_id = self.get_expr_type(&node_id).ok_or_else(|| {
            CodegenError::not_found("lambda type in sema for node", format!("{node_id:?}"))
        })?;

        let arena = self.arena();
        let (sema_params, ret_id, _) = arena.unwrap_function(lambda_type_id).ok_or_else(|| {
            CodegenError::type_mismatch(
                "lambda expression",
                "function type",
                format!("{lambda_type_id:?}"),
            )
        })?;

        // In monomorphized context, substitute type parameters in the individual
        // param/return types. We can't substitute the whole function type because
        // the substituted function type may not be pre-computed in the arena.
        let param_type_ids: Vec<TypeId> = sema_params
            .iter()
            .map(|&p| self.substitute_type(p))
            .collect();
        let return_type_id = self.substitute_type(ret_id);

        Ok((lambda_type_id, param_type_ids, return_type_id))
    }

    /// Build the Cranelift signature for a lambda function.
    ///
    /// All lambdas use the closure calling convention: the first parameter is
    /// a pointer (the closure pointer), followed by the user-visible parameters.
    fn build_lambda_signature(
        &mut self,
        param_types: &[Type],
        return_type: Type,
        return_type_id: TypeId,
    ) -> Signature {
        let mut sig = self.jit_module().make_signature();
        sig.params.push(AbiParam::new(self.ptr_type())); // closure ptr
        for &param_ty in param_types {
            sig.params.push(AbiParam::new(param_ty));
        }
        // For fallible returns, use multi-value return (tag: i64, payload: i64)
        // For wide fallible (i128 success), use (tag: i64, low: i64, high: i64)
        if is_wide_fallible(return_type_id, self.arena()) {
            sig.returns.push(AbiParam::new(types::I64)); // tag
            sig.returns.push(AbiParam::new(types::I64)); // low
            sig.returns.push(AbiParam::new(types::I64)); // high
        } else if self.arena().unwrap_fallible(return_type_id).is_some() {
            sig.returns.push(AbiParam::new(types::I64)); // tag
            sig.returns.push(AbiParam::new(types::I64)); // payload
        } else {
            sig.returns.push(AbiParam::new(return_type));
        }
        sig
    }

    /// Compile a lambda expression (pure or capturing) - returns a closure pointer.
    fn compile_lambda_inner(
        &mut self,
        lambda: &LambdaExpr,
        node_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let captures = lambda.captures.borrow();
        let num_captures = captures.len();
        let has_captures = num_captures > 0;

        let lambda_id = self.next_lambda_id();

        // Get param and return types from sema
        let (func_type_id, param_type_ids, return_type_id) = self.get_lambda_types(node_id)?;

        // Convert to Cranelift types
        let param_types = self.cranelift_types(&param_type_ids);
        let return_type = self.cranelift_type(return_type_id);
        let ptr_type = self.ptr_type();

        let sig = self.build_lambda_signature(&param_types, return_type, return_type_id);

        let func_key = self.funcs().intern_lambda(lambda_id);
        let lambda_name = self.funcs().display(func_key);
        let func_id = self
            .jit_module()
            .declare_function(&lambda_name, cranelift_module::Linkage::Local, &sig)
            .map_err(CodegenError::cranelift)?;

        self.funcs().set_func_id(func_key, func_id);
        self.funcs().set_return_type(func_key, return_type_id);

        // Build capture bindings if this lambda captures variables
        let capture_bindings = if has_captures {
            let parent_captures = self.captures.as_ref().map(|c| c.bindings);
            Some(build_capture_bindings(
                &captures,
                &self.vars,
                parent_captures,
                self.arena(),
            ))
        } else {
            None
        };

        let mut lambda_ctx = self.jit_module().make_context();
        lambda_ctx.func.signature = sig;

        // Build params: Vec<(Symbol, TypeId, Type)>
        let params: Vec<(Symbol, TypeId, Type)> = lambda
            .params
            .iter()
            .enumerate()
            .map(|(i, p)| (p.name, param_type_ids[i], param_types[i]))
            .collect();

        // Compile the lambda body
        {
            let mut lambda_builder_ctx = FunctionBuilderContext::new();
            let lambda_builder =
                FunctionBuilder::new(&mut lambda_ctx.func, &mut lambda_builder_ctx);

            let config = FunctionCompileConfig::lambda(
                &lambda.body,
                params,
                return_type_id,
                capture_bindings.as_ref(),
                ptr_type,
            );

            // Forward parent substitutions so lambdas inside monomorphized
            // methods re-resolve type-parameter method calls on concrete types.
            compile_function_inner_with_params(
                lambda_builder,
                self.codegen_ctx,
                self.env,
                config,
                self.current_module(),
                self.substitutions,
            )?;
        }

        self.jit_module()
            .define_function(func_id, &mut lambda_ctx)
            .map_err(CodegenError::cranelift)?;

        let func_ref = self
            .codegen_ctx
            .module
            .declare_func_in_func(func_id, self.builder.func);
        let func_addr = self.builder.ins().func_addr(ptr_type, func_ref);

        // Allocate closure
        let alloc_ref = self.runtime_func_ref(RuntimeKey::ClosureAlloc)?;
        let num_captures_val = self.builder.ins().iconst(types::I64, num_captures as i64);
        let alloc_call = self
            .builder
            .ins()
            .call(alloc_ref, &[func_addr, num_captures_val]);
        let closure_ptr = self.builder.inst_results(alloc_call)[0];

        // Set up captures if this is a capturing lambda
        if has_captures {
            self.setup_closure_captures(&captures, closure_ptr)?;
        }

        // Use the type ID from sema (already computed during type checking)
        Ok(CompiledValue::new(closure_ptr, ptr_type, func_type_id))
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
        let heap_alloc_ref = self.runtime_func_ref(RuntimeKey::HeapAlloc)?;
        let rc_inc_ref = self.runtime_func_ref(RuntimeKey::RcInc)?;

        for (i, capture) in captures.iter().enumerate() {
            let (current_value, vole_type_id, is_self_capture) =
                self.resolve_capture(capture, closure_ptr)?;

            // Self-captures are weak references (no rc_inc, no rc_dec on drop)
            // to break the reference cycle: closure -> self-capture -> closure.
            let is_rc = !is_self_capture && self.rc_state(vole_type_id).is_capture();

            // If the capture is RC, increment its refcount (the closure now shares ownership)
            if is_rc {
                self.builder.ins().call(rc_inc_ref, &[current_value]);
            }

            let size = self.type_size(vole_type_id);
            let size_val = self.builder.ins().iconst(types::I64, size as i64);

            let alloc_call = self.builder.ins().call(heap_alloc_ref, &[size_val]);
            let heap_ptr = self.builder.inst_results(alloc_call)[0];

            // Structs are stack-allocated pointers -- we must copy the full struct
            // data into the heap allocation (not just store the stack pointer,
            // which would dangle after the creating function returns).
            self.copy_value_to_heap(current_value, heap_ptr, vole_type_id);

            let index_val = self.builder.ins().iconst(types::I64, i as i64);
            self.builder
                .ins()
                .call(set_capture_ref, &[closure_ptr, index_val, heap_ptr]);

            // Set the capture kind so closure_drop knows which captures need rc_dec
            let kind_val = self.builder.ins().iconst(types::I8, is_rc as i64);
            self.builder
                .ins()
                .call(set_kind_ref, &[closure_ptr, index_val, kind_val]);
        }

        Ok(())
    }

    /// Resolve a captured variable's value and type.
    ///
    /// Returns (value, type_id, is_self_capture).
    fn resolve_capture(
        &mut self,
        capture: &Capture,
        closure_ptr: Value,
    ) -> CodegenResult<(Value, TypeId, bool)> {
        let is_self_capture = Some(capture.name) == self.self_capture;

        if is_self_capture {
            // Self-capture: use the closure pointer we just created
            let (_, ty) = self.vars.get(&capture.name).ok_or_else(|| {
                CodegenError::not_found("self-captured variable", format!("{:?}", capture.name))
            })?;
            Ok((closure_ptr, *ty, true))
        } else if let Some((var, ty)) = self.vars.get(&capture.name) {
            // Normal capture: load from local variable
            Ok((self.builder.use_var(*var), *ty, false))
        } else if let Some(binding) = self.get_capture(&capture.name).copied() {
            // Transitive capture: load from parent closure's captures
            let captured = self.load_capture(&binding)?;
            Ok((captured.value, captured.type_id, false))
        } else {
            Err(CodegenError::not_found(
                "captured variable",
                format!("{:?}", capture.name),
            ))
        }
    }

    /// Copy a value into a heap allocation, handling structs with multiple slots.
    fn copy_value_to_heap(&mut self, value: Value, heap_ptr: Value, type_id: TypeId) {
        if let Some(flat_count) = self.struct_flat_slot_count(type_id) {
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

    /// Compile a lambda expression
    pub fn lambda(&mut self, lambda: &LambdaExpr, node_id: NodeId) -> CodegenResult<CompiledValue> {
        self.compile_lambda_inner(lambda, node_id)
    }
}
