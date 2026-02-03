// src/codegen/lambda.rs
//
// Lambda/closure compilation support for code generation.

use rustc_hash::FxHashMap;

use cranelift::prelude::*;
use cranelift_module::Module;

use vole_frontend::{LambdaExpr, NodeId, Symbol};
use vole_sema::type_arena::{TypeArena, TypeId};

use super::RuntimeFn;
use super::compiler::common::{FunctionCompileConfig, compile_function_inner_with_params};
use super::context::Cg;
use super::types::CompiledValue;
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

/// Build capture bindings from a list of captures and variable types
pub(crate) fn build_capture_bindings(
    captures: &[vole_frontend::Capture],
    variables: &FxHashMap<Symbol, (Variable, TypeId)>,
    arena: &TypeArena,
) -> FxHashMap<Symbol, CaptureBinding> {
    let mut bindings = FxHashMap::default();
    let default_type_id = arena.primitives.i64;
    for (i, capture) in captures.iter().enumerate() {
        let vole_type_id = variables
            .get(&capture.name)
            .map(|(_, ty)| *ty)
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
        let lambda_type_id = self
            .get_expr_type(&node_id)
            .ok_or_else(|| format!("Lambda type not found in sema for node {:?}", node_id))?;

        let arena = self.arena();
        let (sema_params, ret_id, _) = arena.unwrap_function(lambda_type_id).ok_or_else(|| {
            format!(
                "Lambda expression has non-function type {:?}",
                lambda_type_id
            )
        })?;

        Ok((lambda_type_id, sema_params.to_vec(), ret_id))
    }

    /// Compile a pure lambda (no captures) - returns a closure pointer.
    fn compile_pure_lambda_inner(
        &mut self,
        lambda: &LambdaExpr,
        node_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let lambda_id = self.next_lambda_id();

        // Get param and return types from sema
        let (func_type_id, param_type_ids, return_type_id) = self.get_lambda_types(node_id)?;

        // Convert to Cranelift types
        let param_types = self.cranelift_types(&param_type_ids);
        let return_type = self.cranelift_type(return_type_id);

        // Always use closure calling convention for consistency
        let mut sig = self.jit_module().make_signature();
        sig.params.push(AbiParam::new(self.ptr_type())); // closure ptr (ignored for pure)
        for &param_ty in &param_types {
            sig.params.push(AbiParam::new(param_ty));
        }
        // For fallible returns, use multi-value return (tag: i64, payload: i64)
        if self.arena().unwrap_fallible(return_type_id).is_some() {
            sig.returns.push(AbiParam::new(types::I64)); // tag
            sig.returns.push(AbiParam::new(types::I64)); // payload
        } else {
            sig.returns.push(AbiParam::new(return_type));
        }

        let func_key = self.funcs().intern_lambda(lambda_id);
        let lambda_name = self.funcs().display(func_key);
        let func_id = self
            .jit_module()
            .declare_function(&lambda_name, cranelift_module::Linkage::Local, &sig)
            .map_err(|e| CodegenError::internal_with_context("cranelift error", e.to_string()))?;

        self.funcs().set_func_id(func_key, func_id);
        self.funcs().set_return_type(func_key, return_type_id);

        let mut lambda_ctx = self.jit_module().make_context();
        lambda_ctx.func.signature = sig.clone();

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

            let config = FunctionCompileConfig::pure_lambda(&lambda.body, params, return_type_id);

            compile_function_inner_with_params(
                lambda_builder,
                self.codegen_ctx,
                self.env,
                config,
                None,
                None,
            )?;
        }

        self.jit_module()
            .define_function(func_id, &mut lambda_ctx)
            .map_err(|e| format!("Failed to define lambda: {:?}", e))?;

        let func_ref = self
            .codegen_ctx
            .module
            .declare_func_in_func(func_id, self.builder.func);
        let ptr_type = self.ptr_type();
        let func_addr = self.builder.ins().func_addr(ptr_type, func_ref);

        // Wrap in Closure struct for consistent calling convention
        let alloc_ref = self.runtime_func_ref(RuntimeFn::ClosureAlloc)?;
        let zero_captures = self.builder.ins().iconst(types::I64, 0);
        let alloc_call = self
            .builder
            .ins()
            .call(alloc_ref, &[func_addr, zero_captures]);
        let closure_ptr = self.builder.inst_results(alloc_call)[0];

        // Use the type ID from sema (already computed during type checking)
        Ok(CompiledValue::new(
            closure_ptr,
            self.ptr_type(),
            func_type_id,
        ))
    }

    /// Compile a lambda with captures - returns a closure pointer.
    fn compile_capturing_lambda_inner(
        &mut self,
        lambda: &LambdaExpr,
        node_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let captures = lambda.captures.borrow();
        let num_captures = captures.len();

        let lambda_id = self.next_lambda_id();

        // Get param and return types from sema
        let (func_type_id, param_type_ids, return_type_id) = self.get_lambda_types(node_id)?;

        // Convert to Cranelift types
        let param_types = self.cranelift_types(&param_type_ids);
        let return_type = self.cranelift_type(return_type_id);

        // First param is the closure pointer
        let mut sig = self.jit_module().make_signature();
        let ptr_type = self.ptr_type();
        sig.params.push(AbiParam::new(ptr_type));
        for &param_ty in &param_types {
            sig.params.push(AbiParam::new(param_ty));
        }
        // For fallible returns, use multi-value return (tag: i64, payload: i64)
        if self.arena().unwrap_fallible(return_type_id).is_some() {
            sig.returns.push(AbiParam::new(types::I64)); // tag
            sig.returns.push(AbiParam::new(types::I64)); // payload
        } else {
            sig.returns.push(AbiParam::new(return_type));
        }

        let func_key = self.funcs().intern_lambda(lambda_id);
        let lambda_name = self.funcs().display(func_key);
        let func_id = self
            .jit_module()
            .declare_function(&lambda_name, cranelift_module::Linkage::Local, &sig)
            .map_err(|e| CodegenError::internal_with_context("cranelift error", e.to_string()))?;

        self.funcs().set_func_id(func_key, func_id);
        self.funcs().set_return_type(func_key, return_type_id);

        let capture_bindings = build_capture_bindings(&captures, &self.vars, self.arena());

        let mut lambda_ctx = self.jit_module().make_context();
        lambda_ctx.func.signature = sig.clone();

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

            let config = FunctionCompileConfig::capturing_lambda(
                &lambda.body,
                params,
                &capture_bindings,
                ptr_type,
                return_type_id,
            );

            compile_function_inner_with_params(
                lambda_builder,
                self.codegen_ctx,
                self.env,
                config,
                None,
                None,
            )?;
        }

        self.jit_module()
            .define_function(func_id, &mut lambda_ctx)
            .map_err(|e| format!("Failed to define lambda: {:?}", e))?;

        // Use split borrows to avoid borrow checker issues
        let func_ref = self
            .codegen_ctx
            .module
            .declare_func_in_func(func_id, self.builder.func);
        let func_addr = self.builder.ins().func_addr(ptr_type, func_ref);

        // Allocate closure
        let alloc_ref = self.runtime_func_ref(RuntimeFn::ClosureAlloc)?;
        let num_captures_val = self.builder.ins().iconst(types::I64, num_captures as i64);
        let alloc_call = self
            .builder
            .ins()
            .call(alloc_ref, &[func_addr, num_captures_val]);
        let closure_ptr = self.builder.inst_results(alloc_call)[0];

        // Set up each capture
        let set_capture_ref = self.runtime_func_ref(RuntimeFn::ClosureSetCapture)?;
        let set_kind_ref = self.runtime_func_ref(RuntimeFn::ClosureSetCaptureKind)?;
        let heap_alloc_ref = self.runtime_func_ref(RuntimeFn::HeapAlloc)?;
        let rc_inc_ref = self.runtime_func_ref(RuntimeFn::RcInc)?;

        for (i, capture) in captures.iter().enumerate() {
            // For self-captures (recursive lambdas), use the closure pointer itself
            let is_self_capture = Some(capture.name) == self.self_capture;
            let (current_value, vole_type_id) = if is_self_capture {
                // Self-capture: use the closure pointer we just created
                let (_, ty) = self.vars.get(&capture.name).ok_or_else(|| {
                    format!("Self-captured variable not found: {:?}", capture.name)
                })?;
                (closure_ptr, *ty)
            } else {
                // Normal capture: load from the variable
                let (var, ty) = self
                    .vars
                    .get(&capture.name)
                    .ok_or_else(|| format!("Captured variable not found: {:?}", capture.name))?;
                (self.builder.use_var(*var), *ty)
            };

            // Self-captures are weak references (no rc_inc, no rc_dec on drop)
            // to break the reference cycle: closure -> self-capture -> closure.
            let is_rc = if is_self_capture {
                false
            } else {
                self.rc_state(vole_type_id).is_capture()
            };

            // If the capture is RC, increment its refcount (the closure now shares ownership)
            if is_rc {
                self.builder.ins().call(rc_inc_ref, &[current_value]);
            }

            let size = self.type_size(vole_type_id);
            let size_val = self.builder.ins().iconst(types::I64, size as i64);

            let alloc_call = self.builder.ins().call(heap_alloc_ref, &[size_val]);
            let heap_ptr = self.builder.inst_results(alloc_call)[0];

            self.builder
                .ins()
                .store(MemFlags::new(), current_value, heap_ptr, 0);

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

        // Use the type ID from sema (already computed during type checking)
        Ok(CompiledValue::new(closure_ptr, ptr_type, func_type_id))
    }

    /// Compile a lambda expression
    pub fn lambda(&mut self, lambda: &LambdaExpr, node_id: NodeId) -> CodegenResult<CompiledValue> {
        let captures = lambda.captures.borrow();
        let has_captures = !captures.is_empty();
        drop(captures);

        if has_captures {
            self.compile_capturing_lambda_inner(lambda, node_id)
        } else {
            self.compile_pure_lambda_inner(lambda, node_id)
        }
    }
}
