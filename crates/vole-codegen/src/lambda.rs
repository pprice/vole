// src/codegen/lambda.rs
//
// Lambda/closure compilation support for code generation.

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_module::Module;

use vole_frontend::{LambdaExpr, NodeId, Symbol};
use vole_sema::type_arena::{TypeArena, TypeId, TypeIdVec};

use super::RuntimeFn;
use super::compiler::common::{FunctionCompileConfig, compile_function_inner_with_params};
use super::context::Cg;
use super::types::{CompiledValue, type_id_to_cranelift};

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
    variables: &HashMap<Symbol, (Variable, TypeId)>,
    arena: &TypeArena,
) -> HashMap<Symbol, CaptureBinding> {
    let mut bindings = HashMap::new();
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
    /// Get lambda param and return types from explicit annotations or inference.
    ///
    /// First tries to get types from sema analysis via node_id.
    /// Falls back to AST annotations or inference if sema types unavailable.
    fn get_lambda_types(&self, lambda: &LambdaExpr, node_id: NodeId) -> (Vec<TypeId>, TypeId) {
        // Try sema-inferred types first
        if let Some(lambda_type_id) = self.get_expr_type(&node_id) {
            let arena = self.arena();
            if let Some((sema_params, ret_id, _)) = arena.unwrap_function(lambda_type_id) {
                return (sema_params.to_vec(), ret_id);
            }
        }

        // Fallback: resolve from AST annotations or infer
        let primitives = self.arena().primitives;

        // Build param type ids from AST annotations, defaulting to i64
        let param_type_ids: Vec<TypeId> = lambda
            .params
            .iter()
            .map(|p| {
                p.ty.as_ref()
                    .map(|t| self.resolve_type_expr(t))
                    .unwrap_or(primitives.i64)
            })
            .collect();

        // Get return type from annotation or infer from body
        let return_type_id = if let Some(t) = &lambda.return_type {
            self.resolve_type_expr(t)
        } else {
            let param_context: Vec<(Symbol, TypeId)> = lambda
                .params
                .iter()
                .zip(param_type_ids.iter())
                .map(|(p, &ty)| (p.name, ty))
                .collect();
            self.infer_lambda_return_type(&lambda.body, &param_context)
        };

        (param_type_ids, return_type_id)
    }

    /// Compile a pure lambda (no captures) - returns a closure pointer.
    fn compile_pure_lambda_inner(
        &mut self,
        lambda: &LambdaExpr,
        node_id: NodeId,
    ) -> Result<CompiledValue, String> {
        let lambda_id = self.next_lambda_id();

        // Get param and return types
        let (param_type_ids, return_type_id) = self.get_lambda_types(lambda, node_id);

        // Convert to Cranelift types
        let param_types: Vec<Type> = {
            let arena = self.arena();
            param_type_ids
                .iter()
                .map(|&ty| type_id_to_cranelift(ty, &arena, self.ptr_type()))
                .collect()
        };

        let return_type = type_id_to_cranelift(return_type_id, &self.arena(), self.ptr_type());

        // Always use closure calling convention for consistency
        let mut sig = self.jit_module().make_signature();
        sig.params.push(AbiParam::new(self.ptr_type())); // closure ptr (ignored for pure)
        for &param_ty in &param_types {
            sig.params.push(AbiParam::new(param_ty));
        }
        sig.returns.push(AbiParam::new(return_type));

        let (name_id, func_key) = self.funcs().intern_lambda_name(lambda_id);
        let lambda_name = self.funcs().name_table_rc().borrow().display(name_id);
        let func_id = self
            .jit_module()
            .declare_function(&lambda_name, cranelift_module::Linkage::Local, &sig)
            .map_err(|e| e.to_string())?;

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
        let alloc_key = self
            .funcs()
            .runtime_key(RuntimeFn::ClosureAlloc)
            .ok_or_else(|| "vole_closure_alloc not found".to_string())?;
        let alloc_id = self
            .funcs()
            .func_id(alloc_key)
            .ok_or_else(|| "vole_closure_alloc not found".to_string())?;
        let alloc_ref = self
            .codegen_ctx
            .module
            .declare_func_in_func(alloc_id, self.builder.func);
        let zero_captures = self.builder.ins().iconst(types::I64, 0);
        let alloc_call = self
            .builder
            .ins()
            .call(alloc_ref, &[func_addr, zero_captures]);
        let closure_ptr = self.builder.inst_results(alloc_call)[0];

        // Create TypeId for the closure
        let func_type_id = {
            let param_ids: TypeIdVec = param_type_ids.iter().copied().collect();
            self.update().function(param_ids, return_type_id, true)
        };

        Ok(CompiledValue {
            value: closure_ptr,
            ty: self.ptr_type(),
            type_id: func_type_id,
        })
    }

    /// Compile a lambda with captures - returns a closure pointer.
    fn compile_capturing_lambda_inner(
        &mut self,
        lambda: &LambdaExpr,
        node_id: NodeId,
    ) -> Result<CompiledValue, String> {
        let captures = lambda.captures.borrow();
        let num_captures = captures.len();

        let lambda_id = self.next_lambda_id();

        // Get param and return types
        let (param_type_ids, return_type_id) = self.get_lambda_types(lambda, node_id);

        // Convert to Cranelift types
        let param_types: Vec<Type> = {
            let arena = self.arena();
            param_type_ids
                .iter()
                .map(|&ty| type_id_to_cranelift(ty, &arena, self.ptr_type()))
                .collect()
        };

        let return_type = type_id_to_cranelift(return_type_id, &self.arena(), self.ptr_type());

        // First param is the closure pointer
        let mut sig = self.jit_module().make_signature();
        let ptr_type = self.ptr_type();
        sig.params.push(AbiParam::new(ptr_type));
        for &param_ty in &param_types {
            sig.params.push(AbiParam::new(param_ty));
        }
        sig.returns.push(AbiParam::new(return_type));

        let (name_id, func_key) = self.funcs().intern_lambda_name(lambda_id);
        let lambda_name = self.funcs().name_table_rc().borrow().display(name_id);
        let func_id = self
            .jit_module()
            .declare_function(&lambda_name, cranelift_module::Linkage::Local, &sig)
            .map_err(|e| e.to_string())?;

        self.funcs().set_func_id(func_key, func_id);
        self.funcs().set_return_type(func_key, return_type_id);

        let capture_bindings = build_capture_bindings(&captures, &self.vars, &self.arena());

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
        let alloc_key = self
            .funcs()
            .runtime_key(RuntimeFn::ClosureAlloc)
            .ok_or_else(|| "vole_closure_alloc not found".to_string())?;
        let alloc_id = self
            .funcs()
            .func_id(alloc_key)
            .ok_or_else(|| "vole_closure_alloc not found".to_string())?;
        let alloc_ref = self
            .codegen_ctx
            .module
            .declare_func_in_func(alloc_id, self.builder.func);
        let num_captures_val = self.builder.ins().iconst(types::I64, num_captures as i64);
        let alloc_call = self
            .builder
            .ins()
            .call(alloc_ref, &[func_addr, num_captures_val]);
        let closure_ptr = self.builder.inst_results(alloc_call)[0];

        // Set up each capture
        let set_capture_key = self
            .funcs()
            .runtime_key(RuntimeFn::ClosureSetCapture)
            .ok_or_else(|| "vole_closure_set_capture not found".to_string())?;
        let set_capture_id = self
            .funcs()
            .func_id(set_capture_key)
            .ok_or_else(|| "vole_closure_set_capture not found".to_string())?;
        let set_capture_ref = self
            .codegen_ctx
            .module
            .declare_func_in_func(set_capture_id, self.builder.func);

        let heap_alloc_key = self
            .funcs()
            .runtime_key(RuntimeFn::HeapAlloc)
            .ok_or_else(|| "vole_heap_alloc not found".to_string())?;
        let heap_alloc_id = self
            .funcs()
            .func_id(heap_alloc_key)
            .ok_or_else(|| "vole_heap_alloc not found".to_string())?;
        let heap_alloc_ref = self
            .codegen_ctx
            .module
            .declare_func_in_func(heap_alloc_id, self.builder.func);

        for (i, capture) in captures.iter().enumerate() {
            // For self-captures (recursive lambdas), use the closure pointer itself
            let (current_value, vole_type_id) = if Some(capture.name) == self.self_capture {
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
        }

        // Create TypeId for the closure
        let func_type_id = {
            let param_ids: TypeIdVec = param_type_ids.iter().copied().collect();
            self.update().function(param_ids, return_type_id, true)
        };

        Ok(CompiledValue {
            value: closure_ptr,
            ty: ptr_type,
            type_id: func_type_id,
        })
    }

    /// Compile a lambda expression
    pub fn lambda(
        &mut self,
        lambda: &LambdaExpr,
        node_id: NodeId,
    ) -> Result<CompiledValue, String> {
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
