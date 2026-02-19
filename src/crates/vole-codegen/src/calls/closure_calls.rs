// calls/closure_calls.rs
//
// Closure call compilation: calling closures, building closure signatures,
// and signature coercion utilities.

use cranelift::prelude::*;
use cranelift_codegen::ir::SigRef;
use cranelift_module::Module;
use smallvec::{SmallVec, smallvec};

use vole_frontend::ast::CallExpr;
use vole_frontend::{Expr, NodeId};
use vole_sema::type_arena::TypeId;

use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, is_wide_fallible, type_id_to_cranelift};
use crate::union_layout;

use super::super::RuntimeKey;
use super::super::context::{Cg, deref_expr_ptr};
use crate::ops::sextend_const;

/// SmallVec for call arguments - most calls have <= 8 args
type ArgVec = SmallVec<[Value; 8]>;

impl Cg<'_, '_, '_> {
    /// Call a function via variable (dispatches to closure or pure function call)
    pub(super) fn call_closure(
        &mut self,
        func_var: Variable,
        func_type_id: TypeId,
        call: &CallExpr,
        call_expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let func_ptr_or_closure = self.builder.use_var(func_var);
        self.call_closure_value(func_ptr_or_closure, func_type_id, call, call_expr_id)
    }

    /// Call a function via value (always uses closure calling convention now that
    /// all lambdas are wrapped in Closure structs for consistent behavior)
    pub(super) fn call_closure_value(
        &mut self,
        func_ptr_or_closure: Value,
        func_type_id: TypeId,
        call: &CallExpr,
        call_expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        // Always use closure calling convention since all lambdas are now
        // wrapped in Closure structs for consistency with interface dispatch
        self.call_actual_closure(func_ptr_or_closure, func_type_id, call, call_expr_id)
    }

    /// Build a Cranelift call signature for a closure call, returning the signature
    /// along with the parameter TypeIds and return TypeId.
    fn build_closure_call_signature(
        &mut self,
        func_type_id: TypeId,
    ) -> CodegenResult<(Signature, Vec<TypeId>, TypeId)> {
        // Get function components from arena
        let (params, ret, _is_closure) = {
            let arena = self.arena();
            let (params, ret, is_closure) =
                arena.unwrap_function(func_type_id).ok_or_else(|| {
                    CodegenError::type_mismatch(
                        "call_actual_closure",
                        "function type",
                        "non-function type",
                    )
                })?;
            (params.clone(), ret, is_closure)
        };

        // Build signature (closure ptr + params)
        let mut sig = self.jit_module().make_signature();
        sig.params.push(AbiParam::new(self.ptr_type())); // closure ptr
        for &param_type_id in &params {
            sig.params
                .push(AbiParam::new(self.cranelift_type(param_type_id)));
        }
        let arena = self.arena();
        if !arena.is_void(ret) {
            // For fallible returns, use multi-value return (tag: i64, payload: i64)
            // For wide fallible (i128 success), use (tag: i64, low: i64, high: i64)
            if is_wide_fallible(ret, arena) {
                sig.returns.push(AbiParam::new(types::I64)); // tag
                sig.returns.push(AbiParam::new(types::I64)); // low
                sig.returns.push(AbiParam::new(types::I64)); // high
            } else if arena.unwrap_fallible(ret).is_some() {
                sig.returns.push(AbiParam::new(types::I64)); // tag
                sig.returns.push(AbiParam::new(types::I64)); // payload
            } else {
                sig.returns.push(AbiParam::new(type_id_to_cranelift(
                    ret,
                    arena,
                    self.ptr_type(),
                )));
            }
        }

        Ok((sig, params.to_vec(), ret))
    }

    /// Call an actual closure (with closure pointer)
    fn call_actual_closure(
        &mut self,
        closure_ptr: Value,
        func_type_id: TypeId,
        call: &CallExpr,
        call_expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let func_ptr = self.call_runtime(RuntimeKey::ClosureGetFunc, &[closure_ptr])?;

        let (sig, params, ret) = self.build_closure_call_signature(func_type_id)?;

        let mut args: ArgVec = smallvec![closure_ptr];

        // Check if this call has lambda defaults
        let lambda_defaults = self
            .analyzed()
            .expression_data
            .get_lambda_defaults(call_expr_id)
            .cloned();

        // Compile provided arguments, tracking RC temps for cleanup
        let mut rc_temp_args = Vec::new();
        for (arg, &param_type_id) in call.args.iter().zip(params.iter()) {
            let compiled = self.expr_with_expected_type(arg, param_type_id)?;
            if compiled.is_owned() {
                rc_temp_args.push(compiled);
            }
            let compiled = self.coerce_to_type(compiled, param_type_id)?;
            args.push(compiled.value);
        }

        // Compile default expressions for missing arguments
        if let Some(defaults_info) = lambda_defaults
            && call.args.len() < params.len()
        {
            // Find the lambda expression by NodeId to get its default expressions
            // Use raw pointers to avoid borrow conflicts (the data lives in Program AST
            // which is owned by AnalyzedProgram and outlives this compilation session)
            let lambda_node_id = defaults_info.lambda_node_id;
            let Some(lambda) = self.find_lambda_by_node_id(lambda_node_id) else {
                return Err(CodegenError::internal_with_context(
                    "lambda expression not found",
                    format!("NodeId {:?}", lambda_node_id),
                ));
            };
            // Get raw pointers to the default expressions for params we need
            let default_ptrs: Vec<Option<*const Expr>> = lambda
                .params
                .iter()
                .skip(call.args.len())
                .map(|p| p.default_value.as_ref().map(|e| e.as_ref() as *const Expr))
                .collect();

            // Compile defaults for missing params (starting from call.args.len())
            for (default_ptr_opt, &param_type_id) in
                default_ptrs.iter().zip(params.iter().skip(call.args.len()))
            {
                let Some(default_ptr) = default_ptr_opt else {
                    return Err(CodegenError::internal(
                        "missing default expression for parameter in lambda call",
                    ));
                };
                let default_expr = deref_expr_ptr(self.analyzed(), *default_ptr);
                let compiled = self.expr_with_expected_type(default_expr, param_type_id)?;
                if compiled.is_owned() {
                    rc_temp_args.push(compiled);
                }
                let compiled = self.coerce_to_type(compiled, param_type_id)?;
                args.push(compiled.value);
            }
        }

        let sig_ref = self.import_sig_and_coerce_args(sig, &mut args);

        let call_inst = self.builder.ins().call_indirect(sig_ref, func_ptr, &args);
        self.field_cache.clear(); // Callee may mutate instance fields

        // Dec RC temp args after the call has consumed them
        self.consume_rc_args(&mut rc_temp_args)?;
        let results = self.builder.inst_results(call_inst);

        if results.is_empty() {
            Ok(self.void_value())
        } else if results.len() == 2 && self.arena().unwrap_fallible(ret).is_some() {
            // Fallible multi-value return: pack (tag, payload) into stack slot
            let tag = results[0];
            let payload = results[1];

            let slot_size = union_layout::STANDARD_SIZE;
            let slot = self.alloc_stack(slot_size);

            self.builder.ins().stack_store(tag, slot, 0);
            self.builder
                .ins()
                .stack_store(payload, slot, union_layout::PAYLOAD_OFFSET);

            let ptr_type = self.ptr_type();
            let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

            Ok(CompiledValue::new(ptr, ptr_type, ret))
        } else {
            // If the return type is a union, the returned value is a pointer to callee's stack.
            // We need to copy the union data to our own stack to prevent it from being
            // overwritten on subsequent calls to the same closure.
            if self.arena().is_union(ret) {
                let src_ptr = results[0];
                Ok(self.copy_union_ptr_to_local(src_ptr, ret))
            } else {
                Ok(self.compiled(results[0], ret))
            }
        }
    }

    /// Import a signature and coerce argument values to match the expected parameter types.
    /// Handles bool values from when/match block params that may be i64 when the
    /// signature expects i8.
    pub(crate) fn import_sig_and_coerce_args(
        &mut self,
        sig: Signature,
        args: &mut [Value],
    ) -> SigRef {
        let sig_param_types: Vec<_> = sig.params.iter().map(|p| p.value_type).collect();
        let sig_ref = self.builder.import_signature(sig);
        for (i, &expected_ty) in sig_param_types.iter().enumerate() {
            if i < args.len() {
                let actual_ty = self.builder.func.dfg.value_type(args[i]);
                if actual_ty != expected_ty && actual_ty.is_int() && expected_ty.is_int() {
                    args[i] = if expected_ty.bits() < actual_ty.bits() {
                        self.builder.ins().ireduce(expected_ty, args[i])
                    } else {
                        sextend_const(self.builder, expected_ty, args[i])
                    };
                }
            }
        }
        sig_ref
    }
}
