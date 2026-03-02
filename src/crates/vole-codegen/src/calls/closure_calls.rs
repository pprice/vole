// calls/closure_calls.rs
//
// Closure call compilation: calling closures, building closure signatures,
// and signature coercion utilities.

use cranelift::prelude::*;
use cranelift_codegen::ir::SigRef;
use cranelift_module::Module;
use smallvec::{SmallVec, smallvec};

use vole_identity::{NodeId, TypeId, VirTypeId};

use crate::errors::{CodegenError, CodegenResult};
use crate::structs::methods::ArgSource;
use crate::types::CompiledValue;
use crate::union_layout;

use super::super::RuntimeKey;
use super::super::context::Cg;
use crate::ops::sextend_const;

/// SmallVec for call arguments - most calls have <= 8 args
type ArgVec = SmallVec<[Value; 8]>;

impl<'a, 'b, 'ctx> Cg<'a, 'b, 'ctx> {
    /// Call a function via variable (dispatches to closure or pure function call)
    pub(super) fn call_closure(
        &mut self,
        func_var: Variable,
        func_type_id: TypeId,
        arg_source: &ArgSource<'_>,
        call_expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let func_ptr_or_closure = self.builder.use_var(func_var);
        let func_vir_type_id = self.vir_lookup(func_type_id);
        self.call_closure_value(
            func_ptr_or_closure,
            func_vir_type_id,
            arg_source,
            call_expr_id,
        )
    }

    /// Call a function via value (always uses closure calling convention now that
    /// all lambdas are wrapped in Closure structs for consistent behavior)
    pub(super) fn call_closure_value(
        &mut self,
        func_ptr_or_closure: Value,
        func_vir_type_id: VirTypeId,
        arg_source: &ArgSource<'_>,
        call_expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        // Always use closure calling convention since all lambdas are now
        // wrapped in Closure structs for consistency with interface dispatch
        self.call_actual_closure(
            func_ptr_or_closure,
            func_vir_type_id,
            arg_source,
            call_expr_id,
        )
    }

    /// Build a Cranelift call signature for a closure call, returning the signature
    /// along with the parameter TypeIds and return TypeId.
    fn build_closure_call_signature(
        &mut self,
        func_vir_type_id: VirTypeId,
    ) -> CodegenResult<(Signature, Vec<TypeId>, TypeId)> {
        // Get function components from VirTypeTable
        let (params, ret) = self
            .vir_query_unwrap_function_sema_v(func_vir_type_id)
            .ok_or_else(|| {
                CodegenError::type_mismatch(
                    "call_actual_closure",
                    "function type",
                    "non-function type",
                )
            })?;

        // Build signature (closure ptr + params)
        let mut sig = self.jit_module().make_signature();
        sig.params.push(AbiParam::new(self.ptr_type())); // closure ptr
        for &param_type_id in &params {
            sig.params
                .push(AbiParam::new(self.cranelift_type(param_type_id)));
        }
        if !self.vir_query_is_void(ret) {
            // For fallible returns, use multi-value return (tag: i64, payload: i64)
            // For wide fallible (i128 success), use (tag: i64, low: i64, high: i64)
            if self.vir_query_is_wide_fallible(ret) {
                sig.returns.push(AbiParam::new(types::I64)); // tag
                sig.returns.push(AbiParam::new(types::I64)); // low
                sig.returns.push(AbiParam::new(types::I64)); // high
            } else if self
                .vir_query_unwrap_fallible_v(self.vir_lookup(ret))
                .is_some()
            {
                sig.returns.push(AbiParam::new(types::I64)); // tag
                sig.returns.push(AbiParam::new(types::I64)); // payload
            } else {
                sig.returns
                    .push(AbiParam::new(self.vir_query_type_to_cranelift(ret)));
            }
        }

        Ok((sig, params, ret))
    }

    /// Call an actual closure (with closure pointer).
    ///
    /// Accepts `ArgSource` so both AST and VIR call sites can share this path.
    /// Lambda defaults come from `self.vir_lambda_defaults` (populated by VIR
    /// call dispatch).
    /// Named-arg reordering comes from `self.vir_resolved_call_args` (populated
    /// by VIR call dispatch).
    fn call_actual_closure(
        &mut self,
        closure_ptr: Value,
        func_vir_type_id: VirTypeId,
        arg_source: &ArgSource<'_>,
        _call_expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let func_ptr = self.call_runtime(RuntimeKey::ClosureGetFunc, &[closure_ptr])?;

        let (sig, params, ret) = self.build_closure_call_signature(func_vir_type_id)?;

        let mut args: ArgVec = smallvec![closure_ptr];

        // Check if this call has lambda defaults from VIR dispatch.
        let lambda_defaults =
            self.vir_lambda_defaults
                .take()
                .map(|info| vole_sema::LambdaDefaults {
                    required_params: info.required_params,
                    lambda_node_id: info.lambda_node_id,
                });

        // Compile provided arguments, tracking RC temps for cleanup.
        // When named args were used, sema stored a resolved_call_args mapping that tells
        // us which arg_source[j] fills each parameter slot i (and None means use the default).
        let mut rc_temp_args = Vec::new();
        let arg_count = arg_source.len();
        let expected_params = params.len();
        let mapping_is_valid = |mapping: &[Option<usize>]| {
            if mapping.len() != expected_params {
                return false;
            }
            let mut seen = vec![false; arg_count];
            let mut mapped_count = 0usize;
            for call_idx in mapping.iter().flatten().copied() {
                if call_idx >= arg_count || seen[call_idx] {
                    return false;
                }
                seen[call_idx] = true;
                mapped_count += 1;
            }
            mapped_count == arg_count
        };
        let named_mapping = self
            .vir_resolved_call_args
            .take()
            .filter(|mapping| mapping_is_valid(mapping));
        if let Some(ref mapping) = named_mapping {
            self.compile_closure_named_args(
                arg_source,
                mapping,
                &params,
                &lambda_defaults,
                &mut args,
                &mut rc_temp_args,
            )?;
        } else {
            self.compile_closure_positional_args(
                arg_source,
                &params,
                &lambda_defaults,
                &mut args,
                &mut rc_temp_args,
            )?;
        }

        let sig_ref = self.import_sig_and_coerce_args(sig, &mut args);

        let call_inst = self.emit_call_indirect(sig_ref, func_ptr, &args);

        // Dec RC temp args after the call has consumed them
        self.consume_rc_args(&mut rc_temp_args)?;
        let results = self.builder.inst_results(call_inst);

        if results.is_empty() {
            Ok(self.void_value())
        } else if results.len() == 2
            && self
                .vir_query_unwrap_fallible_v(self.vir_lookup(ret))
                .is_some()
        {
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

            Ok(CompiledValue::new(ptr, ptr_type, self.vir_lookup(ret)))
        } else {
            // If the return type is a union, the returned value is a pointer to callee's stack.
            // We need to copy the union data to our own stack to prevent it from being
            // overwritten on subsequent calls to the same closure.
            if self.vir_query_is_union(ret) {
                let src_ptr = results[0];
                Ok(self.copy_union_ptr_to_local(src_ptr, ret))
            } else {
                Ok(self.compiled(results[0], ret))
            }
        }
    }

    /// Compile closure arguments in named-arg order using the sema-provided mapping.
    ///
    /// `mapping[slot] = Some(j)` means arg_source[j] fills parameter slot `slot`.
    /// `mapping[slot] = None` means the slot uses its lambda default expression.
    fn compile_closure_named_args(
        &mut self,
        arg_source: &ArgSource<'_>,
        mapping: &[Option<usize>],
        params: &[TypeId],
        lambda_defaults: &Option<vole_sema::LambdaDefaults>,
        args: &mut ArgVec,
        rc_temp_args: &mut Vec<CompiledValue>,
    ) -> CodegenResult<()> {
        // Named arg reordering: compile each slot in parameter order using the mapping.
        // For None slots, compile the lambda's default expression from VIR.
        let lambda_node_id = lambda_defaults.as_ref().map(|d| d.lambda_node_id);

        for (slot, opt_call_idx) in mapping.iter().enumerate() {
            let param_type_id = params[slot];
            let compiled_val = if let Some(&Some(call_arg_idx)) = Some(opt_call_idx) {
                let compiled =
                    self.compile_arg_with_expected_type(arg_source, call_arg_idx, param_type_id)?;
                if compiled.is_owned() {
                    rc_temp_args.push(compiled);
                }
                let compiled =
                    self.coerce_to_type(compiled, self.vir_lookup_or_compat(param_type_id))?;
                compiled.value
            } else if let Some(lambda_node_id) = lambda_node_id {
                let (default_vals, rc_owned) =
                    self.compile_lambda_defaults(lambda_node_id, slot, &[param_type_id])?;
                rc_temp_args.extend(rc_owned);
                if let Some(&val) = default_vals.first() {
                    val
                } else {
                    continue;
                }
            } else {
                continue;
            };
            args.push(compiled_val);
        }
        Ok(())
    }

    /// Compile closure arguments in positional order, appending defaults for
    /// omitted parameters.
    fn compile_closure_positional_args(
        &mut self,
        arg_source: &ArgSource<'_>,
        params: &[TypeId],
        lambda_defaults: &Option<vole_sema::LambdaDefaults>,
        args: &mut ArgVec,
        rc_temp_args: &mut Vec<CompiledValue>,
    ) -> CodegenResult<()> {
        let arg_count = arg_source.len();
        for (i, &param_type_id) in params.iter().enumerate().take(arg_count) {
            let compiled = self.compile_arg_with_expected_type(arg_source, i, param_type_id)?;
            if compiled.is_owned() {
                rc_temp_args.push(compiled);
            }
            let compiled =
                self.coerce_to_type(compiled, self.vir_lookup_or_compat(param_type_id))?;
            args.push(compiled.value);
        }

        // Compile default expressions for missing arguments
        if let Some(defaults_info) = lambda_defaults
            && arg_count < params.len()
        {
            let lambda_node_id = defaults_info.lambda_node_id;
            let skip = arg_count;
            let (default_vals, rc_owned) =
                self.compile_lambda_defaults(lambda_node_id, skip, &params[skip..])?;
            rc_temp_args.extend(rc_owned);
            args.extend(default_vals);
        }
        Ok(())
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
