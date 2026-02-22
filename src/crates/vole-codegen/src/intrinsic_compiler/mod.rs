// src/codegen/intrinsic_compiler/mod.rs
//
// Intrinsic compilation methods - main router for compiler intrinsic dispatch,
// external native function calls, and inline emission of array/string length.
//
// Sub-modules handle specific categories:
// - saturating: saturating arithmetic ops (add/sub/mul for signed/unsigned)
// - checked: checked arithmetic returning Optional<T>
// - int_ops: integer operation dispatch tables (unary/binary)

mod checked;
mod int_ops;
mod saturating;

use cranelift::prelude::{AbiParam, InstBuilder, IntCC, MemFlags, Value, types};
use cranelift_module::Module;

use vole_runtime::native_registry::NativeType;
use vole_sema::implement_registry::ExternalMethodInfo;
use vole_sema::type_arena::TypeId;

use crate::RuntimeKey;
use crate::callable_registry::{CallableKey, ResolvedCallable, resolve_callable_with_preference};
use crate::errors::{CodegenError, CodegenResult};
use crate::structs::convert_to_i64_for_storage;

use super::context::{Cg, resolve_external_names};
use super::types::{
    CompiledValue, array_element_tag_id, native_type_to_cranelift, type_id_to_cranelift,
};
use crate::ops::uextend_const;

/// Get signed integer min/max bounds for a given bit width.
fn signed_min_max(bits: u32) -> (i64, i64) {
    match bits {
        8 => (i8::MIN as i64, i8::MAX as i64),
        16 => (i16::MIN as i64, i16::MAX as i64),
        32 => (i32::MIN as i64, i32::MAX as i64),
        64 => (i64::MIN, i64::MAX),
        _ => panic!("Unsupported bit width: {}", bits),
    }
}

impl<'a, 'b, 'ctx> Cg<'a, 'b, 'ctx> {
    // ========== External native function calls ==========

    /// The module path for compiler intrinsics (e.g., f64.nan(), f32.infinity())
    pub const COMPILER_INTRINSIC_MODULE: &'static str = "vole:compiler_intrinsic";

    /// Call an external native function using TypeId for return type.
    /// If the module path is "vole:compiler_intrinsic", the call is handled as a
    /// compiler intrinsic (e.g., f64_nan emits a constant instead of an FFI call).
    pub fn call_external_id(
        &mut self,
        external_info: &ExternalMethodInfo,
        args: &[Value],
        return_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Get string names from NameId
        let (module_path, native_name) = resolve_external_names(self.name_table(), external_info)?;

        // Check if this is a compiler intrinsic
        if module_path == Self::COMPILER_INTRINSIC_MODULE {
            let key =
                crate::IntrinsicKey::try_from_name(native_name.as_str()).ok_or_else(|| {
                    CodegenError::not_found(
                        "intrinsic handler",
                        format!(
                            "\"{}\" (add handler in codegen/intrinsics.rs)",
                            native_name.as_str()
                        ),
                    )
                })?;
            return self.call_compiler_intrinsic_key_with_line(key, args, return_type_id, 0);
        }

        // Look up native function for FFI call
        let native_func = self
            .native_registry()
            .lookup(&module_path, &native_name)
            .ok_or_else(|| {
                CodegenError::not_found(
                    "native function",
                    format!("{}::{}", module_path, native_name),
                )
            })?;

        // Build the Cranelift signature from NativeSignature
        let ptr_type = self.ptr_type();
        let mut sig = self.jit_module().make_signature();
        for param_type in &native_func.signature.params {
            sig.params.push(AbiParam::new(native_type_to_cranelift(
                param_type, ptr_type,
            )));
        }
        if native_func.signature.return_type != NativeType::Nil {
            sig.returns.push(AbiParam::new(native_type_to_cranelift(
                &native_func.signature.return_type,
                ptr_type,
            )));
        }

        let func_ptr = native_func.ptr;

        // Coerce args to match the native signature types. Boolean values
        // flowing through block parameters (when/match) can be i64 while
        // the native signature expects i8.
        let coerced_args: Vec<Value> = args
            .iter()
            .zip(native_func.signature.params.iter())
            .map(|(&arg, param_type)| {
                let expected_ty = native_type_to_cranelift(param_type, ptr_type);
                let actual_ty = self.builder.func.dfg.value_type(arg);
                self.coerce_cranelift_value(arg, actual_ty, expected_ty)
            })
            .collect();

        // Try to devirtualize: emit a direct `call` if the symbol name is known.
        let call_inst = if let Some(func_ref) = self.try_import_native_func(func_ptr, &sig) {
            self.emit_call(func_ref, &coerced_args)
        } else {
            let sig_ref = self.builder.import_signature(sig);
            let func_ptr_val = self.iconst_cached(ptr_type, func_ptr as i64);
            self.emit_call_indirect(sig_ref, func_ptr_val, &coerced_args)
        };
        let results = self.builder.inst_results(call_inst);

        if results.is_empty() {
            Ok(self.void_value())
        } else {
            let arena = self.arena();
            let cranelift_ty = type_id_to_cranelift(return_type_id, arena, ptr_type);
            let actual_ty = self.builder.func.dfg.value_type(results[0]);
            let result_val = if actual_ty == cranelift_ty {
                results[0]
            } else {
                self.coerce_cranelift_value(results[0], actual_ty, cranelift_ty)
            };
            Ok(CompiledValue::new(result_val, cranelift_ty, return_type_id))
        }
    }

    /// Call a compiler intrinsic using a typed key.
    pub fn call_compiler_intrinsic_key_with_line(
        &mut self,
        intrinsic_key: crate::IntrinsicKey,
        args: &[Value],
        return_type_id: TypeId,
        call_line: u32,
    ) -> CodegenResult<CompiledValue> {
        let typed_args: Vec<CompiledValue> = args
            .iter()
            .map(|&value| {
                let ty = self.builder.func.dfg.value_type(value);
                CompiledValue::new(value, ty, TypeId::VOID)
            })
            .collect();
        self.call_compiler_intrinsic_key_typed_with_line(
            intrinsic_key,
            &typed_args,
            return_type_id,
            call_line,
        )
    }

    /// Call a compiler intrinsic with typed arguments.
    pub fn call_compiler_intrinsic_key_typed_with_line(
        &mut self,
        intrinsic_key: crate::IntrinsicKey,
        typed_args: &[CompiledValue],
        return_type_id: TypeId,
        call_line: u32,
    ) -> CodegenResult<CompiledValue> {
        let args: Vec<Value> = typed_args.iter().map(|arg| arg.value).collect();
        let resolved = resolve_callable_with_preference(
            CallableKey::Intrinsic(intrinsic_key),
            self.callable_backend_preference,
        )
        .map_err(|err| {
            CodegenError::internal_with_context("callable resolution failed", err.to_string())
        })?;

        match resolved {
            ResolvedCallable::InlineIntrinsic(intrinsic_key) => self.compile_inline_intrinsic(
                &intrinsic_key,
                &args,
                typed_args,
                return_type_id,
                call_line,
            ),
            ResolvedCallable::Runtime(runtime) => {
                if matches!(runtime, RuntimeKey::Panic) {
                    self.emit_runtime_panic(&args, call_line)?;
                    return Ok(self.void_value());
                }

                if return_type_id.is_void() {
                    self.call_runtime_void(runtime, &args)?;
                    Ok(self.void_value())
                } else {
                    let value = self.call_runtime(runtime, &args)?;
                    let ty = type_id_to_cranelift(return_type_id, self.arena(), self.ptr_type());
                    Ok(CompiledValue::new(value, ty, return_type_id))
                }
            }
        }
    }

    fn compile_inline_intrinsic(
        &mut self,
        intrinsic_key: &crate::IntrinsicKey,
        args: &[Value],
        typed_args: &[CompiledValue],
        return_type_id: TypeId,
        call_line: u32,
    ) -> CodegenResult<CompiledValue> {
        use crate::intrinsics::{FloatConstant, IntrinsicHandler, IntrinsicKey, UnaryFloatOp};

        match intrinsic_key {
            IntrinsicKey::TaskChannelSend => {
                return self.emit_task_channel_send_intrinsic(typed_args);
            }
            IntrinsicKey::TaskChannelRecv => {
                return self.emit_task_channel_recv_intrinsic(typed_args, return_type_id);
            }
            IntrinsicKey::TaskChannelTryRecv => {
                return self.emit_task_channel_try_recv_intrinsic(typed_args, return_type_id);
            }
            IntrinsicKey::TaskJoin => {
                return self.emit_task_join_intrinsic(typed_args, return_type_id);
            }
            IntrinsicKey::TaskRun => {
                return self.emit_task_run_intrinsic(typed_args);
            }
            _ => {}
        }

        let handler = self
            .intrinsics_registry()
            .lookup(intrinsic_key)
            .ok_or_else(|| {
                CodegenError::not_found(
                    "intrinsic handler",
                    format!("{intrinsic_key:?} (add handler in codegen/intrinsics.rs)"),
                )
            })?;

        let key_display = format!("{intrinsic_key:?}");

        match handler {
            IntrinsicHandler::FloatConstant(fc) => {
                let (value, ty, type_id) = match fc {
                    FloatConstant::F32Nan => {
                        let v = self.builder.ins().f32const(f32::NAN);
                        (v, types::F32, TypeId::F32)
                    }
                    FloatConstant::F64Nan => {
                        let v = self.builder.ins().f64const(f64::NAN);
                        (v, types::F64, TypeId::F64)
                    }
                    FloatConstant::F32Infinity => {
                        let v = self.builder.ins().f32const(f32::INFINITY);
                        (v, types::F32, TypeId::F32)
                    }
                    FloatConstant::F64Infinity => {
                        let v = self.builder.ins().f64const(f64::INFINITY);
                        (v, types::F64, TypeId::F64)
                    }
                    FloatConstant::F32NegInfinity => {
                        let v = self.builder.ins().f32const(f32::NEG_INFINITY);
                        (v, types::F32, TypeId::F32)
                    }
                    FloatConstant::F64NegInfinity => {
                        let v = self.builder.ins().f64const(f64::NEG_INFINITY);
                        (v, types::F64, TypeId::F64)
                    }
                    FloatConstant::F32Epsilon => {
                        let v = self.builder.ins().f32const(f32::EPSILON);
                        (v, types::F32, TypeId::F32)
                    }
                    FloatConstant::F64Epsilon => {
                        let v = self.builder.ins().f64const(f64::EPSILON);
                        (v, types::F64, TypeId::F64)
                    }
                };
                Ok(CompiledValue::new(value, ty, type_id))
            }
            IntrinsicHandler::UnaryFloatOp(op) => {
                if args.is_empty() {
                    return Err(CodegenError::arg_count(key_display, 1, args.len()));
                }
                let arg = args[0];
                let (value, ty, type_id) = match op {
                    UnaryFloatOp::F32Sqrt => {
                        let v = self.builder.ins().sqrt(arg);
                        (v, types::F32, TypeId::F32)
                    }
                    UnaryFloatOp::F64Sqrt => {
                        let v = self.builder.ins().sqrt(arg);
                        (v, types::F64, TypeId::F64)
                    }
                    UnaryFloatOp::F32Abs => {
                        let v = self.builder.ins().fabs(arg);
                        (v, types::F32, TypeId::F32)
                    }
                    UnaryFloatOp::F64Abs => {
                        let v = self.builder.ins().fabs(arg);
                        (v, types::F64, TypeId::F64)
                    }
                    UnaryFloatOp::F32Ceil => {
                        let v = self.builder.ins().ceil(arg);
                        (v, types::F32, TypeId::F32)
                    }
                    UnaryFloatOp::F64Ceil => {
                        let v = self.builder.ins().ceil(arg);
                        (v, types::F64, TypeId::F64)
                    }
                    UnaryFloatOp::F32Floor => {
                        let v = self.builder.ins().floor(arg);
                        (v, types::F32, TypeId::F32)
                    }
                    UnaryFloatOp::F64Floor => {
                        let v = self.builder.ins().floor(arg);
                        (v, types::F64, TypeId::F64)
                    }
                    UnaryFloatOp::F32Trunc => {
                        let v = self.builder.ins().trunc(arg);
                        (v, types::F32, TypeId::F32)
                    }
                    UnaryFloatOp::F64Trunc => {
                        let v = self.builder.ins().trunc(arg);
                        (v, types::F64, TypeId::F64)
                    }
                    UnaryFloatOp::F32Round => {
                        let v = self.builder.ins().nearest(arg);
                        (v, types::F32, TypeId::F32)
                    }
                    UnaryFloatOp::F64Round => {
                        let v = self.builder.ins().nearest(arg);
                        (v, types::F64, TypeId::F64)
                    }
                };
                Ok(CompiledValue::new(value, ty, type_id))
            }
            IntrinsicHandler::BinaryFloatOp(op) => {
                use crate::intrinsics::BinaryFloatOp;
                if args.len() < 2 {
                    return Err(CodegenError::arg_count(key_display, 2, args.len()));
                }
                let arg1 = args[0];
                let arg2 = args[1];
                let (value, ty, type_id) = match op {
                    BinaryFloatOp::F32Min => {
                        let v = self.builder.ins().fmin(arg1, arg2);
                        (v, types::F32, TypeId::F32)
                    }
                    BinaryFloatOp::F64Min => {
                        let v = self.builder.ins().fmin(arg1, arg2);
                        (v, types::F64, TypeId::F64)
                    }
                    BinaryFloatOp::F32Max => {
                        let v = self.builder.ins().fmax(arg1, arg2);
                        (v, types::F32, TypeId::F32)
                    }
                    BinaryFloatOp::F64Max => {
                        let v = self.builder.ins().fmax(arg1, arg2);
                        (v, types::F64, TypeId::F64)
                    }
                };
                Ok(CompiledValue::new(value, ty, type_id))
            }
            IntrinsicHandler::UnaryIntOp(op) => {
                if args.is_empty() {
                    return Err(CodegenError::arg_count(key_display, 1, args.len()));
                }
                let (value, ty, type_id) = self.compile_unary_int_op(*op, args[0]);
                Ok(CompiledValue::new(value, ty, type_id))
            }
            IntrinsicHandler::BinaryIntOp(op) => {
                if args.len() < 2 {
                    return Err(CodegenError::arg_count(key_display, 2, args.len()));
                }
                let (value, ty, type_id) = self.compile_binary_int_op(*op, args[0], args[1]);
                Ok(CompiledValue::new(value, ty, type_id))
            }
            IntrinsicHandler::UnaryIntWrappingOp(op) => {
                use crate::intrinsics::UnaryIntWrappingOp;
                if args.is_empty() {
                    return Err(CodegenError::arg_count(key_display, 1, args.len()));
                }
                let arg = args[0];
                let (value, ty, type_id) = match op {
                    // wrapping_neg - signed (Cranelift ineg wraps by default)
                    UnaryIntWrappingOp::I8WrappingNeg => {
                        let v = self.builder.ins().ineg(arg);
                        (v, types::I8, TypeId::I8)
                    }
                    UnaryIntWrappingOp::I16WrappingNeg => {
                        let v = self.builder.ins().ineg(arg);
                        (v, types::I16, TypeId::I16)
                    }
                    UnaryIntWrappingOp::I32WrappingNeg => {
                        let v = self.builder.ins().ineg(arg);
                        (v, types::I32, TypeId::I32)
                    }
                    UnaryIntWrappingOp::I64WrappingNeg => {
                        let v = self.builder.ins().ineg(arg);
                        (v, types::I64, TypeId::I64)
                    }
                };
                Ok(CompiledValue::new(value, ty, type_id))
            }
            IntrinsicHandler::CheckedIntOp(op) => {
                if args.len() < 2 {
                    return Err(CodegenError::arg_count(key_display, 2, args.len()));
                }
                let arg1 = args[0];
                let arg2 = args[1];

                // Build optional result: if overflow -> nil (tag=0), else -> Some(result) (tag=1, value)
                // Stack layout: [tag: i8] + padding + [value: T] = 16 bytes for alignment
                self.checked_int_op_impl(*op, arg1, arg2, return_type_id)
            }
            IntrinsicHandler::BuiltinPanic => {
                self.emit_runtime_panic(args, call_line)?;
                Ok(self.void_value())
            }
            IntrinsicHandler::BuiltinArrayLen => {
                if args.is_empty() {
                    return Err(CodegenError::arg_count("array_len", 1, 0));
                }
                let len_val = self.emit_inline_array_len(args[0]);
                Ok(self.i64_value(len_val))
            }
            IntrinsicHandler::BuiltinStringLen => {
                if args.is_empty() {
                    return Err(CodegenError::arg_count("string_len", 1, 0));
                }
                let len_val = self.emit_inline_string_len(args[0]);
                Ok(self.i64_value(len_val))
            }
        }
    }

    fn call_std_task_tagged_native(
        &mut self,
        native_name: &str,
        handle: Value,
    ) -> CodegenResult<(Value, Value)> {
        let native_func = self
            .native_registry()
            .lookup("std:task", native_name)
            .ok_or_else(|| {
                CodegenError::not_found("native function", format!("std:task::{native_name}"))
            })?;
        let call_inst = self.call_native_indirect(native_func, &[handle]);
        let results = self.builder.inst_results(call_inst).to_vec();
        if results.len() < 2 {
            return Err(CodegenError::internal_with_context(
                "std:task tagged intrinsic result",
                format!("expected 2 fields from std:task::{native_name}"),
            ));
        }
        Ok((results[0], results[1]))
    }

    fn emit_task_channel_send_intrinsic(
        &mut self,
        typed_args: &[CompiledValue],
    ) -> CodegenResult<CompiledValue> {
        if typed_args.len() < 2 {
            return Err(CodegenError::arg_count(
                "task_channel_send",
                2,
                typed_args.len(),
            ));
        }
        let ch_handle = typed_args[0].value;
        let payload = typed_args[1];
        let tag = {
            let arena = self.arena();
            array_element_tag_id(payload.type_id, arena)
        };
        let tag_val = self.iconst_cached(types::I64, tag);
        // Function-call semantics may clean up temporary RC args after return;
        // hand channel_send its own retained reference up front.
        //
        // Some fallback intrinsic call paths may not carry concrete TypeIds
        // (void/type-param placeholders). Only emit rc_inc when the type is
        // concrete enough for RC classification.
        let can_classify_rc = payload.type_id != TypeId::VOID
            && self.arena().unwrap_type_param(payload.type_id).is_none();
        if can_classify_rc && self.rc_state(payload.type_id).needs_cleanup() {
            self.emit_rc_inc_for_type(payload.value, payload.type_id)?;
        }
        let payload_bits = convert_to_i64_for_storage(self.builder, &payload);

        let native_func = self
            .native_registry()
            .lookup("std:task", "channel_send")
            .ok_or_else(|| CodegenError::not_found("native function", "std:task::channel_send"))?;
        let call_inst = self.call_native_indirect(native_func, &[ch_handle, tag_val, payload_bits]);
        let send_result = self.builder.inst_results(call_inst)[0];
        let is_ok = self.builder.ins().icmp_imm(IntCC::Equal, send_result, 0);
        Ok(CompiledValue::new(is_ok, types::I8, TypeId::BOOL))
    }

    fn emit_task_channel_recv_intrinsic(
        &mut self,
        typed_args: &[CompiledValue],
        return_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        if typed_args.is_empty() {
            return Err(CodegenError::arg_count("task_channel_recv", 1, 0));
        }
        let (_tag, raw_value) =
            self.call_std_task_tagged_native("channel_recv", typed_args[0].value)?;
        Ok(self.convert_field_value(raw_value, return_type_id))
    }

    fn emit_task_channel_try_recv_intrinsic(
        &mut self,
        typed_args: &[CompiledValue],
        return_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        if typed_args.is_empty() {
            return Err(CodegenError::arg_count("task_channel_try_recv", 1, 0));
        }

        let elem_type_id = self
            .arena()
            .unwrap_union(return_type_id)
            .and_then(|variants| variants.iter().copied().find(|&ty| ty != TypeId::DONE))
            .ok_or_else(|| {
                CodegenError::type_mismatch(
                    "task_channel_try_recv return type",
                    "union containing Done",
                    self.arena().display_basic(return_type_id),
                )
            })?;

        let (tag, raw_value) =
            self.call_std_task_tagged_native("channel_recv", typed_args[0].value)?;
        let minus_one = self.iconst_cached(types::I64, -1);
        let is_done = self.builder.ins().icmp(IntCC::Equal, tag, minus_one);
        let cond = uextend_const(self.builder, types::I32, is_done);

        let done_block = self.builder.create_block();
        let value_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder
            .append_block_param(merge_block, self.ptr_type());

        self.emit_brif(cond, done_block, value_block);

        self.switch_to_block(done_block);
        let done_value =
            CompiledValue::new(self.iconst_cached(types::I8, 0), types::I8, TypeId::DONE);
        let done_union = self.construct_union_id(done_value, return_type_id)?;
        self.builder
            .ins()
            .jump(merge_block, &[done_union.value.into()]);
        self.builder.seal_block(done_block);

        self.switch_to_block(value_block);
        let typed_value = self.convert_field_value(raw_value, elem_type_id);
        let value_union = self.construct_union_id(typed_value, return_type_id)?;
        self.builder
            .ins()
            .jump(merge_block, &[value_union.value.into()]);
        self.builder.seal_block(value_block);

        self.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);
        let union_ptr = self.builder.block_params(merge_block)[0];
        Ok(CompiledValue::new(
            union_ptr,
            self.ptr_type(),
            return_type_id,
        ))
    }

    fn emit_task_join_intrinsic(
        &mut self,
        typed_args: &[CompiledValue],
        return_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        if typed_args.is_empty() {
            return Err(CodegenError::arg_count("task_join", 1, 0));
        }
        let (_tag, raw_value) =
            self.call_std_task_tagged_native("task_join", typed_args[0].value)?;
        Ok(self.convert_field_value(raw_value, return_type_id))
    }

    fn emit_task_run_intrinsic(
        &mut self,
        typed_args: &[CompiledValue],
    ) -> CodegenResult<CompiledValue> {
        if typed_args.is_empty() {
            return Err(CodegenError::arg_count("task_run", 1, 0));
        }
        let closure = typed_args[0];
        let closure_return_type = self
            .arena()
            .unwrap_function(closure.type_id)
            .map(|(_, ret, _)| self.try_substitute_type(ret))
            .unwrap_or(TypeId::I64);
        let tag = {
            let arena = self.arena();
            array_element_tag_id(closure_return_type, arena)
        };
        let tag_val = self.iconst_cached(types::I64, tag);
        self.call_runtime_void(RuntimeKey::TaskSetSpawnTag, &[tag_val])?;

        let native_func = self
            .native_registry()
            .lookup("std:task", "task_run")
            .ok_or_else(|| CodegenError::not_found("native function", "std:task::task_run"))?;
        let call_inst = self.call_native_indirect(native_func, &[closure.value]);
        let handle = self.builder.inst_results(call_inst)[0];
        Ok(CompiledValue::new(handle, self.ptr_type(), TypeId::HANDLE))
    }

    fn emit_runtime_panic(&mut self, args: &[Value], call_line: u32) -> CodegenResult<()> {
        if args.is_empty() {
            return Err(CodegenError::arg_count("panic", 1, 0));
        }

        // vole_panic(msg, file_ptr, file_len, line)
        let msg = args[0];
        let (file_ptr, file_len) = self.source_file();
        let ptr_type = self.ptr_type();
        let file_ptr_val = self.iconst_cached(ptr_type, file_ptr as i64);
        let file_len_val = self.iconst_cached(ptr_type, file_len as i64);
        let line_val = self.iconst_cached(types::I32, call_line as i64);

        self.call_runtime_void(
            RuntimeKey::Panic,
            &[msg, file_ptr_val, file_len_val, line_val],
        )?;

        // Panic never returns - emit trap and unreachable block
        self.builder.ins().trap(crate::trap_codes::PANIC);
        let unreachable_block = self.builder.create_block();
        self.switch_and_seal(unreachable_block);
        Ok(())
    }

    fn emit_inline_array_len(&mut self, arr_ptr: Value) -> Value {
        let ptr_type = self.ptr_type();
        let zero_i64 = self.iconst_cached(types::I64, 0);
        let null_ptr = self.iconst_cached(ptr_type, 0);
        let is_null = self.builder.ins().icmp(IntCC::Equal, arr_ptr, null_ptr);

        let null_block = self.builder.create_block();
        let nonnull_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I64);
        self.emit_brif(is_null, null_block, nonnull_block);

        self.switch_to_block(null_block);
        self.builder.ins().jump(merge_block, &[zero_i64.into()]);

        self.switch_to_block(nonnull_block);
        let len_offset = std::mem::offset_of!(vole_runtime::array::RcArray, len) as i32;
        let raw_len = self
            .builder
            .ins()
            .load(ptr_type, MemFlags::new(), arr_ptr, len_offset);
        let len_i64 = if ptr_type == types::I64 {
            raw_len
        } else {
            uextend_const(self.builder, types::I64, raw_len)
        };
        self.builder.ins().jump(merge_block, &[len_i64.into()]);

        self.switch_to_block(merge_block);
        self.builder.block_params(merge_block)[0]
    }

    fn emit_inline_string_len(&mut self, str_ptr: Value) -> Value {
        let ptr_type = self.ptr_type();
        let zero_i64 = self.iconst_cached(types::I64, 0);
        let null_ptr = self.iconst_cached(ptr_type, 0);
        let is_null = self.builder.ins().icmp(IntCC::Equal, str_ptr, null_ptr);

        let null_block = self.builder.create_block();
        let nonnull_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I64);
        self.emit_brif(is_null, null_block, nonnull_block);

        self.switch_to_block(null_block);
        self.builder.ins().jump(merge_block, &[zero_i64.into()]);

        // Load cached char_count directly (O(1) instead of O(n) UTF-8 loop)
        self.switch_to_block(nonnull_block);
        let char_count_offset =
            std::mem::offset_of!(vole_runtime::string::RcString, char_count) as i32;
        let raw_count =
            self.builder
                .ins()
                .load(ptr_type, MemFlags::new(), str_ptr, char_count_offset);
        let count_i64 = if ptr_type == types::I64 {
            raw_count
        } else {
            uextend_const(self.builder, types::I64, raw_count)
        };
        self.builder.ins().jump(merge_block, &[count_i64.into()]);

        self.switch_to_block(merge_block);
        self.builder.block_params(merge_block)[0]
    }
}
