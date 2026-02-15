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

use super::context::{Cg, resolve_external_names};
use super::types::{CompiledValue, native_type_to_cranelift, type_id_to_cranelift};

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
            return self.call_compiler_intrinsic_key_with_line(
                crate::IntrinsicKey::from(native_name.as_str()),
                args,
                return_type_id,
                0,
            );
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

        // Import the signature and emit an indirect call
        let sig_ref = self.builder.import_signature(sig);
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
                if actual_ty == expected_ty {
                    arg
                } else if actual_ty.is_int() && expected_ty.is_int() {
                    if expected_ty.bits() < actual_ty.bits() {
                        self.builder.ins().ireduce(expected_ty, arg)
                    } else {
                        self.builder.ins().sextend(expected_ty, arg)
                    }
                } else {
                    arg
                }
            })
            .collect();

        // Load the function pointer as a constant
        let func_ptr_val = self.builder.ins().iconst(ptr_type, func_ptr as i64);

        // Emit the indirect call
        let call_inst = self
            .builder
            .ins()
            .call_indirect(sig_ref, func_ptr_val, &coerced_args);
        self.field_cache.clear(); // External calls may mutate instance fields
        let results = self.builder.inst_results(call_inst);

        if results.is_empty() {
            Ok(self.void_value())
        } else {
            let arena = self.arena();
            let cranelift_ty = type_id_to_cranelift(return_type_id, arena, ptr_type);
            Ok(CompiledValue::new(results[0], cranelift_ty, return_type_id))
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
        let resolved = resolve_callable_with_preference(
            CallableKey::Intrinsic(intrinsic_key),
            self.callable_backend_preference,
        )
        .map_err(|err| {
            CodegenError::internal_with_context("callable resolution failed", err.to_string())
        })?;

        match resolved {
            ResolvedCallable::InlineIntrinsic(intrinsic_key) => {
                self.compile_inline_intrinsic(&intrinsic_key, args, return_type_id, call_line)
            }
            ResolvedCallable::Runtime(runtime) => {
                if matches!(runtime, RuntimeKey::Panic) {
                    self.emit_runtime_panic(args, call_line)?;
                    return Ok(self.void_value());
                }

                if return_type_id.is_void() {
                    self.call_runtime_void(runtime, args)?;
                    Ok(self.void_value())
                } else {
                    let value = self.call_runtime(runtime, args)?;
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
        return_type_id: TypeId,
        call_line: u32,
    ) -> CodegenResult<CompiledValue> {
        use crate::intrinsics::{FloatConstant, IntrinsicHandler, UnaryFloatOp};

        let intrinsic_name = intrinsic_key.as_str();
        let handler = self
            .intrinsics_registry()
            .lookup(intrinsic_key)
            .ok_or_else(|| {
                CodegenError::not_found(
                    "intrinsic handler",
                    format!(
                        "\"{}\" (add handler in codegen/intrinsics.rs)",
                        intrinsic_name
                    ),
                )
            })?;

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
                    return Err(CodegenError::arg_count(intrinsic_name, 1, args.len()));
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
                    return Err(CodegenError::arg_count(intrinsic_name, 2, args.len()));
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
                    return Err(CodegenError::arg_count(intrinsic_name, 1, args.len()));
                }
                let (value, ty, type_id) = self.compile_unary_int_op(*op, args[0]);
                Ok(CompiledValue::new(value, ty, type_id))
            }
            IntrinsicHandler::BinaryIntOp(op) => {
                if args.len() < 2 {
                    return Err(CodegenError::arg_count(intrinsic_name, 2, args.len()));
                }
                let (value, ty, type_id) = self.compile_binary_int_op(*op, args[0], args[1]);
                Ok(CompiledValue::new(value, ty, type_id))
            }
            IntrinsicHandler::UnaryIntWrappingOp(op) => {
                use crate::intrinsics::UnaryIntWrappingOp;
                if args.is_empty() {
                    return Err(CodegenError::arg_count(intrinsic_name, 1, args.len()));
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
                    return Err(CodegenError::arg_count(intrinsic_name, 2, args.len()));
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

    fn emit_runtime_panic(&mut self, args: &[Value], call_line: u32) -> CodegenResult<()> {
        if args.is_empty() {
            return Err(CodegenError::arg_count("panic", 1, 0));
        }

        // vole_panic(msg, file_ptr, file_len, line)
        let msg = args[0];
        let (file_ptr, file_len) = self.source_file();
        let ptr_type = self.ptr_type();
        let file_ptr_val = self.builder.ins().iconst(ptr_type, file_ptr as i64);
        let file_len_val = self.builder.ins().iconst(ptr_type, file_len as i64);
        let line_val = self.builder.ins().iconst(types::I32, call_line as i64);

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
        let zero_i64 = self.builder.ins().iconst(types::I64, 0);
        let null_ptr = self.builder.ins().iconst(ptr_type, 0);
        let is_null = self.builder.ins().icmp(IntCC::Equal, arr_ptr, null_ptr);

        let null_block = self.builder.create_block();
        let nonnull_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I64);
        self.builder
            .ins()
            .brif(is_null, null_block, &[], nonnull_block, &[]);

        self.builder.switch_to_block(null_block);
        self.builder.ins().jump(merge_block, &[zero_i64.into()]);

        self.builder.switch_to_block(nonnull_block);
        let len_offset = std::mem::offset_of!(vole_runtime::array::RcArray, len) as i32;
        let raw_len = self
            .builder
            .ins()
            .load(ptr_type, MemFlags::new(), arr_ptr, len_offset);
        let len_i64 = if ptr_type == types::I64 {
            raw_len
        } else {
            self.builder.ins().uextend(types::I64, raw_len)
        };
        self.builder.ins().jump(merge_block, &[len_i64.into()]);

        self.builder.switch_to_block(merge_block);
        self.builder.block_params(merge_block)[0]
    }

    fn emit_inline_string_len(&mut self, str_ptr: Value) -> Value {
        let ptr_type = self.ptr_type();
        let zero_i64 = self.builder.ins().iconst(types::I64, 0);
        let null_ptr = self.builder.ins().iconst(ptr_type, 0);
        let is_null = self.builder.ins().icmp(IntCC::Equal, str_ptr, null_ptr);

        let null_block = self.builder.create_block();
        let nonnull_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I64);
        self.builder
            .ins()
            .brif(is_null, null_block, &[], nonnull_block, &[]);

        self.builder.switch_to_block(null_block);
        self.builder.ins().jump(merge_block, &[zero_i64.into()]);

        // Load cached char_count directly (O(1) instead of O(n) UTF-8 loop)
        self.builder.switch_to_block(nonnull_block);
        let char_count_offset =
            std::mem::offset_of!(vole_runtime::string::RcString, char_count) as i32;
        let raw_count =
            self.builder
                .ins()
                .load(ptr_type, MemFlags::new(), str_ptr, char_count_offset);
        let count_i64 = if ptr_type == types::I64 {
            raw_count
        } else {
            self.builder.ins().uextend(types::I64, raw_count)
        };
        self.builder.ins().jump(merge_block, &[count_i64.into()]);

        self.builder.switch_to_block(merge_block);
        self.builder.block_params(merge_block)[0]
    }
}
