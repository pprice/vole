// src/codegen/ops.rs
//
// Binary and compound assignment operations - impl Cg methods.

use cranelift::prelude::*;
use cranelift_codegen::ir::{BlockArg, Function, InstructionData};

use crate::RuntimeKey;
use crate::context::ExternalMethodRef;
use vole_identity::{TypeId, VirTypeId};
use vole_vir::{ComparisonHint, VirBinOp};

use super::context::Cg;
use super::types::{CompiledValue, convert_to_type};
use crate::errors::{CodegenError, CodegenResult};

/// If `val` is defined by an `iconst` instruction, return its immediate value.
///
/// Used for constant folding boolean NOT, AND, and OR at codegen time so that
/// compile-time-constant operands avoid emitting unnecessary control-flow blocks.
pub(crate) fn try_constant_value(func: &Function, val: Value) -> Option<i64> {
    let inst = func.dfg.value_def(val).inst()?;
    if let InstructionData::UnaryImm { imm, .. } = func.dfg.insts[inst] {
        Some(imm.bits())
    } else {
        None
    }
}

/// Zero-extend `val` to `target_ty`, folding to `iconst` when the operand is a
/// known constant.  Falls back to `builder.ins().uextend()` for non-constant
/// operands or when the target is `I128` (which `iconst` cannot represent
/// directly).
pub(crate) fn uextend_const(builder: &mut FunctionBuilder, target_ty: Type, val: Value) -> Value {
    if target_ty != types::I128
        && let Some(c) = try_constant_value(builder.func, val)
    {
        let src_bits = builder.func.dfg.value_type(val).bits();
        let mask = if src_bits >= 64 {
            u64::MAX
        } else {
            (1u64 << src_bits) - 1
        };
        let folded = (c as u64 & mask) as i64;
        return builder.ins().iconst(target_ty, folded);
    }
    builder.ins().uextend(target_ty, val)
}

/// Sign-extend `val` to `target_ty`, folding to `iconst` when the operand is a
/// known constant.  Falls back to `builder.ins().sextend()` for non-constant
/// operands or when the target is `I128`.
pub(crate) fn sextend_const(builder: &mut FunctionBuilder, target_ty: Type, val: Value) -> Value {
    if target_ty != types::I128
        && let Some(c) = try_constant_value(builder.func, val)
    {
        let src_bits = builder.func.dfg.value_type(val).bits();
        let shift = 64u32.saturating_sub(src_bits);
        let folded = (c << shift) >> shift; // arithmetic right shift
        return builder.ins().iconst(target_ty, folded);
    }
    builder.ins().sextend(target_ty, val)
}

/// Convert a numeric VirTypeId to its corresponding Cranelift type.
///
/// # Panics
///
/// Panics in debug builds if `vir_ty` is not a numeric type.  Non-numeric types
/// must never reach the binary-operator path (sema should have rejected them
/// before codegen).
fn vir_type_id_to_cranelift_type(vir_ty: VirTypeId) -> Type {
    match vir_ty {
        VirTypeId::I8 | VirTypeId::U8 => types::I8,
        VirTypeId::I16 | VirTypeId::U16 => types::I16,
        VirTypeId::I32 | VirTypeId::U32 => types::I32,
        VirTypeId::I64 | VirTypeId::U64 => types::I64,
        VirTypeId::I128 => types::I128,
        VirTypeId::F32 => types::F32,
        VirTypeId::F64 => types::F64,
        VirTypeId::F128 => types::F128,
        _ => unreachable!(
            "INTERNAL: vir_type_id_to_cranelift_type called with non-numeric type {:?}; \
             this is a sema bug — only numeric types should reach binary-op codegen",
            vir_ty
        ),
    }
}

/// Evaluate an `IntCC` comparison on two known i64 constants.
/// Returns `true` (1) or `false` (0) as a boolean.
fn eval_int_cc(cc: IntCC, a: i64, b: i64) -> bool {
    match cc {
        IntCC::Equal => a == b,
        IntCC::NotEqual => a != b,
        IntCC::SignedLessThan => a < b,
        IntCC::SignedLessThanOrEqual => a <= b,
        IntCC::SignedGreaterThan => a > b,
        IntCC::SignedGreaterThanOrEqual => a >= b,
        IntCC::UnsignedLessThan => (a as u64) < (b as u64),
        IntCC::UnsignedLessThanOrEqual => (a as u64) <= (b as u64),
        IntCC::UnsignedGreaterThan => (a as u64) > (b as u64),
        IntCC::UnsignedGreaterThanOrEqual => (a as u64) >= (b as u64),
    }
}

impl Cg<'_, '_, '_> {
    /// Concatenate two values as strings.
    /// Left must be a string, right will be converted via to_string() if not already string.
    pub(crate) fn string_concat(
        &mut self,
        mut left: CompiledValue,
        mut right: CompiledValue,
    ) -> CodegenResult<CompiledValue> {
        // Get the right operand as a string
        let right_converted = if right.type_id == VirTypeId::STRING {
            // Right is already a string, use it directly
            None
        } else {
            // Right is not a string, call to_string() on it (allocates a new string)
            Some(self.call_to_string(&right)?)
        };
        let right_string = right_converted.unwrap_or(right.value);

        // Call vole_string_concat(left, right_string)
        let concat_result =
            self.call_runtime(RuntimeKey::StringConcat, &[left.value, right_string])?;

        // Consume RC operands used by string concat
        self.consume_rc_value(&mut left)?;
        self.consume_rc_value(&mut right)?;

        // Dec the to_string intermediate if we created one (it's a fresh allocation
        // that was only needed for the concat call)
        if let Some(to_string_val) = right_converted {
            self.emit_rc_dec(to_string_val)?;
        }

        Ok(self.string_temp(concat_result))
    }

    /// Call to_string() on a value via the Stringable interface.
    /// Returns the resulting string value.
    fn call_to_string(&mut self, val: &CompiledValue) -> CodegenResult<Value> {
        // Look up to_string method via query
        let method_id = self.analyzed().method_name_id_by_str("to_string");

        let (type_name_id, method_impl) = self
            .analyzed()
            .implement_method_for_type_v(val.type_id, method_id)
            .ok_or_else(|| {
                CodegenError::not_found("to_string method", format!("{:?}", val.type_id))
            })?;

        // Check if it's an external (native) method
        if let Some(ref external_info) = method_impl.external_info {
            // Call the external function directly
            let string_type_id = TypeId::STRING;
            let ext = ExternalMethodRef::from(*external_info);
            let result = self.call_external_id(&ext, &[val.value], string_type_id)?;
            return Ok(result.value);
        }

        // Otherwise, it's a Vole method - look up via unified method_func_keys.
        let func_key = *self
            .method_func_keys()
            .get(&(type_name_id, method_id))
            .ok_or_else(|| {
                CodegenError::not_found("method info", "to_string in method_func_keys")
            })?;

        let func_ref = self.func_ref(func_key)?;

        // Call the method with `self` (the value) as the only argument
        let call = self.emit_call(func_ref, &[val.value]);
        let results = self.builder.inst_results(call);

        results
            .first()
            .copied()
            .ok_or_else(|| CodegenError::internal("to_string method did not return a value"))
    }

    /// Compile a binary operation on two values.
    ///
    /// `promoted_ty` is the pre-resolved promoted operand type from the VIR
    /// node.  For arithmetic/bitwise ops it equals the expression result type;
    /// for comparisons it is the common numeric type that both operands are
    /// coerced to before the comparison (the result type is always BOOL).
    ///
    /// `comparison_hint` pre-classifies comparison dispatch (string, float,
    /// struct, optional, integer) so codegen reads the decision rather than
    /// re-detecting types.  `ComparisonHint::None` falls back to the legacy
    /// type-based dispatch for generic/unresolved paths.
    ///
    /// `lhs_is_unsigned` is a VIR-lowering hint that short-circuits the
    /// `VirTypeId::is_unsigned_int()` check for selecting unsigned
    /// Cranelift instructions (udiv, ushr, unsigned icmp).
    #[expect(clippy::too_many_arguments)]
    pub fn binary_op(
        &mut self,
        left: CompiledValue,
        right: CompiledValue,
        op: VirBinOp,
        promoted_ty: VirTypeId,
        line: u32,
        lhs_is_optional: bool,
        rhs_is_optional: bool,
        lhs_is_unsigned: bool,
        comparison_hint: ComparisonHint,
    ) -> CodegenResult<CompiledValue> {
        // Guard: monomorphized generics with structural constraints may have
        // string Add ops that weren't caught by the VIR string_concat hint
        // (sema assigns UNKNOWN to method return types on structural type
        // params).  Use compiled types as fallback.
        if op == VirBinOp::Add && self.vir_query_is_string_v(left.type_id) {
            return self.string_concat(left, right);
        }
        // Assert: string Eq/Ne must always be classified by sema/VIR.
        // The ComparisonHint::StringEq annotation is set during VIR lowering,
        // during monomorphization rederive, or recomputed in codegen's
        // compile_vir_binary_op when the VIR hint was None/stale.
        debug_assert!(
            !(matches!(op, VirBinOp::Eq | VirBinOp::Ne)
                && self.vir_query_is_string_v(left.type_id)
                && comparison_hint != ComparisonHint::StringEq),
            "string Eq/Ne without StringEq hint: hint={comparison_hint:?}, left={:?}, line={line}",
            left.type_id,
        );
        if matches!(op, VirBinOp::Eq | VirBinOp::Ne) {
            match comparison_hint {
                ComparisonHint::OptionalNilEq => {
                    return self.dispatch_optional_nil_eq(
                        left,
                        right,
                        op,
                        lhs_is_optional,
                        rhs_is_optional,
                    );
                }
                ComparisonHint::OptionalValueEq => {
                    return self.dispatch_optional_value_eq(left, right, op);
                }
                ComparisonHint::StructEq => {
                    return self.struct_equality(left, right, op);
                }
                ComparisonHint::StringEq => {
                    return self.dispatch_string_eq(left, right, op);
                }
                ComparisonHint::None => {
                    // Fallback: re-detect for generic/unresolved paths.
                    if let Some(result) = self.detect_eq_special_case(
                        left,
                        right,
                        op,
                        lhs_is_optional,
                        rhs_is_optional,
                    )? {
                        return Ok(result);
                    }
                }
                // F128, Float, Int, UnsignedInt: handled below in numeric path
                _ => {}
            }
        }

        let is_unsigned = match comparison_hint {
            ComparisonHint::UnsignedIntCmp => true,
            ComparisonHint::None => lhs_is_unsigned || left.type_id.is_unsigned_int(),
            _ => lhs_is_unsigned || left.type_id.is_unsigned_int(),
        };

        // Use the pre-resolved promoted operand type from the VIR node.
        let result_vir_ty = promoted_ty;
        let result_ty = if promoted_ty.is_numeric() {
            vir_type_id_to_cranelift_type(promoted_ty)
        } else {
            left.ty
        };

        let (left_val, right_val) = if result_ty == types::F128 {
            (
                self.coerce_value_to_f128(left)?,
                self.coerce_value_to_f128(right)?,
            )
        } else {
            (
                convert_to_type(self.builder, left, result_ty),
                convert_to_type(self.builder, right, result_ty),
            )
        };

        let result = match op {
            VirBinOp::Add => {
                if result_ty == types::F128 {
                    self.call_f128_binary_op(RuntimeKey::F128Add, left_val, right_val)?
                } else if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder.ins().fadd(left_val, right_val)
                } else {
                    self.builder.ins().iadd(left_val, right_val)
                }
            }
            VirBinOp::Sub => {
                if result_ty == types::F128 {
                    self.call_f128_binary_op(RuntimeKey::F128Sub, left_val, right_val)?
                } else if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder.ins().fsub(left_val, right_val)
                } else {
                    self.builder.ins().isub(left_val, right_val)
                }
            }
            VirBinOp::Mul => {
                if result_ty == types::F128 {
                    self.call_f128_binary_op(RuntimeKey::F128Mul, left_val, right_val)?
                } else if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder.ins().fmul(left_val, right_val)
                } else {
                    self.builder.ins().imul(left_val, right_val)
                }
            }
            VirBinOp::Div => {
                if result_ty == types::F128 {
                    self.call_f128_binary_op(RuntimeKey::F128Div, left_val, right_val)?
                } else if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder.ins().fdiv(left_val, right_val)
                } else if result_ty == types::I128 {
                    self.call_runtime(RuntimeKey::I128Sdiv, &[left_val, right_val])?
                } else if is_unsigned {
                    self.emit_div_by_zero_check(right_val, line)?;
                    self.builder.ins().udiv(left_val, right_val)
                } else {
                    self.emit_div_by_zero_check(right_val, line)?;
                    self.emit_signed_div_overflow_check(left_val, right_val, result_ty, line)?;
                    self.builder.ins().sdiv(left_val, right_val)
                }
            }
            VirBinOp::Mod => {
                if result_ty == types::F128 {
                    self.call_f128_binary_op(RuntimeKey::F128Rem, left_val, right_val)?
                } else if result_ty == types::F64 || result_ty == types::F32 {
                    let div = self.builder.ins().fdiv(left_val, right_val);
                    let floor = self.builder.ins().floor(div);
                    let mul = self.builder.ins().fmul(floor, right_val);
                    self.builder.ins().fsub(left_val, mul)
                } else if result_ty == types::I128 {
                    self.call_runtime(RuntimeKey::I128Srem, &[left_val, right_val])?
                } else if is_unsigned {
                    self.emit_div_by_zero_check(right_val, line)?;
                    self.builder.ins().urem(left_val, right_val)
                } else {
                    self.emit_div_by_zero_check(right_val, line)?;
                    self.emit_signed_div_overflow_check(left_val, right_val, result_ty, line)?;
                    self.builder.ins().srem(left_val, right_val)
                }
            }
            VirBinOp::Eq => self.emit_eq(
                comparison_hint,
                result_ty,
                left.type_id == VirTypeId::STRING,
                left_val,
                right_val,
            )?,
            VirBinOp::Ne => self.emit_ne(
                comparison_hint,
                result_ty,
                left.type_id == VirTypeId::STRING,
                left_val,
                right_val,
            )?,
            VirBinOp::Lt => self.emit_ord_cmp(
                comparison_hint,
                result_ty,
                is_unsigned,
                left_val,
                right_val,
                FloatCC::LessThan,
                IntCC::UnsignedLessThan,
                IntCC::SignedLessThan,
                RuntimeKey::F128Lt,
            )?,
            VirBinOp::Gt => self.emit_ord_cmp(
                comparison_hint,
                result_ty,
                is_unsigned,
                left_val,
                right_val,
                FloatCC::GreaterThan,
                IntCC::UnsignedGreaterThan,
                IntCC::SignedGreaterThan,
                RuntimeKey::F128Gt,
            )?,
            VirBinOp::Le => self.emit_ord_cmp(
                comparison_hint,
                result_ty,
                is_unsigned,
                left_val,
                right_val,
                FloatCC::LessThanOrEqual,
                IntCC::UnsignedLessThanOrEqual,
                IntCC::SignedLessThanOrEqual,
                RuntimeKey::F128Le,
            )?,
            VirBinOp::Ge => self.emit_ord_cmp(
                comparison_hint,
                result_ty,
                is_unsigned,
                left_val,
                right_val,
                FloatCC::GreaterThanOrEqual,
                IntCC::UnsignedGreaterThanOrEqual,
                IntCC::SignedGreaterThanOrEqual,
                RuntimeKey::F128Ge,
            )?,
            VirBinOp::And | VirBinOp::Or => unreachable!("handled above"),
            VirBinOp::BitAnd => self.builder.ins().band(left_val, right_val),
            VirBinOp::BitOr => self.builder.ins().bor(left_val, right_val),
            VirBinOp::BitXor => self.builder.ins().bxor(left_val, right_val),
            VirBinOp::Shl => self.builder.ins().ishl(left_val, right_val),
            VirBinOp::Shr => {
                if is_unsigned {
                    self.builder.ins().ushr(left_val, right_val)
                } else {
                    self.builder.ins().sshr(left_val, right_val)
                }
            }
        };

        // For comparison ops, result is bool; otherwise use the promoted type
        let (final_ty, final_vir_ty) = match op {
            VirBinOp::Eq
            | VirBinOp::Ne
            | VirBinOp::Lt
            | VirBinOp::Gt
            | VirBinOp::Le
            | VirBinOp::Ge => (types::I8, VirTypeId::BOOL),
            VirBinOp::And | VirBinOp::Or => unreachable!(),
            _ => (result_ty, result_vir_ty),
        };

        Ok(CompiledValue::new(result, final_ty, final_vir_ty))
    }

    fn coerce_value_to_f128(&mut self, value: CompiledValue) -> CodegenResult<Value> {
        match value.ty {
            ty if ty == types::F128 => Ok(value.value),
            ty if ty == types::F64 => {
                let bits = self.call_runtime(RuntimeKey::F64ToF128, &[value.value])?;
                Ok(self
                    .builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), bits))
            }
            ty if ty == types::F32 => {
                let bits = self.call_runtime(RuntimeKey::F32ToF128, &[value.value])?;
                Ok(self
                    .builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), bits))
            }
            ty if ty == types::I128 => {
                let bits = self.call_runtime(RuntimeKey::I128ToF128, &[value.value])?;
                Ok(self
                    .builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), bits))
            }
            ty if ty.is_int() => {
                let v = if ty == types::I64 {
                    value.value
                } else {
                    sextend_const(self.builder, types::I64, value.value)
                };
                let bits = self.call_runtime(RuntimeKey::I64ToF128, &[v])?;
                Ok(self
                    .builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), bits))
            }
            _ => Err(CodegenError::type_mismatch(
                "f128 coercion",
                "numeric type",
                format!("{:?}", value.ty),
            )),
        }
    }

    fn call_f128_binary_op(
        &mut self,
        key: RuntimeKey,
        left: Value,
        right: Value,
    ) -> CodegenResult<Value> {
        let left_bits = self
            .builder
            .ins()
            .bitcast(types::I128, MemFlags::new(), left);
        let right_bits = self
            .builder
            .ins()
            .bitcast(types::I128, MemFlags::new(), right);
        let result_bits = self.call_runtime(key, &[left_bits, right_bits])?;
        Ok(self
            .builder
            .ins()
            .bitcast(types::F128, MemFlags::new(), result_bits))
    }

    pub(crate) fn call_f128_cmp(
        &mut self,
        key: RuntimeKey,
        left: Value,
        right: Value,
    ) -> CodegenResult<Value> {
        let left_bits = self
            .builder
            .ins()
            .bitcast(types::I128, MemFlags::new(), left);
        let right_bits = self
            .builder
            .ins()
            .bitcast(types::I128, MemFlags::new(), right);
        self.call_runtime(key, &[left_bits, right_bits])
    }

    /// String equality comparison
    pub(crate) fn string_eq(&mut self, left: Value, right: Value) -> CodegenResult<Value> {
        if self.funcs().has_runtime(RuntimeKey::StringEq) {
            self.call_runtime(RuntimeKey::StringEq, &[left, right])
        } else {
            Ok(self.builder.ins().icmp(IntCC::Equal, left, right))
        }
    }

    /// Struct equality: compare all flat slots field-by-field.
    /// For Eq, returns true iff all slots are equal; for Ne, returns true iff any slot differs.
    /// Float fields use IEEE 754 fcmp so that NaN != NaN (correct), not bitwise icmp.
    fn struct_equality(
        &mut self,
        left: CompiledValue,
        right: CompiledValue,
        op: VirBinOp,
    ) -> CodegenResult<CompiledValue> {
        let field_slots = self.cached_struct_flat_slots(left.type_id).ok_or_else(|| {
            CodegenError::type_mismatch("struct_equality", "struct type", "non-struct")
        })?;

        // Start with true (1) - all fields equal so far
        let mut result = self.iconst_cached(types::I8, 1);

        for (offset, slot_type) in field_slots {
            let eq = self.struct_slot_eq(left.value, right.value, offset, slot_type)?;
            result = self.builder.ins().band(result, eq);
        }

        // For NotEq, negate the result
        if op == VirBinOp::Ne {
            let one = self.iconst_cached(types::I8, 1);
            result = self.builder.ins().bxor(result, one);
        }

        Ok(self.bool_value(result))
    }

    /// Compare one flat struct slot for equality, returning an I8 bool (1 = equal).
    ///
    /// Dispatches on `slot_type` (the Cranelift type from `leaf_cranelift_type`):
    /// - F32: stored as zero-extended I64; load I64, ireduce to I32, bitcast to F32, fcmp
    /// - F64: stored directly as F64 (8 bytes); load F64, fcmp
    /// - F128: stored as two independent 8-byte slots (low at offset, high at offset+8);
    ///   load two I64 halves, reconstruct_i128, bitcast to F128, call_f128_cmp
    /// - I64/I128/other: load with slot_type, icmp
    fn struct_slot_eq(
        &mut self,
        left_ptr: Value,
        right_ptr: Value,
        offset: i32,
        slot_type: Type,
    ) -> CodegenResult<Value> {
        if slot_type == types::F32 {
            // F32 fields are stored as zero-extended I64 (8 bytes).
            // Loading as F32 (4 bytes) would be a type-size mismatch.
            let left_i64 = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), left_ptr, offset);
            let right_i64 = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), right_ptr, offset);
            let left_i32 = self.builder.ins().ireduce(types::I32, left_i64);
            let right_i32 = self.builder.ins().ireduce(types::I32, right_i64);
            let left_f32 = self
                .builder
                .ins()
                .bitcast(types::F32, MemFlags::new(), left_i32);
            let right_f32 = self
                .builder
                .ins()
                .bitcast(types::F32, MemFlags::new(), right_i32);
            Ok(self.builder.ins().fcmp(FloatCC::Equal, left_f32, right_f32))
        } else if slot_type == types::F128 {
            // F128 fields occupy 16 bytes stored as two independent 8-byte slots:
            // low half at `offset`, high half at `offset + 8` (written by store_value_to_stack).
            // A single I128 load would assume 16-byte alignment, but struct fields are only
            // guaranteed 8-byte aligned. Use the paired I64 + reconstruct_i128 pattern.
            // Cranelift has no native fcmp for F128; use the runtime call instead.
            let left_low = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), left_ptr, offset);
            let left_high =
                self.builder
                    .ins()
                    .load(types::I64, MemFlags::new(), left_ptr, offset + 8);
            let right_low = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), right_ptr, offset);
            let right_high =
                self.builder
                    .ins()
                    .load(types::I64, MemFlags::new(), right_ptr, offset + 8);
            let left_i128 = crate::structs::reconstruct_i128(self.builder, left_low, left_high);
            let right_i128 = crate::structs::reconstruct_i128(self.builder, right_low, right_high);
            let left_f128 = self
                .builder
                .ins()
                .bitcast(types::F128, MemFlags::new(), left_i128);
            let right_f128 = self
                .builder
                .ins()
                .bitcast(types::F128, MemFlags::new(), right_i128);
            self.call_f128_cmp(RuntimeKey::F128Eq, left_f128, right_f128)
        } else if slot_type == types::F64 {
            let left_f64 = self
                .builder
                .ins()
                .load(types::F64, MemFlags::new(), left_ptr, offset);
            let right_f64 = self
                .builder
                .ins()
                .load(types::F64, MemFlags::new(), right_ptr, offset);
            Ok(self.builder.ins().fcmp(FloatCC::Equal, left_f64, right_f64))
        } else {
            // Integer types (I64, I128) and everything else: load and compare by value.
            // I128 loads 16 bytes (wide), all others load 8 bytes.
            let left_slot = self
                .builder
                .ins()
                .load(slot_type, MemFlags::new(), left_ptr, offset);
            let right_slot = self
                .builder
                .ins()
                .load(slot_type, MemFlags::new(), right_ptr, offset);
            Ok(self.builder.ins().icmp(IntCC::Equal, left_slot, right_slot))
        }
    }

    /// Compare an optional value with nil
    /// Returns true if the optional's tag matches the nil tag
    fn optional_nil_compare(
        &mut self,
        optional: CompiledValue,
        op: VirBinOp,
    ) -> CodegenResult<CompiledValue> {
        let meta = self.cached_optional_meta(optional.type_id).ok_or_else(|| {
            CodegenError::type_mismatch("optional_nil_compare", "optional type", "non-optional")
        })?;

        // Compare tag with nil_tag
        let result = match op {
            VirBinOp::Eq => self.tag_eq(optional.value, meta.nil_position as i64),
            VirBinOp::Ne => self.tag_ne(optional.value, meta.nil_position as i64),
            _ => unreachable!("optional_nil_compare only handles Eq and Ne"),
        };

        Ok(self.bool_value(result))
    }

    /// Compare an optional value with a non-nil value (e.g., optional == 42)
    /// Returns false if the optional is nil, otherwise compares the payload
    fn optional_value_compare(
        &mut self,
        optional: CompiledValue,
        value: CompiledValue,
        op: VirBinOp,
    ) -> CodegenResult<CompiledValue> {
        let meta = self.cached_optional_meta(optional.type_id).ok_or_else(|| {
            CodegenError::type_mismatch("optional_value_compare", "optional type", "non-optional")
        })?;

        // Check if not nil (tag != nil_tag)
        let is_not_nil = self.tag_ne(optional.value, meta.nil_position as i64);

        // Resolve the inner (non-nil) VirTypeId for dispatch
        let inner_vir_ty = meta.inner_type;
        let payload_cranelift_type = self.cranelift_type_v(inner_vir_ty);

        // Struct payloads are pointers to stack data; loading fields from a nil optional's
        // payload pointer causes a segfault. Use conditional branching to guard the load.
        if self.vir_query_is_struct_v(inner_vir_ty) {
            return self.optional_struct_compare(optional, value, op, is_not_nil, inner_vir_ty);
        }

        let payload =
            self.load_union_payload_v(optional.value, optional.type_id, payload_cranelift_type);

        // Compare payload with value, dispatching on VirTypeId rather than Cranelift type.
        // This correctly handles string (content equality), float, and integer/pointer types.
        // Cranelift-type dispatch would incorrectly treat string pointers as plain integers.
        let values_equal =
            self.compare_optional_payload_eq(inner_vir_ty, payload, payload_cranelift_type, value)?;

        // Result is: is_not_nil AND values_equal
        let result = match op {
            VirBinOp::Eq => {
                // (not nil) AND (values equal)
                self.builder.ins().band(is_not_nil, values_equal)
            }
            VirBinOp::Ne => {
                // NOT ((not nil) AND (values equal)) = is_nil OR (values not equal)
                let equal = self.builder.ins().band(is_not_nil, values_equal);
                let one = self.iconst_cached(types::I8, 1);
                self.builder.ins().isub(one, equal)
            }
            _ => unreachable!("optional_value_compare only handles Eq and Ne"),
        };

        Ok(self.bool_value(result))
    }

    /// Compare a struct? optional against a struct value using conditional branching.
    ///
    /// Struct field loads must not execute when the optional is nil (payload pointer is 0).
    /// Emits: if is_not_nil { struct_equality(payload, value) } else { false } then merges.
    fn optional_struct_compare(
        &mut self,
        optional: CompiledValue,
        value: CompiledValue,
        op: VirBinOp,
        is_not_nil: Value,
        inner_vir_ty: VirTypeId,
    ) -> CodegenResult<CompiledValue> {
        let payload_cranelift_type = self.cranelift_type_v(inner_vir_ty);
        let not_nil_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I8);

        // When nil: Eq -> false (0), Ne -> true (1)
        let nil_result: i64 = match op {
            VirBinOp::Eq => 0,
            VirBinOp::Ne => 1,
            _ => unreachable!("optional_struct_compare only handles Eq and Ne"),
        };
        let nil_block = self.builder.create_block();
        self.emit_brif(is_not_nil, not_nil_block, nil_block);

        // Nil branch: return the nil_result without loading from the payload pointer
        self.switch_and_seal(nil_block);
        let nil_val = self.iconst_cached(types::I8, nil_result);
        let nil_arg = BlockArg::from(nil_val);
        self.builder.ins().jump(merge_block, &[nil_arg]);

        // Non-nil branch: load payload and compare struct fields
        self.switch_and_seal(not_nil_block);
        let payload =
            self.load_union_payload_v(optional.value, optional.type_id, payload_cranelift_type);
        let payload_compiled = CompiledValue::new(payload, payload_cranelift_type, inner_vir_ty);
        let eq_result = self.struct_equality(payload_compiled, value, op)?;
        let eq_arg = BlockArg::from(eq_result.value);
        self.builder.ins().jump(merge_block, &[eq_arg]);

        // Merge
        self.switch_and_seal(merge_block);
        let result = self.builder.block_params(merge_block)[0];

        Ok(self.bool_value(result))
    }

    /// Compare an optional payload against a value, returning an I8 bool (1 = equal, 0 = not equal).
    ///
    /// Dispatches via [`classify_eq_hint_from_type`] on the unwrapped optional's
    /// inner type, using the same comparison hint taxonomy as `binary_op`.
    ///
    /// Note: Structs are handled before this function is called (see `optional_struct_compare`)
    /// because struct field loads must be guarded by a nil check to avoid segfaults.
    fn compare_optional_payload_eq(
        &mut self,
        inner_vir_ty: VirTypeId,
        payload: Value,
        payload_cranelift_type: Type,
        value: CompiledValue,
    ) -> CodegenResult<Value> {
        let hint = self.classify_eq_hint_from_type(inner_vir_ty);
        match hint {
            ComparisonHint::F128Cmp => self.call_f128_cmp(RuntimeKey::F128Eq, payload, value.value),
            ComparisonHint::FloatCmp => {
                Ok(self
                    .builder
                    .ins()
                    .fcmp(FloatCC::Equal, payload, value.value))
            }
            ComparisonHint::StringEq => self.string_eq(payload, value.value),
            _ => {
                // Integer, bool, pointer, interface, handle, union: compare by value/identity.
                // Widen mismatched operands to the larger type.
                let (cmp_payload, cmp_value) = if payload_cranelift_type.bytes() < value.ty.bytes()
                {
                    let extended = sextend_const(self.builder, value.ty, payload);
                    (extended, value.value)
                } else if payload_cranelift_type.bytes() > value.ty.bytes() {
                    let extended = sextend_const(self.builder, payload_cranelift_type, value.value);
                    (payload, extended)
                } else {
                    (payload, value.value)
                };
                Ok(self
                    .builder
                    .ins()
                    .icmp(IntCC::Equal, cmp_payload, cmp_value))
            }
        }
    }

    /// Emit division by zero check for integer division/remainder.
    /// Creates a branch: if divisor == 0, panic; else continue.
    /// Returns the continue block that should be used for subsequent code.
    fn emit_div_by_zero_check(&mut self, divisor: Value, line: u32) -> CodegenResult<Block> {
        // Constant-fold: if divisor is a known constant, skip the branch.
        if let Some(d) = try_constant_value(self.builder.func, divisor) {
            if d == 0 {
                // Divisor is known to be zero — always panic.
                self.emit_panic_static("division by zero", line)?;
                // Unreachable, but Cranelift needs a valid block to continue building.
                let unreachable_block = self.builder.create_block();
                self.switch_and_seal(unreachable_block);
                return Ok(unreachable_block);
            }
            // Divisor is known non-zero — no check needed, continue in current block.
            return self
                .builder
                .current_block()
                .ok_or_else(|| CodegenError::internal("no current block in div-by-zero check"));
        }

        let is_zero = self.builder.ins().icmp_imm(IntCC::Equal, divisor, 0);

        let panic_block = self.builder.create_block();
        let continue_block = self.builder.create_block();

        self.emit_brif(is_zero, panic_block, continue_block);

        // Panic block
        self.switch_and_seal(panic_block);
        self.emit_panic_static("division by zero", line)?;

        // Continue block
        self.switch_and_seal(continue_block);

        Ok(continue_block)
    }

    /// Emit signed division overflow check for MIN / -1 case.
    /// For signed division, INT_MIN / -1 causes overflow.
    /// Creates a branch: if (dividend == MIN && divisor == -1), panic; else continue.
    fn emit_signed_div_overflow_check(
        &mut self,
        dividend: Value,
        divisor: Value,
        result_ty: Type,
        line: u32,
    ) -> CodegenResult<()> {
        // Get MIN value for the integer type
        let min_val = match result_ty {
            types::I8 => i8::MIN as i64,
            types::I16 => i16::MIN as i64,
            types::I32 => i32::MIN as i64,
            types::I64 => i64::MIN,
            _ => return Ok(()), // Not a standard signed integer type
        };

        // Constant-fold: if both operands are known, evaluate at compile time.
        if let (Some(d), Some(v)) = (
            try_constant_value(self.builder.func, dividend),
            try_constant_value(self.builder.func, divisor),
        ) {
            if d == min_val && v == -1 {
                // Known overflow — always panic.
                self.emit_panic_static("integer overflow in division", line)?;
                let continue_block = self.builder.create_block();
                self.switch_and_seal(continue_block);
            }
            // Otherwise no overflow — skip the check entirely.
            return Ok(());
        }

        // Check if dividend == MIN
        let is_min = self.builder.ins().icmp_imm(IntCC::Equal, dividend, min_val);

        // Check if divisor == -1
        let is_neg_one = self.builder.ins().icmp_imm(IntCC::Equal, divisor, -1);

        // Combine: both must be true for overflow
        let would_overflow = self.builder.ins().band(is_min, is_neg_one);

        let panic_block = self.builder.create_block();
        let continue_block = self.builder.create_block();

        self.emit_brif(would_overflow, panic_block, continue_block);

        // Panic block
        self.switch_and_seal(panic_block);
        self.emit_panic_static("integer overflow in division", line)?;

        // Continue block
        self.switch_and_seal(continue_block);

        Ok(())
    }

    // =========================================================================
    // Comparison hint dispatch helpers
    // =========================================================================

    /// Dispatch optional == nil using the pre-resolved hint.
    /// Determines which operand is the optional and which is nil.
    fn dispatch_optional_nil_eq(
        &mut self,
        left: CompiledValue,
        right: CompiledValue,
        op: VirBinOp,
        lhs_is_optional: bool,
        rhs_is_optional: bool,
    ) -> CodegenResult<CompiledValue> {
        if (lhs_is_optional || self.vir_query_is_optional_v(left.type_id)) && right.type_id.is_nil()
        {
            self.optional_nil_compare(left, op)
        } else if (rhs_is_optional || self.vir_query_is_optional_v(right.type_id))
            && left.type_id.is_nil()
        {
            self.optional_nil_compare(right, op)
        } else {
            // Shouldn't happen with correct hint, but fallback gracefully.
            self.optional_nil_compare(left, op)
        }
    }

    /// Dispatch optional == value using the pre-resolved hint.
    /// Determines which operand is the optional and which is the value.
    fn dispatch_optional_value_eq(
        &mut self,
        left: CompiledValue,
        right: CompiledValue,
        op: VirBinOp,
    ) -> CodegenResult<CompiledValue> {
        if self.cached_optional_meta(left.type_id).is_some() {
            self.optional_value_compare(left, right, op)
        } else {
            self.optional_value_compare(right, left, op)
        }
    }

    /// Dispatch string equality/inequality with RC cleanup.
    fn dispatch_string_eq(
        &mut self,
        mut left: CompiledValue,
        mut right: CompiledValue,
        op: VirBinOp,
    ) -> CodegenResult<CompiledValue> {
        let result = match op {
            VirBinOp::Eq => self.string_eq(left.value, right.value)?,
            VirBinOp::Ne => {
                let eq = self.string_eq(left.value, right.value)?;
                let one = self.iconst_cached(types::I8, 1);
                self.builder.ins().isub(one, eq)
            }
            _ => unreachable!("dispatch_string_eq only handles Eq and Ne"),
        };
        self.consume_rc_value(&mut left)?;
        self.consume_rc_value(&mut right)?;
        Ok(self.bool_value(result))
    }

    /// Fallback Eq/Ne detection for `ComparisonHint::None` (generic paths).
    fn detect_eq_special_case(
        &mut self,
        left: CompiledValue,
        right: CompiledValue,
        op: VirBinOp,
        lhs_is_optional: bool,
        rhs_is_optional: bool,
    ) -> CodegenResult<Option<CompiledValue>> {
        let left_is_opt = lhs_is_optional || self.vir_query_is_optional_v(left.type_id);
        if left_is_opt && right.type_id.is_nil() {
            return Ok(Some(self.optional_nil_compare(left, op)?));
        }
        if (rhs_is_optional || self.vir_query_is_optional_v(right.type_id)) && left.type_id.is_nil()
        {
            return Ok(Some(self.optional_nil_compare(right, op)?));
        }
        if let Some(meta) = self.cached_optional_meta(left.type_id)
            && (meta.inner_type == right.type_id
                || (self.vir_query_is_integer_v(meta.inner_type)
                    && self.vir_query_is_integer_v(right.type_id)))
        {
            return Ok(Some(self.optional_value_compare(left, right, op)?));
        }
        if let Some(meta) = self.cached_optional_meta(right.type_id)
            && (meta.inner_type == left.type_id
                || (self.vir_query_is_integer_v(meta.inner_type)
                    && self.vir_query_is_integer_v(left.type_id)))
        {
            return Ok(Some(self.optional_value_compare(right, left, op)?));
        }
        if self.vir_query_is_struct_v(left.type_id) && self.vir_query_is_struct_v(right.type_id) {
            return Ok(Some(self.struct_equality(left, right, op)?));
        }
        Ok(None)
    }

    // =========================================================================
    // Comparison helpers using ComparisonHint
    // =========================================================================

    /// Emit Eq comparison, dispatching on the pre-resolved hint.
    ///
    /// String, struct, and optional Eq cases are handled as early returns
    /// before this function is called.  This handles numeric Eq and the
    /// `None` fallback for unresolved/generic paths.
    fn emit_eq(
        &mut self,
        hint: ComparisonHint,
        result_ty: Type,
        left_is_string: bool,
        left: Value,
        right: Value,
    ) -> CodegenResult<Value> {
        match hint {
            ComparisonHint::F128Cmp => self.call_f128_cmp(RuntimeKey::F128Eq, left, right),
            ComparisonHint::FloatCmp => Ok(self.builder.ins().fcmp(FloatCC::Equal, left, right)),
            ComparisonHint::IntCmp | ComparisonHint::UnsignedIntCmp => {
                Ok(self.emit_int_eq(left, right))
            }
            // None fallback: use operand type for string, Cranelift type for numerics.
            _ => {
                if left_is_string {
                    self.string_eq(left, right)
                } else if result_ty == types::F128 {
                    self.call_f128_cmp(RuntimeKey::F128Eq, left, right)
                } else if result_ty == types::F64 || result_ty == types::F32 {
                    Ok(self.builder.ins().fcmp(FloatCC::Equal, left, right))
                } else {
                    Ok(self.emit_int_eq(left, right))
                }
            }
        }
    }

    /// Emit Ne comparison, dispatching on the pre-resolved hint.
    fn emit_ne(
        &mut self,
        hint: ComparisonHint,
        result_ty: Type,
        left_is_string: bool,
        left: Value,
        right: Value,
    ) -> CodegenResult<Value> {
        match hint {
            ComparisonHint::F128Cmp => {
                let eq = self.call_f128_cmp(RuntimeKey::F128Eq, left, right)?;
                let one = self.iconst_cached(types::I8, 1);
                Ok(self.builder.ins().isub(one, eq))
            }
            ComparisonHint::FloatCmp => Ok(self.builder.ins().fcmp(FloatCC::NotEqual, left, right)),
            ComparisonHint::IntCmp | ComparisonHint::UnsignedIntCmp => {
                Ok(self.emit_int_ne(left, right))
            }
            _ => {
                if left_is_string {
                    let eq = self.string_eq(left, right)?;
                    let one = self.iconst_cached(types::I8, 1);
                    Ok(self.builder.ins().isub(one, eq))
                } else if result_ty == types::F128 {
                    let eq = self.call_f128_cmp(RuntimeKey::F128Eq, left, right)?;
                    let one = self.iconst_cached(types::I8, 1);
                    Ok(self.builder.ins().isub(one, eq))
                } else if result_ty == types::F64 || result_ty == types::F32 {
                    Ok(self.builder.ins().fcmp(FloatCC::NotEqual, left, right))
                } else {
                    Ok(self.emit_int_ne(left, right))
                }
            }
        }
    }

    /// Emit an ordered comparison (Lt, Le, Gt, Ge) using the hint.
    #[expect(clippy::too_many_arguments)]
    fn emit_ord_cmp(
        &mut self,
        hint: ComparisonHint,
        result_ty: Type,
        is_unsigned: bool,
        left: Value,
        right: Value,
        float_cc: FloatCC,
        unsigned_cc: IntCC,
        signed_cc: IntCC,
        f128_key: RuntimeKey,
    ) -> CodegenResult<Value> {
        match hint {
            ComparisonHint::F128Cmp => self.call_f128_cmp(f128_key, left, right),
            ComparisonHint::FloatCmp => Ok(self.builder.ins().fcmp(float_cc, left, right)),
            ComparisonHint::UnsignedIntCmp => {
                Ok(self.emit_int_cmp_with_fold(unsigned_cc, left, right))
            }
            ComparisonHint::IntCmp => Ok(self.emit_int_cmp_with_fold(signed_cc, left, right)),
            _ => {
                // Fallback for ComparisonHint::None (generic/unresolved).
                if result_ty == types::F128 {
                    self.call_f128_cmp(f128_key, left, right)
                } else if result_ty == types::F64 || result_ty == types::F32 {
                    Ok(self.builder.ins().fcmp(float_cc, left, right))
                } else {
                    let cc = if is_unsigned { unsigned_cc } else { signed_cc };
                    Ok(self.emit_int_cmp_with_fold(cc, left, right))
                }
            }
        }
    }

    /// Integer equality with constant folding.
    fn emit_int_eq(&mut self, left: Value, right: Value) -> Value {
        if let (Some(a), Some(b)) = (
            try_constant_value(self.builder.func, left),
            try_constant_value(self.builder.func, right),
        ) {
            self.iconst_cached(types::I8, i64::from(eval_int_cc(IntCC::Equal, a, b)))
        } else {
            self.builder.ins().icmp(IntCC::Equal, left, right)
        }
    }

    /// Integer not-equal with constant folding.
    fn emit_int_ne(&mut self, left: Value, right: Value) -> Value {
        if let (Some(a), Some(b)) = (
            try_constant_value(self.builder.func, left),
            try_constant_value(self.builder.func, right),
        ) {
            self.iconst_cached(types::I8, i64::from(eval_int_cc(IntCC::NotEqual, a, b)))
        } else {
            self.builder.ins().icmp(IntCC::NotEqual, left, right)
        }
    }

    /// Integer comparison with constant folding for any condition code.
    fn emit_int_cmp_with_fold(&mut self, cc: IntCC, left: Value, right: Value) -> Value {
        if let (Some(a), Some(b)) = (
            try_constant_value(self.builder.func, left),
            try_constant_value(self.builder.func, right),
        ) {
            self.iconst_cached(types::I8, i64::from(eval_int_cc(cc, a, b)))
        } else {
            self.builder.ins().icmp(cc, left, right)
        }
    }
}
