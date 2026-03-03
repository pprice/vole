// src/codegen/ops.rs
//
// Binary and compound assignment operations - impl Cg methods.

use cranelift::prelude::*;
use cranelift_codegen::ir::{BlockArg, Function, InstructionData};

use crate::RuntimeKey;
use crate::context::ExternalMethodRef;
use vole_identity::{TypeId, VirTypeId};
use vole_vir::VirBinOp;
use vole_vir::numeric_model::numeric_result_type_v;

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

/// Comparison condition codes for float, unsigned int, and signed int operations.
struct CmpCodes {
    float: FloatCC,
    unsigned: IntCC,
    signed: IntCC,
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

    /// Compile a binary operation on two values
    pub fn binary_op(
        &mut self,
        mut left: CompiledValue,
        mut right: CompiledValue,
        op: VirBinOp,
        line: u32,
    ) -> CodegenResult<CompiledValue> {
        // Handle optional/nil comparisons specially
        // When comparing optional == nil or optional != nil, we need to check the tag
        if matches!(op, VirBinOp::Eq | VirBinOp::Ne) {
            // Check if left is optional and right is nil
            let left_is_opt = self.vir_query_is_optional_v(left.type_id);
            let right_is_nil = right.type_id.is_nil();
            if left_is_opt && right_is_nil {
                return self.optional_nil_compare(left, op);
            }
            // Check if right is optional and left is nil
            if self.vir_query_is_optional_v(right.type_id) && left.type_id.is_nil() {
                return self.optional_nil_compare(right, op);
            }
            // Check if left is optional and right is a compatible value type (using VirTypeId)
            if let Some(inner_vir) = self.vir_query_unwrap_optional_v(left.type_id)
                && (inner_vir == right.type_id
                    || (self.vir_query_is_integer_v(inner_vir)
                        && self.vir_query_is_integer_v(right.type_id)))
            {
                return self.optional_value_compare(left, right, op);
            }
            // Check if right is optional and left is a compatible value type (using VirTypeId)
            if let Some(inner_vir) = self.vir_query_unwrap_optional_v(right.type_id)
                && (inner_vir == left.type_id
                    || (self.vir_query_is_integer_v(inner_vir)
                        && self.vir_query_is_integer_v(left.type_id)))
            {
                return self.optional_value_compare(right, left, op);
            }
            // Check if both operands are structs
            if self.vir_query_is_struct_v(left.type_id) && self.vir_query_is_struct_v(right.type_id)
            {
                return self.struct_equality(left, right, op);
            }
        }

        let left_vir_ty = left.type_id;
        let left_is_string = left_vir_ty == VirTypeId::STRING;

        // Determine result type using type promotion rules.
        // For numeric types, delegate to the canonical VIR numeric_model function.
        // For non-numeric types (like strings), use left's type directly.
        let (result_vir_ty, result_ty) = if left_vir_ty.is_numeric() && right.type_id.is_numeric() {
            let promoted = numeric_result_type_v(left_vir_ty, right.type_id);
            (promoted, vir_type_id_to_cranelift_type(promoted))
        } else {
            (left_vir_ty, left.ty)
        };

        let (left_val, right_val) = if result_ty == types::F128 {
            (
                self.coerce_value_to_f128(left)?,
                self.coerce_value_to_f128(right)?,
            )
        } else {
            // Convert operands to matching types
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
                    // Cranelift x64 doesn't support sdiv.i128; use runtime helper
                    self.call_runtime(RuntimeKey::I128Sdiv, &[left_val, right_val])?
                } else if left_vir_ty.is_unsigned_int() {
                    // Unsigned division: check for division by zero
                    self.emit_div_by_zero_check(right_val, line)?;
                    self.builder.ins().udiv(left_val, right_val)
                } else {
                    // Signed division: check for division by zero and MIN/-1 overflow
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
                    // Cranelift x64 doesn't support srem.i128; use runtime helper
                    self.call_runtime(RuntimeKey::I128Srem, &[left_val, right_val])?
                } else if left_vir_ty.is_unsigned_int() {
                    // Unsigned remainder: check for division by zero
                    self.emit_div_by_zero_check(right_val, line)?;
                    self.builder.ins().urem(left_val, right_val)
                } else {
                    // Signed remainder: check for division by zero and MIN/-1 overflow
                    self.emit_div_by_zero_check(right_val, line)?;
                    self.emit_signed_div_overflow_check(left_val, right_val, result_ty, line)?;
                    self.builder.ins().srem(left_val, right_val)
                }
            }
            VirBinOp::Eq => {
                if left_is_string {
                    self.string_eq(left_val, right_val)?
                } else if result_ty == types::F128 {
                    self.call_f128_cmp(RuntimeKey::F128Eq, left_val, right_val)?
                } else if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder.ins().fcmp(FloatCC::Equal, left_val, right_val)
                } else if let (Some(a), Some(b)) = (
                    try_constant_value(self.builder.func, left_val),
                    try_constant_value(self.builder.func, right_val),
                ) {
                    self.iconst_cached(types::I8, i64::from(eval_int_cc(IntCC::Equal, a, b)))
                } else {
                    self.builder.ins().icmp(IntCC::Equal, left_val, right_val)
                }
            }
            VirBinOp::Ne => {
                if left_is_string {
                    let eq = self.string_eq(left_val, right_val)?;
                    let one = self.iconst_cached(types::I8, 1);
                    self.builder.ins().isub(one, eq)
                } else if result_ty == types::F128 {
                    let eq = self.call_f128_cmp(RuntimeKey::F128Eq, left_val, right_val)?;
                    let one = self.iconst_cached(types::I8, 1);
                    self.builder.ins().isub(one, eq)
                } else if result_ty == types::F64 || result_ty == types::F32 {
                    self.builder
                        .ins()
                        .fcmp(FloatCC::NotEqual, left_val, right_val)
                } else if let (Some(a), Some(b)) = (
                    try_constant_value(self.builder.func, left_val),
                    try_constant_value(self.builder.func, right_val),
                ) {
                    self.iconst_cached(types::I8, i64::from(eval_int_cc(IntCC::NotEqual, a, b)))
                } else {
                    self.builder
                        .ins()
                        .icmp(IntCC::NotEqual, left_val, right_val)
                }
            }
            VirBinOp::Lt => {
                if result_ty == types::F128 {
                    self.call_f128_cmp(RuntimeKey::F128Lt, left_val, right_val)?
                } else {
                    self.emit_cmp(
                        result_ty,
                        left_vir_ty,
                        left_val,
                        right_val,
                        CmpCodes {
                            float: FloatCC::LessThan,
                            unsigned: IntCC::UnsignedLessThan,
                            signed: IntCC::SignedLessThan,
                        },
                    )
                }
            }
            VirBinOp::Gt => {
                if result_ty == types::F128 {
                    self.call_f128_cmp(RuntimeKey::F128Gt, left_val, right_val)?
                } else {
                    self.emit_cmp(
                        result_ty,
                        left_vir_ty,
                        left_val,
                        right_val,
                        CmpCodes {
                            float: FloatCC::GreaterThan,
                            unsigned: IntCC::UnsignedGreaterThan,
                            signed: IntCC::SignedGreaterThan,
                        },
                    )
                }
            }
            VirBinOp::Le => {
                if result_ty == types::F128 {
                    self.call_f128_cmp(RuntimeKey::F128Le, left_val, right_val)?
                } else {
                    self.emit_cmp(
                        result_ty,
                        left_vir_ty,
                        left_val,
                        right_val,
                        CmpCodes {
                            float: FloatCC::LessThanOrEqual,
                            unsigned: IntCC::UnsignedLessThanOrEqual,
                            signed: IntCC::SignedLessThanOrEqual,
                        },
                    )
                }
            }
            VirBinOp::Ge => {
                if result_ty == types::F128 {
                    self.call_f128_cmp(RuntimeKey::F128Ge, left_val, right_val)?
                } else {
                    self.emit_cmp(
                        result_ty,
                        left_vir_ty,
                        left_val,
                        right_val,
                        CmpCodes {
                            float: FloatCC::GreaterThanOrEqual,
                            unsigned: IntCC::UnsignedGreaterThanOrEqual,
                            signed: IntCC::SignedGreaterThanOrEqual,
                        },
                    )
                }
            }
            VirBinOp::And | VirBinOp::Or => unreachable!("handled above"),
            VirBinOp::BitAnd => self.builder.ins().band(left_val, right_val),
            VirBinOp::BitOr => self.builder.ins().bor(left_val, right_val),
            VirBinOp::BitXor => self.builder.ins().bxor(left_val, right_val),
            VirBinOp::Shl => self.builder.ins().ishl(left_val, right_val),
            VirBinOp::Shr => {
                if left_vir_ty.is_unsigned_int() {
                    self.builder.ins().ushr(left_val, right_val)
                } else {
                    self.builder.ins().sshr(left_val, right_val)
                }
            }
        };

        // Consume RC operands used by string comparison
        if left_is_string && matches!(op, VirBinOp::Eq | VirBinOp::Ne) {
            self.consume_rc_value(&mut left)?;
            self.consume_rc_value(&mut right)?;
        }

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

    fn call_f128_cmp(
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
    fn string_eq(&mut self, left: Value, right: Value) -> CodegenResult<Value> {
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
        let field_slots = self
            .struct_flat_field_cranelift_types_v(left.type_id)
            .ok_or_else(|| {
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
        // Find the position of nil in the variants (this is the nil tag value)
        // Use VIR path for correct variant ordering (round-tripped sema TypeId
        // can have reversed variants due to arena.lookup_optional non-determinism).
        let nil_tag = self.find_nil_variant_vir(optional.type_id).ok_or_else(|| {
            CodegenError::type_mismatch("optional_nil_compare", "optional type", "non-optional")
        })?;

        // Compare tag with nil_tag
        let result = match op {
            VirBinOp::Eq => self.tag_eq(optional.value, nil_tag as i64),
            VirBinOp::Ne => self.tag_ne(optional.value, nil_tag as i64),
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
        // Find the position of nil in the variants (this is the nil tag value)
        let nil_tag = self.find_nil_variant_vir(optional.type_id).ok_or_else(|| {
            CodegenError::type_mismatch("optional_value_compare", "optional type", "non-optional")
        })?;

        // Check if not nil (tag != nil_tag)
        let is_not_nil = self.tag_ne(optional.value, nil_tag as i64);

        // Resolve the inner (non-nil) VirTypeId for dispatch
        let inner_vir_ty = self
            .vir_query_unwrap_optional_v(optional.type_id)
            .unwrap_or(VirTypeId::I64);
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
    /// Dispatches on `inner_vir_ty` (the VirTypeId of the unwrapped optional's inner type):
    /// - f128                -> call_f128_cmp (Cranelift has no native fcmp for F128)
    /// - f32 / f64           -> fcmp
    /// - String              -> string_eq (content equality via RuntimeKey::StringEq)
    /// - Everything else     -> icmp (int, bool, pointer, interface, handle, union)
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
        if inner_vir_ty == VirTypeId::F128 {
            // F128 requires a runtime call; Cranelift has no native fcmp for 128-bit floats.
            self.call_f128_cmp(RuntimeKey::F128Eq, payload, value.value)
        } else if self.vir_query_is_float_v(inner_vir_ty) {
            // F32 / F64 use the native Cranelift fcmp instruction.
            Ok(self
                .builder
                .ins()
                .fcmp(FloatCC::Equal, payload, value.value))
        } else if self.vir_query_is_string_v(inner_vir_ty) {
            self.string_eq(payload, value.value)
        } else {
            // Integer, bool, pointer, interface, handle, union: compare by value/identity
            let (cmp_payload, cmp_value) = if payload_cranelift_type.bytes() < value.ty.bytes() {
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

    /// Emit a comparison instruction, dispatching based on type (float vs int, signed vs unsigned).
    /// When both operands are known integer constants, the result is computed at compile time.
    fn emit_cmp(
        &mut self,
        result_ty: Type,
        left_vir_ty: VirTypeId,
        left_val: Value,
        right_val: Value,
        codes: CmpCodes,
    ) -> Value {
        if result_ty == types::F64 || result_ty == types::F32 {
            self.builder.ins().fcmp(codes.float, left_val, right_val)
        } else if let (Some(a), Some(b)) = (
            try_constant_value(self.builder.func, left_val),
            try_constant_value(self.builder.func, right_val),
        ) {
            let cc = if left_vir_ty.is_unsigned_int() {
                codes.unsigned
            } else {
                codes.signed
            };
            self.iconst_cached(types::I8, i64::from(eval_int_cc(cc, a, b)))
        } else if left_vir_ty.is_unsigned_int() {
            self.builder.ins().icmp(codes.unsigned, left_val, right_val)
        } else {
            self.builder.ins().icmp(codes.signed, left_val, right_val)
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
}
