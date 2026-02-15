// src/codegen/intrinsic_compiler/checked.rs
//
// Checked arithmetic operations returning Optional<T>.
// On overflow/error: returns nil (tag=0). On success: returns Some(result) (tag=1, value).

use cranelift::prelude::{InstBuilder, IntCC, Type, Value, types};

use vole_sema::type_arena::TypeId;

use super::signed_min_max;
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::CompiledValue;
use crate::union_layout;

impl<'a, 'b, 'ctx> Cg<'a, 'b, 'ctx> {
    /// Implement a checked integer operation returning Optional<T>.
    /// On overflow/error: returns nil (tag=0)
    /// On success: returns Some(result) (tag=1, value)
    pub(super) fn checked_int_op_impl(
        &mut self,
        op: crate::intrinsics::CheckedIntOp,
        arg1: Value,
        arg2: Value,
        return_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        use crate::intrinsics::CheckedIntOp;

        // Determine the operation and type
        let (result, overflow, ty, value_type_id) = match op {
            // Checked add - signed
            CheckedIntOp::I8CheckedAdd => {
                let (r, o) = self.builder.ins().sadd_overflow(arg1, arg2);
                (r, o, types::I8, TypeId::I8)
            }
            CheckedIntOp::I16CheckedAdd => {
                let (r, o) = self.builder.ins().sadd_overflow(arg1, arg2);
                (r, o, types::I16, TypeId::I16)
            }
            CheckedIntOp::I32CheckedAdd => {
                let (r, o) = self.builder.ins().sadd_overflow(arg1, arg2);
                (r, o, types::I32, TypeId::I32)
            }
            CheckedIntOp::I64CheckedAdd => {
                let (r, o) = self.builder.ins().sadd_overflow(arg1, arg2);
                (r, o, types::I64, TypeId::I64)
            }
            // Checked add - unsigned
            CheckedIntOp::U8CheckedAdd => {
                let (r, o) = self.builder.ins().uadd_overflow(arg1, arg2);
                (r, o, types::I8, TypeId::U8)
            }
            CheckedIntOp::U16CheckedAdd => {
                let (r, o) = self.builder.ins().uadd_overflow(arg1, arg2);
                (r, o, types::I16, TypeId::U16)
            }
            CheckedIntOp::U32CheckedAdd => {
                let (r, o) = self.builder.ins().uadd_overflow(arg1, arg2);
                (r, o, types::I32, TypeId::U32)
            }
            CheckedIntOp::U64CheckedAdd => {
                let (r, o) = self.builder.ins().uadd_overflow(arg1, arg2);
                (r, o, types::I64, TypeId::U64)
            }
            // Checked sub - signed
            CheckedIntOp::I8CheckedSub => {
                let (r, o) = self.builder.ins().ssub_overflow(arg1, arg2);
                (r, o, types::I8, TypeId::I8)
            }
            CheckedIntOp::I16CheckedSub => {
                let (r, o) = self.builder.ins().ssub_overflow(arg1, arg2);
                (r, o, types::I16, TypeId::I16)
            }
            CheckedIntOp::I32CheckedSub => {
                let (r, o) = self.builder.ins().ssub_overflow(arg1, arg2);
                (r, o, types::I32, TypeId::I32)
            }
            CheckedIntOp::I64CheckedSub => {
                let (r, o) = self.builder.ins().ssub_overflow(arg1, arg2);
                (r, o, types::I64, TypeId::I64)
            }
            // Checked sub - unsigned
            CheckedIntOp::U8CheckedSub => {
                let (r, o) = self.builder.ins().usub_overflow(arg1, arg2);
                (r, o, types::I8, TypeId::U8)
            }
            CheckedIntOp::U16CheckedSub => {
                let (r, o) = self.builder.ins().usub_overflow(arg1, arg2);
                (r, o, types::I16, TypeId::U16)
            }
            CheckedIntOp::U32CheckedSub => {
                let (r, o) = self.builder.ins().usub_overflow(arg1, arg2);
                (r, o, types::I32, TypeId::U32)
            }
            CheckedIntOp::U64CheckedSub => {
                let (r, o) = self.builder.ins().usub_overflow(arg1, arg2);
                (r, o, types::I64, TypeId::U64)
            }
            // Checked mul - signed
            CheckedIntOp::I8CheckedMul => {
                let (r, o) = self.builder.ins().smul_overflow(arg1, arg2);
                (r, o, types::I8, TypeId::I8)
            }
            CheckedIntOp::I16CheckedMul => {
                let (r, o) = self.builder.ins().smul_overflow(arg1, arg2);
                (r, o, types::I16, TypeId::I16)
            }
            CheckedIntOp::I32CheckedMul => {
                let (r, o) = self.builder.ins().smul_overflow(arg1, arg2);
                (r, o, types::I32, TypeId::I32)
            }
            CheckedIntOp::I64CheckedMul => {
                let (r, o) = self.builder.ins().smul_overflow(arg1, arg2);
                (r, o, types::I64, TypeId::I64)
            }
            // Checked mul - unsigned
            CheckedIntOp::U8CheckedMul => {
                let (r, o) = self.builder.ins().umul_overflow(arg1, arg2);
                (r, o, types::I8, TypeId::U8)
            }
            CheckedIntOp::U16CheckedMul => {
                let (r, o) = self.builder.ins().umul_overflow(arg1, arg2);
                (r, o, types::I16, TypeId::U16)
            }
            CheckedIntOp::U32CheckedMul => {
                let (r, o) = self.builder.ins().umul_overflow(arg1, arg2);
                (r, o, types::I32, TypeId::U32)
            }
            CheckedIntOp::U64CheckedMul => {
                let (r, o) = self.builder.ins().umul_overflow(arg1, arg2);
                (r, o, types::I64, TypeId::U64)
            }
            // Checked div - signed (check div-by-zero and MIN/-1)
            CheckedIntOp::I8CheckedDiv => {
                return self.checked_signed_div(arg1, arg2, types::I8, TypeId::I8, return_type_id);
            }
            CheckedIntOp::I16CheckedDiv => {
                return self.checked_signed_div(
                    arg1,
                    arg2,
                    types::I16,
                    TypeId::I16,
                    return_type_id,
                );
            }
            CheckedIntOp::I32CheckedDiv => {
                return self.checked_signed_div(
                    arg1,
                    arg2,
                    types::I32,
                    TypeId::I32,
                    return_type_id,
                );
            }
            CheckedIntOp::I64CheckedDiv => {
                return self.checked_signed_div(
                    arg1,
                    arg2,
                    types::I64,
                    TypeId::I64,
                    return_type_id,
                );
            }
            // Checked div - unsigned (check div-by-zero only)
            CheckedIntOp::U8CheckedDiv => {
                return self.checked_unsigned_div(
                    arg1,
                    arg2,
                    types::I8,
                    TypeId::U8,
                    return_type_id,
                );
            }
            CheckedIntOp::U16CheckedDiv => {
                return self.checked_unsigned_div(
                    arg1,
                    arg2,
                    types::I16,
                    TypeId::U16,
                    return_type_id,
                );
            }
            CheckedIntOp::U32CheckedDiv => {
                return self.checked_unsigned_div(
                    arg1,
                    arg2,
                    types::I32,
                    TypeId::U32,
                    return_type_id,
                );
            }
            CheckedIntOp::U64CheckedDiv => {
                return self.checked_unsigned_div(
                    arg1,
                    arg2,
                    types::I64,
                    TypeId::U64,
                    return_type_id,
                );
            }
        };

        // Build the optional result on the stack
        self.build_checked_optional_result(result, overflow, ty, value_type_id, return_type_id)
    }

    /// Build an Optional<T> result from a value and overflow flag.
    /// If overflow is true, returns nil. Otherwise returns Some(result).
    /// The tag values are determined by the position of nil and the value type
    /// in the union variants.
    fn build_checked_optional_result(
        &mut self,
        result: Value,
        overflow: Value,
        ty: Type,
        value_type_id: TypeId,
        return_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Find the nil and value variant positions in the union
        let nil_tag = self.find_nil_variant(return_type_id).ok_or_else(|| {
            CodegenError::type_mismatch(
                "checked arithmetic intrinsic",
                "optional type",
                "non-optional",
            )
        })?;

        // The value tag is the other position (0 or 1 in a 2-variant union)
        let value_tag = if nil_tag == 0 { 1 } else { 0 };

        // Allocate stack slot for optional: [tag: i8] + padding(7) + [value: T(8)]
        let slot = self.alloc_stack(union_layout::STANDARD_SIZE);

        // Determine tag based on overflow flag:
        // if overflow => nil_tag, else => value_tag
        let nil_tag_val = self.builder.ins().iconst(types::I8, nil_tag as i64);
        let value_tag_val = self.builder.ins().iconst(types::I8, value_tag as i64);
        let tag = self
            .builder
            .ins()
            .select(overflow, nil_tag_val, value_tag_val);

        // Store tag at offset 0
        self.builder.ins().stack_store(tag, slot, 0);

        // Store value at offset 8 (only matters if not overflow, but always store for simplicity)
        // Need to extend smaller types to i64 for storage
        let value_to_store = if ty.bytes() < 8 {
            if value_type_id.is_signed_int() {
                self.builder.ins().sextend(types::I64, result)
            } else {
                self.builder.ins().uextend(types::I64, result)
            }
        } else {
            result
        };
        self.builder
            .ins()
            .stack_store(value_to_store, slot, union_layout::PAYLOAD_OFFSET);

        // Return pointer to the stack slot
        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
        Ok(CompiledValue::new(ptr, ptr_type, return_type_id))
    }

    /// Checked signed division: returns nil on div-by-zero or MIN/-1 overflow.
    fn checked_signed_div(
        &mut self,
        dividend: Value,
        divisor: Value,
        ty: Type,
        value_type_id: TypeId,
        return_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let bits = ty.bits();
        let (min_val, _) = signed_min_max(bits);

        let zero = self.builder.ins().iconst(ty, 0);
        let one = self.builder.ins().iconst(ty, 1);
        let neg_one = self.builder.ins().iconst(ty, -1);
        let min = self.builder.ins().iconst(ty, min_val);

        // Check for div-by-zero: divisor == 0
        let is_zero = self.builder.ins().icmp(IntCC::Equal, divisor, zero);

        // Check for MIN/-1 overflow: dividend == MIN && divisor == -1
        let is_min = self.builder.ins().icmp(IntCC::Equal, dividend, min);
        let is_neg_one = self.builder.ins().icmp(IntCC::Equal, divisor, neg_one);
        let is_min_neg_one = self.builder.ins().band(is_min, is_neg_one);

        // Either condition causes nil result
        let should_return_nil = self.builder.ins().bor(is_zero, is_min_neg_one);

        // Perform the division with a safe divisor to avoid hardware faults
        // Use 1 as safe divisor when any error condition is true
        let safe_divisor = self.builder.ins().select(should_return_nil, one, divisor);
        let result = self.builder.ins().sdiv(dividend, safe_divisor);

        // Build optional result
        self.build_checked_optional_result(
            result,
            should_return_nil,
            ty,
            value_type_id,
            return_type_id,
        )
    }

    /// Checked unsigned division: returns nil on div-by-zero.
    fn checked_unsigned_div(
        &mut self,
        dividend: Value,
        divisor: Value,
        ty: Type,
        value_type_id: TypeId,
        return_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let zero = self.builder.ins().iconst(ty, 0);
        let one = self.builder.ins().iconst(ty, 1);

        // Check for div-by-zero
        let is_zero = self.builder.ins().icmp(IntCC::Equal, divisor, zero);

        // Perform division with safe divisor to avoid fault
        let safe_divisor = self.builder.ins().select(is_zero, one, divisor);
        let result = self.builder.ins().udiv(dividend, safe_divisor);

        // Build optional result
        self.build_checked_optional_result(result, is_zero, ty, value_type_id, return_type_id)
    }
}
