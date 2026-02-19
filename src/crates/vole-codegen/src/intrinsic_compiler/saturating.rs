// src/codegen/intrinsic_compiler/saturating.rs
//
// Saturating arithmetic operations for signed/unsigned integers.
// Includes overflow-detect-and-clamp methods for i32/i64, and
// widen-clamp-narrow helpers for i8/i16 (where Cranelift lacks native support).

use cranelift::prelude::{InstBuilder, IntCC, Type, Value, types};

use super::signed_min_max;
use crate::context::Cg;
use crate::ops::{sextend_const, uextend_const};

/// Macro to generate saturating arithmetic functions using widen-clamp-narrow approach.
/// Cranelift's sadd_sat/uadd_sat/ssub_sat/usub_sat don't support i8/i16, so we widen first.
macro_rules! impl_sat_widen_narrow {
    // Signed add: sextend, iadd, smax(min), smin(max), ireduce
    (signed_add, $fn_name:ident, $src_ty:expr, $wide_ty:expr, $min:expr, $max:expr) => {
        pub fn $fn_name(&mut self, a: Value, b: Value) -> Value {
            let a_wide = sextend_const(&mut self.builder, $wide_ty, a);
            let b_wide = sextend_const(&mut self.builder, $wide_ty, b);
            let sum = self.builder.ins().iadd(a_wide, b_wide);
            let min = self.builder.ins().iconst($wide_ty, $min);
            let max = self.builder.ins().iconst($wide_ty, $max);
            let clamped = self.builder.ins().smax(sum, min);
            let clamped = self.builder.ins().smin(clamped, max);
            self.builder.ins().ireduce($src_ty, clamped)
        }
    };
    // Unsigned add: uextend, iadd, umin(max), ireduce
    (unsigned_add, $fn_name:ident, $src_ty:expr, $wide_ty:expr, $max:expr) => {
        pub fn $fn_name(&mut self, a: Value, b: Value) -> Value {
            let a_wide = uextend_const(&mut self.builder, $wide_ty, a);
            let b_wide = uextend_const(&mut self.builder, $wide_ty, b);
            let sum = self.builder.ins().iadd(a_wide, b_wide);
            let max = self.builder.ins().iconst($wide_ty, $max);
            let clamped = self.builder.ins().umin(sum, max);
            self.builder.ins().ireduce($src_ty, clamped)
        }
    };
    // Signed sub: sextend, isub, smax(min), smin(max), ireduce
    (signed_sub, $fn_name:ident, $src_ty:expr, $wide_ty:expr, $min:expr, $max:expr) => {
        pub fn $fn_name(&mut self, a: Value, b: Value) -> Value {
            let a_wide = sextend_const(&mut self.builder, $wide_ty, a);
            let b_wide = sextend_const(&mut self.builder, $wide_ty, b);
            let diff = self.builder.ins().isub(a_wide, b_wide);
            let min = self.builder.ins().iconst($wide_ty, $min);
            let max = self.builder.ins().iconst($wide_ty, $max);
            let clamped = self.builder.ins().smax(diff, min);
            let clamped = self.builder.ins().smin(clamped, max);
            self.builder.ins().ireduce($src_ty, clamped)
        }
    };
    // Unsigned sub: uextend, isub, smax(0), ireduce (result can go negative)
    (unsigned_sub, $fn_name:ident, $src_ty:expr, $wide_ty:expr) => {
        pub fn $fn_name(&mut self, a: Value, b: Value) -> Value {
            let a_wide = uextend_const(&mut self.builder, $wide_ty, a);
            let b_wide = uextend_const(&mut self.builder, $wide_ty, b);
            let diff = self.builder.ins().isub(a_wide, b_wide);
            let zero = self.builder.ins().iconst($wide_ty, 0);
            let clamped = self.builder.ins().smax(diff, zero);
            self.builder.ins().ireduce($src_ty, clamped)
        }
    };
}

impl<'a, 'b, 'ctx> Cg<'a, 'b, 'ctx> {
    /// Signed saturating multiplication using overflow detection.
    /// If overflow occurs, clamp to MIN or MAX based on the sign of the result.
    /// Logic: If signs are same and overflow, result should be MAX.
    ///        If signs differ and overflow, result should be MIN.
    pub fn signed_saturating_mul(&mut self, a: Value, b: Value, ty: Type) -> Value {
        // Compute min and max for this type
        let bits = ty.bits();
        let (min_val, max_val) = signed_min_max(bits);
        let max = self.builder.ins().iconst(ty, max_val);
        let min = self.builder.ins().iconst(ty, min_val);
        let zero = self.builder.ins().iconst(ty, 0);

        // Perform multiplication with overflow detection
        let (result, overflow) = self.builder.ins().smul_overflow(a, b);

        // Determine if the result should be positive or negative
        // If a and b have same sign, positive overflow -> MAX
        // If a and b have different sign, negative overflow -> MIN
        let a_neg = self.builder.ins().icmp(IntCC::SignedLessThan, a, zero);
        let b_neg = self.builder.ins().icmp(IntCC::SignedLessThan, b, zero);
        let signs_differ = self.builder.ins().bxor(a_neg, b_neg);

        // If overflow: use min if signs differ (result would be negative), else max
        let sat_value = self.builder.ins().select(signs_differ, min, max);

        // Final result: if overflow, use saturated value, else use computed result
        self.builder.ins().select(overflow, sat_value, result)
    }

    /// Unsigned saturating multiplication.
    /// If overflow occurs, clamp to MAX.
    pub fn unsigned_saturating_mul(&mut self, a: Value, b: Value, ty: Type) -> Value {
        // Compute max for this type
        let bits = ty.bits();
        let max_val = if bits == 64 {
            // u64 max can't be represented as positive i64, use -1 which is all 1s
            -1i64
        } else {
            (1i64 << bits) - 1
        };
        let max = self.builder.ins().iconst(ty, max_val);

        // Perform multiplication with overflow detection
        let (result, overflow) = self.builder.ins().umul_overflow(a, b);

        // If overflow, use max, else use result
        self.builder.ins().select(overflow, max, result)
    }

    /// Signed saturating addition using overflow detection.
    /// If overflow occurs, clamp to MIN or MAX based on direction.
    pub fn signed_saturating_add(&mut self, a: Value, b: Value, ty: Type) -> Value {
        // Compute min and max for this type
        let bits = ty.bits();
        let (min_val, max_val) = signed_min_max(bits);
        let max = self.builder.ins().iconst(ty, max_val);
        let min = self.builder.ins().iconst(ty, min_val);
        let zero = self.builder.ins().iconst(ty, 0);

        // Perform addition with overflow detection
        let (result, overflow) = self.builder.ins().sadd_overflow(a, b);

        // On overflow: if b >= 0 (positive overflow), use max; else use min
        let b_non_neg = self
            .builder
            .ins()
            .icmp(IntCC::SignedGreaterThanOrEqual, b, zero);
        let sat_value = self.builder.ins().select(b_non_neg, max, min);

        // Final result: if overflow, use saturated value, else use computed result
        self.builder.ins().select(overflow, sat_value, result)
    }

    /// Unsigned saturating addition using overflow detection.
    /// If overflow occurs, clamp to MAX.
    pub fn unsigned_saturating_add(&mut self, a: Value, b: Value, ty: Type) -> Value {
        // Compute max for this type
        let bits = ty.bits();
        let max_val = if bits == 64 {
            -1i64 // All 1s
        } else {
            (1i64 << bits) - 1
        };
        let max = self.builder.ins().iconst(ty, max_val);

        // Perform addition with overflow detection
        let (result, overflow) = self.builder.ins().uadd_overflow(a, b);

        // If overflow, use max, else use result
        self.builder.ins().select(overflow, max, result)
    }

    /// Signed saturating subtraction using overflow detection.
    /// If overflow occurs, clamp to MIN or MAX based on direction.
    pub fn signed_saturating_sub(&mut self, a: Value, b: Value, ty: Type) -> Value {
        // Compute min and max for this type
        let bits = ty.bits();
        let (min_val, max_val) = signed_min_max(bits);
        let max = self.builder.ins().iconst(ty, max_val);
        let min = self.builder.ins().iconst(ty, min_val);
        let zero = self.builder.ins().iconst(ty, 0);

        // Perform subtraction with overflow detection
        let (result, overflow) = self.builder.ins().ssub_overflow(a, b);

        // On overflow: if b > 0 (subtracting positive -> underflow), use min; else use max
        let b_positive = self.builder.ins().icmp(IntCC::SignedGreaterThan, b, zero);
        let sat_value = self.builder.ins().select(b_positive, min, max);

        // Final result: if overflow, use saturated value, else use computed result
        self.builder.ins().select(overflow, sat_value, result)
    }

    /// Unsigned saturating subtraction using overflow detection.
    /// If overflow occurs, clamp to 0.
    pub fn unsigned_saturating_sub(&mut self, a: Value, b: Value, ty: Type) -> Value {
        let zero = self.builder.ins().iconst(ty, 0);

        // Perform subtraction with overflow detection
        let (result, overflow) = self.builder.ins().usub_overflow(a, b);

        // If overflow (underflow), use 0, else use result
        self.builder.ins().select(overflow, zero, result)
    }

    // Saturating arithmetic helpers for i8/u8/i16/u16 using widen-clamp-narrow approach.
    // Cranelift's sadd_sat/uadd_sat/ssub_sat/usub_sat don't support i8/i16.
    impl_sat_widen_narrow!(signed_add, i8_sadd_sat, types::I8, types::I16, -128, 127);
    impl_sat_widen_narrow!(unsigned_add, u8_uadd_sat, types::I8, types::I16, 255);
    impl_sat_widen_narrow!(signed_sub, i8_ssub_sat, types::I8, types::I16, -128, 127);
    impl_sat_widen_narrow!(unsigned_sub, u8_usub_sat, types::I8, types::I16);
    impl_sat_widen_narrow!(
        signed_add,
        i16_sadd_sat,
        types::I16,
        types::I32,
        -32768,
        32767
    );
    impl_sat_widen_narrow!(unsigned_add, u16_uadd_sat, types::I16, types::I32, 65535);
    impl_sat_widen_narrow!(
        signed_sub,
        i16_ssub_sat,
        types::I16,
        types::I32,
        -32768,
        32767
    );
    impl_sat_widen_narrow!(unsigned_sub, u16_usub_sat, types::I16, types::I32);
}
