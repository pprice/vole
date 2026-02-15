// src/codegen/intrinsic_compiler.rs
//
// Intrinsic compilation methods - impl Cg methods for saturating/checked arithmetic,
// compiler intrinsics, and inline intrinsic dispatch.
//
// Handles saturating arithmetic (mul/add/sub for signed/unsigned), checked arithmetic
// with optional results, compiler intrinsic dispatch (float constants, unary/binary ops),
// and inline emission of array/string length. Split from context.rs.

use cranelift::prelude::{AbiParam, InstBuilder, IntCC, MemFlags, Type, Value, types};
use cranelift_module::Module;
use paste::paste;

use vole_runtime::native_registry::NativeType;
use vole_sema::implement_registry::ExternalMethodInfo;
use vole_sema::type_arena::TypeId;

use crate::RuntimeKey;
use crate::callable_registry::{CallableKey, ResolvedCallable, resolve_callable_with_preference};
use crate::errors::{CodegenError, CodegenResult};
use crate::union_layout;

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

/// Macro to generate saturating arithmetic functions using widen-clamp-narrow approach.
/// Cranelift's sadd_sat/uadd_sat/ssub_sat/usub_sat don't support i8/i16, so we widen first.
macro_rules! impl_sat_widen_narrow {
    // Signed add: sextend, iadd, smax(min), smin(max), ireduce
    (signed_add, $fn_name:ident, $src_ty:expr, $wide_ty:expr, $min:expr, $max:expr) => {
        pub fn $fn_name(&mut self, a: Value, b: Value) -> Value {
            let a_wide = self.builder.ins().sextend($wide_ty, a);
            let b_wide = self.builder.ins().sextend($wide_ty, b);
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
            let a_wide = self.builder.ins().uextend($wide_ty, a);
            let b_wide = self.builder.ins().uextend($wide_ty, b);
            let sum = self.builder.ins().iadd(a_wide, b_wide);
            let max = self.builder.ins().iconst($wide_ty, $max);
            let clamped = self.builder.ins().umin(sum, max);
            self.builder.ins().ireduce($src_ty, clamped)
        }
    };
    // Signed sub: sextend, isub, smax(min), smin(max), ireduce
    (signed_sub, $fn_name:ident, $src_ty:expr, $wide_ty:expr, $min:expr, $max:expr) => {
        pub fn $fn_name(&mut self, a: Value, b: Value) -> Value {
            let a_wide = self.builder.ins().sextend($wide_ty, a);
            let b_wide = self.builder.ins().sextend($wide_ty, b);
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
            let a_wide = self.builder.ins().uextend($wide_ty, a);
            let b_wide = self.builder.ins().uextend($wide_ty, b);
            let diff = self.builder.ins().isub(a_wide, b_wide);
            let zero = self.builder.ins().iconst($wide_ty, 0);
            let clamped = self.builder.ins().smax(diff, zero);
            self.builder.ins().ireduce($src_ty, clamped)
        }
    };
}

// =============================================================================
// Dispatch macros for integer intrinsic operations
// =============================================================================
//
// Each macro below takes a list of typed operation descriptors and produces a
// complete `match` expression wrapped in `paste! {}`. Since all `[<>]` concat
// tokens live directly inside the paste! block (not hidden in sub-macro calls),
// paste can resolve them before the compiler parses match arms.
//
// Usage example:
//   dispatch_unary_int_op!(self, UnaryIntOp, op, arg, {
//       signed(Abs, iabs),
//       merged(Clz, clz),
//       all(Bitrev, bitrev),
//   })

/// Generate a complete match expression dispatching unary integer operations.
///
/// Entry kinds:
///   `signed(Op, ins)`  - 4 arms for I8..I64 with one Cranelift instruction
///   `merged(Op, ins)`  - 4 arms merging I+U per width (result TypeId always signed)
///   `all(Op, ins)`     - 8 arms preserving signed/unsigned TypeId
macro_rules! dispatch_unary_int_op {
    // Accept a list of entries, each separated by semicolons.
    // Each entry is prefixed with its kind token.
    ($self:ident, $Enum:ident, $op:expr, $arg:expr, {
        $(signed($s_Op:ident, $s_ins:ident)),*;
        $(merged($m_Op:ident, $m_ins:ident)),*;
        $(all($a_Op:ident, $a_ins:ident)),*;
    }) => {
        paste! { match $op {
            // signed: 4 arms per op
            $(
                $Enum::[<I8  $s_Op>] => ($self.builder.ins().$s_ins($arg), types::I8,  TypeId::I8),
                $Enum::[<I16 $s_Op>] => ($self.builder.ins().$s_ins($arg), types::I16, TypeId::I16),
                $Enum::[<I32 $s_Op>] => ($self.builder.ins().$s_ins($arg), types::I32, TypeId::I32),
                $Enum::[<I64 $s_Op>] => ($self.builder.ins().$s_ins($arg), types::I64, TypeId::I64),
            )*
            // merged: 4 arms per op (I+U share arms)
            $(
                $Enum::[<I8  $m_Op>] | $Enum::[<U8  $m_Op>] => ($self.builder.ins().$m_ins($arg), types::I8,  TypeId::I8),
                $Enum::[<I16 $m_Op>] | $Enum::[<U16 $m_Op>] => ($self.builder.ins().$m_ins($arg), types::I16, TypeId::I16),
                $Enum::[<I32 $m_Op>] | $Enum::[<U32 $m_Op>] => ($self.builder.ins().$m_ins($arg), types::I32, TypeId::I32),
                $Enum::[<I64 $m_Op>] | $Enum::[<U64 $m_Op>] => ($self.builder.ins().$m_ins($arg), types::I64, TypeId::I64),
            )*
            // all: 8 arms per op (separate signed/unsigned TypeIds)
            $(
                $Enum::[<I8  $a_Op>] => ($self.builder.ins().$a_ins($arg), types::I8,  TypeId::I8),
                $Enum::[<I16 $a_Op>] => ($self.builder.ins().$a_ins($arg), types::I16, TypeId::I16),
                $Enum::[<I32 $a_Op>] => ($self.builder.ins().$a_ins($arg), types::I32, TypeId::I32),
                $Enum::[<I64 $a_Op>] => ($self.builder.ins().$a_ins($arg), types::I64, TypeId::I64),
                $Enum::[<U8  $a_Op>] => ($self.builder.ins().$a_ins($arg), types::I8,  TypeId::U8),
                $Enum::[<U16 $a_Op>] => ($self.builder.ins().$a_ins($arg), types::I16, TypeId::U16),
                $Enum::[<U32 $a_Op>] => ($self.builder.ins().$a_ins($arg), types::I32, TypeId::U32),
                $Enum::[<U64 $a_Op>] => ($self.builder.ins().$a_ins($arg), types::I64, TypeId::U64),
            )*
        }}
    };
}

/// Generate a complete match expression dispatching binary integer operations.
///
/// Entry kinds:
///   `su(Op, s_ins, u_ins)`     - signed/unsigned use different CL instructions
///   `all(Op, ins)`             - same instruction for all types
///   `rotate(Op, ins)`          - uextend arg2 for types > I8
///   `sat(Op, [s_fns], [u_fns])` - saturating with per-width helpers
///   `sat_method(Op, s_fn, u_fn)` - saturating with uniform method(a, b, ty)
macro_rules! dispatch_binary_int_op {
    ($self:ident, $Enum:ident, $op:expr, $a1:expr, $a2:expr, {
        $(su($su_Op:ident, $su_s:ident, $su_u:ident)),*;
        $(rotate($r_Op:ident, $r_ins:ident)),*;
        $(all($al_Op:ident, $al_ins:ident)),*;
        $(sat($sat_Op:ident,
              [$si8:ident, $si16:ident, $si32:ident, $si64:ident],
              [$ui8:ident, $ui16:ident, $ui32:ident, $ui64:ident])),*;
        $(sat_method($sm_Op:ident, $sm_s:ident, $sm_u:ident)),*;
    }) => {
        paste! { match $op {
            // su: 8 arms with different signed/unsigned instructions
            $(
                $Enum::[<I8  $su_Op>] => ($self.builder.ins().$su_s($a1, $a2), types::I8,  TypeId::I8),
                $Enum::[<I16 $su_Op>] => ($self.builder.ins().$su_s($a1, $a2), types::I16, TypeId::I16),
                $Enum::[<I32 $su_Op>] => ($self.builder.ins().$su_s($a1, $a2), types::I32, TypeId::I32),
                $Enum::[<I64 $su_Op>] => ($self.builder.ins().$su_s($a1, $a2), types::I64, TypeId::I64),
                $Enum::[<U8  $su_Op>] => ($self.builder.ins().$su_u($a1, $a2), types::I8,  TypeId::U8),
                $Enum::[<U16 $su_Op>] => ($self.builder.ins().$su_u($a1, $a2), types::I16, TypeId::U16),
                $Enum::[<U32 $su_Op>] => ($self.builder.ins().$su_u($a1, $a2), types::I32, TypeId::U32),
                $Enum::[<U64 $su_Op>] => ($self.builder.ins().$su_u($a1, $a2), types::I64, TypeId::U64),
            )*
            // rotate: 8 arms with uextend for shift amounts > I8
            $(
                $Enum::[<I8  $r_Op>] => ($self.builder.ins().$r_ins($a1, $a2), types::I8, TypeId::I8),
                $Enum::[<I16 $r_Op>] => {
                    let amt = $self.builder.ins().uextend(types::I16, $a2);
                    ($self.builder.ins().$r_ins($a1, amt), types::I16, TypeId::I16)
                }
                $Enum::[<I32 $r_Op>] => {
                    let amt = $self.builder.ins().uextend(types::I32, $a2);
                    ($self.builder.ins().$r_ins($a1, amt), types::I32, TypeId::I32)
                }
                $Enum::[<I64 $r_Op>] => {
                    let amt = $self.builder.ins().uextend(types::I64, $a2);
                    ($self.builder.ins().$r_ins($a1, amt), types::I64, TypeId::I64)
                }
                $Enum::[<U8  $r_Op>] => ($self.builder.ins().$r_ins($a1, $a2), types::I8, TypeId::U8),
                $Enum::[<U16 $r_Op>] => {
                    let amt = $self.builder.ins().uextend(types::I16, $a2);
                    ($self.builder.ins().$r_ins($a1, amt), types::I16, TypeId::U16)
                }
                $Enum::[<U32 $r_Op>] => {
                    let amt = $self.builder.ins().uextend(types::I32, $a2);
                    ($self.builder.ins().$r_ins($a1, amt), types::I32, TypeId::U32)
                }
                $Enum::[<U64 $r_Op>] => {
                    let amt = $self.builder.ins().uextend(types::I64, $a2);
                    ($self.builder.ins().$r_ins($a1, amt), types::I64, TypeId::U64)
                }
            )*
            // all: 8 arms with same instruction
            $(
                $Enum::[<I8  $al_Op>] => ($self.builder.ins().$al_ins($a1, $a2), types::I8,  TypeId::I8),
                $Enum::[<I16 $al_Op>] => ($self.builder.ins().$al_ins($a1, $a2), types::I16, TypeId::I16),
                $Enum::[<I32 $al_Op>] => ($self.builder.ins().$al_ins($a1, $a2), types::I32, TypeId::I32),
                $Enum::[<I64 $al_Op>] => ($self.builder.ins().$al_ins($a1, $a2), types::I64, TypeId::I64),
                $Enum::[<U8  $al_Op>] => ($self.builder.ins().$al_ins($a1, $a2), types::I8,  TypeId::U8),
                $Enum::[<U16 $al_Op>] => ($self.builder.ins().$al_ins($a1, $a2), types::I16, TypeId::U16),
                $Enum::[<U32 $al_Op>] => ($self.builder.ins().$al_ins($a1, $a2), types::I32, TypeId::U32),
                $Enum::[<U64 $al_Op>] => ($self.builder.ins().$al_ins($a1, $a2), types::I64, TypeId::U64),
            )*
            // sat: 8 arms - i8/i16 use 2-arg helpers, i32/i64 use 3-arg methods
            $(
                $Enum::[<I8  $sat_Op>] => ($self.$si8($a1, $a2),  types::I8,  TypeId::I8),
                $Enum::[<I16 $sat_Op>] => ($self.$si16($a1, $a2), types::I16, TypeId::I16),
                $Enum::[<I32 $sat_Op>] => {
                    let v = $self.$si32($a1, $a2, types::I32);
                    (v, types::I32, TypeId::I32)
                }
                $Enum::[<I64 $sat_Op>] => {
                    let v = $self.$si64($a1, $a2, types::I64);
                    (v, types::I64, TypeId::I64)
                }
                $Enum::[<U8  $sat_Op>] => ($self.$ui8($a1, $a2),  types::I8,  TypeId::U8),
                $Enum::[<U16 $sat_Op>] => ($self.$ui16($a1, $a2), types::I16, TypeId::U16),
                $Enum::[<U32 $sat_Op>] => {
                    let v = $self.$ui32($a1, $a2, types::I32);
                    (v, types::I32, TypeId::U32)
                }
                $Enum::[<U64 $sat_Op>] => {
                    let v = $self.$ui64($a1, $a2, types::I64);
                    (v, types::I64, TypeId::U64)
                }
            )*
            // sat_method: 8 arms, all widths use method(a, b, ty)
            $(
                $Enum::[<I8  $sm_Op>] => { let v = $self.$sm_s($a1, $a2, types::I8);  (v, types::I8,  TypeId::I8)  }
                $Enum::[<I16 $sm_Op>] => { let v = $self.$sm_s($a1, $a2, types::I16); (v, types::I16, TypeId::I16) }
                $Enum::[<I32 $sm_Op>] => { let v = $self.$sm_s($a1, $a2, types::I32); (v, types::I32, TypeId::I32) }
                $Enum::[<I64 $sm_Op>] => { let v = $self.$sm_s($a1, $a2, types::I64); (v, types::I64, TypeId::I64) }
                $Enum::[<U8  $sm_Op>] => { let v = $self.$sm_u($a1, $a2, types::I8);  (v, types::I8,  TypeId::U8)  }
                $Enum::[<U16 $sm_Op>] => { let v = $self.$sm_u($a1, $a2, types::I16); (v, types::I16, TypeId::U16) }
                $Enum::[<U32 $sm_Op>] => { let v = $self.$sm_u($a1, $a2, types::I32); (v, types::I32, TypeId::U32) }
                $Enum::[<U64 $sm_Op>] => { let v = $self.$sm_u($a1, $a2, types::I64); (v, types::I64, TypeId::U64) }
            )*
        }}
    };
}

impl<'a, 'b, 'ctx> Cg<'a, 'b, 'ctx> {
    // ========== Saturating arithmetic ==========

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

    // ========== Checked arithmetic helpers ==========

    /// Implement a checked integer operation returning Optional<T>.
    /// On overflow/error: returns nil (tag=0)
    /// On success: returns Some(result) (tag=1, value)
    fn checked_int_op_impl(
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

    /// Dispatch table for unary integer intrinsic operations.
    fn compile_unary_int_op(
        &mut self,
        op: crate::intrinsics::UnaryIntOp,
        arg: Value,
    ) -> (Value, Type, TypeId) {
        use crate::intrinsics::UnaryIntOp;
        dispatch_unary_int_op!(self, UnaryIntOp, op, arg, {
            signed(Abs, iabs);
            merged(Clz, clz), merged(Ctz, ctz), merged(Popcnt, popcnt);
            all(Bitrev, bitrev);
        })
    }

    /// Dispatch table for binary integer intrinsic operations.
    fn compile_binary_int_op(
        &mut self,
        op: crate::intrinsics::BinaryIntOp,
        arg1: Value,
        arg2: Value,
    ) -> (Value, Type, TypeId) {
        use crate::intrinsics::BinaryIntOp;
        dispatch_binary_int_op!(self, BinaryIntOp, op, arg1, arg2, {
            su(Min, smin, umin), su(Max, smax, umax);
            rotate(Rotl, rotl), rotate(Rotr, rotr);
            all(WrappingAdd, iadd), all(WrappingSub, isub), all(WrappingMul, imul);
            sat(SaturatingAdd,
                [i8_sadd_sat, i16_sadd_sat, signed_saturating_add, signed_saturating_add],
                [u8_uadd_sat, u16_uadd_sat, unsigned_saturating_add, unsigned_saturating_add]),
            sat(SaturatingSub,
                [i8_ssub_sat, i16_ssub_sat, signed_saturating_sub, signed_saturating_sub],
                [u8_usub_sat, u16_usub_sat, unsigned_saturating_sub, unsigned_saturating_sub]);
            sat_method(SaturatingMul, signed_saturating_mul, unsigned_saturating_mul);
        })
    }
}
