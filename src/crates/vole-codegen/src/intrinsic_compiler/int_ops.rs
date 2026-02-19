// src/codegen/intrinsic_compiler/int_ops.rs
//
// Integer operation dispatch tables for unary and binary intrinsic operations.
// Uses paste-based macros to generate exhaustive match arms across all integer
// type/signedness combinations.

use cranelift::prelude::{InstBuilder, Type, Value, types};
use paste::paste;

use vole_sema::type_arena::TypeId;

use crate::context::Cg;
use crate::ops::uextend_const;

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
                    let amt = uextend_const(&mut $self.builder, types::I16, $a2);
                    ($self.builder.ins().$r_ins($a1, amt), types::I16, TypeId::I16)
                }
                $Enum::[<I32 $r_Op>] => {
                    let amt = uextend_const(&mut $self.builder, types::I32, $a2);
                    ($self.builder.ins().$r_ins($a1, amt), types::I32, TypeId::I32)
                }
                $Enum::[<I64 $r_Op>] => {
                    let amt = uextend_const(&mut $self.builder, types::I64, $a2);
                    ($self.builder.ins().$r_ins($a1, amt), types::I64, TypeId::I64)
                }
                $Enum::[<U8  $r_Op>] => ($self.builder.ins().$r_ins($a1, $a2), types::I8, TypeId::U8),
                $Enum::[<U16 $r_Op>] => {
                    let amt = uextend_const(&mut $self.builder, types::I16, $a2);
                    ($self.builder.ins().$r_ins($a1, amt), types::I16, TypeId::U16)
                }
                $Enum::[<U32 $r_Op>] => {
                    let amt = uextend_const(&mut $self.builder, types::I32, $a2);
                    ($self.builder.ins().$r_ins($a1, amt), types::I32, TypeId::U32)
                }
                $Enum::[<U64 $r_Op>] => {
                    let amt = uextend_const(&mut $self.builder, types::I64, $a2);
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
    /// Dispatch table for unary integer intrinsic operations.
    pub(super) fn compile_unary_int_op(
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
    pub(super) fn compile_binary_int_op(
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
