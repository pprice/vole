// types/wide_ops.rs
//
// Unified abstraction for 128-bit wide types (i128, f128).
//
// i128/f128 values occupy 2 x 8-byte slots in storage and require special
// handling throughout codegen: splitting into halves for stores, reconstructing
// from halves on loads, and bitcasting between f128 and i128 (Cranelift has no
// native f128 operations so we pass f128 as i128 bits to runtime calls).
//
// This module centralises those patterns so call sites can work with `WideType`
// instead of duplicating the i128/f128 branching logic.

use cranelift::prelude::*;
use vole_identity::{TypeId, VirTypeId};

use crate::types::CompiledValue;

/// A 128-bit wide type that needs 2 u64 slots in storage.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WideType {
    I128,
    F128,
}

impl WideType {
    /// Try to classify a Vole `TypeId` as a wide type.
    /// Returns `None` for non-wide types.
    pub fn from_type_id(type_id: TypeId) -> Option<Self> {
        if type_id == TypeId::I128 {
            Some(WideType::I128)
        } else if type_id == TypeId::F128 {
            Some(WideType::F128)
        } else {
            None
        }
    }

    /// Try to classify a `VirTypeId` as a wide type.
    ///
    /// VIR equivalent of [`WideType::from_type_id`].  Uses reserved
    /// `VirTypeId` constants rather than looking up the type table, since
    /// F128 has no `VirPrimitiveKind` variant yet.
    pub fn from_vir_type_id(vir_ty: VirTypeId) -> Option<Self> {
        if vir_ty == VirTypeId::I128 {
            Some(WideType::I128)
        } else if vir_ty == VirTypeId::F128 {
            Some(WideType::F128)
        } else {
            None
        }
    }

    /// Try to classify a Cranelift `Type` as a wide type.
    pub fn from_cranelift_type(ty: Type) -> Option<Self> {
        if ty == types::I128 {
            Some(WideType::I128)
        } else if ty == types::F128 {
            Some(WideType::F128)
        } else {
            None
        }
    }

    /// The Cranelift type for this wide type.
    pub fn cranelift_type(self) -> Type {
        match self {
            WideType::I128 => types::I128,
            WideType::F128 => types::F128,
        }
    }

    /// Convert a wide value to its i128 bit representation.
    ///
    /// - I128: pass through unchanged
    /// - F128: bitcast to I128
    ///
    /// This is the standard "prepare for storage / runtime call" step.
    pub fn to_i128_bits(self, builder: &mut FunctionBuilder, value: Value) -> Value {
        match self {
            WideType::I128 => value,
            WideType::F128 => builder.ins().bitcast(types::I128, MemFlags::new(), value),
        }
    }

    /// Convert raw i128 bits to the correct Cranelift value for this wide type.
    ///
    /// - I128: pass through unchanged
    /// - F128: bitcast from I128 to F128
    ///
    /// This is the standard "reconstruct after load / runtime call" step.
    pub fn reinterpret_i128(self, builder: &mut FunctionBuilder, i128_bits: Value) -> Value {
        match self {
            WideType::I128 => i128_bits,
            WideType::F128 => builder
                .ins()
                .bitcast(types::F128, MemFlags::new(), i128_bits),
        }
    }

    /// The VIR type ID for this wide type.
    pub fn vir_type_id(self) -> VirTypeId {
        match self {
            WideType::I128 => VirTypeId::I128,
            WideType::F128 => VirTypeId::F128,
        }
    }

    /// Build a `CompiledValue` from raw i128 bits, applying the correct
    /// bitcast for F128 types.
    pub fn compiled_value_from_i128(
        self,
        builder: &mut FunctionBuilder,
        i128_bits: Value,
        _type_id: TypeId,
    ) -> CompiledValue {
        let value = self.reinterpret_i128(builder, i128_bits);
        CompiledValue::new(value, self.cranelift_type(), self.vir_type_id())
    }
}
