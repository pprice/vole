// func.rs
//
// VIR function and body representations.

use vole_identity::{FunctionId, MethodId, NameId, Span, Symbol, VirTypeId};

use crate::refs::VirRef;
use crate::stmt::VirStmt;
use crate::type_table::VirTypeTable;
use crate::types::VirType;

// ---------------------------------------------------------------------------
// ReturnAbi — pre-computed return ABI convention
// ---------------------------------------------------------------------------

/// Maximum number of flat struct fields that fit in register returns.
///
/// Structs with this many or fewer 8-byte slots use multi-value register
/// returns (`SmallStruct`).  Larger structs use the sret (stack return
/// pointer) convention (`SretStruct`).
pub const MAX_SMALL_STRUCT_FIELDS: usize = 2;

/// Pre-computed return ABI for a VIR function's signature.
///
/// Determined by the function's VIR return type during lowering or
/// monomorphization.  Codegen reads this hint to build Cranelift
/// signatures (register counts, sret pointers, union stack copies)
/// without re-inspecting type properties.
///
/// Distinct from `VirStmt::Return`'s `ReturnConvention`, which describes
/// value-level preparation (boxing, wrapping).  `ReturnAbi` describes
/// the ABI-level register layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ReturnAbi {
    /// No return value (void, never).
    Void,
    /// Single register return (most scalar types, classes, interfaces, unknown).
    Single,
    /// Two-register return for wide types (i128, f128, range).
    Wide,
    /// Fallible return with non-wide success: `(tag, payload)`.
    Fallible,
    /// Fallible return with wide success (i128): `(tag, low, high)`.
    WideFallible,
    /// Small struct return via registers (1–2 flat slots, padded to
    /// `MAX_SMALL_STRUCT_FIELDS`).
    SmallStruct { field_count: usize },
    /// Large struct return via sret convention (3+ flat slots, hidden
    /// first parameter points to caller-allocated buffer).
    SretStruct { field_count: usize },
    /// Union return — the callee returns a pointer to its stack-allocated
    /// union buffer.  The caller must copy to local storage before the
    /// callee's frame is reused.
    UnionPtr,
}

impl ReturnAbi {
    /// Classify the return ABI from a VIR return type.
    ///
    /// Uses the `VirTypeTable` to determine whether the type is void,
    /// wide, fallible, struct, or union.
    ///
    /// `struct_flat_slot_count` is the pre-computed number of flat 8-byte
    /// slots for struct types.  Callers that have entity-registry access
    /// should pass `Some(count)` for struct return types; when `None` is
    /// passed for a struct type, the result falls back to `Single` (safe
    /// for pointer-sized struct pointers, but the convention will be
    /// recomputed after monomorphization when the count is available).
    ///
    /// For generic templates (pre-monomorphization), returns `Single` as
    /// a safe default — the convention will be recomputed after
    /// monomorphization when types are concrete.
    pub fn classify(
        vir_return_type: VirTypeId,
        table: &VirTypeTable,
        struct_flat_slot_count: Option<usize>,
    ) -> Self {
        // Void / Never → no return value
        if matches!(vir_return_type, VirTypeId::VOID | VirTypeId::NEVER) {
            return Self::Void;
        }

        // Fallible → check if success type is wide
        if let VirType::Fallible { success, .. } = table.get(vir_return_type) {
            return if table.is_wide(*success) {
                Self::WideFallible
            } else {
                Self::Fallible
            };
        }

        // Wide type (i128, f128, range)
        if table.is_wide(vir_return_type) {
            return Self::Wide;
        }

        // Struct → small register return or sret depending on field count
        if table.is_struct(vir_return_type)
            && let Some(count) = struct_flat_slot_count
        {
            return if count <= MAX_SMALL_STRUCT_FIELDS {
                Self::SmallStruct { field_count: count }
            } else {
                Self::SretStruct { field_count: count }
            };
        }
        // Struct but no field count available (generic mode) — fall
        // through to Single.  Will be recomputed after monomorphization.

        // Union / Optional → pointer to stack-allocated buffer
        if table.is_union_or_optional(vir_return_type) {
            return Self::UnionPtr;
        }

        Self::Single
    }

    /// Whether this ABI uses the sret (stack return pointer) convention.
    ///
    /// When true, the Cranelift signature has a hidden first parameter
    /// pointing to the caller-allocated return buffer.
    pub fn is_sret(&self) -> bool {
        matches!(self, Self::SretStruct { .. })
    }

    /// Whether this is a struct return (small or sret).
    pub fn is_struct_return(&self) -> bool {
        matches!(self, Self::SmallStruct { .. } | Self::SretStruct { .. })
    }

    /// The flat slot count for struct returns, or `None` for non-struct ABIs.
    pub fn struct_field_count(&self) -> Option<usize> {
        match self {
            Self::SmallStruct { field_count } | Self::SretStruct { field_count } => {
                Some(*field_count)
            }
            _ => None,
        }
    }
}

/// A VIR function definition.
///
/// Each `VirFunction` is a monomorphized, fully-typed function ready for
/// codegen.  Generic functions produce one `VirFunction` per instantiation.
/// There is no `is_monomorphized` flag — post-monomorphization, all functions
/// are concrete.
#[derive(Debug, Clone)]
pub struct VirFunction {
    /// Identity of this function in the name table.
    pub id: FunctionId,
    /// Human-readable name (for diagnostics and debug output).
    pub name: String,
    /// Typed parameter list: each entry is `(param_name, concrete_type, vir_type)`.
    pub params: Vec<(Symbol, VirTypeId, VirTypeId)>,
    /// Return type (concrete after monomorphization).
    pub return_type: VirTypeId,
    /// VIR return type.
    pub vir_return_type: VirTypeId,
    /// Pre-computed return ABI convention.
    ///
    /// Determined from `vir_return_type` during VIR lowering or
    /// monomorphization.  Codegen reads this instead of re-querying
    /// type width/fallibility for signature building.
    pub return_abi: ReturnAbi,
    /// The function body.
    pub body: VirBody,
    /// For monomorphized instances, the mangled NameId used by codegen for
    /// function lookup.  `None` for non-generic (non-monomorphized) functions.
    pub mangled_name_id: Option<NameId>,
    /// For class/struct methods and static methods, the semantic MethodId.
    /// `None` for free functions.  Used by `vir_method_map` for O(1) lookup
    /// when routing method compilation through VIR.
    pub method_id: Option<MethodId>,
    /// Type parameter names for generic function templates.
    ///
    /// Empty for concrete (non-generic) functions.  For generic templates
    /// lowered with `VirType::Param` entries, this stores the ordered list
    /// of type parameter `NameId`s.  The VIR monomorphization fixpoint loop
    /// uses this to build the substitution map: `type_params[i]` maps to
    /// `CallTarget::GenericCall::type_args[i]`.
    pub type_params: Vec<NameId>,
}

/// The body of a VIR function: a linear sequence of statements with an
/// optional trailing expression that produces the body's value.
#[derive(Debug, Clone)]
pub struct VirBody {
    /// The statements in this body.
    pub stmts: Vec<VirStmt>,
    /// An optional trailing expression whose value becomes the body's result.
    pub trailing: Option<VirRef>,
}

/// A VIR test case: a named test body with its source span.
#[derive(Debug, Clone)]
pub struct VirTest {
    /// The test name from `test "name" { ... }`.
    pub name: String,
    /// The test body.
    pub body: VirBody,
    /// Source span for span-based lookup in codegen.
    pub span: Span,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classify_void() {
        let table = VirTypeTable::new();
        assert_eq!(
            ReturnAbi::classify(VirTypeId::VOID, &table, None),
            ReturnAbi::Void
        );
        assert_eq!(
            ReturnAbi::classify(VirTypeId::NEVER, &table, None),
            ReturnAbi::Void
        );
    }

    #[test]
    fn classify_single() {
        let table = VirTypeTable::new();
        assert_eq!(
            ReturnAbi::classify(VirTypeId::I64, &table, None),
            ReturnAbi::Single
        );
        assert_eq!(
            ReturnAbi::classify(VirTypeId::BOOL, &table, None),
            ReturnAbi::Single
        );
        assert_eq!(
            ReturnAbi::classify(VirTypeId::STRING, &table, None),
            ReturnAbi::Single
        );
        assert_eq!(
            ReturnAbi::classify(VirTypeId::F64, &table, None),
            ReturnAbi::Single
        );
    }

    #[test]
    fn classify_wide() {
        let table = VirTypeTable::new();
        assert_eq!(
            ReturnAbi::classify(VirTypeId::I128, &table, None),
            ReturnAbi::Wide
        );
        assert_eq!(
            ReturnAbi::classify(VirTypeId::F128, &table, None),
            ReturnAbi::Wide
        );
        assert_eq!(
            ReturnAbi::classify(VirTypeId::RANGE, &table, None),
            ReturnAbi::Wide
        );
    }

    #[test]
    fn classify_fallible() {
        let mut table = VirTypeTable::new();
        let fallible = table.intern(
            VirType::Fallible {
                success: VirTypeId::I64,
                errors: vec![VirTypeId::STRING],
            },
            None,
        );
        assert_eq!(
            ReturnAbi::classify(fallible, &table, None),
            ReturnAbi::Fallible
        );
    }

    #[test]
    fn classify_wide_fallible() {
        let mut table = VirTypeTable::new();
        let fallible = table.intern(
            VirType::Fallible {
                success: VirTypeId::I128,
                errors: vec![VirTypeId::STRING],
            },
            None,
        );
        assert_eq!(
            ReturnAbi::classify(fallible, &table, None),
            ReturnAbi::WideFallible
        );
    }

    #[test]
    fn classify_small_struct() {
        let mut table = VirTypeTable::new();
        let struct_ty = table.intern(
            VirType::Struct {
                def: vole_identity::TypeDefId::new(1),
                type_args: vec![],
            },
            None,
        );
        // With field count 2 → SmallStruct
        assert_eq!(
            ReturnAbi::classify(struct_ty, &table, Some(2)),
            ReturnAbi::SmallStruct { field_count: 2 }
        );
        // With field count 1 → SmallStruct
        assert_eq!(
            ReturnAbi::classify(struct_ty, &table, Some(1)),
            ReturnAbi::SmallStruct { field_count: 1 }
        );
    }

    #[test]
    fn classify_sret_struct() {
        let mut table = VirTypeTable::new();
        let struct_ty = table.intern(
            VirType::Struct {
                def: vole_identity::TypeDefId::new(1),
                type_args: vec![],
            },
            None,
        );
        // With field count 3 → SretStruct
        assert_eq!(
            ReturnAbi::classify(struct_ty, &table, Some(3)),
            ReturnAbi::SretStruct { field_count: 3 }
        );
    }

    #[test]
    fn classify_struct_no_field_count() {
        let mut table = VirTypeTable::new();
        let struct_ty = table.intern(
            VirType::Struct {
                def: vole_identity::TypeDefId::new(1),
                type_args: vec![],
            },
            None,
        );
        // Without field count → falls back to Single
        assert_eq!(
            ReturnAbi::classify(struct_ty, &table, None),
            ReturnAbi::Single
        );
    }

    #[test]
    fn classify_union() {
        let mut table = VirTypeTable::new();
        let union_ty = table.intern(
            VirType::Union {
                variants: vec![VirTypeId::I64, VirTypeId::STRING],
            },
            None,
        );
        assert_eq!(
            ReturnAbi::classify(union_ty, &table, None),
            ReturnAbi::UnionPtr
        );
    }

    #[test]
    fn classify_optional() {
        let mut table = VirTypeTable::new();
        let optional_ty = table.intern_optional(VirTypeId::STRING, None);
        assert_eq!(
            ReturnAbi::classify(optional_ty, &table, None),
            ReturnAbi::UnionPtr
        );
    }
}
