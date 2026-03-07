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

/// Pre-computed return ABI for a VIR function's signature.
///
/// Determined by the function's VIR return type during lowering or
/// monomorphization.  Codegen reads this hint to build Cranelift
/// signatures (register counts) without re-inspecting type properties.
///
/// Distinct from `VirStmt::Return`'s `ReturnConvention`, which describes
/// value-level preparation (boxing, wrapping).  `ReturnAbi` describes
/// the ABI-level register layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ReturnAbi {
    /// No return value (void, never).
    Void,
    /// Single register return (most types).
    Single,
    /// Two-register return for wide types (i128, f128, range).
    Wide,
    /// Fallible return with non-wide success: `(tag, payload)`.
    Fallible,
    /// Fallible return with wide success (i128): `(tag, low, high)`.
    WideFallible,
}

impl ReturnAbi {
    /// Classify the return ABI from a VIR return type.
    ///
    /// Uses the `VirTypeTable` to determine whether the type is void,
    /// wide, or fallible.  For generic templates (pre-monomorphization),
    /// returns `Single` as a safe default — the convention will be
    /// recomputed after monomorphization when types are concrete.
    pub fn classify(vir_return_type: VirTypeId, table: &VirTypeTable) -> Self {
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

        Self::Single
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
            ReturnAbi::classify(VirTypeId::VOID, &table),
            ReturnAbi::Void
        );
        assert_eq!(
            ReturnAbi::classify(VirTypeId::NEVER, &table),
            ReturnAbi::Void
        );
    }

    #[test]
    fn classify_single() {
        let table = VirTypeTable::new();
        assert_eq!(
            ReturnAbi::classify(VirTypeId::I64, &table),
            ReturnAbi::Single
        );
        assert_eq!(
            ReturnAbi::classify(VirTypeId::BOOL, &table),
            ReturnAbi::Single
        );
        assert_eq!(
            ReturnAbi::classify(VirTypeId::STRING, &table),
            ReturnAbi::Single
        );
        assert_eq!(
            ReturnAbi::classify(VirTypeId::F64, &table),
            ReturnAbi::Single
        );
    }

    #[test]
    fn classify_wide() {
        let table = VirTypeTable::new();
        assert_eq!(
            ReturnAbi::classify(VirTypeId::I128, &table),
            ReturnAbi::Wide
        );
        assert_eq!(
            ReturnAbi::classify(VirTypeId::F128, &table),
            ReturnAbi::Wide
        );
        assert_eq!(
            ReturnAbi::classify(VirTypeId::RANGE, &table),
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
        assert_eq!(ReturnAbi::classify(fallible, &table), ReturnAbi::Fallible);
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
            ReturnAbi::classify(fallible, &table),
            ReturnAbi::WideFallible
        );
    }
}
