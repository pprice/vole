// func.rs
//
// VIR function and body representations.

use vole_identity::{FunctionId, MethodId, NameId, Span, Symbol, VirTypeId};

use crate::refs::VirRef;
use crate::stmt::VirStmt;

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
