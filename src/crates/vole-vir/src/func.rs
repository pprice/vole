// func.rs
//
// VIR function and body representations.

use vole_identity::{FunctionId, NameId, Symbol, TypeId};

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
    /// Typed parameter list: each entry is `(param_name, concrete_type)`.
    pub params: Vec<(Symbol, TypeId)>,
    /// Return type (concrete after monomorphization).
    pub return_type: TypeId,
    /// The function body.
    pub body: VirBody,
    /// For monomorphized instances, the mangled NameId used by codegen for
    /// function lookup.  `None` for non-generic (non-monomorphized) functions.
    pub mangled_name_id: Option<NameId>,
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
