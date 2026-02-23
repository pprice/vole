// func.rs
//
// VIR function and body representations.

use vole_identity::{FunctionId, TypeId};

use crate::stmt::VirStmt;

/// A VIR function definition.
///
/// Each `VirFunction` is a monomorphized, fully-typed function ready for
/// codegen.  Generic functions produce one `VirFunction` per instantiation.
#[derive(Debug, Clone)]
pub struct VirFunction {
    /// Identity of this function in the name table.
    pub id: FunctionId,
    /// Return type (concrete after monomorphization).
    pub return_type: TypeId,
    /// The function body.
    pub body: VirBody,
}

/// The body of a VIR function: a linear sequence of statements.
#[derive(Debug, Clone)]
pub struct VirBody {
    pub stmts: Vec<VirStmt>,
}
