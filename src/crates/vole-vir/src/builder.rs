// builder.rs
//
// VirBuilder: incremental construction of VIR trees.

use crate::func::VirBody;
use crate::stmt::VirStmt;

/// Builder for constructing VIR function bodies statement by statement.
///
/// This is the primary API that sema (or a future lowering pass) will use
/// to emit VIR.  For now it is a minimal stub.
#[derive(Debug, Clone)]
pub struct VirBuilder {
    stmts: Vec<VirStmt>,
}

impl VirBuilder {
    /// Create a new, empty builder.
    pub fn new() -> Self {
        Self { stmts: Vec::new() }
    }

    /// Append a statement to the body under construction.
    pub fn push(&mut self, stmt: VirStmt) {
        self.stmts.push(stmt);
    }

    /// Consume the builder, producing a finished `VirBody`.
    pub fn build(self) -> VirBody {
        VirBody { stmts: self.stmts }
    }
}

impl Default for VirBuilder {
    fn default() -> Self {
        Self::new()
    }
}
