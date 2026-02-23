// refs.rs
//
// VirRef: the standard way to reference sub-expressions in VIR trees.

use crate::expr::VirExpr;

/// A boxed reference to a VIR expression.
///
/// Using `Box<VirExpr>` (rather than arena indices) keeps the tree
/// self-contained and trivially serializable. If profiling shows allocation
/// pressure we can swap to an arena later without changing the public API.
pub type VirRef = Box<VirExpr>;
