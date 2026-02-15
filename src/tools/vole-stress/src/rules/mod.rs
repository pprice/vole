//! Rule registry -- collects all rule implementations and provides them
//! to Emit for dispatch.
//!
//! [`RuleRegistry`] is constructed once at startup and owns every registered
//! [`StmtRule`] and [`ExprRule`].  The `stmt` and `expr` sub-modules each
//! expose an `all()` function that serves as the single source of truth for
//! which rules exist.

mod expr;
mod stmt;

use crate::rule::{ExprRule, StmtRule};

/// Central collection of all statement and expression rules.
///
/// Constructed once at startup via [`RuleRegistry::new`] and handed to the
/// emit phase for dispatch.
pub struct RuleRegistry {
    pub stmt_rules: Vec<Box<dyn StmtRule>>,
    pub expr_rules: Vec<Box<dyn ExprRule>>,
}

impl RuleRegistry {
    /// Build the registry by collecting every registered rule.
    pub fn new() -> Self {
        Self {
            stmt_rules: stmt::all(),
            expr_rules: expr::all(),
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn registry_construction_succeeds() {
        let registry = RuleRegistry::new();
        // Initially empty -- rules are added during migration tickets.
        assert!(registry.stmt_rules.is_empty());
        assert!(registry.expr_rules.is_empty());
    }

    #[test]
    fn registry_vecs_are_accessible() {
        let registry = RuleRegistry::new();
        // Verify the public fields are usable (no accidental privacy).
        let _stmt_count = registry.stmt_rules.len();
        let _expr_count = registry.expr_rules.len();
    }
}
