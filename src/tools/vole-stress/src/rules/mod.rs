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
        assert_eq!(registry.stmt_rules.len(), 176);
        assert_eq!(registry.expr_rules.len(), 24);
    }

    #[test]
    fn stmt_rule_names_are_unique() {
        let registry = RuleRegistry::new();
        let mut names: Vec<&str> = registry.stmt_rules.iter().map(|r| r.name()).collect();
        let original_len = names.len();
        names.sort();
        names.dedup();
        assert_eq!(names.len(), original_len, "duplicate rule names found");
    }

    #[test]
    fn expr_rule_names_are_unique() {
        let registry = RuleRegistry::new();
        let mut names: Vec<&str> = registry.expr_rules.iter().map(|r| r.name()).collect();
        let original_len = names.len();
        names.sort();
        names.dedup();
        assert_eq!(names.len(), original_len, "duplicate expr rule names found");
    }

    #[test]
    fn registry_vecs_are_accessible() {
        let registry = RuleRegistry::new();
        // Verify the public fields are usable (no accidental privacy).
        let _stmt_count = registry.stmt_rules.len();
        let _expr_count = registry.expr_rules.len();
    }
}
