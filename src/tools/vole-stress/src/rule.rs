//! Core rule traits and parameter system for vole-stress code generation.
//!
//! Rules are the fundamental building blocks of the generation pipeline. Each
//! rule knows how to emit one kind of statement or expression, declares the
//! parameters it needs, and can gate itself behind a precondition.
//!
//! The two traits ([`StmtRule`] and [`ExprRule`]) differ only in mutability of
//! `Scope`: statement rules may add locals (`&mut Scope`), while expression
//! rules are read-only (`&Scope`).

use std::collections::HashMap;

// ---------------------------------------------------------------------------
// Placeholder types (replaced by vol-0bex and vol-fosu)
// ---------------------------------------------------------------------------

/// Placeholder for the scope abstraction that tracks locals and type context.
///
/// Will be replaced with a real implementation in vol-0bex.
pub struct Scope;

/// Placeholder for the emit abstraction that handles sub-generation and RNG.
///
/// Will be replaced with a real implementation in vol-fosu.
pub struct Emit;

// ---------------------------------------------------------------------------
// Parameter value types
// ---------------------------------------------------------------------------

/// A single parameter value resolved from a profile.
#[derive(Debug, Clone, PartialEq)]
pub enum ParamValue {
    /// A probability in `0.0..=1.0`.
    Probability(f64),
    /// An inclusive range `(min, max)` for randomised counts.
    Range(usize, usize),
    /// A fixed count.
    Count(usize),
    /// A boolean toggle.
    Flag(bool),
}

/// Declaration of a parameter a rule expects, together with its default value.
#[derive(Debug, Clone)]
pub struct Param {
    /// Machine-readable name used as the lookup key in [`Params`].
    pub name: &'static str,
    /// Default value used when the profile does not override this parameter.
    pub default: ParamValue,
}

impl Param {
    /// Create a probability parameter with the given default (0.0..=1.0).
    pub fn prob(name: &'static str, default: f64) -> Self {
        Self {
            name,
            default: ParamValue::Probability(default),
        }
    }

    /// Create a range parameter with inclusive `(min, max)` bounds.
    pub fn range(name: &'static str, min: usize, max: usize) -> Self {
        Self {
            name,
            default: ParamValue::Range(min, max),
        }
    }

    /// Create a fixed-count parameter.
    pub fn count(name: &'static str, default: usize) -> Self {
        Self {
            name,
            default: ParamValue::Count(default),
        }
    }

    /// Create a boolean flag parameter.
    pub fn flag(name: &'static str, default: bool) -> Self {
        Self {
            name,
            default: ParamValue::Flag(default),
        }
    }
}

// ---------------------------------------------------------------------------
// Resolved parameter bag
// ---------------------------------------------------------------------------

/// Resolved parameters for a single rule instance.
///
/// Built by the profile resolver at startup (vol-e2qj). Rules receive a
/// `&Params` and pull values out by name through typed accessors.
#[derive(Debug, Clone)]
pub struct Params {
    values: HashMap<&'static str, ParamValue>,
}

impl Params {
    /// Create a `Params` bag from an iterator of `(name, value)` pairs.
    pub fn from_iter(iter: impl IntoIterator<Item = (&'static str, ParamValue)>) -> Self {
        Self {
            values: iter.into_iter().collect(),
        }
    }

    /// Look up a probability parameter.
    ///
    /// # Panics
    ///
    /// Panics if the key is missing or holds a non-`Probability` variant.
    pub fn prob(&self, key: &str) -> f64 {
        match self.values.get(key) {
            Some(ParamValue::Probability(p)) => *p,
            Some(other) => panic!("param '{key}' is {other:?}, expected Probability"),
            None => panic!("param '{key}' not found"),
        }
    }

    /// Look up a range parameter, returning `(min, max)`.
    ///
    /// # Panics
    ///
    /// Panics if the key is missing or holds a non-`Range` variant.
    pub fn range(&self, key: &str) -> (usize, usize) {
        match self.values.get(key) {
            Some(ParamValue::Range(lo, hi)) => (*lo, *hi),
            Some(other) => panic!("param '{key}' is {other:?}, expected Range"),
            None => panic!("param '{key}' not found"),
        }
    }

    /// Look up a count parameter.
    ///
    /// # Panics
    ///
    /// Panics if the key is missing or holds a non-`Count` variant.
    pub fn count(&self, key: &str) -> usize {
        match self.values.get(key) {
            Some(ParamValue::Count(n)) => *n,
            Some(other) => panic!("param '{key}' is {other:?}, expected Count"),
            None => panic!("param '{key}' not found"),
        }
    }

    /// Look up a boolean flag parameter.
    ///
    /// # Panics
    ///
    /// Panics if the key is missing or holds a non-`Flag` variant.
    pub fn flag(&self, key: &str) -> bool {
        match self.values.get(key) {
            Some(ParamValue::Flag(b)) => *b,
            Some(other) => panic!("param '{key}' is {other:?}, expected Flag"),
            None => panic!("param '{key}' not found"),
        }
    }
}

// ---------------------------------------------------------------------------
// Rule traits
// ---------------------------------------------------------------------------

/// A rule that generates a single kind of statement.
///
/// Statement rules receive `&mut Scope` because they may add local variables
/// (e.g., `let` bindings, loop variables).
pub trait StmtRule: Send + Sync {
    /// Human-readable name used in profiles and diagnostics.
    fn name(&self) -> &'static str;

    /// Declare the parameters this rule reads from the profile.
    fn params(&self) -> Vec<Param>;

    /// Check whether this rule can fire given the current scope and params.
    ///
    /// The default implementation always returns `true`.
    fn precondition(&self, _scope: &Scope, _params: &Params) -> bool {
        true
    }

    /// Generate a statement, returning its Vole source text.
    ///
    /// Returns `None` if the rule cannot produce output in the current context
    /// (e.g., no variables of the required type are in scope).
    fn generate(&self, scope: &mut Scope, emit: &mut Emit, params: &Params) -> Option<String>;
}

/// A rule that generates a single kind of expression.
///
/// Expression rules receive `&Scope` (read-only) because expressions do not
/// introduce new bindings.
pub trait ExprRule: Send + Sync {
    /// Human-readable name used in profiles and diagnostics.
    fn name(&self) -> &'static str;

    /// Declare the parameters this rule reads from the profile.
    fn params(&self) -> Vec<Param>;

    /// Check whether this rule can fire given the current scope and params.
    ///
    /// The default implementation always returns `true`.
    fn precondition(&self, _scope: &Scope, _params: &Params) -> bool {
        true
    }

    /// Generate an expression, returning its Vole source text.
    ///
    /// Returns `None` if the rule cannot produce output in the current context
    /// (e.g., no variables of the required type are in scope).
    fn generate(&self, scope: &Scope, emit: &mut Emit, params: &Params) -> Option<String>;
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- Param constructors -------------------------------------------------

    #[test]
    fn param_prob_constructor() {
        let p = Param::prob("fire_rate", 0.75);
        assert_eq!(p.name, "fire_rate");
        assert_eq!(p.default, ParamValue::Probability(0.75));
    }

    #[test]
    fn param_range_constructor() {
        let p = Param::range("arms", 2, 5);
        assert_eq!(p.name, "arms");
        assert_eq!(p.default, ParamValue::Range(2, 5));
    }

    #[test]
    fn param_count_constructor() {
        let p = Param::count("depth", 3);
        assert_eq!(p.name, "depth");
        assert_eq!(p.default, ParamValue::Count(3));
    }

    #[test]
    fn param_flag_constructor() {
        let p = Param::flag("enabled", true);
        assert_eq!(p.name, "enabled");
        assert_eq!(p.default, ParamValue::Flag(true));
    }

    // -- Params accessors ---------------------------------------------------

    fn sample_params() -> Params {
        Params::from_iter([
            ("fire_rate", ParamValue::Probability(0.5)),
            ("arms", ParamValue::Range(1, 4)),
            ("depth", ParamValue::Count(3)),
            ("enabled", ParamValue::Flag(true)),
        ])
    }

    #[test]
    fn params_prob_accessor() {
        let p = sample_params();
        assert!((p.prob("fire_rate") - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn params_range_accessor() {
        let p = sample_params();
        assert_eq!(p.range("arms"), (1, 4));
    }

    #[test]
    fn params_count_accessor() {
        let p = sample_params();
        assert_eq!(p.count("depth"), 3);
    }

    #[test]
    fn params_flag_accessor() {
        let p = sample_params();
        assert!(p.flag("enabled"));
    }

    #[test]
    #[should_panic(expected = "not found")]
    fn params_missing_key_panics() {
        let p = sample_params();
        p.prob("nonexistent");
    }

    #[test]
    #[should_panic(expected = "expected Probability")]
    fn params_wrong_variant_panics() {
        let p = sample_params();
        p.prob("depth"); // depth is Count, not Probability
    }

    // -- Trait object construction ------------------------------------------

    /// Minimal statement rule used only for trait-object tests.
    struct DummyStmtRule;

    impl StmtRule for DummyStmtRule {
        fn name(&self) -> &'static str {
            "dummy_stmt"
        }

        fn params(&self) -> Vec<Param> {
            vec![Param::prob("p", 0.5)]
        }

        fn generate(
            &self,
            _scope: &mut Scope,
            _emit: &mut Emit,
            _params: &Params,
        ) -> Option<String> {
            Some("let x = 1".to_string())
        }
    }

    /// Minimal expression rule used only for trait-object tests.
    struct DummyExprRule;

    impl ExprRule for DummyExprRule {
        fn name(&self) -> &'static str {
            "dummy_expr"
        }

        fn params(&self) -> Vec<Param> {
            vec![Param::count("n", 1)]
        }

        fn generate(&self, _scope: &Scope, _emit: &mut Emit, _params: &Params) -> Option<String> {
            Some("42".to_string())
        }
    }

    #[test]
    fn stmt_rule_as_trait_object() {
        let rule: Box<dyn StmtRule> = Box::new(DummyStmtRule);
        assert_eq!(rule.name(), "dummy_stmt");
        assert_eq!(rule.params().len(), 1);
        assert_eq!(rule.params()[0].name, "p");

        // Default precondition returns true.
        let params = Params::from_iter([("p", ParamValue::Probability(0.5))]);
        assert!(rule.precondition(&Scope, &params));

        let result = rule.generate(&mut Scope, &mut Emit, &params);
        assert_eq!(result.as_deref(), Some("let x = 1"));
    }

    #[test]
    fn expr_rule_as_trait_object() {
        let rule: Box<dyn ExprRule> = Box::new(DummyExprRule);
        assert_eq!(rule.name(), "dummy_expr");
        assert_eq!(rule.params().len(), 1);
        assert_eq!(rule.params()[0].name, "n");

        // Default precondition returns true.
        let params = Params::from_iter([("n", ParamValue::Count(1))]);
        assert!(rule.precondition(&Scope, &params));

        let result = rule.generate(&Scope, &mut Emit, &params);
        assert_eq!(result.as_deref(), Some("42"));
    }

    #[test]
    fn precondition_can_be_overridden() {
        struct GatedRule;

        impl StmtRule for GatedRule {
            fn name(&self) -> &'static str {
                "gated"
            }

            fn params(&self) -> Vec<Param> {
                vec![Param::flag("active", false)]
            }

            fn precondition(&self, _scope: &Scope, params: &Params) -> bool {
                params.flag("active")
            }

            fn generate(
                &self,
                _scope: &mut Scope,
                _emit: &mut Emit,
                _params: &Params,
            ) -> Option<String> {
                Some("gated output".to_string())
            }
        }

        let rule: Box<dyn StmtRule> = Box::new(GatedRule);

        let off = Params::from_iter([("active", ParamValue::Flag(false))]);
        assert!(!rule.precondition(&Scope, &off));

        let on = Params::from_iter([("active", ParamValue::Flag(true))]);
        assert!(rule.precondition(&Scope, &on));
    }

    #[test]
    fn generate_can_return_none() {
        struct EmptyRule;

        impl ExprRule for EmptyRule {
            fn name(&self) -> &'static str {
                "empty"
            }

            fn params(&self) -> Vec<Param> {
                vec![]
            }

            fn generate(
                &self,
                _scope: &Scope,
                _emit: &mut Emit,
                _params: &Params,
            ) -> Option<String> {
                None
            }
        }

        let rule: Box<dyn ExprRule> = Box::new(EmptyRule);
        let params = Params::from_iter([]);
        assert!(rule.generate(&Scope, &mut Emit, &params).is_none());
    }

    // -- Send + Sync --------------------------------------------------------

    #[test]
    fn stmt_rule_is_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<DummyStmtRule>();
    }

    #[test]
    fn expr_rule_is_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<DummyExprRule>();
    }

    // -- ParamValue equality ------------------------------------------------

    #[test]
    fn param_value_equality() {
        assert_eq!(ParamValue::Probability(0.5), ParamValue::Probability(0.5));
        assert_ne!(ParamValue::Probability(0.5), ParamValue::Probability(0.6));
        assert_eq!(ParamValue::Range(1, 5), ParamValue::Range(1, 5));
        assert_ne!(ParamValue::Range(1, 5), ParamValue::Range(2, 5));
        assert_eq!(ParamValue::Count(3), ParamValue::Count(3));
        assert_ne!(ParamValue::Count(3), ParamValue::Count(4));
        assert_eq!(ParamValue::Flag(true), ParamValue::Flag(true));
        assert_ne!(ParamValue::Flag(true), ParamValue::Flag(false));
    }

    #[test]
    fn params_from_defaults() {
        let declarations = vec![
            Param::prob("p", 0.3),
            Param::range("r", 1, 10),
            Param::count("c", 5),
            Param::flag("f", false),
        ];

        let params = Params::from_iter(declarations.iter().map(|d| (d.name, d.default.clone())));

        assert!((params.prob("p") - 0.3).abs() < f64::EPSILON);
        assert_eq!(params.range("r"), (1, 10));
        assert_eq!(params.count("c"), 5);
        assert!(!params.flag("f"));
    }
}
