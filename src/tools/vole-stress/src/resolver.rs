//! Profile resolver -- merges rule-declared param defaults with TOML profile
//! overrides into an immutable [`ResolvedParams`] map.
//!
//! Built once at startup and handed to [`Emit`](crate::emit::Emit) for the
//! lifetime of the generation run.

use std::collections::HashMap;

use crate::rule::{ExprRule, Param, ParamValue, Params, StmtRule};
use crate::rules::RuleRegistry;

// ---------------------------------------------------------------------------
// RuleOverrides (TOML-deserializable)
// ---------------------------------------------------------------------------

/// Per-rule parameter overrides loaded from a TOML `[rules]` section.
///
/// ```toml
/// [rules.stmt.match_let]
/// probability = 0.15
/// max_arms = 5
///
/// [rules.expr.method_chain]
/// probability = 0.3
/// max_chain = 4
/// ```
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
#[serde(default)]
pub struct RuleOverrides {
    /// Overrides for statement rules, keyed by rule name.
    pub stmt: HashMap<String, HashMap<String, toml::Value>>,
    /// Overrides for expression rules, keyed by rule name.
    pub expr: HashMap<String, HashMap<String, toml::Value>>,
}

// ---------------------------------------------------------------------------
// ResolvedParams
// ---------------------------------------------------------------------------

/// Map from rule name to its resolved parameter bag.
///
/// Built by [`resolve`] at startup. Rules receive a `&Params` reference
/// through [`Emit::params_for`](crate::emit::Emit::params_for).
#[derive(Debug, Clone)]
pub struct ResolvedParams {
    inner: HashMap<String, Params>,
}

impl ResolvedParams {
    /// Create an empty `ResolvedParams` (no rules registered).
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    /// Insert resolved params for a rule.
    ///
    /// Primarily used in tests to build a `ResolvedParams` by hand.
    pub fn insert(&mut self, rule_name: impl Into<String>, params: Params) {
        self.inner.insert(rule_name.into(), params);
    }

    /// Look up the resolved params for the named rule.
    ///
    /// Returns `None` if the rule has no entry.
    pub fn get(&self, rule_name: &str) -> Option<&Params> {
        self.inner.get(rule_name)
    }

    /// Return the resolved params for the named rule, or an empty bag.
    pub fn for_rule(&self, rule_name: &str) -> &Params {
        static EMPTY: std::sync::OnceLock<Params> = std::sync::OnceLock::new();
        self.inner
            .get(rule_name)
            .unwrap_or_else(|| EMPTY.get_or_init(|| Params::from_iter(std::iter::empty())))
    }

    /// Convenience: extract the `"probability"` param for the named rule.
    ///
    /// Returns `None` if the rule or the param does not exist.
    pub fn probability(&self, rule_name: &str) -> Option<f64> {
        let params = self.inner.get(rule_name)?;
        if params.contains("probability") {
            Some(params.prob("probability"))
        } else {
            None
        }
    }
}

impl Default for ResolvedParams {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Resolution
// ---------------------------------------------------------------------------

/// Build [`ResolvedParams`] by merging rule-declared defaults with optional
/// TOML overrides.
///
/// For each rule in the registry:
/// 1. Collect the rule's declared [`Param`] defaults into a [`Params`] bag.
/// 2. If `overrides` contains entries for this rule, overlay them on top.
/// 3. Store the result keyed by rule name.
///
/// Unknown rule names or param keys in the TOML are warned about but do not
/// cause errors (forward compatibility).
pub fn resolve(registry: &RuleRegistry, overrides: Option<&RuleOverrides>) -> ResolvedParams {
    let mut map = HashMap::new();

    // Resolve statement rules.
    for rule in &registry.stmt_rules {
        let name = rule.name();
        let params = resolve_one_rule(
            name,
            &rule.params(),
            overrides.and_then(|o| o.stmt.get(name)),
        );
        map.insert(name.to_string(), params);
    }

    // Resolve expression rules.
    for rule in &registry.expr_rules {
        let name = rule.name();
        let params = resolve_one_rule(
            name,
            &rule.params(),
            overrides.and_then(|o| o.expr.get(name)),
        );
        map.insert(name.to_string(), params);
    }

    // Warn about TOML rule names that don't match any registered rule.
    if let Some(ovr) = overrides {
        warn_unknown_rules(&ovr.stmt, &registry.stmt_rules, "stmt");
        warn_unknown_rules_expr(&ovr.expr, &registry.expr_rules, "expr");
    }

    ResolvedParams { inner: map }
}

/// Resolve parameters for a single rule: start from declared defaults, then
/// overlay any TOML overrides.
fn resolve_one_rule(
    rule_name: &str,
    declared: &[Param],
    toml_overrides: Option<&HashMap<String, toml::Value>>,
) -> Params {
    // Build from declared defaults.
    let mut params = Params::from_iter(declared.iter().map(|d| (d.name, d.default.clone())));

    // Overlay TOML overrides.
    let Some(overrides) = toml_overrides else {
        return params;
    };

    for (key, value) in overrides {
        // Find the declared param with this name so we can use its static key.
        let Some(decl) = declared.iter().find(|d| d.name == key.as_str()) else {
            eprintln!(
                "vole-stress: warning: unknown param '{}' for rule '{}' in profile (ignored)",
                key, rule_name
            );
            continue;
        };

        match convert_toml_value(value) {
            Some(pv) => {
                params.insert(decl.name, pv);
            }
            None => {
                eprintln!(
                    "vole-stress: warning: cannot convert TOML value for '{}.{}': {:?} (ignored)",
                    rule_name, key, value
                );
            }
        }
    }

    params
}

/// Convert a [`toml::Value`] to a [`ParamValue`].
///
/// Mapping:
/// - Float -> Probability(f64)
/// - Integer -> Count(usize)
/// - Boolean -> Flag(bool)
/// - Array of exactly 2 integers -> Range(usize, usize)
fn convert_toml_value(value: &toml::Value) -> Option<ParamValue> {
    match value {
        toml::Value::Float(f) => Some(ParamValue::Probability(*f)),
        toml::Value::Integer(i) => {
            let n = usize::try_from(*i).ok()?;
            Some(ParamValue::Count(n))
        }
        toml::Value::Boolean(b) => Some(ParamValue::Flag(*b)),
        toml::Value::Array(arr) if arr.len() == 2 => {
            let lo = arr[0].as_integer().and_then(|i| usize::try_from(i).ok())?;
            let hi = arr[1].as_integer().and_then(|i| usize::try_from(i).ok())?;
            Some(ParamValue::Range(lo, hi))
        }
        _ => None,
    }
}

/// Warn about TOML stmt rule names that don't match any registered rule.
fn warn_unknown_rules(
    overrides: &HashMap<String, HashMap<String, toml::Value>>,
    rules: &[Box<dyn StmtRule>],
    category: &str,
) {
    for name in overrides.keys() {
        if !rules.iter().any(|r| r.name() == name.as_str()) {
            eprintln!(
                "vole-stress: warning: unknown {} rule '{}' in profile overrides (ignored)",
                category, name
            );
        }
    }
}

/// Warn about TOML expr rule names that don't match any registered rule.
fn warn_unknown_rules_expr(
    overrides: &HashMap<String, HashMap<String, toml::Value>>,
    rules: &[Box<dyn ExprRule>],
    category: &str,
) {
    for name in overrides.keys() {
        if !rules.iter().any(|r| r.name() == name.as_str()) {
            eprintln!(
                "vole-stress: warning: unknown {} rule '{}' in profile overrides (ignored)",
                category, name
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rule::{Emit, ExprRule, Param, ParamValue, Params, Scope, StmtRule};

    // -- Helper rule implementations ----------------------------------------

    struct TestStmtRule;

    impl StmtRule for TestStmtRule {
        fn name(&self) -> &'static str {
            "test_stmt"
        }

        fn params(&self) -> Vec<Param> {
            vec![
                Param::prob("probability", 0.5),
                Param::count("max_arms", 3),
                Param::range("depth", 1, 5),
                Param::flag("enabled", true),
            ]
        }

        fn generate(
            &self,
            _scope: &mut Scope,
            _emit: &mut Emit,
            _params: &Params,
        ) -> Option<String> {
            None
        }
    }

    struct TestExprRule;

    impl ExprRule for TestExprRule {
        fn name(&self) -> &'static str {
            "test_expr"
        }

        fn params(&self) -> Vec<Param> {
            vec![
                Param::prob("probability", 0.3),
                Param::count("max_chain", 2),
            ]
        }

        fn generate(&self, _scope: &Scope, _emit: &mut Emit, _params: &Params) -> Option<String> {
            None
        }
    }

    fn test_registry() -> RuleRegistry {
        RuleRegistry {
            stmt_rules: vec![Box::new(TestStmtRule)],
            expr_rules: vec![Box::new(TestExprRule)],
        }
    }

    // -- ResolvedParams -----------------------------------------------------

    #[test]
    fn resolved_params_new_is_empty() {
        let rp = ResolvedParams::new();
        assert!(rp.get("anything").is_none());
    }

    #[test]
    fn resolved_params_default_is_empty() {
        let rp = ResolvedParams::default();
        assert!(rp.get("anything").is_none());
    }

    #[test]
    fn for_rule_returns_empty_for_unknown() {
        let rp = ResolvedParams::new();
        let params = rp.for_rule("nonexistent");
        assert!(!params.contains("probability"));
    }

    #[test]
    fn probability_returns_none_for_unknown_rule() {
        let rp = ResolvedParams::new();
        assert!(rp.probability("nonexistent").is_none());
    }

    // -- resolve with no overrides ------------------------------------------

    #[test]
    fn resolve_without_overrides_uses_defaults() {
        let registry = test_registry();
        let resolved = resolve(&registry, None);

        // Statement rule defaults.
        let stmt_params = resolved.get("test_stmt").expect("test_stmt should exist");
        assert!((stmt_params.prob("probability") - 0.5).abs() < f64::EPSILON);
        assert_eq!(stmt_params.count("max_arms"), 3);
        assert_eq!(stmt_params.range("depth"), (1, 5));
        assert!(stmt_params.flag("enabled"));

        // Expression rule defaults.
        let expr_params = resolved.get("test_expr").expect("test_expr should exist");
        assert!((expr_params.prob("probability") - 0.3).abs() < f64::EPSILON);
        assert_eq!(expr_params.count("max_chain"), 2);
    }

    #[test]
    fn for_rule_returns_resolved_params() {
        let registry = test_registry();
        let resolved = resolve(&registry, None);

        let params = resolved.for_rule("test_stmt");
        assert!((params.prob("probability") - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn probability_convenience() {
        let registry = test_registry();
        let resolved = resolve(&registry, None);

        assert!((resolved.probability("test_stmt").unwrap() - 0.5).abs() < f64::EPSILON);
        assert!((resolved.probability("test_expr").unwrap() - 0.3).abs() < f64::EPSILON);
    }

    // -- resolve with overrides ---------------------------------------------

    #[test]
    fn resolve_overlays_toml_overrides() {
        let registry = test_registry();
        let mut overrides = RuleOverrides::default();

        // Override probability and max_arms for the stmt rule.
        let mut stmt_ovr = HashMap::new();
        stmt_ovr.insert("probability".to_string(), toml::Value::Float(0.75));
        stmt_ovr.insert("max_arms".to_string(), toml::Value::Integer(10));
        overrides.stmt.insert("test_stmt".to_string(), stmt_ovr);

        let resolved = resolve(&registry, Some(&overrides));

        let params = resolved.get("test_stmt").unwrap();
        assert!((params.prob("probability") - 0.75).abs() < f64::EPSILON);
        assert_eq!(params.count("max_arms"), 10);
        // Non-overridden params keep defaults.
        assert_eq!(params.range("depth"), (1, 5));
        assert!(params.flag("enabled"));
    }

    #[test]
    fn resolve_overlays_expr_overrides() {
        let registry = test_registry();
        let mut overrides = RuleOverrides::default();

        let mut expr_ovr = HashMap::new();
        expr_ovr.insert("max_chain".to_string(), toml::Value::Integer(8));
        overrides.expr.insert("test_expr".to_string(), expr_ovr);

        let resolved = resolve(&registry, Some(&overrides));

        let params = resolved.get("test_expr").unwrap();
        assert_eq!(params.count("max_chain"), 8);
        // probability keeps default.
        assert!((params.prob("probability") - 0.3).abs() < f64::EPSILON);
    }

    #[test]
    fn resolve_range_from_toml_array() {
        let registry = test_registry();
        let mut overrides = RuleOverrides::default();

        let mut stmt_ovr = HashMap::new();
        stmt_ovr.insert(
            "depth".to_string(),
            toml::Value::Array(vec![toml::Value::Integer(2), toml::Value::Integer(8)]),
        );
        overrides.stmt.insert("test_stmt".to_string(), stmt_ovr);

        let resolved = resolve(&registry, Some(&overrides));

        let params = resolved.get("test_stmt").unwrap();
        assert_eq!(params.range("depth"), (2, 8));
    }

    #[test]
    fn resolve_flag_from_toml_bool() {
        let registry = test_registry();
        let mut overrides = RuleOverrides::default();

        let mut stmt_ovr = HashMap::new();
        stmt_ovr.insert("enabled".to_string(), toml::Value::Boolean(false));
        overrides.stmt.insert("test_stmt".to_string(), stmt_ovr);

        let resolved = resolve(&registry, Some(&overrides));

        let params = resolved.get("test_stmt").unwrap();
        assert!(!params.flag("enabled"));
    }

    // -- convert_toml_value -------------------------------------------------

    #[test]
    fn convert_float_to_probability() {
        let v = toml::Value::Float(0.42);
        assert_eq!(convert_toml_value(&v), Some(ParamValue::Probability(0.42)));
    }

    #[test]
    fn convert_integer_to_count() {
        let v = toml::Value::Integer(7);
        assert_eq!(convert_toml_value(&v), Some(ParamValue::Count(7)));
    }

    #[test]
    fn convert_negative_integer_returns_none() {
        let v = toml::Value::Integer(-1);
        assert_eq!(convert_toml_value(&v), None);
    }

    #[test]
    fn convert_bool_to_flag() {
        let v = toml::Value::Boolean(true);
        assert_eq!(convert_toml_value(&v), Some(ParamValue::Flag(true)));
    }

    #[test]
    fn convert_two_int_array_to_range() {
        let v = toml::Value::Array(vec![toml::Value::Integer(1), toml::Value::Integer(10)]);
        assert_eq!(convert_toml_value(&v), Some(ParamValue::Range(1, 10)));
    }

    #[test]
    fn convert_wrong_size_array_returns_none() {
        let v = toml::Value::Array(vec![toml::Value::Integer(1)]);
        assert_eq!(convert_toml_value(&v), None);
    }

    #[test]
    fn convert_three_element_array_returns_none() {
        let v = toml::Value::Array(vec![
            toml::Value::Integer(1),
            toml::Value::Integer(2),
            toml::Value::Integer(3),
        ]);
        assert_eq!(convert_toml_value(&v), None);
    }

    #[test]
    fn convert_string_returns_none() {
        let v = toml::Value::String("hello".to_string());
        assert_eq!(convert_toml_value(&v), None);
    }

    // -- RuleOverrides serde ------------------------------------------------

    #[test]
    fn rule_overrides_default_is_empty() {
        let ovr = RuleOverrides::default();
        assert!(ovr.stmt.is_empty());
        assert!(ovr.expr.is_empty());
    }

    #[test]
    fn rule_overrides_deserializes_from_toml() {
        let toml_str = r#"
[stmt.match_let]
probability = 0.15
max_arms = 5

[stmt.for_loop]
probability = 0.2
nested_probability = 0.1

[expr.method_chain]
probability = 0.3
max_chain = 4
"#;
        let ovr: RuleOverrides = toml::from_str(toml_str).expect("should parse");

        assert_eq!(ovr.stmt.len(), 2);
        assert_eq!(ovr.expr.len(), 1);

        let match_let = &ovr.stmt["match_let"];
        assert_eq!(match_let["probability"], toml::Value::Float(0.15));
        assert_eq!(match_let["max_arms"], toml::Value::Integer(5));

        let for_loop = &ovr.stmt["for_loop"];
        assert_eq!(for_loop["probability"], toml::Value::Float(0.2));
        assert_eq!(for_loop["nested_probability"], toml::Value::Float(0.1));

        let method_chain = &ovr.expr["method_chain"];
        assert_eq!(method_chain["probability"], toml::Value::Float(0.3));
        assert_eq!(method_chain["max_chain"], toml::Value::Integer(4));
    }

    #[test]
    fn rule_overrides_empty_toml_parses() {
        let ovr: RuleOverrides = toml::from_str("").expect("empty TOML should parse");
        assert!(ovr.stmt.is_empty());
        assert!(ovr.expr.is_empty());
    }

    #[test]
    fn rule_overrides_with_range_array() {
        let toml_str = r#"
[stmt.test_rule]
depth = [2, 8]
"#;
        let ovr: RuleOverrides = toml::from_str(toml_str).expect("should parse");
        let depth = &ovr.stmt["test_rule"]["depth"];
        assert!(depth.is_array());
        let arr = depth.as_array().unwrap();
        assert_eq!(arr.len(), 2);
        assert_eq!(arr[0].as_integer(), Some(2));
        assert_eq!(arr[1].as_integer(), Some(8));
    }

    // -- Params insert method -----------------------------------------------

    #[test]
    fn params_insert_overwrites_value() {
        let mut params = Params::from_iter([("x", ParamValue::Count(1))]);
        assert_eq!(params.count("x"), 1);
        params.insert("x", ParamValue::Count(99));
        assert_eq!(params.count("x"), 99);
    }

    #[test]
    fn params_insert_adds_new_key() {
        let mut params = Params::from_iter([]);
        assert!(!params.contains("y"));
        params.insert("y", ParamValue::Flag(true));
        assert!(params.flag("y"));
    }

    // -- Empty registry -----------------------------------------------------

    #[test]
    fn resolve_empty_registry_produces_empty_map() {
        let registry = RuleRegistry {
            stmt_rules: vec![],
            expr_rules: vec![],
        };
        let resolved = resolve(&registry, None);
        assert!(resolved.get("anything").is_none());
    }

    #[test]
    fn resolve_empty_registry_with_overrides_warns_but_succeeds() {
        let registry = RuleRegistry {
            stmt_rules: vec![],
            expr_rules: vec![],
        };
        let mut overrides = RuleOverrides::default();
        overrides.stmt.insert(
            "ghost_rule".to_string(),
            HashMap::from([("p".to_string(), toml::Value::Float(0.5))]),
        );
        // Should not panic; just warns on stderr.
        let resolved = resolve(&registry, Some(&overrides));
        assert!(resolved.get("ghost_rule").is_none());
    }
}
