//! Expression generation configuration and helpers.
//!
//! The old grammar-based `ExprGenerator` has been replaced by the rule-based
//! dispatch system in [`crate::emit`] + [`crate::rules::expr`].  This module
//! retains [`ExprConfig`] (embedded in [`crate::stmt::StmtConfig`], itself
//! embedded in [`crate::emitter::EmitConfig`], deserialized from profile TOML
//! files) and a few shared helper functions used by rules.

use crate::symbols::{InterfaceInfo, MethodInfo, ModuleId, SymbolId, SymbolKind, SymbolTable};

/// Configuration for expression generation.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(default)]
#[allow(dead_code)]
pub struct ExprConfig {
    /// Maximum nesting depth for expressions.
    pub max_depth: usize,
    /// Probability of generating a binary expression vs simpler form.
    pub binary_probability: f64,
    /// Probability of generating a when expression.
    pub when_probability: f64,
    /// Probability of generating a match expression.
    pub match_probability: f64,
    /// Probability of generating an if expression.
    pub if_expr_probability: f64,
    /// Probability of generating a lambda expression.
    pub lambda_probability: f64,
    /// Probability of chaining another method call when the return type supports it.
    pub method_chain_probability: f64,
    /// Maximum depth of method chains (e.g., 2 means a.b().c() is allowed).
    pub max_chain_depth: usize,
    /// Probability of using `unreachable` in match/when wildcard arms.
    pub unreachable_probability: f64,
    /// Maximum number of arms in match/when expressions (excluding wildcard).
    pub max_match_arms: usize,
    /// Probability of generating a `when` or `if` expression in argument/field-value
    /// positions instead of a simple literal or variable reference.
    pub inline_expr_arg_probability: f64,
    /// Probability of generating a tuple index expression (`tupleVar[index]`).
    pub tuple_index_probability: f64,
    /// Probability of chaining multiple optional variables in a null coalescing
    /// expression.
    pub chained_coalesce_probability: f64,
    /// Probability of generating a string method call when a string-typed
    /// variable is in scope.
    pub string_method_probability: f64,
    /// Probability of generating a multi-arm when expression (3-4 arms).
    pub multi_arm_when_probability: f64,
    /// Probability of generating a match guard on the wildcard arm.
    pub match_guard_probability: f64,
    /// Probability that a generated closure captures variables from
    /// the enclosing scope.
    pub closure_capture_probability: f64,
    /// Probability of constructing a concrete class instance when an
    /// interface type is expected.
    pub interface_upcast_probability: f64,
}

impl Default for ExprConfig {
    fn default() -> Self {
        // Default values match the "full" profile so TOML files only specify overrides.
        Self {
            max_depth: 4,
            binary_probability: 0.5,
            when_probability: 0.2,
            match_probability: 0.15,
            if_expr_probability: 0.2,
            lambda_probability: 0.15,
            method_chain_probability: 0.20,
            max_chain_depth: 2,
            unreachable_probability: 0.05,
            max_match_arms: 6,
            inline_expr_arg_probability: 0.12,
            tuple_index_probability: 0.15,
            chained_coalesce_probability: 0.30,
            string_method_probability: 0.15,
            multi_arm_when_probability: 0.35,
            match_guard_probability: 0.15,
            closure_capture_probability: 0.30,
            interface_upcast_probability: 0.30,
        }
    }
}

// ---------------------------------------------------------------------------
// Shared helpers used by rules
// ---------------------------------------------------------------------------

/// Collect all methods from an interface and its parents (transitive).
pub fn get_interface_methods(
    table: &SymbolTable,
    mod_id: ModuleId,
    iface_id: SymbolId,
) -> Vec<MethodInfo> {
    let mut all_methods = Vec::new();
    let mut seen_names = std::collections::HashSet::new();
    let mut stack = vec![(mod_id, iface_id)];
    let mut visited = std::collections::HashSet::new();

    while let Some((mid, sid)) = stack.pop() {
        if !visited.insert((mid, sid)) {
            continue; // Avoid infinite loops from cycles
        }

        if let Some(symbol) = table.get_symbol(mid, sid)
            && let SymbolKind::Interface(ref info) = symbol.kind
        {
            for method in &info.methods {
                if seen_names.insert(method.name.clone()) {
                    all_methods.push(method.clone());
                }
            }

            for &(parent_mid, parent_sid) in &info.extends {
                stack.push((parent_mid, parent_sid));
            }
        }
    }

    all_methods
}

/// Get methods callable on a type parameter based on its interface constraints.
///
/// Returns all methods from all constraining interfaces (de-duplicated by name).
pub fn get_type_param_constraint_methods(
    table: &SymbolTable,
    constraints: &[(ModuleId, SymbolId)],
) -> Vec<(InterfaceInfo, MethodInfo)> {
    let mut methods = Vec::new();
    let mut seen_names = std::collections::HashSet::new();

    for &(mod_id, iface_id) in constraints {
        if let Some(symbol) = table.get_symbol(mod_id, iface_id)
            && let SymbolKind::Interface(ref iface_info) = symbol.kind
        {
            let iface_methods = get_interface_methods(table, mod_id, iface_id);
            for method in iface_methods {
                if seen_names.insert(method.name.clone()) {
                    methods.push((iface_info.clone(), method));
                }
            }
        }
    }

    methods
}
