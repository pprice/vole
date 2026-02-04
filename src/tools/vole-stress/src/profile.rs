//! Generation profiles for vole-stress.
//!
//! Profiles define presets for the planner configuration that produce
//! codebases of varying complexity and size.

use crate::emitter::EmitConfig;
use crate::expr::ExprConfig;
use crate::planner::PlanConfig;
use crate::stmt::StmtConfig;

/// A generation profile combining plan and emit configurations.
#[derive(Debug, Clone)]
pub struct Profile {
    /// Configuration for the planning phase.
    pub plan: PlanConfig,
    /// Configuration for the emit phase.
    pub emit: EmitConfig,
}

/// Error type for profile lookup failures.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnknownProfileError(pub String);

impl std::fmt::Display for UnknownProfileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "unknown profile '{}', available profiles: {}",
            self.0,
            available_profiles().join(", ")
        )
    }
}

impl std::error::Error for UnknownProfileError {}

/// Returns a list of available profile names.
pub fn available_profiles() -> Vec<&'static str> {
    vec!["minimal", "full", "deep-nesting"]
}

/// Get a profile by name.
///
/// Returns `Err` if the profile name is not recognized.
pub fn get_profile(name: &str) -> Result<Profile, UnknownProfileError> {
    match name {
        "minimal" => Ok(minimal_profile()),
        "full" => Ok(full_profile()),
        "deep-nesting" => Ok(deep_nesting_profile()),
        _ => Err(UnknownProfileError(name.to_string())),
    }
}

/// Minimal profile - small but valid codebase for quick sanity checks.
///
/// Target characteristics:
/// - 1 module + main.vole
/// - 2-3 simple functions
/// - Basic types only (i64, string, bool)
/// - No generics, no interfaces
/// - Simple expressions (arithmetic, comparisons, calls)
/// - Target: <100 lines total, compiles in <100ms
fn minimal_profile() -> Profile {
    let plan = PlanConfig {
        // Single layer with 1 module (plus implicit main)
        layers: 1,
        modules_per_layer: 1,
        // No classes, interfaces, or errors
        classes_per_module: (0, 0),
        interfaces_per_module: (0, 0),
        errors_per_module: (0, 0),
        // 2-3 simple functions
        functions_per_module: (2, 3),
        // 1 global constant
        globals_per_module: (1, 1),
        // Function parameters: 0-2
        params_per_function: (0, 2),
        // No generics
        type_params_per_class: (0, 0),
        type_params_per_interface: (0, 0),
        type_params_per_function: (0, 0),
        constraints_per_type_param: (0, 0),
        // No interface relationships
        interface_extends_probability: 0.0,
        implement_blocks_per_module: (0, 0),
        // No cross-layer imports (only one layer anyway)
        cross_layer_import_probability: 0.0,
        enable_diamond_dependencies: false,
        // These won't be used since we have no classes
        fields_per_class: (0, 0),
        methods_per_class: (0, 0),
        methods_per_interface: (0, 0),
        fields_per_error: (0, 0),
    };

    let emit = EmitConfig {
        stmt_config: StmtConfig {
            expr_config: ExprConfig {
                // Shallow expression depth for simple expressions
                max_depth: 2,
                // Moderate binary expressions
                binary_probability: 0.3,
                // No complex expressions
                when_probability: 0.0,
                match_probability: 0.0,
                if_expr_probability: 0.0,
                lambda_probability: 0.0,
            },
            // Shallow statement depth
            max_depth: 1,
            // Few statements per block
            statements_per_block: (1, 2),
            // No control flow statements (simple arithmetic/comparisons only)
            if_probability: 0.0,
            while_probability: 0.0,
            for_probability: 0.0,
        },
    };

    Profile { plan, emit }
}

/// Full profile - comprehensive codebase with all language features.
///
/// This is the default profile for stress testing the compiler with
/// a realistic, complex codebase.
fn full_profile() -> Profile {
    Profile {
        plan: PlanConfig::default(),
        emit: EmitConfig::default(),
    }
}

/// Deep-nesting profile - stress parser stack and AST depth.
///
/// This profile generates code with extreme nesting to test:
/// - Parser recursion limits and stack usage
/// - AST traversal efficiency in all compiler phases
/// - Memory usage with deeply nested structures
///
/// Target: expressions and statements nested 100-500 levels deep.
fn deep_nesting_profile() -> Profile {
    let plan = PlanConfig {
        // Small module structure - focus is on depth, not breadth
        layers: 1,
        modules_per_layer: 1,
        // Few declarations, but each will have deeply nested bodies
        classes_per_module: (0, 1),
        interfaces_per_module: (0, 0),
        errors_per_module: (0, 0),
        functions_per_module: (3, 5),
        globals_per_module: (1, 2),
        // Function parameters to provide variables for nested expressions
        params_per_function: (2, 4),
        // No generics - keep focus on nesting
        type_params_per_class: (0, 0),
        type_params_per_interface: (0, 0),
        type_params_per_function: (0, 0),
        constraints_per_type_param: (0, 0),
        // No interface relationships
        interface_extends_probability: 0.0,
        implement_blocks_per_module: (0, 0),
        // Single module, no imports
        cross_layer_import_probability: 0.0,
        enable_diamond_dependencies: false,
        // Minimal class structure
        fields_per_class: (1, 2),
        methods_per_class: (1, 2),
        methods_per_interface: (0, 0),
        fields_per_error: (0, 0),
    };

    let emit = EmitConfig {
        stmt_config: StmtConfig {
            expr_config: ExprConfig {
                // Very deep expression nesting (100-500 levels target)
                // Each level can spawn sub-expressions, so effective depth compounds
                max_depth: 150,
                // High probability of binary expressions for deep a + (b + (c + ...))
                binary_probability: 0.8,
                // when expressions add depth with multiple arms
                when_probability: 0.3,
                // match expressions for deep pattern matching
                match_probability: 0.2,
                // if expressions for deep conditional chains
                if_expr_probability: 0.3,
                // lambda expressions for deep captures
                lambda_probability: 0.15,
            },
            // Deep statement nesting for { { { ... } } }
            max_depth: 100,
            // More statements per block to compound nesting
            statements_per_block: (2, 4),
            // High probability of control flow for deep if-else chains
            if_probability: 0.6,
            // while loops add block depth
            while_probability: 0.2,
            // for loops add block depth
            for_probability: 0.2,
        },
    };

    Profile { plan, emit }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn minimal_profile_exists() {
        let profile = get_profile("minimal").expect("minimal profile should exist");
        // Verify minimal characteristics
        assert_eq!(profile.plan.layers, 1);
        assert_eq!(profile.plan.modules_per_layer, 1);
        assert_eq!(profile.plan.classes_per_module, (0, 0));
        assert_eq!(profile.plan.interfaces_per_module, (0, 0));
    }

    #[test]
    fn full_profile_exists() {
        let profile = get_profile("full").expect("full profile should exist");
        // Full should have multiple layers
        assert!(profile.plan.layers >= 2);
    }

    #[test]
    fn unknown_profile_returns_error() {
        let result = get_profile("nonexistent");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(err.to_string().contains("nonexistent"));
        assert!(err.to_string().contains("minimal"));
        assert!(err.to_string().contains("full"));
    }

    #[test]
    fn available_profiles_includes_minimal() {
        let profiles = available_profiles();
        assert!(profiles.contains(&"minimal"));
        assert!(profiles.contains(&"full"));
        assert!(profiles.contains(&"deep-nesting"));
    }

    #[test]
    fn deep_nesting_profile_exists() {
        let profile = get_profile("deep-nesting").expect("deep-nesting profile should exist");
        // Verify deep nesting characteristics
        assert_eq!(profile.plan.layers, 1);
        assert_eq!(profile.plan.modules_per_layer, 1);
        // Deep expression nesting
        assert!(
            profile.emit.stmt_config.expr_config.max_depth >= 100,
            "expression max_depth should be >= 100 for deep nesting"
        );
        // Deep statement nesting
        assert!(
            profile.emit.stmt_config.max_depth >= 50,
            "statement max_depth should be >= 50 for deep nesting"
        );
        // High binary probability for deep a + (b + (c + ...))
        assert!(
            profile.emit.stmt_config.expr_config.binary_probability >= 0.5,
            "binary_probability should be high for deep nesting"
        );
        // High if probability for deep if-else chains
        assert!(
            profile.emit.stmt_config.if_probability >= 0.5,
            "if_probability should be high for deep nesting"
        );
    }

    #[test]
    fn unknown_profile_error_includes_deep_nesting() {
        let result = get_profile("nonexistent");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.to_string().contains("deep-nesting"),
            "error message should mention deep-nesting profile"
        );
    }
}
