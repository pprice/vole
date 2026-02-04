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
    vec![
        "minimal",
        "full",
        "deep-nesting",
        "wide-types",
        "many-modules",
    ]
}

/// Get a profile by name.
///
/// Returns `Err` if the profile name is not recognized.
pub fn get_profile(name: &str) -> Result<Profile, UnknownProfileError> {
    match name {
        "minimal" => Ok(minimal_profile()),
        "full" => Ok(full_profile()),
        "deep-nesting" => Ok(deep_nesting_profile()),
        "wide-types" => Ok(wide_types_profile()),
        "many-modules" => Ok(many_modules_profile()),
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

/// Wide-types profile - stress type system with breadth.
///
/// This profile generates code with extreme type widths to test:
/// - Functions with many parameters (20-50 params)
/// - Generics with many type parameters (5-10 type params)
/// - Types with many fields (20-50 fields)
/// - Interfaces with many methods
///
/// Target: stress signature processing, type checking width,
/// memory for type representations.
fn wide_types_profile() -> Profile {
    let plan = PlanConfig {
        // Moderate module structure - focus is on wide types, not modules
        layers: 2,
        modules_per_layer: 3,
        // Several classes with wide field counts
        classes_per_module: (2, 4),
        // Several interfaces with many methods
        interfaces_per_module: (2, 3),
        // A few errors for completeness
        errors_per_module: (1, 2),
        // Functions with extreme parameter counts
        functions_per_module: (3, 5),
        // A few globals
        globals_per_module: (1, 2),
        // Wide fields: 20-50 fields per class
        fields_per_class: (20, 50),
        // Many methods per class: 10-20
        methods_per_class: (10, 20),
        // Many methods per interface: 10-20
        methods_per_interface: (10, 20),
        // Wide error fields: 5-15
        fields_per_error: (5, 15),
        // Wide parameter counts: 20-50 params per function
        params_per_function: (20, 50),
        // Many type parameters for generics: 5-10
        type_params_per_class: (5, 10),
        type_params_per_interface: (3, 6),
        type_params_per_function: (5, 10),
        // Multiple constraints per type param
        constraints_per_type_param: (1, 3),
        // Some interface inheritance
        interface_extends_probability: 0.3,
        // Some implement blocks
        implement_blocks_per_module: (1, 2),
        // Standard import behavior
        cross_layer_import_probability: 0.2,
        enable_diamond_dependencies: true,
    };

    let emit = EmitConfig {
        stmt_config: StmtConfig {
            expr_config: ExprConfig {
                // Moderate expression depth - focus on width not depth
                max_depth: 3,
                // Standard binary expression probability
                binary_probability: 0.3,
                // Some complex expressions but not the focus
                when_probability: 0.1,
                match_probability: 0.1,
                if_expr_probability: 0.1,
                lambda_probability: 0.05,
            },
            // Moderate statement depth
            max_depth: 2,
            // Standard statements per block
            statements_per_block: (1, 3),
            // Standard control flow probabilities
            if_probability: 0.2,
            while_probability: 0.1,
            for_probability: 0.1,
        },
    };

    Profile { plan, emit }
}

/// Many-modules profile - stress import resolution and module caching.
///
/// This profile generates a large module graph to test:
/// - 5+ layers with 10+ modules per layer (50+ total modules)
/// - Heavy cross-layer imports for import resolution stress
/// - Diamond dependencies where A imports B,C; B,C both import D
/// - Repeated imports of the same module from different files
/// - Re-exports and transitive dependencies
///
/// Target: stress module loader, test caching effectiveness,
/// import resolution performance, and module graph handling.
fn many_modules_profile() -> Profile {
    let plan = PlanConfig {
        // Deep module hierarchy: 5 layers with 10 modules each = 50 modules
        layers: 5,
        modules_per_layer: 10,
        // Light declarations per module - focus is on module graph, not content
        classes_per_module: (1, 2),
        interfaces_per_module: (0, 1),
        errors_per_module: (0, 1),
        functions_per_module: (2, 4),
        globals_per_module: (1, 2),
        // Simple class/interface structure
        fields_per_class: (1, 3),
        methods_per_class: (1, 2),
        methods_per_interface: (1, 2),
        fields_per_error: (0, 1),
        // Simple function signatures
        params_per_function: (0, 2),
        // No generics - keep focus on module loading, not type complexity
        type_params_per_class: (0, 0),
        type_params_per_interface: (0, 0),
        type_params_per_function: (0, 0),
        constraints_per_type_param: (0, 0),
        // Some interface relationships for realistic module usage
        interface_extends_probability: 0.2,
        implement_blocks_per_module: (0, 1),
        // High cross-layer import probability for heavy import graph
        cross_layer_import_probability: 0.7,
        // Enable diamond dependencies (A imports B,C; B,C both import D)
        enable_diamond_dependencies: true,
    };

    let emit = EmitConfig {
        stmt_config: StmtConfig {
            expr_config: ExprConfig {
                // Shallow expression depth - focus on modules, not code complexity
                max_depth: 2,
                // Moderate expression complexity
                binary_probability: 0.2,
                // Minimal complex expressions
                when_probability: 0.0,
                match_probability: 0.0,
                if_expr_probability: 0.0,
                lambda_probability: 0.0,
            },
            // Shallow statement depth
            max_depth: 1,
            // Few statements per block
            statements_per_block: (1, 2),
            // Minimal control flow
            if_probability: 0.1,
            while_probability: 0.0,
            for_probability: 0.0,
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

    #[test]
    fn wide_types_profile_exists() {
        let profile = get_profile("wide-types").expect("wide-types profile should exist");
        // Verify wide-types characteristics: focus on breadth, not depth

        // Wide parameter counts (20-50)
        assert!(
            profile.plan.params_per_function.0 >= 20,
            "params_per_function min should be >= 20 for wide types"
        );
        assert!(
            profile.plan.params_per_function.1 >= 50,
            "params_per_function max should be >= 50 for wide types"
        );

        // Many type parameters (5-10)
        assert!(
            profile.plan.type_params_per_class.0 >= 5,
            "type_params_per_class min should be >= 5 for wide types"
        );
        assert!(
            profile.plan.type_params_per_function.0 >= 5,
            "type_params_per_function min should be >= 5 for wide types"
        );

        // Wide field counts (20-50)
        assert!(
            profile.plan.fields_per_class.0 >= 20,
            "fields_per_class min should be >= 20 for wide types"
        );
        assert!(
            profile.plan.fields_per_class.1 >= 50,
            "fields_per_class max should be >= 50 for wide types"
        );

        // Many methods per interface (10-20)
        assert!(
            profile.plan.methods_per_interface.0 >= 10,
            "methods_per_interface min should be >= 10 for wide types"
        );

        // Moderate depth (not the focus)
        assert!(
            profile.emit.stmt_config.max_depth <= 5,
            "statement max_depth should be moderate for wide types"
        );
        assert!(
            profile.emit.stmt_config.expr_config.max_depth <= 5,
            "expression max_depth should be moderate for wide types"
        );
    }

    #[test]
    fn available_profiles_includes_wide_types() {
        let profiles = available_profiles();
        assert!(
            profiles.contains(&"wide-types"),
            "available_profiles should include wide-types"
        );
    }

    #[test]
    fn unknown_profile_error_includes_wide_types() {
        let result = get_profile("nonexistent");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.to_string().contains("wide-types"),
            "error message should mention wide-types profile"
        );
    }

    #[test]
    fn many_modules_profile_exists() {
        let profile = get_profile("many-modules").expect("many-modules profile should exist");
        // Verify many-modules characteristics: focus on module graph breadth

        // 5+ layers
        assert!(
            profile.plan.layers >= 5,
            "layers should be >= 5 for many-modules"
        );

        // 10+ modules per layer
        assert!(
            profile.plan.modules_per_layer >= 10,
            "modules_per_layer should be >= 10 for many-modules"
        );

        // High cross-layer import probability for heavy import graph
        assert!(
            profile.plan.cross_layer_import_probability >= 0.5,
            "cross_layer_import_probability should be >= 0.5 for many-modules"
        );

        // Diamond dependencies enabled
        assert!(
            profile.plan.enable_diamond_dependencies,
            "enable_diamond_dependencies should be true for many-modules"
        );

        // Light declarations - focus on modules, not content complexity
        assert!(
            profile.plan.classes_per_module.1 <= 3,
            "classes_per_module max should be <= 3 for many-modules"
        );
        assert!(
            profile.plan.functions_per_module.1 <= 5,
            "functions_per_module max should be <= 5 for many-modules"
        );

        // Shallow nesting - focus on module graph, not code depth
        assert!(
            profile.emit.stmt_config.max_depth <= 2,
            "statement max_depth should be <= 2 for many-modules"
        );
        assert!(
            profile.emit.stmt_config.expr_config.max_depth <= 2,
            "expression max_depth should be <= 2 for many-modules"
        );
    }

    #[test]
    fn available_profiles_includes_many_modules() {
        let profiles = available_profiles();
        assert!(
            profiles.contains(&"many-modules"),
            "available_profiles should include many-modules"
        );
    }

    #[test]
    fn unknown_profile_error_includes_many_modules() {
        let result = get_profile("nonexistent");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.to_string().contains("many-modules"),
            "error message should mention many-modules profile"
        );
    }
}
