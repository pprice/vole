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
        "generics-heavy",
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
        "generics-heavy" => Ok(generics_heavy_profile()),
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
        // No classes, interfaces, structs, or errors
        structs_per_module: (0, 0),
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
        // No fallible functions (no error types in minimal)
        fallible_probability: 0.0,
        // No generators in minimal
        generator_probability: 0.0,
        // No never-returning functions in minimal
        never_probability: 0.0,
        // No nested class fields in minimal (no classes)
        nested_class_field_probability: 0.0,
        struct_param_probability: 0.0,
        struct_return_probability: 0.0,
        // These won't be used since we have no classes or structs
        fields_per_struct: (0, 0),
        fields_per_class: (0, 0),
        methods_per_class: (0, 0),
        static_methods_per_class: (0, 0),
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
                // No method chaining in minimal profile
                method_chain_probability: 0.0,
                max_chain_depth: 0,
                // No unreachable in minimal
                unreachable_probability: 0.0,
            },
            // Shallow statement depth
            max_depth: 1,
            // Few statements per block
            statements_per_block: (1, 2),
            // No control flow statements (simple arithmetic/comparisons only)
            if_probability: 0.0,
            while_probability: 0.0,
            for_probability: 0.0,
            break_continue_probability: 0.0,
            compound_assign_probability: 0.0,
            // No fallible (no error types in minimal)
            raise_probability: 0.0,
            try_probability: 0.0,
            // No tuples in minimal
            tuple_probability: 0.0,
            // No fixed arrays in minimal
            fixed_array_probability: 0.0,
            // No struct destructuring in minimal
            struct_destructure_probability: 0.0,
            // No discards in minimal
            discard_probability: 0.0,
            // No early returns in minimal
            early_return_probability: 0.0,
            // No else-if chains in minimal
            else_if_probability: 0.0,
            // No static method calls in minimal
            static_call_probability: 0.0,
        },
        // No destructured imports in minimal (no multi-layer modules)
        destructured_import_probability: 0.0,
        // No expression-bodied functions in minimal (keep output simple)
        expr_body_probability: 0.0,
    };

    Profile { plan, emit }
}

/// Full profile - comprehensive syntax coverage at moderate size.
///
/// Target characteristics:
/// - 3 layers, 3-5 modules per layer (~9-15 modules total)
/// - All declaration types: class, interface, implement, error, globals, functions
/// - All expression types exercised with moderate probabilities
/// - All statement types exercised with moderate probabilities
/// - Generics with constraints on classes, interfaces, and functions
/// - Lambdas with captures
/// - Match and when expressions
/// - Target: ~2000-5000 lines, exercises all compiler paths
///
/// Note: Struct and type alias declarations are not yet in the vole-stress
/// symbol system. When added, this profile should include them.
fn full_profile() -> Profile {
    let plan = PlanConfig {
        // 3 layers with 3-5 modules per layer (using 4 as midpoint)
        layers: 3,
        modules_per_layer: 4,

        // All declaration types with moderate counts
        structs_per_module: (1, 3),
        classes_per_module: (2, 4),
        interfaces_per_module: (1, 3),
        errors_per_module: (1, 2),
        functions_per_module: (3, 6),
        globals_per_module: (1, 3),

        // Class/interface/struct structure for comprehensive testing
        fields_per_struct: (2, 4),
        fields_per_class: (2, 5),
        methods_per_class: (2, 4),
        static_methods_per_class: (1, 2),
        methods_per_interface: (2, 3),
        fields_per_error: (1, 3),

        // Function parameters
        params_per_function: (1, 4),

        // Generics with constraints (moderate, not extreme)
        type_params_per_class: (0, 2),
        type_params_per_interface: (0, 2),
        type_params_per_function: (0, 2),
        constraints_per_type_param: (0, 2),

        // Interface relationships
        interface_extends_probability: 0.4,
        implement_blocks_per_module: (1, 2),

        // Module imports
        cross_layer_import_probability: 0.3,
        enable_diamond_dependencies: true,

        // Fallible functions: ~18% of non-generic functions get fallible return types
        fallible_probability: 0.18,
        // ~15% of non-generic functions become generators
        generator_probability: 0.15,
        // ~2% of functions are never-returning (diverging)
        never_probability: 0.02,
        // ~25% of non-generic classes get a field referencing another class
        nested_class_field_probability: 0.25,
        struct_param_probability: 0.10,
        struct_return_probability: 0.10,
    };

    let emit = EmitConfig {
        stmt_config: StmtConfig {
            expr_config: ExprConfig {
                // Moderate depth to generate non-trivial expressions
                max_depth: 4,
                // Higher probabilities to exercise all expression types
                binary_probability: 0.5,
                when_probability: 0.2,
                match_probability: 0.15,
                if_expr_probability: 0.2,
                lambda_probability: 0.15, // Elevated for lambda coverage
                // Method chaining on class instances
                method_chain_probability: 0.20,
                max_chain_depth: 2,
                // ~5% unreachable in match/when arms
                unreachable_probability: 0.05,
            },
            // Moderate statement depth for nested control flow
            max_depth: 3,
            // Reasonable statements per block
            statements_per_block: (2, 4),
            // Higher probabilities for control flow coverage
            if_probability: 0.3,
            while_probability: 0.15,
            for_probability: 0.2,
            break_continue_probability: 0.12,
            compound_assign_probability: 0.15,
            // Fallible: raise in fallible bodies, try when calling fallible funcs
            raise_probability: 0.12,
            try_probability: 0.15,
            // Tuples with destructuring
            tuple_probability: 0.12,
            // Fixed-size arrays with destructuring
            fixed_array_probability: 0.12,
            // Struct destructuring when struct-typed variables are in scope
            struct_destructure_probability: 0.15,
            // Discard expressions (_ = func()) to exercise syntax
            discard_probability: 0.05,
            // Early returns in function bodies (~15%)
            early_return_probability: 0.15,
            // Else-if chains in if statements (~30%)
            else_if_probability: 0.30,
            // Use static method calls ~30% of the time when constructing classes
            static_call_probability: 0.30,
        },
        // Destructured imports are disabled due to a compiler bug (vol-vzjx):
        // Module-level destructured imports fail when the module is transitively imported.
        // Re-enable at ~0.30 once the bug is fixed.
        destructured_import_probability: 0.0,
        // ~20% of eligible functions use expression-body syntax (=> expr)
        expr_body_probability: 0.20,
    };

    Profile { plan, emit }
}

/// Deep-nesting profile - stress parser stack and AST depth.
///
/// This profile generates code with significant nesting to test:
/// - Parser recursion limits and stack usage
/// - AST traversal efficiency in all compiler phases
/// - Memory usage with deeply nested structures
///
/// Target: expressions nested 5 levels, statements nested 6 levels.
/// Higher expression depths cause exponential AST growth from multi-arm
/// when/match expressions, producing functions too large for Cranelift.
fn deep_nesting_profile() -> Profile {
    let plan = PlanConfig {
        // Small module structure - focus is on depth, not breadth
        layers: 1,
        modules_per_layer: 1,
        // Few declarations, but each will have deeply nested bodies
        structs_per_module: (0, 0),
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
        // No fallible functions - focus is on nesting
        fallible_probability: 0.0,
        // No generators - focus is on nesting depth
        generator_probability: 0.0,
        // No never-returning functions - focus is on nesting
        never_probability: 0.0,
        // Some nested class fields for variety in deep nesting
        nested_class_field_probability: 0.15,
        struct_param_probability: 0.10,
        struct_return_probability: 0.10,
        // Minimal class/struct structure
        fields_per_struct: (0, 0),
        fields_per_class: (1, 2),
        methods_per_class: (1, 2),
        static_methods_per_class: (0, 0),
        methods_per_interface: (0, 0),
        fields_per_error: (0, 0),
    };

    let emit = EmitConfig {
        stmt_config: StmtConfig {
            expr_config: ExprConfig {
                // Expression nesting depth. Must stay moderate because
                // multi-arm expressions (when/match) have a branching
                // factor of 3-7 per level.  At depth 8 some seeds hit
                // worst-case ~7^8 ≈ 5 million leaf expressions, producing
                // functions with 100K+ CLIF instructions that hang in
                // Cranelift register allocation.  Depth 5 still gives
                // meaningful nesting while keeping worst-case size bounded
                // (~7^5 ≈ 17K leaves, well within Cranelift's budget).
                max_depth: 5,
                // High probability of binary expressions for deep a + (b + (c + ...))
                binary_probability: 0.6,
                // Multi-branch expressions at moderate probability
                when_probability: 0.15,
                match_probability: 0.1,
                if_expr_probability: 0.15,
                // Some lambdas for capture depth
                lambda_probability: 0.05,
                // Light method chaining (not the focus of this profile)
                method_chain_probability: 0.10,
                max_chain_depth: 2,
                // Some unreachable for variety
                unreachable_probability: 0.05,
            },
            // Deep statement nesting for nested control flow
            max_depth: 6,
            // Keep blocks small to bound total output size
            statements_per_block: (1, 2),
            // High probability of if for deep if-else chains
            if_probability: 0.5,
            // while/for loops add block depth
            while_probability: 0.15,
            for_probability: 0.15,
            break_continue_probability: 0.12,
            compound_assign_probability: 0.15,
            // No fallible - focus is on nesting depth
            raise_probability: 0.0,
            try_probability: 0.0,
            // Some tuples for variety
            tuple_probability: 0.08,
            // Some fixed arrays for variety
            fixed_array_probability: 0.08,
            // Some struct destructuring for variety
            struct_destructure_probability: 0.08,
            // Some discards for variety
            discard_probability: 0.05,
            // Some early returns for variety
            early_return_probability: 0.10,
            // Higher else-if probability for deep nested if-else-if chains
            else_if_probability: 0.40,
            // No static method calls in deep-nesting (focus is on control flow depth)
            static_call_probability: 0.0,
        },
        // No destructured imports in deep-nesting (single module focus)
        destructured_import_probability: 0.0,
        // Some expression-bodied functions for syntax variety
        expr_body_probability: 0.15,
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
        // Several structs with wide field counts
        structs_per_module: (1, 2),
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
        // Wide struct fields: 10-25
        fields_per_struct: (10, 25),
        // Wide fields: 20-50 fields per class
        fields_per_class: (20, 50),
        // Many methods per class: 10-20
        methods_per_class: (10, 20),
        // A few static methods for variety
        static_methods_per_class: (0, 1),
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
        // Some fallible functions
        fallible_probability: 0.10,
        // Some generators
        generator_probability: 0.08,
        // Some never-returning functions
        never_probability: 0.02,
        // Moderate nested class fields
        nested_class_field_probability: 0.20,
        struct_param_probability: 0.10,
        struct_return_probability: 0.10,
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
                // Standard method chaining
                method_chain_probability: 0.15,
                max_chain_depth: 2,
                // Some unreachable
                unreachable_probability: 0.05,
            },
            // Moderate statement depth
            max_depth: 2,
            // Standard statements per block
            statements_per_block: (1, 3),
            // Standard control flow probabilities
            if_probability: 0.2,
            while_probability: 0.1,
            for_probability: 0.1,
            break_continue_probability: 0.12,
            compound_assign_probability: 0.15,
            // Some fallible support
            raise_probability: 0.08,
            try_probability: 0.10,
            // Some tuples
            tuple_probability: 0.10,
            // Some fixed arrays
            fixed_array_probability: 0.10,
            // Some struct destructuring
            struct_destructure_probability: 0.10,
            // Some discards
            discard_probability: 0.05,
            // Some early returns
            early_return_probability: 0.10,
            // Some else-if chains
            else_if_probability: 0.25,
            // Use static method calls ~20% of the time
            static_call_probability: 0.20,
        },
        // Destructured imports are disabled due to a compiler bug (vol-vzjx):
        // Module-level destructured imports fail when the module is transitively imported.
        // Re-enable at ~0.20 once the bug is fixed.
        destructured_import_probability: 0.0,
        // ~15% expression-bodied functions
        expr_body_probability: 0.15,
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
        structs_per_module: (0, 1),
        classes_per_module: (1, 2),
        interfaces_per_module: (0, 1),
        errors_per_module: (0, 1),
        functions_per_module: (2, 4),
        globals_per_module: (1, 2),
        // Simple class/interface/struct structure
        fields_per_struct: (1, 3),
        fields_per_class: (1, 3),
        methods_per_class: (1, 2),
        static_methods_per_class: (0, 0),
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
        // No fallible functions - focus on module loading
        fallible_probability: 0.0,
        // No generators - focus on module loading
        generator_probability: 0.0,
        // No never-returning functions - focus on module loading
        never_probability: 0.0,
        // Light nested class fields - focus on module loading
        nested_class_field_probability: 0.10,
        struct_param_probability: 0.10,
        struct_return_probability: 0.10,
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
                // No method chaining - focus on module loading
                method_chain_probability: 0.0,
                max_chain_depth: 0,
                // No unreachable - focus on module loading
                unreachable_probability: 0.0,
            },
            // Shallow statement depth
            max_depth: 1,
            // Few statements per block
            statements_per_block: (1, 2),
            // Minimal control flow
            if_probability: 0.1,
            while_probability: 0.0,
            for_probability: 0.0,
            break_continue_probability: 0.0,
            compound_assign_probability: 0.0,
            // No fallible - focus on module loading
            raise_probability: 0.0,
            try_probability: 0.0,
            // No tuples - focus on module loading
            tuple_probability: 0.0,
            // No fixed arrays - focus on module loading
            fixed_array_probability: 0.0,
            // No struct destructuring - focus on module loading
            struct_destructure_probability: 0.0,
            // No discards - focus on module loading
            discard_probability: 0.0,
            // No early returns - focus on module loading
            early_return_probability: 0.0,
            // No else-if chains - focus on module loading
            else_if_probability: 0.0,
            // No static method calls - focus on module loading
            static_call_probability: 0.0,
        },
        // Destructured imports are disabled due to a compiler bug (vol-vzjx):
        // Module-level destructured imports fail when the module is transitively imported.
        // Re-enable at ~0.30 once the bug is fixed.
        destructured_import_probability: 0.0,
        // No expression-bodied functions - focus on module loading
        expr_body_probability: 0.0,
    };

    Profile { plan, emit }
}

/// Generics-heavy profile - stress generic instantiation and monomorphization.
///
/// This profile generates code that heavily uses generics to test:
/// - Deeply parameterized types: Foo<Bar<Baz<Qux<T>>>>
/// - Multiple constraints: T: Hashable + Serializable + Comparable
/// - Generic methods on generic classes
/// - Generic lambdas passed to generic functions
/// - Chained generic method calls
/// - Many monomorphization sites (same generic with different type args)
///
/// Target: stress type inference, constraint checking, monomorph cache.
fn generics_heavy_profile() -> Profile {
    let plan = PlanConfig {
        // Moderate module structure - focus is on generics, not module graph
        layers: 2,
        modules_per_layer: 3,
        // A few structs (structs don't have generics, but add some for variety)
        structs_per_module: (0, 1),
        // Many classes - each will be generic
        classes_per_module: (3, 5),
        // Many interfaces for constraints
        interfaces_per_module: (3, 5),
        // A few errors for completeness
        errors_per_module: (1, 2),
        // Many generic functions
        functions_per_module: (4, 6),
        // Some globals
        globals_per_module: (1, 2),
        // Struct fields
        fields_per_struct: (2, 3),
        // Moderate field counts - fields can use type params
        fields_per_class: (2, 4),
        // Many methods - methods will also be generic on generic classes
        methods_per_class: (3, 5),
        // No static methods - focus on generics (statics are non-generic only)
        static_methods_per_class: (0, 0),
        // Many interface methods for constraint satisfaction
        methods_per_interface: (2, 4),
        // Simple error fields
        fields_per_error: (0, 2),
        // Moderate parameter counts - params can use type params
        params_per_function: (2, 4),
        // High type parameter counts for deep generics (2-4 type params)
        type_params_per_class: (2, 4),
        type_params_per_interface: (1, 3),
        type_params_per_function: (2, 4),
        // Multiple constraints per type param for T: A + B + C patterns
        constraints_per_type_param: (1, 3),
        // High interface extends for constraint hierarchies
        interface_extends_probability: 0.5,
        // Some implement blocks for generic impl scenarios
        implement_blocks_per_module: (1, 3),
        // Standard import behavior
        cross_layer_import_probability: 0.3,
        enable_diamond_dependencies: true,
        // Some fallible functions for generics-heavy profile
        fallible_probability: 0.10,
        // Some generators for generics-heavy profile
        generator_probability: 0.10,
        // Some never-returning functions
        never_probability: 0.02,
        // No nested class fields - focus on generics, not nested types
        // (nested class fields are only for non-generic classes)
        nested_class_field_probability: 0.0,
        struct_param_probability: 0.0,
        struct_return_probability: 0.0,
    };

    let emit = EmitConfig {
        stmt_config: StmtConfig {
            expr_config: ExprConfig {
                // Moderate expression depth
                max_depth: 3,
                // Standard binary expression probability
                binary_probability: 0.3,
                // Some when expressions
                when_probability: 0.1,
                // Some match expressions
                match_probability: 0.1,
                // Some if expressions
                if_expr_probability: 0.1,
                // Higher lambda probability for generic lambdas
                lambda_probability: 0.15,
                // Standard method chaining
                method_chain_probability: 0.15,
                max_chain_depth: 2,
                // Some unreachable
                unreachable_probability: 0.05,
            },
            // Moderate statement depth
            max_depth: 2,
            // Standard statements per block
            statements_per_block: (2, 3),
            // Standard control flow probabilities
            if_probability: 0.2,
            while_probability: 0.1,
            for_probability: 0.15,
            break_continue_probability: 0.12,
            compound_assign_probability: 0.15,
            // Some fallible support
            raise_probability: 0.08,
            try_probability: 0.10,
            // Some tuples
            tuple_probability: 0.10,
            // Some fixed arrays
            fixed_array_probability: 0.10,
            // Some struct destructuring
            struct_destructure_probability: 0.10,
            // Some discards
            discard_probability: 0.05,
            // Some early returns
            early_return_probability: 0.12,
            // Some else-if chains
            else_if_probability: 0.25,
            // No static method calls - focus on generics (statics are non-generic only)
            static_call_probability: 0.0,
        },
        // Destructured imports are disabled due to a compiler bug (vol-vzjx):
        // Module-level destructured imports fail when the module is transitively imported.
        // Re-enable at ~0.20 once the bug is fixed.
        destructured_import_probability: 0.0,
        // ~15% expression-bodied functions
        expr_body_probability: 0.15,
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

        // Verify ticket requirements: 3 layers, 3-5 modules per layer
        assert_eq!(profile.plan.layers, 3, "full profile should have 3 layers");
        assert!(
            profile.plan.modules_per_layer >= 3 && profile.plan.modules_per_layer <= 5,
            "full profile should have 3-5 modules per layer"
        );

        // All declaration types should be enabled (non-zero ranges)
        assert!(
            profile.plan.classes_per_module.1 > 0,
            "full profile should generate classes"
        );
        assert!(
            profile.plan.interfaces_per_module.1 > 0,
            "full profile should generate interfaces"
        );
        assert!(
            profile.plan.errors_per_module.1 > 0,
            "full profile should generate errors"
        );
        assert!(
            profile.plan.functions_per_module.1 > 0,
            "full profile should generate functions"
        );
        assert!(
            profile.plan.implement_blocks_per_module.1 > 0,
            "full profile should generate implement blocks"
        );

        // Generics with constraints
        assert!(
            profile.plan.type_params_per_class.1 > 0,
            "full profile should support generic classes"
        );
        assert!(
            profile.plan.type_params_per_function.1 > 0,
            "full profile should support generic functions"
        );
        assert!(
            profile.plan.constraints_per_type_param.1 > 0,
            "full profile should support type param constraints"
        );

        // All expression types exercised (non-zero probabilities)
        let expr_cfg = &profile.emit.stmt_config.expr_config;
        assert!(
            expr_cfg.binary_probability > 0.0,
            "full profile should generate binary expressions"
        );
        assert!(
            expr_cfg.when_probability > 0.0,
            "full profile should generate when expressions"
        );
        assert!(
            expr_cfg.match_probability > 0.0,
            "full profile should generate match expressions"
        );
        assert!(
            expr_cfg.lambda_probability > 0.0,
            "full profile should generate lambda expressions"
        );

        // All statement types exercised
        let stmt_cfg = &profile.emit.stmt_config;
        assert!(
            stmt_cfg.if_probability > 0.0,
            "full profile should generate if statements"
        );
        assert!(
            stmt_cfg.while_probability > 0.0,
            "full profile should generate while statements"
        );
        assert!(
            stmt_cfg.for_probability > 0.0,
            "full profile should generate for statements"
        );
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
        // Expression nesting depth (5+ avoids exponential blowup from
        // multi-arm when/match while still achieving meaningful depth)
        assert!(
            profile.emit.stmt_config.expr_config.max_depth >= 5,
            "expression max_depth should be >= 5 for deep nesting"
        );
        // Statement nesting depth
        assert!(
            profile.emit.stmt_config.max_depth >= 6,
            "statement max_depth should be >= 6 for deep nesting"
        );
        // High binary probability for deep a + (b + (c + ...))
        assert!(
            profile.emit.stmt_config.expr_config.binary_probability >= 0.5,
            "binary_probability should be high for deep nesting"
        );
        // High if probability for deep if-else chains
        assert!(
            profile.emit.stmt_config.if_probability >= 0.4,
            "if_probability should be moderately high for deep nesting"
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

    #[test]
    fn generics_heavy_profile_exists() {
        let profile = get_profile("generics-heavy").expect("generics-heavy profile should exist");
        // Verify generics-heavy characteristics: focus on generic type parameters

        // Multiple type parameters per class (2-4)
        assert!(
            profile.plan.type_params_per_class.0 >= 2,
            "type_params_per_class min should be >= 2 for generics-heavy"
        );
        assert!(
            profile.plan.type_params_per_class.1 >= 4,
            "type_params_per_class max should be >= 4 for generics-heavy"
        );

        // Multiple type parameters per function (2-4)
        assert!(
            profile.plan.type_params_per_function.0 >= 2,
            "type_params_per_function min should be >= 2 for generics-heavy"
        );
        assert!(
            profile.plan.type_params_per_function.1 >= 4,
            "type_params_per_function max should be >= 4 for generics-heavy"
        );

        // Multiple constraints per type param (1-3)
        assert!(
            profile.plan.constraints_per_type_param.0 >= 1,
            "constraints_per_type_param min should be >= 1 for generics-heavy"
        );
        assert!(
            profile.plan.constraints_per_type_param.1 >= 3,
            "constraints_per_type_param max should be >= 3 for generics-heavy"
        );

        // Many interfaces for constraints
        assert!(
            profile.plan.interfaces_per_module.0 >= 3,
            "interfaces_per_module min should be >= 3 for generics-heavy"
        );

        // Many generic classes
        assert!(
            profile.plan.classes_per_module.0 >= 3,
            "classes_per_module min should be >= 3 for generics-heavy"
        );

        // Many methods for generic method testing
        assert!(
            profile.plan.methods_per_class.0 >= 3,
            "methods_per_class min should be >= 3 for generics-heavy"
        );

        // High interface extends probability for constraint hierarchies
        assert!(
            profile.plan.interface_extends_probability >= 0.5,
            "interface_extends_probability should be >= 0.5 for generics-heavy"
        );

        // Higher lambda probability for generic lambdas
        assert!(
            profile.emit.stmt_config.expr_config.lambda_probability >= 0.1,
            "lambda_probability should be >= 0.1 for generics-heavy"
        );
    }

    #[test]
    fn available_profiles_includes_generics_heavy() {
        let profiles = available_profiles();
        assert!(
            profiles.contains(&"generics-heavy"),
            "available_profiles should include generics-heavy"
        );
    }

    #[test]
    fn unknown_profile_error_includes_generics_heavy() {
        let result = get_profile("nonexistent");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.to_string().contains("generics-heavy"),
            "error message should mention generics-heavy profile"
        );
    }
}
