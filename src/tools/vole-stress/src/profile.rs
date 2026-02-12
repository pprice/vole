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
        "stdlib-heavy",
        "closures-heavy",
        "fallible-heavy",
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
        "stdlib-heavy" => Ok(stdlib_heavy_profile()),
        "closures-heavy" => Ok(closures_heavy_profile()),
        "fallible-heavy" => Ok(fallible_heavy_profile()),
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
        interface_param_probability: 0.0,
        // No generics in minimal
        generic_closure_interface_fn_probability: 0.0,
        // No closure-returning functions in minimal
        closure_return_probability: 0.0,
        // These won't be used since we have no classes or structs
        fields_per_struct: (0, 0),
        fields_per_class: (0, 0),
        methods_per_class: (0, 0),
        static_methods_per_class: (0, 0),
        static_methods_per_struct: (0, 0),
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
                max_match_arms: 3,
                // No inline expressions in args for minimal
                inline_expr_arg_probability: 0.0,
                // No tuple indexing in minimal (no tuples)
                tuple_index_probability: 0.0,
                // No chained coalescing in minimal
                chained_coalesce_probability: 0.0,
                // No string methods in minimal
                string_method_probability: 0.0,
                // No multi-arm when in minimal
                multi_arm_when_probability: 0.0,
                // No match guards in minimal
                match_guard_probability: 0.0,
                // No closure capture in minimal (no lambdas)
                closure_capture_probability: 0.0,
                // No interface upcast in minimal (no interfaces)
                interface_upcast_probability: 0.0,
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
            reassign_probability: 0.0,
            // No fallible (no error types in minimal)
            raise_probability: 0.0,
            try_probability: 0.0,
            // No tuples in minimal
            tuple_probability: 0.0,
            // No fixed arrays in minimal
            fixed_array_probability: 0.0,
            // No struct destructuring in minimal
            struct_destructure_probability: 0.0,
            // No class destructuring in minimal (no classes)
            class_destructure_probability: 0.0,
            // No discards in minimal
            discard_probability: 0.0,
            // No early returns in minimal
            early_return_probability: 0.0,
            // No else-if chains in minimal
            else_if_probability: 0.0,
            // No static method calls in minimal
            static_call_probability: 0.0,
            // No array mutation in minimal
            array_index_assign_probability: 0.0,
            array_push_probability: 0.0,
            array_index_compound_assign_probability: 0.0,
            mutable_array_probability: 0.0,
            // No instance method calls in minimal (no classes)
            method_call_probability: 0.0,
            // No interface dispatch in minimal (no interfaces)
            interface_dispatch_probability: 0.0,
            // Some match expressions even in minimal
            match_probability: 0.06,
            // Some string match expressions even in minimal
            string_match_probability: 0.04,
            // Some when-expression let-bindings even in minimal
            when_let_probability: 0.04,
            // No nested loops in minimal
            nested_loop_probability: 0.0,
            // No union match in minimal (no union-typed params likely)
            union_match_probability: 0.0,
            // No iterator map/filter in minimal
            iter_map_filter_probability: 0.0,
            // No interface function calls in minimal (no interfaces)
            iface_function_call_probability: 0.0,
            // No generic closure+interface chains in minimal (no generics)
            generic_closure_interface_probability: 0.0,
            // No empty array iter in minimal
            empty_array_iter_probability: 0.0,
            // No match-closure-arm in minimal (no lambdas)
            match_closure_arm_probability: 0.0,
            // No range-based iterators in minimal
            range_iter_probability: 0.0,
            // No field-closure-let in minimal (no classes)
            field_closure_let_probability: 0.0,
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
        static_methods_per_struct: (1, 2),
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
        // ~12% of non-generic functions get an interface-typed param (vtable dispatch)
        interface_param_probability: 0.12,
        // ~15% of planned functions get the "generic closure interface" shape
        generic_closure_interface_fn_probability: 0.15,
        // ~12% of non-generic functions return a closure
        closure_return_probability: 0.12,
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
                max_match_arms: 6,
                // ~12% inline when/if expressions in call args and field values
                inline_expr_arg_probability: 0.12,
                // ~15% tuple indexing on tuple-typed variables
                tuple_index_probability: 0.15,
                // ~30% chained coalescing when multiple optionals match
                chained_coalesce_probability: 0.30,
                // ~15% string method calls (length, contains, trim, etc.)
                string_method_probability: 0.15,
                // ~35% multi-arm when (3-4 arms instead of 2)
                multi_arm_when_probability: 0.35,
                // ~15% match guards on wildcard arms
                match_guard_probability: 0.15,
                closure_capture_probability: 0.30,
                // ~30% chance to construct a class instance for interface args
                interface_upcast_probability: 0.30,
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
            reassign_probability: 0.15,
            // Fallible: raise in fallible bodies, try when calling fallible funcs
            raise_probability: 0.12,
            try_probability: 0.15,
            // Tuples with destructuring
            tuple_probability: 0.12,
            // Fixed-size arrays with destructuring
            fixed_array_probability: 0.12,
            // Struct destructuring when struct-typed variables are in scope
            struct_destructure_probability: 0.15,
            // Class destructuring when class-typed variables are in scope
            class_destructure_probability: 0.12,
            // Discard expressions (_ = func()) to exercise syntax
            discard_probability: 0.05,
            // Early returns in function bodies (~15%)
            early_return_probability: 0.15,
            // Else-if chains in if statements (~30%)
            else_if_probability: 0.30,
            // Use static method calls ~30% of the time when constructing classes
            static_call_probability: 0.30,
            // Array mutation: index assignment and push on mutable dynamic arrays
            array_index_assign_probability: 0.10,
            array_push_probability: 0.08,
            array_index_compound_assign_probability: 0.10,
            mutable_array_probability: 0.4,
            // Instance method calls on class-typed locals (~12%)
            method_call_probability: 0.12,
            // Interface vtable dispatch on interface-typed locals/params (~10%)
            interface_dispatch_probability: 0.10,
            // Match expression let-bindings on i64 variables
            match_probability: 0.08,
            // Match expression let-bindings on string variables
            string_match_probability: 0.06,
            // When expression let-bindings (~8%)
            when_let_probability: 0.08,
            // Nested for-loops with break/continue (~6%)
            nested_loop_probability: 0.06,
            // Union match expression let-bindings (~10%)
            union_match_probability: 0.10,
            // Iterator map/filter on array variables (~10%)
            iter_map_filter_probability: 0.10,
            // Calls to free functions with interface-typed params (~10%)
            iface_function_call_probability: 0.10,
            // Generic closure + interface dispatch in iterator chains (~15%)
            generic_closure_interface_probability: 0.15,
            // Empty array through iterator chain (~6%) — boundary edge case
            empty_array_iter_probability: 0.06,
            // ~10% match arms produce closures capturing surrounding scope
            match_closure_arm_probability: 0.10,
            range_iter_probability: 0.08,
            // ~8% field-closure-let: extract field, capture in closure, invoke/map
            field_closure_let_probability: 0.08,
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
        interface_param_probability: 0.0,
        // No generics in deep-nesting
        generic_closure_interface_fn_probability: 0.0,
        // No closure-returning functions in deep-nesting (focus is on nesting)
        closure_return_probability: 0.0,
        // Minimal class/struct structure
        fields_per_struct: (0, 0),
        fields_per_class: (1, 2),
        methods_per_class: (1, 2),
        static_methods_per_class: (0, 0),
        static_methods_per_struct: (0, 0),
        methods_per_interface: (0, 0),
        fields_per_error: (0, 0),
    };

    let emit = EmitConfig {
        stmt_config: StmtConfig {
            expr_config: ExprConfig {
                // Expression nesting depth. Multi-arm expressions
                // (when/match) branch 3-7x per level.  Depth 5 gives
                // ~7^5 ≈ 17K worst-case leaves per expression tree.
                // Combined with stmt depth 4 this stays within
                // Cranelift's budget while producing meaningful depth.
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
                max_match_arms: 8,
                // Higher inline expr args for nesting stress
                inline_expr_arg_probability: 0.15,
                // Some tuple indexing for variety
                tuple_index_probability: 0.10,
                // ~30% chained coalescing for nesting variety
                chained_coalesce_probability: 0.30,
                // Some string method calls for variety
                string_method_probability: 0.10,
                // ~25% multi-arm when for nesting variety
                multi_arm_when_probability: 0.25,
                // ~10% match guards for nesting variety
                match_guard_probability: 0.10,
                closure_capture_probability: 0.20,
                // No interface upcast in deep-nesting (no interfaces)
                interface_upcast_probability: 0.0,
            },
            // Statement nesting for nested control flow. Combined with
            // expression depth 4, this keeps total output per function
            // bounded while still exercising deep nesting paths.
            max_depth: 4,
            // Keep blocks small to bound total output size
            statements_per_block: (1, 2),
            // High probability of if for deep if-else chains
            if_probability: 0.5,
            // while/for loops add block depth
            while_probability: 0.15,
            for_probability: 0.15,
            break_continue_probability: 0.12,
            compound_assign_probability: 0.15,
            reassign_probability: 0.12,
            // No fallible - focus is on nesting depth
            raise_probability: 0.0,
            try_probability: 0.0,
            // Some tuples for variety
            tuple_probability: 0.08,
            // Some fixed arrays for variety
            fixed_array_probability: 0.08,
            // Some struct destructuring for variety
            struct_destructure_probability: 0.08,
            // Some class destructuring for variety
            class_destructure_probability: 0.06,
            // Some discards for variety
            discard_probability: 0.05,
            // Some early returns for variety
            early_return_probability: 0.10,
            // Higher else-if probability for deep nested if-else-if chains
            else_if_probability: 0.40,
            // No static method calls in deep-nesting (focus is on control flow depth)
            static_call_probability: 0.0,
            // Some array mutation for variety
            array_index_assign_probability: 0.08,
            array_push_probability: 0.05,
            array_index_compound_assign_probability: 0.08,
            mutable_array_probability: 0.3,
            // Some instance method calls for variety
            method_call_probability: 0.08,
            // No interface dispatch in deep-nesting (no interfaces)
            interface_dispatch_probability: 0.0,
            // Higher match probability for nesting-focused profile
            match_probability: 0.10,
            // Some string match expressions for variety
            string_match_probability: 0.06,
            // Some when-expression let-bindings for variety
            when_let_probability: 0.08,
            // Higher nested loop probability for deep nesting profile
            nested_loop_probability: 0.10,
            // Some union match for variety
            union_match_probability: 0.06,
            // Some iterator map/filter for variety
            iter_map_filter_probability: 0.06,
            // No interface function calls in deep-nesting (no interfaces)
            iface_function_call_probability: 0.0,
            // No generic closure+interface chains in deep-nesting (no generics)
            generic_closure_interface_probability: 0.0,
            // Some empty array iter for boundary condition variety
            empty_array_iter_probability: 0.04,
            // Some match-closure-arm for nesting variety
            match_closure_arm_probability: 0.06,
            range_iter_probability: 0.04,
            // Some field-closure-let for nesting variety
            field_closure_let_probability: 0.04,
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
        static_methods_per_struct: (0, 1),
        // Many methods per interface: 10-20
        methods_per_interface: (10, 20),
        // Wide error fields: 5-15
        fields_per_error: (5, 15),
        // Wide parameter counts: 20-50 params per function
        params_per_function: (20, 50),
        // Many type parameters for generics: 5-10
        type_params_per_class: (5, 10),
        // Range starts at 0 so some interfaces are non-generic —
        // only non-generic interfaces can serve as type param constraints (T: IFace).
        type_params_per_interface: (0, 6),
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
        // Some interface-typed params for vtable dispatch coverage
        interface_param_probability: 0.08,
        // Some GCI functions for closure+generic+iterator coverage
        generic_closure_interface_fn_probability: 0.06,
        // Some closure-returning functions for variety
        closure_return_probability: 0.06,
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
                max_match_arms: 5,
                // Some inline when/if in args — not the focus but adds variety
                inline_expr_arg_probability: 0.08,
                // Some tuple indexing
                tuple_index_probability: 0.12,
                // ~25% chained coalescing
                chained_coalesce_probability: 0.25,
                // Some string method calls
                string_method_probability: 0.10,
                // ~25% multi-arm when
                multi_arm_when_probability: 0.25,
                // ~10% match guards
                match_guard_probability: 0.10,
                closure_capture_probability: 0.20,
                // ~25% chance to construct a class instance for interface args
                interface_upcast_probability: 0.25,
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
            reassign_probability: 0.12,
            // Some fallible support
            raise_probability: 0.08,
            try_probability: 0.10,
            // Some tuples
            tuple_probability: 0.10,
            // Some fixed arrays
            fixed_array_probability: 0.10,
            // Some struct destructuring
            struct_destructure_probability: 0.10,
            // Some class destructuring
            class_destructure_probability: 0.08,
            // Some discards
            discard_probability: 0.05,
            // Some early returns
            early_return_probability: 0.10,
            // Some else-if chains
            else_if_probability: 0.25,
            // Use static method calls ~20% of the time
            static_call_probability: 0.20,
            // Some array mutation
            array_index_assign_probability: 0.08,
            array_push_probability: 0.05,
            array_index_compound_assign_probability: 0.08,
            mutable_array_probability: 0.3,
            // Some instance method calls
            method_call_probability: 0.10,
            // Some interface vtable dispatch
            interface_dispatch_probability: 0.08,
            // Match expression let-bindings on i64 variables
            match_probability: 0.08,
            // Match expression let-bindings on string variables
            string_match_probability: 0.06,
            // Some when-expression let-bindings
            when_let_probability: 0.06,
            // Some nested for-loops with break/continue
            nested_loop_probability: 0.04,
            // Some union match expressions
            union_match_probability: 0.06,
            // Some iterator map/filter for variety
            iter_map_filter_probability: 0.06,
            // Some interface function calls for vtable dispatch
            iface_function_call_probability: 0.06,
            // Some generic closure+interface chains
            generic_closure_interface_probability: 0.06,
            // Some empty array iter for boundary condition variety
            empty_array_iter_probability: 0.04,
            // Some match-closure-arm for variety
            match_closure_arm_probability: 0.06,
            range_iter_probability: 0.04,
            // Some field-closure-let for variety
            field_closure_let_probability: 0.04,
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
        static_methods_per_struct: (0, 0),
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
        interface_param_probability: 0.0,
        // No GCI functions - focus on module loading
        generic_closure_interface_fn_probability: 0.0,
        // No closure-returning functions - focus on module loading
        closure_return_probability: 0.0,
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
                max_match_arms: 3,
                // No inline expressions in args - focus on module loading
                inline_expr_arg_probability: 0.0,
                // No tuple indexing - focus on module loading
                tuple_index_probability: 0.0,
                // No chained coalescing - focus on module loading
                chained_coalesce_probability: 0.0,
                // No string methods - focus on module loading
                string_method_probability: 0.0,
                // No multi-arm when - focus on module loading
                multi_arm_when_probability: 0.0,
                // No match guards - focus on module loading
                match_guard_probability: 0.0,
                // No closure capture - focus on module loading
                closure_capture_probability: 0.0,
                // No interface upcast - focus on module loading
                interface_upcast_probability: 0.0,
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
            reassign_probability: 0.0,
            // No fallible - focus on module loading
            raise_probability: 0.0,
            try_probability: 0.0,
            // No tuples - focus on module loading
            tuple_probability: 0.0,
            // No fixed arrays - focus on module loading
            fixed_array_probability: 0.0,
            // No struct destructuring - focus on module loading
            struct_destructure_probability: 0.0,
            // No class destructuring - focus on module loading
            class_destructure_probability: 0.0,
            // No discards - focus on module loading
            discard_probability: 0.0,
            // No early returns - focus on module loading
            early_return_probability: 0.0,
            // No else-if chains - focus on module loading
            else_if_probability: 0.0,
            // No static method calls - focus on module loading
            static_call_probability: 0.0,
            // No array mutation - focus on module loading
            array_index_assign_probability: 0.0,
            array_push_probability: 0.0,
            array_index_compound_assign_probability: 0.0,
            mutable_array_probability: 0.0,
            // No instance method calls - focus on module loading
            method_call_probability: 0.0,
            // No interface dispatch - focus on module loading
            interface_dispatch_probability: 0.0,
            // Some match expressions even in many-modules
            match_probability: 0.06,
            // Some string match expressions even in many-modules
            string_match_probability: 0.04,
            // Some when-expression let-bindings even in many-modules
            when_let_probability: 0.04,
            // No nested loops in many-modules - focus on module loading
            nested_loop_probability: 0.0,
            // No union match in many-modules - focus on module loading
            union_match_probability: 0.0,
            // No iterator map/filter in many-modules - focus on module loading
            iter_map_filter_probability: 0.0,
            // No interface function calls in many-modules - focus on module loading
            iface_function_call_probability: 0.0,
            // No generic closure+interface chains in many-modules - focus on module loading
            generic_closure_interface_probability: 0.0,
            // No empty array iter in many-modules - focus on module loading
            empty_array_iter_probability: 0.0,
            // No match-closure-arm in many-modules - focus on module loading
            match_closure_arm_probability: 0.0,
            // No range-based iterators in many-modules - focus on module loading
            range_iter_probability: 0.0,
            // No field-closure-let in many-modules - focus on module loading
            field_closure_let_probability: 0.0,
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
        static_methods_per_struct: (0, 0),
        // Many interface methods for constraint satisfaction
        methods_per_interface: (2, 4),
        // Simple error fields
        fields_per_error: (0, 2),
        // Moderate parameter counts - params can use type params
        params_per_function: (2, 4),
        // High type parameter counts for deep generics (2-4 type params)
        type_params_per_class: (2, 4),
        // Range starts at 0 so some interfaces are non-generic —
        // only non-generic interfaces can serve as type param constraints (T: IFace).
        type_params_per_interface: (0, 3),
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
        interface_param_probability: 0.0,
        // Elevated probability for GCI functions - core generics focus
        generic_closure_interface_fn_probability: 0.20,
        // Some closure-returning functions for higher-order variety
        closure_return_probability: 0.08,
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
                max_match_arms: 5,
                // Some inline when/if in args — adds variety to generic calls
                inline_expr_arg_probability: 0.10,
                // Some tuple indexing
                tuple_index_probability: 0.12,
                // ~25% chained coalescing
                chained_coalesce_probability: 0.25,
                // Some string method calls
                string_method_probability: 0.10,
                // ~25% multi-arm when
                multi_arm_when_probability: 0.25,
                // ~10% match guards
                match_guard_probability: 0.10,
                closure_capture_probability: 0.25,
                // ~30% chance to construct a class instance for interface args
                interface_upcast_probability: 0.30,
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
            reassign_probability: 0.12,
            // Some fallible support
            raise_probability: 0.08,
            try_probability: 0.10,
            // Some tuples
            tuple_probability: 0.10,
            // Some fixed arrays
            fixed_array_probability: 0.10,
            // Some struct destructuring
            struct_destructure_probability: 0.10,
            // Some class destructuring
            class_destructure_probability: 0.08,
            // Some discards
            discard_probability: 0.05,
            // Some early returns
            early_return_probability: 0.12,
            // Some else-if chains
            else_if_probability: 0.25,
            // No static method calls - focus on generics (statics are non-generic only)
            static_call_probability: 0.0,
            // Some array mutation for variety
            array_index_assign_probability: 0.08,
            array_push_probability: 0.05,
            array_index_compound_assign_probability: 0.08,
            mutable_array_probability: 0.3,
            // No instance method calls - focus on generics (generic classes
            // are skipped, and non-generic classes are rare in this profile)
            method_call_probability: 0.0,
            // No interface dispatch - focus on generics
            interface_dispatch_probability: 0.0,
            // Some match expressions in generics profile
            match_probability: 0.06,
            // Some string match expressions in generics profile
            string_match_probability: 0.04,
            // Some when-expression let-bindings in generics profile
            when_let_probability: 0.06,
            // Some nested for-loops with break/continue
            nested_loop_probability: 0.04,
            // Some union match expressions
            union_match_probability: 0.06,
            // Some iterator map/filter for variety
            iter_map_filter_probability: 0.06,
            // No interface function calls in generics-heavy (focus on generics)
            iface_function_call_probability: 0.0,
            // Elevated generic closure+interface chains (~20%) — core focus of this profile
            generic_closure_interface_probability: 0.20,
            // Some empty array iter for boundary condition variety
            empty_array_iter_probability: 0.04,
            // Some match-closure-arm for variety
            match_closure_arm_probability: 0.06,
            range_iter_probability: 0.04,
            // Some field-closure-let for variety
            field_closure_let_probability: 0.04,
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

/// Stdlib-heavy profile - stress standard library usage and method chaining.
///
/// This profile generates code that heavily exercises the standard library:
/// - String methods, string interpolation, string matching
/// - Array methods: push, index, iteration via map/filter/reduce/sum
/// - Iterator chains: `.iter().map(...).filter(...).collect()`
/// - Method chaining on class instances
/// - Higher lambda usage for iterator callbacks
///
/// Structurally moderate (2 layers, 6-8 modules) — the focus is on
/// expression richness and stdlib surface area, not structural depth.
///
/// Target: stress runtime builtins, string/array codegen paths,
/// iterator protocol, and method dispatch.
fn stdlib_heavy_profile() -> Profile {
    let plan = PlanConfig {
        // Moderate module structure — 2 layers, ~7 modules per layer
        layers: 2,
        modules_per_layer: 7,

        // Standard declaration counts — not the focus of this profile
        structs_per_module: (1, 2),
        classes_per_module: (2, 4),
        interfaces_per_module: (1, 2),
        errors_per_module: (0, 1),
        functions_per_module: (4, 7),
        globals_per_module: (2, 4),

        // Class/interface structure
        fields_per_struct: (2, 4),
        fields_per_class: (2, 4),
        methods_per_class: (2, 4),
        static_methods_per_class: (1, 2),
        static_methods_per_struct: (1, 2),
        methods_per_interface: (2, 3),
        fields_per_error: (0, 2),

        // Function parameters: moderate
        params_per_function: (1, 4),

        // Light generics — not the focus
        type_params_per_class: (0, 1),
        type_params_per_interface: (0, 1),
        type_params_per_function: (0, 1),
        constraints_per_type_param: (0, 1),

        // Some interface relationships
        interface_extends_probability: 0.3,
        implement_blocks_per_module: (1, 2),

        // Standard imports
        cross_layer_import_probability: 0.3,
        enable_diamond_dependencies: true,

        // Some fallible functions for try coverage
        fallible_probability: 0.10,
        // Some generators — iterator chains pair well with generators
        generator_probability: 0.12,
        // No never-returning functions
        never_probability: 0.0,
        // Moderate nested class fields for method chaining targets
        nested_class_field_probability: 0.20,
        struct_param_probability: 0.10,
        struct_return_probability: 0.10,
        // Some interface-typed params for vtable dispatch on stdlib types
        interface_param_probability: 0.10,
        // Some GCI functions for closure+generic+iterator coverage
        generic_closure_interface_fn_probability: 0.08,
        // Some closure-returning functions for higher-order variety
        closure_return_probability: 0.08,
    };

    let emit = EmitConfig {
        stmt_config: StmtConfig {
            expr_config: ExprConfig {
                // Moderate expression depth — deep enough for method chains
                max_depth: 4,
                // Standard binary expression probability
                binary_probability: 0.4,
                // Some when/match/if expressions
                when_probability: 0.15,
                match_probability: 0.12,
                if_expr_probability: 0.15,
                // Elevated lambda probability for iterator callbacks
                lambda_probability: 0.25,
                // High method chaining for stdlib method stress
                method_chain_probability: 0.35,
                max_chain_depth: 3,
                // Some unreachable
                unreachable_probability: 0.05,
                max_match_arms: 8,
                // Moderate inline when/if in method args — exercises stdlib with complex args
                inline_expr_arg_probability: 0.12,
                // Some tuple indexing
                tuple_index_probability: 0.12,
                // ~30% chained coalescing
                chained_coalesce_probability: 0.30,
                // Elevated string method calls for stdlib stress
                string_method_probability: 0.25,
                // ~30% multi-arm when
                multi_arm_when_probability: 0.30,
                // ~10% match guards
                match_guard_probability: 0.10,
                closure_capture_probability: 0.30,
                // ~25% chance to construct a class instance for interface args
                interface_upcast_probability: 0.25,
            },
            // Moderate statement depth — not too deep structurally
            max_depth: 2,
            // Reasonable statements per block
            statements_per_block: (2, 4),
            // Standard control flow
            if_probability: 0.25,
            while_probability: 0.10,
            // Elevated for-loop probability — iterating over arrays
            for_probability: 0.25,
            break_continue_probability: 0.10,
            compound_assign_probability: 0.15,
            reassign_probability: 0.15,
            // Some fallible support
            raise_probability: 0.08,
            try_probability: 0.10,
            // Moderate tuples
            tuple_probability: 0.10,
            // Elevated fixed-array probability — more arrays to call methods on
            fixed_array_probability: 0.20,
            // Some struct destructuring
            struct_destructure_probability: 0.12,
            // Some class destructuring
            class_destructure_probability: 0.10,
            // Some discards
            discard_probability: 0.05,
            // Some early returns
            early_return_probability: 0.12,
            // Some else-if chains
            else_if_probability: 0.25,
            // Some static method calls
            static_call_probability: 0.25,
            // Elevated array mutation — push and index assignment for stdlib stress
            array_index_assign_probability: 0.15,
            array_push_probability: 0.15,
            array_index_compound_assign_probability: 0.15,
            // High mutable array probability — more mutable arrays for mutation ops
            mutable_array_probability: 0.6,
            // Elevated instance method calls for method chaining
            method_call_probability: 0.20,
            // Some interface dispatch
            interface_dispatch_probability: 0.10,
            // Elevated match on i64 variables
            match_probability: 0.10,
            // Elevated string match — exercises string comparison paths
            string_match_probability: 0.12,
            // Some when-expression let-bindings
            when_let_probability: 0.08,
            // Some nested loops
            nested_loop_probability: 0.06,
            // Some union match
            union_match_probability: 0.08,
            // High iterator map/filter — the core of this profile
            iter_map_filter_probability: 0.25,
            // Some interface function calls for vtable dispatch on stdlib types
            iface_function_call_probability: 0.08,
            // Some generic closure+interface chains
            generic_closure_interface_probability: 0.08,
            // Elevated empty array iter (~8%) — stdlib focus stresses iterator boundaries
            empty_array_iter_probability: 0.08,
            // Some match-closure-arm for variety
            match_closure_arm_probability: 0.08,
            range_iter_probability: 0.10,
            // Some field-closure-let for stdlib variety
            field_closure_let_probability: 0.06,
        },
        // Destructured imports are disabled due to a compiler bug (vol-vzjx):
        // Module-level destructured imports fail when the module is transitively imported.
        // Re-enable at ~0.30 once the bug is fixed.
        destructured_import_probability: 0.0,
        // ~20% expression-bodied functions
        expr_body_probability: 0.20,
    };

    Profile { plan, emit }
}

/// Closures-heavy profile - stress lambda/closure and function type codegen.
///
/// This profile generates code emphasizing:
/// - Lambda expressions as arguments and return values
/// - Higher-order functions (functions taking/returning functions)
/// - Expression-bodied functions (=> syntax)
/// - Method chains with closures (map, filter, reduce)
/// - Iterator pipelines with closure-heavy transforms
/// - Elevated match/when expression probabilities (closures in arms)
fn closures_heavy_profile() -> Profile {
    let plan = PlanConfig {
        // Moderate structure — focus is on function bodies, not module layout
        layers: 2,
        modules_per_layer: 3,

        structs_per_module: (1, 2),
        classes_per_module: (1, 3),
        interfaces_per_module: (1, 2),
        errors_per_module: (0, 1),
        // Many functions to maximize lambda/closure opportunities
        functions_per_module: (4, 8),
        globals_per_module: (1, 2),

        fields_per_struct: (1, 3),
        fields_per_class: (2, 4),
        methods_per_class: (2, 4),
        static_methods_per_class: (0, 1),
        static_methods_per_struct: (0, 1),
        methods_per_interface: (1, 3),
        fields_per_error: (0, 2),

        // More params = more closure opportunities in generated bodies
        params_per_function: (2, 5),

        // Moderate generics
        type_params_per_class: (0, 1),
        type_params_per_interface: (0, 1),
        type_params_per_function: (0, 1),
        constraints_per_type_param: (0, 1),

        interface_extends_probability: 0.3,
        implement_blocks_per_module: (1, 2),

        cross_layer_import_probability: 0.2,
        enable_diamond_dependencies: false,

        // Elevated generator probability — generators produce iterators
        // that are consumed with closure-heavy chains (map/filter/reduce)
        fallible_probability: 0.10,
        generator_probability: 0.25,
        never_probability: 0.01,
        nested_class_field_probability: 0.15,
        struct_param_probability: 0.05,
        struct_return_probability: 0.05,
        interface_param_probability: 0.10,
        // Moderate GCI functions — closures are the focus here
        generic_closure_interface_fn_probability: 0.10,
        // HIGH closure-returning functions — core focus of this profile
        closure_return_probability: 0.20,
    };

    let emit = EmitConfig {
        stmt_config: StmtConfig {
            expr_config: ExprConfig {
                max_depth: 4,
                binary_probability: 0.35,
                // Elevated conditional expressions — closures in arms
                when_probability: 0.15,
                match_probability: 0.12,
                if_expr_probability: 0.20,
                // HIGH lambda probability — the core focus of this profile
                lambda_probability: 0.35,
                // Elevated method chaining — drives closure usage in chains
                method_chain_probability: 0.30,
                max_chain_depth: 3,
                unreachable_probability: 0.03,
                max_match_arms: 5,
                // Some inline when/if in args — closures + conditional args
                inline_expr_arg_probability: 0.10,
                // Some tuple indexing
                tuple_index_probability: 0.12,
                // ~25% chained coalescing
                chained_coalesce_probability: 0.25,
                // Some string method calls
                string_method_probability: 0.10,
                // ~25% multi-arm when
                multi_arm_when_probability: 0.25,
                // ~8% match guards
                match_guard_probability: 0.08,
                closure_capture_probability: 0.50,
                // ~25% chance to construct a class instance for interface args
                interface_upcast_probability: 0.25,
            },
            max_depth: 3,
            statements_per_block: (2, 4),
            if_probability: 0.20,
            while_probability: 0.10,
            for_probability: 0.15,
            break_continue_probability: 0.08,
            compound_assign_probability: 0.10,
            reassign_probability: 0.10,
            raise_probability: 0.08,
            try_probability: 0.10,
            tuple_probability: 0.10,
            fixed_array_probability: 0.08,
            struct_destructure_probability: 0.10,
            class_destructure_probability: 0.08,
            discard_probability: 0.05,
            early_return_probability: 0.10,
            else_if_probability: 0.25,
            static_call_probability: 0.20,
            array_index_assign_probability: 0.08,
            array_push_probability: 0.06,
            array_index_compound_assign_probability: 0.08,
            mutable_array_probability: 0.4,
            method_call_probability: 0.12,
            interface_dispatch_probability: 0.10,
            match_probability: 0.08,
            string_match_probability: 0.06,
            when_let_probability: 0.08,
            nested_loop_probability: 0.04,
            union_match_probability: 0.08,
            // HIGH iterator map/filter — generates many closure-bearing chains
            iter_map_filter_probability: 0.25,
            // Some interface function calls for vtable dispatch
            iface_function_call_probability: 0.08,
            // Some generic closure+interface chains for closure + dispatch combo
            generic_closure_interface_probability: 0.10,
            // Some empty array iter for boundary condition variety
            empty_array_iter_probability: 0.06,
            // HIGH match-closure-arm — closures from match arms are core to this profile
            match_closure_arm_probability: 0.15,
            range_iter_probability: 0.06,
            // HIGH field-closure-let — closure capturing struct/class fields is core
            field_closure_let_probability: 0.12,
        },
        destructured_import_probability: 0.0,
        // HIGH expression-body — exercises => lambda-like syntax on functions
        expr_body_probability: 0.40,
    };

    Profile { plan, emit }
}

/// Fallible-heavy profile - stress fallible functions, try/raise patterns, error handling.
///
/// This profile generates code emphasizing:
/// - Many error types per module (2-4) to provide diverse error payloads
/// - High fallible function probability (~60% of non-generic functions)
/// - Frequent raise statements inside fallible function bodies
/// - Frequent try expressions calling other fallible functions
/// - Early returns with raise for guard-style error handling
/// - No generics (fallible functions require no type params, so disabling
///   generics maximizes the proportion of functions that become fallible)
///
/// Structurally moderate (2 layers, 4 modules per layer) -- the focus is
/// on exercising fallible codegen paths (error coercion, try propagation,
/// raise lowering, fallible return type checking), not module breadth.
///
/// Target: stress fallible return type planning, raise/try emission,
/// error type field construction, and match-on-fallible unwrapping.
fn fallible_heavy_profile() -> Profile {
    let plan = PlanConfig {
        // Moderate module structure -- focus is on fallible functions, not module graph
        layers: 2,
        modules_per_layer: 4,

        // Some structs for variety
        structs_per_module: (1, 2),
        // Moderate classes -- some methods will be fallible-callers
        classes_per_module: (2, 3),
        // Some interfaces for variety
        interfaces_per_module: (1, 2),
        // HIGH error count -- every module needs plenty of error types for
        // fallible functions to use as their error channel
        errors_per_module: (2, 4),
        // Many functions -- maximizes number of fallible function sites
        functions_per_module: (5, 8),
        // Some globals
        globals_per_module: (1, 3),

        // Class/interface/struct structure
        fields_per_struct: (2, 4),
        fields_per_class: (2, 4),
        methods_per_class: (2, 3),
        static_methods_per_class: (0, 1),
        static_methods_per_struct: (0, 1),
        methods_per_interface: (1, 3),
        // Rich error fields so error constructors are non-trivial
        fields_per_error: (2, 4),

        // Moderate function parameters
        params_per_function: (1, 4),

        // NO generics -- fallible return types are only assigned to non-generic
        // functions, so eliminating generics maximizes fallible coverage
        type_params_per_class: (0, 0),
        type_params_per_interface: (0, 0),
        type_params_per_function: (0, 0),
        constraints_per_type_param: (0, 0),

        // Some interface relationships for variety
        interface_extends_probability: 0.3,
        implement_blocks_per_module: (1, 2),

        // Standard imports
        cross_layer_import_probability: 0.3,
        enable_diamond_dependencies: true,

        // HIGH fallible probability -- the core focus of this profile.
        // ~60% of functions will have fallible return types.
        fallible_probability: 0.60,
        // No generators -- keep focus on fallible paths
        generator_probability: 0.0,
        // Some never-returning functions for unreachable-after-raise patterns
        never_probability: 0.03,
        // Moderate nested class fields for variety
        nested_class_field_probability: 0.15,
        struct_param_probability: 0.08,
        struct_return_probability: 0.08,
        // Some interface-typed params for variety
        interface_param_probability: 0.08,
        // No GCI functions -- focus on fallible paths
        generic_closure_interface_fn_probability: 0.0,
        // No closure-returning functions -- focus on fallible paths
        closure_return_probability: 0.0,
    };

    let emit = EmitConfig {
        stmt_config: StmtConfig {
            expr_config: ExprConfig {
                // Moderate expression depth
                max_depth: 3,
                // Standard binary expressions
                binary_probability: 0.35,
                // Some when/match/if expressions for variety
                when_probability: 0.12,
                match_probability: 0.10,
                if_expr_probability: 0.15,
                // Some lambdas for variety
                lambda_probability: 0.10,
                // Standard method chaining
                method_chain_probability: 0.15,
                max_chain_depth: 2,
                // Some unreachable
                unreachable_probability: 0.05,
                max_match_arms: 5,
                // Some inline expressions in args
                inline_expr_arg_probability: 0.10,
                // Some tuple indexing
                tuple_index_probability: 0.10,
                // ~25% chained coalescing
                chained_coalesce_probability: 0.25,
                // Some string methods
                string_method_probability: 0.10,
                // ~25% multi-arm when
                multi_arm_when_probability: 0.25,
                // ~10% match guards
                match_guard_probability: 0.10,
                closure_capture_probability: 0.20,
                // ~25% chance to construct a class instance for interface args
                interface_upcast_probability: 0.25,
            },
            // Moderate statement depth -- enough for if-raise guard patterns
            max_depth: 3,
            // Reasonable statements per block
            statements_per_block: (2, 4),
            // Standard control flow
            if_probability: 0.25,
            while_probability: 0.10,
            for_probability: 0.15,
            break_continue_probability: 0.08,
            compound_assign_probability: 0.10,
            reassign_probability: 0.10,
            // HIGH raise probability -- the core focus: raise in fallible bodies
            raise_probability: 0.30,
            // HIGH try probability -- the core focus: try when calling fallible funcs
            try_probability: 0.35,
            // Some tuples
            tuple_probability: 0.10,
            // Some fixed arrays
            fixed_array_probability: 0.08,
            // Some struct destructuring
            struct_destructure_probability: 0.10,
            // Some class destructuring
            class_destructure_probability: 0.08,
            // Some discards -- useful for discarding fallible results
            discard_probability: 0.08,
            // Elevated early returns -- guard-style raise-then-return patterns
            early_return_probability: 0.20,
            // Some else-if chains for multi-condition error checking
            else_if_probability: 0.30,
            // Some static method calls
            static_call_probability: 0.20,
            // Some array mutation
            array_index_assign_probability: 0.08,
            array_push_probability: 0.05,
            array_index_compound_assign_probability: 0.08,
            mutable_array_probability: 0.3,
            // Some instance method calls
            method_call_probability: 0.10,
            // Some interface dispatch
            interface_dispatch_probability: 0.08,
            // Some match expressions
            match_probability: 0.08,
            // Some string match
            string_match_probability: 0.06,
            // Some when-expression let-bindings
            when_let_probability: 0.06,
            // Some nested loops
            nested_loop_probability: 0.04,
            // Some union match
            union_match_probability: 0.08,
            // Some iterator map/filter
            iter_map_filter_probability: 0.08,
            // Some interface function calls
            iface_function_call_probability: 0.08,
            // No generic closure+interface chains in fallible-heavy (no generics)
            generic_closure_interface_probability: 0.0,
            // Some empty array iter for boundary condition variety
            empty_array_iter_probability: 0.04,
            // Some match-closure-arm for variety
            match_closure_arm_probability: 0.06,
            range_iter_probability: 0.04,
            // Some field-closure-let for variety
            field_closure_let_probability: 0.04,
        },
        // Destructured imports are disabled due to a compiler bug (vol-vzjx)
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
        // Expression nesting depth (5+ for meaningful depth)
        assert!(
            profile.emit.stmt_config.expr_config.max_depth >= 5,
            "expression max_depth should be >= 5 for deep nesting"
        );
        // Statement nesting depth
        assert!(
            profile.emit.stmt_config.max_depth >= 4,
            "statement max_depth should be >= 4 for deep nesting"
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

    #[test]
    fn fallible_heavy_profile_exists() {
        let profile = get_profile("fallible-heavy").expect("fallible-heavy profile should exist");

        // High fallible probability (>= 0.5)
        assert!(
            profile.plan.fallible_probability >= 0.5,
            "fallible_probability should be >= 0.5 for fallible-heavy"
        );

        // Many error types per module (min >= 2)
        assert!(
            profile.plan.errors_per_module.0 >= 2,
            "errors_per_module min should be >= 2 for fallible-heavy"
        );

        // High raise probability (>= 0.25)
        assert!(
            profile.emit.stmt_config.raise_probability >= 0.25,
            "raise_probability should be >= 0.25 for fallible-heavy"
        );

        // High try probability (>= 0.25)
        assert!(
            profile.emit.stmt_config.try_probability >= 0.25,
            "try_probability should be >= 0.25 for fallible-heavy"
        );

        // No generics (fallible functions require no type params)
        assert_eq!(
            profile.plan.type_params_per_class,
            (0, 0),
            "type_params_per_class should be (0,0) for fallible-heavy"
        );
        assert_eq!(
            profile.plan.type_params_per_function,
            (0, 0),
            "type_params_per_function should be (0,0) for fallible-heavy"
        );
    }

    #[test]
    fn available_profiles_includes_fallible_heavy() {
        let profiles = available_profiles();
        assert!(
            profiles.contains(&"fallible-heavy"),
            "available_profiles should include fallible-heavy"
        );
    }

    #[test]
    fn unknown_profile_error_includes_fallible_heavy() {
        let result = get_profile("nonexistent");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.to_string().contains("fallible-heavy"),
            "error message should mention fallible-heavy profile"
        );
    }
}
