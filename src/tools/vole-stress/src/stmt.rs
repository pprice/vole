//! Grammar-based statement generation.
//!
//! This module generates type-correct Vole statements using grammar rules.
//! Statements are generated with depth limits and proper control flow.

use rand::Rng;

use crate::expr::{ExprConfig, ExprContext, ExprGenerator, get_chainable_methods};
use crate::symbols::{
    ClassInfo, FunctionInfo, InterfaceInfo, ModuleId, ParamInfo, PrimitiveType, StaticMethodInfo,
    SymbolId, SymbolKind, SymbolTable, TypeInfo, TypeParam,
};

/// Configuration for statement generation.
#[derive(Debug, Clone)]
pub struct StmtConfig {
    /// Configuration for expression generation.
    pub expr_config: ExprConfig,
    /// Maximum nesting depth for statements.
    pub max_depth: usize,
    /// Number of statements per block (range).
    pub statements_per_block: (usize, usize),
    /// Probability of generating an if statement.
    pub if_probability: f64,
    /// Probability of generating a while loop.
    pub while_probability: f64,
    /// Probability of generating a for loop.
    pub for_probability: f64,
    /// Probability of generating break/continue inside loops.
    pub break_continue_probability: f64,
    /// Probability of generating a compound assignment (+=, -=, *=).
    pub compound_assign_probability: f64,
    /// Probability of generating a direct variable reassignment (x = new_value).
    pub reassign_probability: f64,
    /// Probability of generating a raise statement in fallible functions.
    pub raise_probability: f64,
    /// Probability of generating a try expression when calling fallible functions.
    pub try_probability: f64,
    /// Probability of generating a tuple let-binding with destructuring.
    pub tuple_probability: f64,
    /// Probability of generating a fixed-size array let-binding with destructuring.
    pub fixed_array_probability: f64,
    /// Probability of generating a struct let-binding with destructuring.
    /// When a struct-typed variable is in scope, this probability controls
    /// whether we destructure it into its field bindings.
    pub struct_destructure_probability: f64,
    /// Probability of generating a class let-binding with destructuring.
    /// When a class-typed variable is in scope, this probability controls
    /// whether we destructure it into its field bindings.
    /// E.g., `let { x, y } = classInstance`
    pub class_destructure_probability: f64,
    /// Probability of generating a discard expression (_ = expr) statement.
    pub discard_probability: f64,
    /// Probability of generating an early return statement in function bodies.
    pub early_return_probability: f64,
    /// Probability of generating else-if chains in if statements.
    /// When an if statement is generated, this probability controls whether
    /// it becomes an if-else-if chain instead of a simple if/else.
    pub else_if_probability: f64,
    /// Probability of using a static method call instead of direct construction
    /// when instantiating a class with static methods. Set to 0.0 to disable.
    pub static_call_probability: f64,
    /// Probability of generating an array index assignment (`arr[i] = expr`)
    /// when mutable dynamic arrays are in scope. Set to 0.0 to disable.
    pub array_index_assign_probability: f64,
    /// Probability of generating an `arr.push(value)` statement
    /// when mutable dynamic arrays are in scope. Set to 0.0 to disable.
    pub array_push_probability: f64,
    /// Probability of generating an array index compound assignment (`arr[i] += expr`)
    /// when mutable dynamic arrays with numeric element types are in scope.
    pub array_index_compound_assign_probability: f64,
    /// Probability that `generate_array_let` produces a `let mut` binding.
    pub mutable_array_probability: f64,
    /// Probability of generating an instance method call on a class-typed local.
    /// When class-typed locals are in scope, this controls generating
    /// `instance.method(args)` calls. Set to 0.0 to disable.
    pub method_call_probability: f64,
    /// Probability of generating a method call on an interface-typed variable
    /// (vtable dispatch). Set to 0.0 to disable.
    pub interface_dispatch_probability: f64,
    /// Probability of generating a `let x = match var { ... }` statement
    /// when i64-typed variables are in scope. Set to 0.0 to disable.
    pub match_probability: f64,
    /// Probability of generating a `let x = match str_var { "a" => ..., _ => ... }`
    /// statement when string-typed variables are in scope. Set to 0.0 to disable.
    pub string_match_probability: f64,
    /// Probability of generating a `let x = when { cond => val, ... }` statement.
    /// Uses boolean conditions with a wildcard default arm. Set to 0.0 to disable.
    pub when_let_probability: f64,
    /// Probability of generating nested for-loops with break/continue in the
    /// inner loop. This exercises complex control flow paths in the compiler
    /// (multiple loop scopes, break/continue targeting the correct loop).
    /// Set to 0.0 to disable.
    pub nested_loop_probability: f64,
    /// Probability of generating a `let x = match union_var { Type1 => ..., Type2 => ... }`
    /// statement when union-typed variables are in scope. Exercises the match-on-union
    /// codepath with type-pattern arms. Set to 0.0 to disable.
    pub union_match_probability: f64,
    /// Probability of generating an iterator map/filter let-binding when
    /// array-typed variables are in scope. Produces expressions like:
    /// `let x = arr.iter().map((x) => x * 2).collect()`
    /// `let x = arr.iter().filter((x) => x > 0).collect()`
    /// Set to 0.0 to disable.
    pub iter_map_filter_probability: f64,
    /// Probability of generating a call to a free function that has an
    /// interface-typed parameter. This exercises the codegen path where a
    /// class instance is passed where an interface type is expected (implicit
    /// upcast at the call site). Set to 0.0 to disable.
    pub iface_function_call_probability: f64,
    /// Probability of generating a generic-closure-interface iterator chain.
    /// When inside a generic function with: (a) a type-param-typed parameter
    /// with interface constraints, (b) a function-typed parameter, and (c) an
    /// array parameter, generates an iterator chain that combines the closure
    /// parameter AND interface method dispatch on the constrained type param.
    /// E.g.: `items.iter().map(transform).filter((n: i64) => n > criterion.threshold()).collect()`
    /// Set to 0.0 to disable.
    pub generic_closure_interface_probability: f64,
    /// Probability of generating an empty-array-through-iterator-chain pattern.
    /// Creates `let arr: [T] = []` then runs an iterator chain on it
    /// (map/filter/collect/count/sum/first/last/reduce), stressing boundary
    /// conditions around zero-length collections. Set to 0.0 to disable.
    pub empty_array_iter_probability: f64,
    /// Probability of generating a match expression whose arms produce closures
    /// that capture surrounding variables. The resulting closure is then either
    /// immediately invoked or passed to an iterator chain (.map). This exercises:
    /// - Closure creation inside match arms (multiple codegen paths per arm)
    /// - Variable capture scope interaction with match arm expressions
    /// - Function-typed match results used in higher-order contexts
    /// Set to 0.0 to disable.
    pub match_closure_arm_probability: f64,
    /// Probability of generating a range-based iterator chain let-binding.
    /// Produces expressions like `(0..10).iter().map((x) => x * 2).collect()`
    /// or `(1..=5).iter().filter((x) => x > 2).sum()`. This exercises a
    /// different iterator source codegen path (range iterators vs array iterators).
    /// Range elements are always i64, so all numeric iterator operations apply.
    /// Set to 0.0 to disable.
    pub range_iter_probability: f64,
    /// Probability of generating a closure that captures a field value extracted
    /// from a class or struct instance in scope. The closure is then either
    /// immediately invoked or passed to an iterator `.map()` chain. This
    /// exercises the interaction between:
    /// - Field access on class/struct instances
    /// - Closure capture of the extracted field value
    /// - Higher-order usage (direct invocation or iterator chain)
    /// Requires a class/struct-typed local with at least one primitive field.
    /// Set to 0.0 to disable.
    pub field_closure_let_probability: f64,
    /// Probability of generating a sentinel union let-binding with match or is-check.
    /// Creates `let x: PrimType | Sentinel = ...` then matches on the union or
    /// uses `x is Sentinel` in an if-expression. Exercises sentinel type codegen
    /// paths (union with sentinel, match on sentinel arm, is-check narrowing).
    /// Set to 0.0 to disable.
    pub sentinel_union_probability: f64,
    /// Probability of generating an optional destructure match let-binding.
    /// Creates `let x: ClassName? = ClassName { ... }` (or nil), then generates
    /// `let result = match x { ClassName { field1, field2 } => expr, nil => default }`.
    /// Exercises optional type + destructuring pattern match codegen paths.
    /// Set to 0.0 to disable.
    pub optional_destructure_match_probability: f64,
    /// Probability of generating a closure that captures a sentinel union variable.
    /// Creates a `PrimType | Sentinel` union, then a closure that captures it and
    /// uses `when { var is Sentinel => ..., _ => ... }` internally. Exercises the
    /// interaction between closure capture and sentinel union dispatch codegen.
    /// Set to 0.0 to disable.
    pub sentinel_closure_capture_probability: f64,

    /// Probability of generating a closure that captures a whole struct variable
    /// and accesses multiple fields inside the closure body. This exercises the
    /// interaction between struct value capture in closure environments and field
    /// access through captured aggregates.
    /// Set to 0.0 to disable.
    pub closure_struct_capture_probability: f64,

    /// Probability of generating a nested closure pattern where one closure
    /// captures and invokes another closure. This exercises the interaction
    /// between closure capture of function-typed values and indirect invocation
    /// through captured closure pointers.
    /// Set to 0.0 to disable.
    pub nested_closure_capture_probability: f64,

    /// Probability of generating a string interpolation let-binding.
    /// Creates strings with `{expr}` interpolations using variables in scope.
    /// Exercises the parser's handling of nested expressions inside strings
    /// and the codegen for string formatting/concatenation.
    /// Set to 0.0 to disable.
    pub string_interpolation_probability: f64,

    /// Probability of generating a method call result used in a match expression.
    /// Calls a class/interface method that returns i64, then uses the result
    /// in a match with multiple arms. Exercises the interaction between method
    /// dispatch and match codegen.
    /// Set to 0.0 to disable.
    pub match_on_method_result_probability: f64,

    /// Probability of generating an iterator-map that calls a class method
    /// inside the closure. Requires both an i64 array and a class instance
    /// with an i64-returning method in scope.
    /// Pattern: `let r = arr.iter().map((x: i64) -> i64 => inst.method(x)).collect()`
    /// Set to 0.0 to disable.
    pub iter_method_map_probability: f64,

    /// Probability of generating a `"a,b,c".split(",").collect()` let-binding.
    /// Creates a `[string]` array from splitting a string literal. Exercises
    /// string method codegen, iterator-to-array collect, and string arrays.
    /// Set to 0.0 to disable.
    pub string_split_probability: f64,

    /// Probability of generating a string method call let-binding when string
    /// variables are in scope. Produces patterns like:
    /// - `let n = str.length()` (→ i64)
    /// - `let b = str.contains("x")` (→ bool)
    /// - `let b = str.starts_with("x")` (→ bool)
    /// - `let s = str.trim()` (→ string)
    /// - `let s = str.to_upper()` (→ string)
    /// Exercises string method dispatch codegen paths.
    /// Set to 0.0 to disable.
    pub string_method_probability: f64,

    /// Probability of generating an iterator predicate let-binding.
    /// Produces `let b = arr.iter().any((x) => x > 0)` or `.all(...)` patterns
    /// that return bool. Exercises iterator predicate codegen paths.
    /// Set to 0.0 to disable.
    pub iter_predicate_probability: f64,

    /// Probability of generating an iterator chunks/windows let-binding.
    /// Produces `.chunks(N).count()`, `.windows(N).count()`, or
    /// `.chunks(N).flatten().collect()` patterns.
    /// Set to 0.0 to disable.
    pub iter_chunks_windows_probability: f64,

    /// Probability of generating a checked/wrapping/saturating arithmetic call.
    /// Requires that the module has imported `std:lowlevel` (controlled by
    /// `has_lowlevel_import` on StmtContext). Generates patterns like:
    /// - `let x = wrapping_add(a, b)` (wrapping on overflow)
    /// - `let x = saturating_add(a, b)` (clamp on overflow)
    /// - `let x = checked_add(a, b) ?? 0` (nil on overflow, unwrap with default)
    /// Exercises intrinsic function codegen paths across integer types.
    /// Set to 0.0 to disable.
    pub checked_arithmetic_probability: f64,
}

impl Default for StmtConfig {
    fn default() -> Self {
        Self {
            expr_config: ExprConfig::default(),
            max_depth: 2,
            statements_per_block: (1, 3),
            if_probability: 0.2,
            while_probability: 0.1,
            for_probability: 0.15,
            break_continue_probability: 0.12,
            compound_assign_probability: 0.15,
            reassign_probability: 0.15,
            raise_probability: 0.10,
            try_probability: 0.12,
            tuple_probability: 0.10,
            fixed_array_probability: 0.10,
            struct_destructure_probability: 0.12,
            class_destructure_probability: 0.10,
            discard_probability: 0.05,
            early_return_probability: 0.15,
            else_if_probability: 0.3,
            static_call_probability: 0.3,
            array_index_assign_probability: 0.10,
            array_push_probability: 0.08,
            array_index_compound_assign_probability: 0.10,
            mutable_array_probability: 0.4,
            method_call_probability: 0.12,
            interface_dispatch_probability: 0.10,
            match_probability: 0.08,
            string_match_probability: 0.06,
            when_let_probability: 0.08,
            nested_loop_probability: 0.06,
            union_match_probability: 0.08,
            iter_map_filter_probability: 0.08,
            iface_function_call_probability: 0.08,
            generic_closure_interface_probability: 0.0,
            empty_array_iter_probability: 0.0,
            match_closure_arm_probability: 0.0,
            range_iter_probability: 0.0,
            field_closure_let_probability: 0.0,
            sentinel_union_probability: 0.0,
            optional_destructure_match_probability: 0.0,
            sentinel_closure_capture_probability: 0.0,
            closure_struct_capture_probability: 0.0,
            nested_closure_capture_probability: 0.0,
            string_interpolation_probability: 0.0,
            match_on_method_result_probability: 0.0,
            iter_method_map_probability: 0.0,
            string_split_probability: 0.0,
            string_method_probability: 0.0,
            iter_predicate_probability: 0.0,
            iter_chunks_windows_probability: 0.0,
            checked_arithmetic_probability: 0.0,
        }
    }
}

/// Context for statement generation.
#[allow(dead_code)]
pub struct StmtContext<'a> {
    /// Parameters in scope.
    pub params: &'a [ParamInfo],
    /// Local variables (name, type, is_mutable).
    pub locals: Vec<(String, TypeInfo, bool)>,
    /// Symbol table for type lookups.
    pub table: &'a SymbolTable,
    /// The module being generated (for class lookups).
    pub module_id: Option<ModuleId>,
    /// Whether we're in a loop (break/continue valid).
    pub in_loop: bool,
    /// Whether the innermost loop is a while loop (continue would skip increment).
    pub in_while_loop: bool,
    /// Whether this function is fallible.
    pub is_fallible: bool,
    /// The error type of this fallible function (if any).
    pub fallible_error_type: Option<TypeInfo>,
    /// Counter for generating unique local variable names.
    pub local_counter: usize,
    /// Name of the function currently being generated (to prevent self-recursion).
    pub current_function_name: Option<String>,
    /// Symbol ID of the free function currently being generated.
    /// When set, only free functions with a lower symbol ID may be called,
    /// preventing mutual recursion between free functions.
    pub current_function_sym_id: Option<SymbolId>,
    /// The class whose method body is being generated (to prevent mutual recursion).
    /// When set, method calls on instances of this class are suppressed.
    pub current_class_sym_id: Option<(ModuleId, SymbolId)>,
    /// Variables that should not be modified by compound assignments.
    /// Used to protect while-loop counter and guard variables from modification.
    pub protected_vars: Vec<String>,
    /// The effective return type (success type for fallible functions).
    /// Set when generating function bodies to enable early returns.
    pub return_type: Option<TypeInfo>,
    /// Type parameters of the current function (for generic functions).
    /// Used to pass constraints to expression generation for interface method calls.
    pub type_params: Vec<TypeParam>,
    /// Whether `std:lowlevel` functions (wrapping_add, checked_add, etc.) are
    /// available in this module. Set by the emitter when the module imports lowlevel.
    pub has_lowlevel_import: bool,
}

impl<'a> StmtContext<'a> {
    /// Create a new statement context (without module context).
    #[cfg(test)]
    pub fn new(params: &'a [ParamInfo], table: &'a SymbolTable) -> Self {
        Self {
            params,
            locals: Vec::new(),
            table,
            module_id: None,
            in_loop: false,
            in_while_loop: false,
            is_fallible: false,
            fallible_error_type: None,
            local_counter: 0,
            current_function_name: None,
            current_function_sym_id: None,
            current_class_sym_id: None,
            protected_vars: Vec::new(),
            return_type: None,
            type_params: Vec::new(),
            has_lowlevel_import: false,
        }
    }

    /// Create a new statement context with a module ID for class lookups.
    pub fn with_module(
        params: &'a [ParamInfo],
        table: &'a SymbolTable,
        module_id: ModuleId,
    ) -> Self {
        Self {
            params,
            locals: Vec::new(),
            table,
            module_id: Some(module_id),
            in_loop: false,
            in_while_loop: false,
            is_fallible: false,
            fallible_error_type: None,
            local_counter: 0,
            current_function_name: None,
            current_function_sym_id: None,
            current_class_sym_id: None,
            protected_vars: Vec::new(),
            return_type: None,
            has_lowlevel_import: false,
            type_params: Vec::new(),
        }
    }

    /// Create an expression context from this statement context.
    fn to_expr_context(&self) -> ExprContext<'_> {
        let locals_for_expr: Vec<(String, TypeInfo)> = self
            .locals
            .iter()
            .map(|(name, ty, _)| (name.clone(), ty.clone()))
            .collect();
        // We need to handle the lifetime issue by creating a temporary
        ExprContext {
            params: self.params,
            locals: Box::leak(locals_for_expr.into_boxed_slice()),
            table: self.table,
            type_params: Box::leak(self.type_params.clone().into_boxed_slice()),
        }
    }

    /// Generate a new unique local variable name.
    pub fn new_local_name(&mut self) -> String {
        let name = format!("local{}", self.local_counter);
        self.local_counter += 1;
        name
    }

    /// Add a local variable to scope.
    pub fn add_local(&mut self, name: String, ty: TypeInfo, is_mutable: bool) {
        self.locals.push((name, ty, is_mutable));
    }

    /// Get mutable local variables of a specific type.
    #[allow(dead_code)]
    pub fn mutable_locals_of_type(&self, target_type: &TypeInfo) -> Vec<String> {
        self.locals
            .iter()
            .filter(|(_, ty, is_mut)| *is_mut && types_match(ty, target_type))
            .map(|(name, _, _)| name.clone())
            .collect()
    }
}

/// Check if two types match.
#[allow(dead_code)]
fn types_match(a: &TypeInfo, b: &TypeInfo) -> bool {
    match (a, b) {
        (TypeInfo::Primitive(pa), TypeInfo::Primitive(pb)) => pa == pb,
        (TypeInfo::Void, TypeInfo::Void) => true,
        (TypeInfo::Optional(ia), TypeInfo::Optional(ib)) => types_match(ia, ib),
        (TypeInfo::Array(ea), TypeInfo::Array(eb)) => types_match(ea, eb),
        (TypeInfo::FixedArray(ea, sa), TypeInfo::FixedArray(eb, sb)) => {
            sa == sb && types_match(ea, eb)
        }
        (TypeInfo::Tuple(ea), TypeInfo::Tuple(eb)) => {
            ea.len() == eb.len() && ea.iter().zip(eb.iter()).all(|(a, b)| types_match(a, b))
        }
        _ => false,
    }
}

/// Check if a class has at least one field with a primitive type.
fn has_primitive_field(info: &ClassInfo) -> bool {
    info.fields.iter().any(|f| f.field_type.is_primitive())
}

/// Statement generator.
pub struct StmtGenerator<'a, R> {
    rng: &'a mut R,
    config: &'a StmtConfig,
    indent: usize,
}

impl<'a, R: Rng> StmtGenerator<'a, R> {
    /// Create a new statement generator.
    pub fn new(rng: &'a mut R, config: &'a StmtConfig) -> Self {
        Self {
            rng,
            config,
            indent: 0,
        }
    }

    /// Generate a function body with statements and a return.
    ///
    /// Optionally generates an early return inside an if block for functions
    /// with non-void return types. The early return probability is controlled
    /// by `config.early_return_probability`.
    pub fn generate_body(
        &mut self,
        return_type: &TypeInfo,
        ctx: &mut StmtContext,
        depth: usize,
    ) -> Vec<String> {
        let mut lines = Vec::new();
        let stmt_count = self
            .rng
            .gen_range(self.config.statements_per_block.0..=self.config.statements_per_block.1);

        // For fallible functions, use the success type for the return expression
        let effective_return_type = return_type.success_type().clone();

        // Set the return type in context for early return generation
        ctx.return_type = Some(effective_return_type.clone());

        // Generate statements
        for _ in 0..stmt_count {
            let stmt = self.generate_statement(ctx, depth);
            lines.push(stmt);
        }

        // Optionally generate an early return inside an if block for non-void functions
        if !matches!(effective_return_type, TypeInfo::Void)
            && self.rng.gen_bool(self.config.early_return_probability)
        {
            if let Some(early_return_stmt) = self.generate_early_return(ctx) {
                lines.push(early_return_stmt);
            }
        }

        // Generate final return statement (always needed for non-void functions)
        if !matches!(effective_return_type, TypeInfo::Void) {
            let expr_ctx = ctx.to_expr_context();
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            let return_expr = expr_gen.generate(&effective_return_type, &expr_ctx, 0);
            lines.push(format!("return {}", return_expr));
        }

        lines
    }

    /// Generate an early return statement wrapped in an if block.
    ///
    /// Produces a pattern like:
    /// ```vole
    /// if <condition> {
    ///     return <expr>
    /// }
    /// ```
    ///
    /// Returns `None` if the function has a void return type.
    fn generate_early_return(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let return_type = ctx.return_type.as_ref()?;
        if matches!(return_type, TypeInfo::Void) {
            return None;
        }

        let expr_ctx = ctx.to_expr_context();

        // Generate a simple boolean condition (avoid multi-line expressions in if)
        let cond = {
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            expr_gen.generate_simple(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx)
        };

        // Generate the return expression
        let return_expr = {
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            expr_gen.generate(return_type, &expr_ctx, 0)
        };

        let indent = "    ".repeat(self.indent + 1);
        Some(format!(
            "if {} {{\n{}return {}\n{}}}",
            cond,
            indent,
            return_expr,
            "    ".repeat(self.indent)
        ))
    }

    /// Generate a single statement.
    pub fn generate_statement(&mut self, ctx: &mut StmtContext, depth: usize) -> String {
        // At max depth, only generate simple statements
        if depth >= self.config.max_depth {
            return self.generate_let_statement(ctx);
        }

        // Inside loops, occasionally generate break or continue
        if ctx.in_loop && self.rng.gen_bool(self.config.break_continue_probability) {
            return self.generate_break_continue(ctx);
        }

        // In fallible functions, occasionally generate a raise statement
        if ctx.is_fallible && self.rng.gen_bool(self.config.raise_probability) {
            if let Some(stmt) = self.try_generate_raise_statement(ctx) {
                return stmt;
            }
        }

        // Occasionally generate a try expression calling a fallible function
        if self.rng.gen_bool(self.config.try_probability) {
            if let Some(stmt) = self.try_generate_try_let(ctx) {
                return stmt;
            }
        }

        // If mutable numeric locals are in scope, occasionally generate a compound assignment
        if self.has_mutable_numeric_locals(ctx)
            && self.rng.gen_bool(self.config.compound_assign_probability)
        {
            return self.generate_compound_assignment(ctx);
        }

        // If mutable locals are in scope, occasionally generate a direct reassignment
        if self.has_mutable_locals(ctx) && self.rng.gen_bool(self.config.reassign_probability) {
            return self.generate_reassignment(ctx);
        }

        // If mutable dynamic arrays are in scope, occasionally generate index assignment
        if !Self::mutable_dynamic_arrays(ctx).is_empty()
            && self
                .rng
                .gen_bool(self.config.array_index_assign_probability)
        {
            return self.generate_array_index_assignment(ctx);
        }

        // If mutable dynamic arrays are in scope, occasionally generate push
        if !Self::mutable_dynamic_arrays(ctx).is_empty()
            && self.rng.gen_bool(self.config.array_push_probability)
        {
            return self.generate_array_push(ctx);
        }

        // If mutable numeric arrays are in scope, occasionally generate compound assignment
        if !Self::mutable_numeric_arrays(ctx).is_empty()
            && self
                .rng
                .gen_bool(self.config.array_index_compound_assign_probability)
        {
            return self.generate_array_index_compound_assignment(ctx);
        }

        // ~20% chance to call a function-typed parameter if one is in scope
        if self.rng.gen_bool(0.20) {
            if let Some(stmt) = self.try_generate_fn_param_call(ctx) {
                return stmt;
            }
        }

        // Occasionally generate a discard statement (_ = func()) to exercise the syntax
        if self.rng.gen_bool(self.config.discard_probability) {
            if let Some(stmt) = self.try_generate_discard_statement(ctx) {
                return stmt;
            }
        }

        // Occasionally generate a standalone static method call
        if self.rng.gen_bool(self.config.static_call_probability) {
            if let Some(stmt) = self.try_generate_static_call_statement(ctx) {
                return stmt;
            }
        }

        // Occasionally generate an instance method call on a class-typed local
        if self.rng.gen_bool(self.config.method_call_probability) {
            if let Some(stmt) = self.try_generate_method_call(ctx) {
                return stmt;
            }
        }

        // Occasionally generate a method call on an interface-typed variable (vtable dispatch)
        if self
            .rng
            .gen_bool(self.config.interface_dispatch_probability)
        {
            if let Some(stmt) = self.try_generate_interface_method_call(ctx) {
                return stmt;
            }
        }

        // Occasionally call a free function that takes an interface-typed parameter
        if self
            .rng
            .gen_bool(self.config.iface_function_call_probability)
        {
            if let Some(stmt) = self.try_generate_iface_function_call(ctx) {
                return stmt;
            }
        }

        let choice: f64 = self.rng.gen_range(0.0..1.0);

        if choice < self.config.if_probability {
            self.generate_if_statement(ctx, depth)
        } else if choice < self.config.if_probability + self.config.while_probability {
            self.generate_while_statement(ctx, depth)
        } else if choice
            < self.config.if_probability
                + self.config.while_probability
                + self.config.for_probability
        {
            self.generate_for_statement(ctx, depth)
        } else if choice
            < self.config.if_probability
                + self.config.while_probability
                + self.config.for_probability
                + self.config.nested_loop_probability
        {
            self.generate_nested_for_loop(ctx, depth)
        } else {
            // Default to let statement
            self.generate_let_statement(ctx)
        }
    }

    /// Generate a let statement.
    fn generate_let_statement(&mut self, ctx: &mut StmtContext) -> String {
        // Occasionally generate a lambda let-binding to exercise closures
        if self
            .rng
            .gen_bool(self.config.expr_config.lambda_probability)
        {
            return self.generate_lambda_let(ctx);
        }

        // ~15% chance to generate a class-typed local for field access
        if self.rng.gen_bool(0.15) {
            if let Some(stmt) = self.try_generate_class_let(ctx) {
                return stmt;
            }
        }

        // Chance to generate an interface-typed local via upcast (for vtable dispatch)
        if self
            .rng
            .gen_bool(self.config.interface_dispatch_probability)
        {
            if let Some(stmt) = self.try_generate_interface_let(ctx) {
                return stmt;
            }
        }

        // ~10% chance to generate a struct-typed local for struct usage patterns
        if self.rng.gen_bool(0.10) {
            if let Some(stmt) = self.try_generate_struct_let(ctx) {
                return stmt;
            }
        }

        // ~12% chance to generate an array-typed local for array indexing
        if self.rng.gen_bool(0.12) {
            return self.generate_array_let(ctx);
        }

        // Iterator map/filter on array variables in scope
        if self.rng.gen_bool(self.config.iter_map_filter_probability) {
            if let Some(stmt) = self.try_generate_iter_map_filter_let(ctx) {
                return stmt;
            }
        }

        // Empty array through iterator chain — boundary condition stress test.
        // Creates `let arr: [T] = []` then chains .iter().op().terminal().
        if self.rng.gen_bool(self.config.empty_array_iter_probability) {
            return self.generate_empty_array_iter_let(ctx);
        }

        // Empty string iteration — boundary condition stress test.
        // Creates `let s = ""` then chains .iter().op().terminal().
        if self.rng.gen_bool(self.config.empty_array_iter_probability) {
            return self.generate_empty_string_iter_let(ctx);
        }

        // Wildcard-only match — degenerate match with only `_ => expr`.
        if self.rng.gen_bool(0.03) {
            if let Some(stmt) = self.generate_wildcard_only_match(ctx) {
                return stmt;
            }
        }

        // Nested when expressions — when inside when arms.
        if self.rng.gen_bool(0.03) {
            if let Some(stmt) = self.try_generate_nested_when_let(ctx) {
                return stmt;
            }
        }

        // Zero-take / max-skip — iterator chains that produce empty results.
        if self.rng.gen_bool(0.03) {
            if let Some(stmt) = self.try_generate_empty_iter_edge(ctx) {
                return stmt;
            }
        }

        // Chained string method calls — str.to_upper().trim().length() etc.
        if self.rng.gen_bool(0.04) {
            if let Some(stmt) = self.try_generate_chained_string_methods(ctx) {
                return stmt;
            }
        }

        // Match on array element — match arr[0] { ... }
        if self.rng.gen_bool(0.03) {
            if let Some(stmt) = self.try_generate_match_array_elem(ctx) {
                return stmt;
            }
        }

        // Match on iterator terminal — match arr.iter().count() { ... }
        if self.rng.gen_bool(0.03) {
            if let Some(stmt) = self.try_generate_match_iter_terminal(ctx) {
                return stmt;
            }
        }

        // Range-based iterator chain — exercises range iterators (different source
        // than array iterators). Generates `(start..end).iter().chain().terminal()`.
        if self.rng.gen_bool(self.config.range_iter_probability) {
            return self.generate_range_iter_let(ctx);
        }

        // Generic closure + interface dispatch in iterator chains.
        // When inside a generic function with a constrained type param, a closure param,
        // and an array in scope, generate a chain like:
        // `items.iter().map(transform).filter((n: i64) => n > criterion.threshold()).collect()`
        if self
            .rng
            .gen_bool(self.config.generic_closure_interface_probability)
        {
            if let Some(stmt) = self.try_generate_generic_closure_interface_chain(ctx) {
                return stmt;
            }
        }

        // Match expression whose arms produce closures capturing surrounding scope.
        // Generates `let f = match var { N => (x) => x + captured, ... }` then
        // either invokes the closure or passes it to an iterator chain.
        if self.rng.gen_bool(self.config.match_closure_arm_probability) {
            if let Some(stmt) = self.try_generate_match_closure_arms(ctx) {
                return stmt;
            }
        }

        // Field-closure-let: extract a primitive field from a class/struct instance,
        // capture it in a closure, and either invoke the closure or pass it to
        // an iterator .map() chain.
        if self.rng.gen_bool(self.config.field_closure_let_probability) {
            if let Some(stmt) = self.try_generate_field_closure_let(ctx) {
                return stmt;
            }
        }

        // String split to array: "a,b,c".split(",").collect()
        if self.rng.gen_bool(self.config.string_split_probability) {
            return self.generate_string_split_let(ctx);
        }

        // String method call: str.length(), str.contains("x"), str.trim(), etc.
        if self.rng.gen_bool(self.config.string_method_probability) {
            if let Some(stmt) = self.try_generate_string_method_let(ctx) {
                return stmt;
            }
        }

        // Checked/wrapping/saturating arithmetic (requires lowlevel import)
        if ctx.has_lowlevel_import
            && self
                .rng
                .gen_bool(self.config.checked_arithmetic_probability)
        {
            return self.generate_checked_arithmetic_let(ctx);
        }

        // Tuple let-binding with destructuring
        if self.rng.gen_bool(self.config.tuple_probability) {
            return self.generate_tuple_let(ctx);
        }

        // Fixed-size array let-binding with destructuring
        if self.rng.gen_bool(self.config.fixed_array_probability) {
            return self.generate_fixed_array_let(ctx);
        }

        // Struct destructuring: if we have a struct-typed variable in scope,
        // destructure it into its fields
        if self
            .rng
            .gen_bool(self.config.struct_destructure_probability)
        {
            if let Some(stmt) = self.try_generate_struct_destructure(ctx) {
                return stmt;
            }
        }

        // Class destructuring: if we have a class-typed variable in scope,
        // destructure it into its fields (let { x, y } = classInstance)
        if self.rng.gen_bool(self.config.class_destructure_probability) {
            if let Some(stmt) = self.try_generate_class_destructure(ctx) {
                return stmt;
            }
        }

        // ~8% chance to generate a struct copy (let copy = structVar)
        if self.rng.gen_bool(0.08) {
            if let Some(stmt) = self.try_generate_struct_copy(ctx) {
                return stmt;
            }
        }

        // Match expression let-binding: let x = match var { 1 => ..., _ => ... }
        if self.rng.gen_bool(self.config.match_probability) {
            if let Some(stmt) = self.try_generate_match_let(ctx) {
                return stmt;
            }
        }

        // String match expression let-binding: let x = match str { "a" => ..., _ => ... }
        if self.rng.gen_bool(self.config.string_match_probability) {
            if let Some(stmt) = self.try_generate_string_match_let(ctx) {
                return stmt;
            }
        }

        // Union match expression let-binding: let x = match union_var { Type1 => ..., ... }
        if self.rng.gen_bool(self.config.union_match_probability) {
            if let Some(stmt) = self.try_generate_union_match_let(ctx) {
                return stmt;
            }
        }

        // Sentinel union let-binding: let x: PrimType | Sentinel = ... then match/is-check
        if self.rng.gen_bool(self.config.sentinel_union_probability) {
            if let Some(stmt) = self.try_generate_sentinel_union_let(ctx) {
                return stmt;
            }
        }

        // Optional destructure match: let x: Type? = ... then match with destructuring
        if self
            .rng
            .gen_bool(self.config.optional_destructure_match_probability)
        {
            if let Some(stmt) = self.try_generate_optional_destructure_match(ctx) {
                return stmt;
            }
        }

        // Sentinel closure capture: closure captures PrimType | Sentinel union variable
        if self
            .rng
            .gen_bool(self.config.sentinel_closure_capture_probability)
        {
            if let Some(stmt) = self.try_generate_sentinel_closure_capture(ctx) {
                return stmt;
            }
        }

        // Closure capturing whole struct and accessing fields inside
        if self
            .rng
            .gen_bool(self.config.closure_struct_capture_probability)
        {
            if let Some(stmt) = self.try_generate_closure_struct_capture(ctx) {
                return stmt;
            }
        }

        // Nested closure capture: closure captures and invokes another closure
        if self
            .rng
            .gen_bool(self.config.nested_closure_capture_probability)
        {
            if let Some(stmt) = self.try_generate_nested_closure_capture(ctx) {
                return stmt;
            }
        }

        // String interpolation let-binding: let s = "prefix {var} suffix"
        if self
            .rng
            .gen_bool(self.config.string_interpolation_probability)
        {
            if let Some(stmt) = self.try_generate_string_interpolation_let(ctx) {
                return stmt;
            }
        }

        // Match on method call result
        if self
            .rng
            .gen_bool(self.config.match_on_method_result_probability)
        {
            if let Some(stmt) = self.try_generate_match_on_method_result(ctx) {
                return stmt;
            }
        }

        // Iterator map using method call on class instance
        if self
            .rng
            .gen_bool(self.config.iter_method_map_probability)
        {
            if let Some(stmt) = self.try_generate_iter_method_map(ctx) {
                return stmt;
            }
        }

        // When expression let-binding: let x = when { cond => val, _ => val }
        if self.rng.gen_bool(self.config.when_let_probability) {
            if let Some(stmt) = self.try_generate_when_let(ctx) {
                return stmt;
            }
        }

        // Iterator predicate: let b = arr.iter().any((x) => x > 0)
        if self.rng.gen_bool(self.config.iter_predicate_probability) {
            if let Some(stmt) = self.try_generate_iter_predicate_let(ctx) {
                return stmt;
            }
        }

        // Iterator chunks/windows: let c = arr.iter().chunks(2).count()
        if self.rng.gen_bool(self.config.iter_chunks_windows_probability) {
            if let Some(stmt) = self.try_generate_iter_chunks_windows_let(ctx) {
                return stmt;
            }
        }

        // ~8% chance to re-iterate: take an existing array local and chain
        // a new iterator operation on it. Exercises iterating over dynamically-
        // created arrays (e.g. results of collect()).
        if self.rng.gen_bool(0.08) {
            if let Some(stmt) = self.try_generate_reiterate_let(ctx) {
                return stmt;
            }
        }

        // ~5% chance: for_each as a standalone statement
        if self.rng.gen_bool(0.05) {
            if let Some(stmt) = self.try_generate_for_each_stmt(ctx) {
                return stmt;
            }
        }

        // ~5% chance: nth with match on optional result
        if self.rng.gen_bool(0.05) {
            if let Some(stmt) = self.try_generate_nth_let(ctx) {
                return stmt;
            }
        }

        // ~5% chance: string iteration (str.iter().chain.terminal)
        if self.rng.gen_bool(0.05) {
            if let Some(stmt) = self.try_generate_string_iter_let(ctx) {
                return stmt;
            }
        }

        // ~4% chance: variable shadowing — re-declare existing variable with new value
        if self.rng.gen_bool(0.04) {
            if let Some(stmt) = self.try_generate_variable_shadow(ctx) {
                return stmt;
            }
        }

        // ~3% chance: assert statement with a tautological condition
        if self.rng.gen_bool(0.03) {
            if let Some(stmt) = self.try_generate_assert_stmt(ctx) {
                return stmt;
            }
        }

        // ~3% chance: match on boolean value
        if self.rng.gen_bool(0.03) {
            if let Some(stmt) = self.try_generate_bool_match_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: dead-code assertion (if false { assert(false) })
        if self.rng.gen_bool(0.02) {
            return self.generate_dead_code_assert();
        }

        // ~2% chance: zero/single-iteration for loop
        if self.rng.gen_bool(0.02) {
            return self.generate_edge_case_for_loop(ctx, 2);
        }

        // ~2% chance: empty array iterator operation
        if self.rng.gen_bool(0.02) {
            return self.generate_empty_array_iter(ctx);
        }

        // ~2% chance: edge-case string split
        if self.rng.gen_bool(0.02) {
            return self.generate_edge_case_split(ctx);
        }

        // ~2% chance: iterator terminal inside while-loop accumulator
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_iter_while_accum(ctx) {
                return stmt;
            }
        }

        // ~2% chance: for-in loop with match on iteration variable
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_for_in_match_accum(ctx) {
                return stmt;
            }
        }

        // ~3% chance: string concatenation with + operator
        if self.rng.gen_bool(0.03) {
            if let Some(stmt) = self.try_generate_string_concat_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: map-to-string-then-reduce (join pattern)
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_map_tostring_reduce(ctx) {
                return stmt;
            }
        }

        // ~2% chance: numeric .to_string() in string expression
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_to_string_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: struct field in string interpolation
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_struct_field_interpolation(ctx) {
                return stmt;
            }
        }

        // ~2% chance: when with iterator predicate condition
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_when_iter_predicate(ctx) {
                return stmt;
            }
        }

        // ~2% chance: closure result in string concat
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_closure_result_concat(ctx) {
                return stmt;
            }
        }

        // ~2% chance: split result in for-in loop
        if self.rng.gen_bool(0.02) {
            return self.generate_split_for_loop(ctx);
        }

        // ~2% chance: for-in loop pushing derived values to mutable array
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_for_push_collect(ctx) {
                return stmt;
            }
        }

        // ~3% chance: array literal with variable elements
        if self.rng.gen_bool(0.03) {
            if let Some(stmt) = self.try_generate_array_from_vars(ctx) {
                return stmt;
            }
        }

        // ~2% chance: multiple pushes onto a mutable array
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_multi_push(ctx) {
                return stmt;
            }
        }

        // ~2% chance: method call on a literal value (string/numeric)
        if self.rng.gen_bool(0.02) {
            return self.generate_literal_method_call(ctx);
        }

        // ~2% chance: nested when-in-when expression
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_nested_when(ctx) {
                return stmt;
            }
        }

        // ~2% chance: match on method call result
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_match_on_method(ctx) {
                return stmt;
            }
        }

        // ~2% chance: struct construction with iterator field values
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_struct_with_iter_fields(ctx) {
                return stmt;
            }
        }

        // ~2% chance: iterator terminal + method chain (e.g., arr.iter().count().to_string())
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_iter_terminal_chain(ctx) {
                return stmt;
            }
        }

        // ~2% chance: when with string method conditions
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_when_string_method_conds(ctx) {
                return stmt;
            }
        }

        // ~2% chance: single-element array operations
        if self.rng.gen_bool(0.02) {
            return self.generate_single_elem_array_ops(ctx);
        }

        // ~2% chance: tautological comparison in when
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_tautological_when(ctx) {
                return stmt;
            }
        }

        // ~2% chance: empty string concatenation edge case
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_empty_string_concat(ctx) {
                return stmt;
            }
        }

        // ~2% chance: last element access via computed index
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_last_elem_access(ctx) {
                return stmt;
            }
        }

        // ~2% chance: for-loop indexed by array length
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_for_length_indexed(ctx) {
                return stmt;
            }
        }

        // ~2% chance: while-loop string building
        if self.rng.gen_bool(0.02) {
            return self.generate_while_string_build(ctx);
        }

        // ~3% chance: compound boolean from numeric comparisons
        if self.rng.gen_bool(0.03) {
            if let Some(stmt) = self.try_generate_compound_bool_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: boolean from length comparisons
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_length_comparison_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: string interpolation with iterator terminal
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_interpolation_with_iter(ctx) {
                return stmt;
            }
        }

        // ~2% chance: reassign from when expression
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_reassign_from_when(ctx) {
                return stmt;
            }
        }

        // ~2% chance: identity arithmetic edge case (x + 0, x * 1, etc.)
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_identity_arithmetic(ctx) {
                return stmt;
            }
        }

        // ~2% chance: string equality edge case (s == s, "" == "", etc.)
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_string_equality_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: modulo edge cases (N % 1 == 0, N % N == 0)
        if self.rng.gen_bool(0.02) {
            return self.generate_modulo_edge_case(ctx);
        }

        // ~2% chance: uniform array operations
        if self.rng.gen_bool(0.02) {
            return self.generate_array_uniform_ops(ctx);
        }

        // ~2% chance: for-loop with when-based accumulation
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_for_when_accumulate(ctx) {
                return stmt;
            }
        }

        // ~2% chance: when with iterator terminals as arm values
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_iter_in_when_arms(ctx) {
                return stmt;
            }
        }

        // ~2% chance: multi-arm when (4+ arms)
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_multi_arm_when(ctx) {
                return stmt;
            }
        }

        // ~2% chance: match with computed arm values
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_match_with_computation(ctx) {
                return stmt;
            }
        }

        // ~2% chance: string replace/replace_all
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_string_replace_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: nested match expression
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_nested_match_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: string length on literal edge cases
        if self.rng.gen_bool(0.02) {
            return self.generate_string_length_edge_cases(ctx);
        }

        // ~2% chance: range check boolean (x > lo && x < hi)
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_range_check_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: for-loop string build with match
        if self.rng.gen_bool(0.02) {
            return self.generate_for_string_build_with_match(ctx);
        }

        // ~2% chance: when with string concat arm values
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_when_with_string_concat_arms(ctx) {
                return stmt;
            }
        }

        // ~2% chance: boolean negation edge cases
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_bool_negation_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: chained methods on literal strings
        if self.rng.gen_bool(0.02) {
            return self.generate_chained_literal_method(ctx);
        }

        // ~2% chance: method call on when result
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_when_result_method(ctx) {
                return stmt;
            }
        }

        // ~2% chance: for-loop building string with when body
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_for_iter_when_string_body(ctx) {
                return stmt;
            }
        }

        // ~2% chance: while false dead code
        if self.rng.gen_bool(0.02) {
            return self.generate_while_false_deadcode(ctx);
        }

        // ~2% chance: division by power of 2
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_power_of_two_div(ctx) {
                return stmt;
            }
        }

        // ~2% chance: string predicate (contains/starts_with/ends_with)
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_string_predicate_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: string interpolation with complex expressions
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_interpolation_expr_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: match on string length
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_match_string_length(ctx) {
                return stmt;
            }
        }

        // ~2% chance: array length guard (safe indexing)
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_array_length_guard(ctx) {
                return stmt;
            }
        }

        // ~2% chance: repeat literal array
        if self.rng.gen_bool(0.02) {
            return self.generate_repeat_literal_let(ctx);
        }

        // ~2% chance: iter().reduce() on array
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_iter_reduce_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: i32 near-boundary operations
        if self.rng.gen_bool(0.02) {
            return self.generate_i32_boundary_safe(ctx);
        }

        // ~2% chance: empty string operations
        if self.rng.gen_bool(0.02) {
            return self.generate_empty_string_ops(ctx);
        }

        // ~2% chance: manual for-loop reduce pattern
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_for_reduce_pattern(ctx) {
                return stmt;
            }
        }

        // ~2% chance: when containing match expression
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_when_match_combo(ctx) {
                return stmt;
            }
        }

        // ~2% chance: string split iteration
        if self.rng.gen_bool(0.02) {
            return self.generate_string_split_for(ctx);
        }

        // ~2% chance: nested when expression with string result
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_nested_when_string_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: .to_string() on numeric values
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_numeric_to_string_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: .substring() on strings
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_substring_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: match with to_string arm values
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_match_to_string_arms(ctx) {
                return stmt;
            }
        }

        // ~2% chance: for loop with string interpolation concat
        if self.rng.gen_bool(0.02) {
            return self.generate_for_interpolation_concat(ctx);
        }

        // ~2% chance: boolean chain expression
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_bool_chain_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: comparison chain expression
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_comparison_chain_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: when with string predicate (contains/starts_with)
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_when_with_contains(ctx) {
                return stmt;
            }
        }

        // ~2% chance: match on array length
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_match_array_length(ctx) {
                return stmt;
            }
        }

        // ~2% chance: sorted collect on array
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_sorted_collect_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: reverse collect on array
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_reverse_collect_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: guarded division (when { b != 0 => a / b, _ => 0 })
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_zero_division_guard(ctx) {
                return stmt;
            }
        }

        // ~2% chance: single-character string operations
        if self.rng.gen_bool(0.02) {
            return self.generate_single_char_string_ops(ctx);
        }

        // ~2% chance: f64 literal arithmetic operations
        if self.rng.gen_bool(0.02) {
            return self.generate_f64_literal_ops_let(ctx);
        }

        // ~2% chance: f64 equality/comparison edge cases
        if self.rng.gen_bool(0.02) {
            return self.generate_f64_comparison_edge_let(ctx);
        }

        // ~2% chance: string with repeated characters operations
        if self.rng.gen_bool(0.02) {
            return self.generate_repeated_string_ops(ctx);
        }

        // ~2% chance: iterator take/skip collect on parameter arrays
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_iter_take_skip_collect_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: when expression with f64 variable conditions
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_when_f64_cond_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: for-range building string via i.to_string()
        if self.rng.gen_bool(0.02) {
            return self.generate_for_range_tostring_build(ctx);
        }

        // ~2% chance: match with when expression in arm values
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_match_when_arm_let(ctx) {
                return stmt;
            }
        }

        // ~2% chance: sorted iteration with accumulation
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_sorted_iter_accum(ctx) {
                return stmt;
            }
        }

        // ~2% chance: filter-collect then iterate with to_string
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_filter_iter_tostring(ctx) {
                return stmt;
            }
        }

        // ~2% chance: when comparing lengths of array and string
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_when_length_compare(ctx) {
                return stmt;
            }
        }

        // ~2% chance: character extraction via substring
        if self.rng.gen_bool(0.02) {
            return self.generate_string_char_at_let(ctx);
        }

        // ~2% chance: range-based iterator with map and collect
        if self.rng.gen_bool(0.02) {
            return self.generate_range_iter_map_collect(ctx);
        }

        // ~2% chance: match on interpolated string length
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_match_interpolation_length(ctx) {
                return stmt;
            }
        }

        // ~2% chance: range for-loop with when body accumulation
        if self.rng.gen_bool(0.02) {
            return self.generate_for_range_when_accum(ctx);
        }

        // ~2% chance: when with to_string in arms
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_when_tostring_arms(ctx) {
                return stmt;
            }
        }

        // ~2% chance: match on sorted array length
        if self.rng.gen_bool(0.02) {
            if let Some(stmt) = self.try_generate_match_sorted_length(ctx) {
                return stmt;
            }
        }

        // ~2% chance: single-element range operations
        if self.rng.gen_bool(0.02) {
            return self.generate_single_elem_range_let(ctx);
        }

        // ~2% chance: whitespace-heavy string operations
        if self.rng.gen_bool(0.02) {
            return self.generate_whitespace_string_ops(ctx);
        }

        // ~10% chance to generate a widening let statement
        // (assign narrower type expression to wider type variable)
        if self.rng.gen_bool(0.10) {
            if let Some(stmt) = self.try_generate_widening_let(ctx) {
                return stmt;
            }
        }

        let name = ctx.new_local_name();
        let is_mutable = self.rng.gen_bool(0.3);
        let ty = self.random_primitive_type();

        let expr_ctx = ctx.to_expr_context();
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let value = expr_gen.generate(&ty, &expr_ctx, 0);

        ctx.add_local(name.clone(), ty.clone(), is_mutable);

        let mutability = if is_mutable { "let mut" } else { "let" };
        // ~15% chance: add explicit type annotation
        if self.rng.gen_bool(0.15) {
            let type_str = ty.to_vole_syntax(ctx.table);
            format!("{} {}: {} = {}", mutability, name, type_str, value)
        } else {
            format!("{} {} = {}", mutability, name, value)
        }
    }

    /// Try to generate a match expression let-binding.
    ///
    /// Finds an i64-typed variable in scope and generates:
    /// ```vole
    /// let result = match var {
    ///     1 => <expr>
    ///     2 => <expr>
    ///     _ => <expr>
    /// }
    /// ```
    ///
    /// Returns `None` if no i64/i32-typed variable is in scope.
    /// Generate an expression for a match arm value: either a simple expression
    /// or (25% of the time) a nested `when` expression to stress-test the
    /// match-arm + when-expression interaction.
    fn generate_match_arm_value(
        &mut self,
        result_type: &TypeInfo,
        expr_ctx: &ExprContext,
    ) -> String {
        if self.rng.gen_bool(0.25) {
            // Nested when expression
            let inner_indent = "    ".repeat(self.indent + 2);
            let inner_close = "    ".repeat(self.indent + 1);
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            let cond =
                expr_gen.generate_simple(&TypeInfo::Primitive(PrimitiveType::Bool), expr_ctx);
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            let true_val = expr_gen.generate_simple(result_type, expr_ctx);
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            let false_val = expr_gen.generate_simple(result_type, expr_ctx);
            format!(
                "when {{\n{}{} => {}\n{}_ => {}\n{}}}",
                inner_indent, cond, true_val, inner_indent, false_val, inner_close
            )
        } else {
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            expr_gen.generate_simple(result_type, expr_ctx)
        }
    }

    fn try_generate_match_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find i64 or i32-typed variables in scope (locals + params)
        let mut candidates: Vec<(String, PrimitiveType)> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            match ty {
                TypeInfo::Primitive(p @ PrimitiveType::I64)
                | TypeInfo::Primitive(p @ PrimitiveType::I32) => {
                    candidates.push((name.clone(), *p));
                }
                _ => {}
            }
        }
        for param in ctx.params.iter() {
            match &param.param_type {
                TypeInfo::Primitive(p @ PrimitiveType::I64)
                | TypeInfo::Primitive(p @ PrimitiveType::I32) => {
                    candidates.push((param.name.clone(), *p));
                }
                _ => {}
            }
        }
        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, scrutinee_prim) = candidates[idx].clone();
        let is_i32 = matches!(scrutinee_prim, PrimitiveType::I32);
        // For i32 matches, use i32 literal suffix; for i64, no suffix needed
        let suffix = if is_i32 { "_i32" } else { "" };

        // ~15% chance to use an iterator chain as the scrutinee (feature interaction):
        // match arr.iter().count() { ... } or match arr.iter().filter(...).count() { ... }
        // This stresses iterator evaluation as match subject. Only for i64 matches.
        let i64_arrays: Vec<String> = ctx
            .locals
            .iter()
            .filter_map(|(name, ty, _)| match ty {
                TypeInfo::Array(inner)
                    if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::I64)) =>
                {
                    Some(name.clone())
                }
                _ => None,
            })
            .collect();
        let scrutinee = if !is_i32 && !i64_arrays.is_empty() && self.rng.gen_bool(0.15) {
            let arr = &i64_arrays[self.rng.gen_range(0..i64_arrays.len())];
            match self.rng.gen_range(0..3) {
                0 => format!("{}.iter().count()", arr),
                1 => format!("{}.iter().filter((x) => x > 0).count()", arr),
                _ => format!("{}.iter().sum()", arr),
            }
        } else if self.rng.gen_bool(0.30) {
            // ~30% of the time, generate a complex scrutinee expression (var + lit, var * lit)
            // instead of a plain variable. This exercises expression-as-scrutinee codegen.
            let op = match self.rng.gen_range(0..4) {
                0 => "+",
                1 => "-",
                2 => "*",
                _ => "%",
            };
            let lit = self.rng.gen_range(1..10);
            format!("({} {} {}{})", var_name, op, lit, suffix)
        } else {
            var_name
        };

        // Decide if we want to use unreachable in the default arm
        // Complex scrutinee expressions can't prove value, so skip unreachable for them
        let has_complex_scrutinee = scrutinee.starts_with('(');
        let use_unreachable = !has_complex_scrutinee
            && self
                .rng
                .gen_bool(self.config.expr_config.unreachable_probability);

        // Pick a result type for all arms (same type to keep it simple)
        let result_type = self.random_primitive_type();
        let result_name = ctx.new_local_name();

        // Generate 2-3 literal arms plus a wildcard
        let arm_count = self.rng.gen_range(2..=3);
        let indent = "    ".repeat(self.indent + 1);

        let expr_ctx = ctx.to_expr_context();
        let mut arms = Vec::new();

        if use_unreachable {
            // Match on a known literal so the wildcard is provably dead code
            let known_val: i64 = self.rng.gen_range(-10..20);

            // First arm matches the known literal
            let arm_expr = self.generate_match_arm_value(&result_type, &expr_ctx);
            arms.push(format!("{}{}{} => {}", indent, known_val, suffix, arm_expr));

            // Additional non-matching arms (dead code but syntactically valid)
            let mut used_values = std::collections::HashSet::new();
            used_values.insert(known_val);
            for _ in 1..arm_count {
                let mut val: i64 = self.rng.gen_range(-10..20);
                while used_values.contains(&val) {
                    val = self.rng.gen_range(-10..20);
                }
                used_values.insert(val);

                let arm_expr = self.generate_match_arm_value(&result_type, &expr_ctx);
                arms.push(format!("{}{}{} => {}", indent, val, suffix, arm_expr));
            }

            // Wildcard arm with unreachable
            arms.push(format!("{}_ => unreachable", indent));

            let close_indent = "    ".repeat(self.indent);
            ctx.add_local(result_name.clone(), result_type, false);

            Some(format!(
                "let {} = match {}{} {{\n{}\n{}}}",
                result_name,
                known_val,
                suffix,
                arms.join("\n"),
                close_indent,
            ))
        } else {
            // Generate distinct integer literal patterns
            let mut used_values = std::collections::HashSet::new();
            for _ in 0..arm_count {
                let mut val: i64 = self.rng.gen_range(-10..20);
                while used_values.contains(&val) {
                    val = self.rng.gen_range(-10..20);
                }
                used_values.insert(val);

                let arm_expr = self.generate_match_arm_value(&result_type, &expr_ctx);
                arms.push(format!("{}{}{} => {}", indent, val, suffix, arm_expr));
            }

            // Sometimes generate a guarded wildcard arm before the bare wildcard
            if self
                .rng
                .gen_bool(self.config.expr_config.match_guard_probability)
            {
                let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                let guard_cond = expr_gen.generate_guard_condition(Some(&expr_ctx), 0);
                let guarded_expr = self.generate_match_arm_value(&result_type, &expr_ctx);
                arms.push(format!("{}_ if {} => {}", indent, guard_cond, guarded_expr));
            }

            // Wildcard arm
            let wildcard_expr = self.generate_match_arm_value(&result_type, &expr_ctx);
            arms.push(format!("{}_ => {}", indent, wildcard_expr));

            let close_indent = "    ".repeat(self.indent);
            ctx.add_local(result_name.clone(), result_type, false);

            Some(format!(
                "let {} = match {} {{\n{}\n{}}}",
                result_name,
                scrutinee,
                arms.join("\n"),
                close_indent,
            ))
        }
    }

    /// Try to generate a match expression whose arms produce closures that
    /// capture surrounding variables.
    ///
    /// Finds an i64-typed variable to match on, plus a capturable numeric
    /// variable from the surrounding scope, and generates one of two patterns:
    ///
    /// **Pattern A — immediate invocation:**
    /// ```vole
    /// let f = match var {
    ///     1 => (n: i64) => n + captured
    ///     2 => (n: i64) => n * captured
    ///     _ => (n: i64) => n - captured
    /// }
    /// let result = f(some_arg)
    /// ```
    ///
    /// **Pattern B — iterator chain:**
    /// ```vole
    /// let f = match var {
    ///     1 => (n: i64) => n + captured
    ///     2 => (n: i64) => n * captured
    ///     _ => (n: i64) => n - captured
    /// }
    /// let result = arr.iter().map(f).collect()
    /// ```
    ///
    /// This exercises closure creation inside match arms, variable capture
    /// scope interaction, and function-typed match results in higher-order
    /// contexts.
    ///
    /// Returns `None` if preconditions are not met (need an i64 scrutinee
    /// and a capturable numeric variable).
    fn try_generate_match_closure_arms(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Guard: closures that capture variables inside generic class methods hit a
        // compiler bug ("Captured variable not found"). Skip this pattern entirely
        // when we're generating a method body for a generic class.
        if let Some((cls_mod, cls_sym)) = ctx.current_class_sym_id {
            if let Some(symbol) = ctx.table.get_symbol(cls_mod, cls_sym) {
                if let SymbolKind::Class(info) = &symbol.kind {
                    if !info.type_params.is_empty() {
                        return None;
                    }
                }
            }
        }

        // Step 1: Find an i64-typed variable to use as the match scrutinee
        let mut scrutinee_candidates: Vec<String> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)) {
                scrutinee_candidates.push(name.clone());
            }
        }
        for param in ctx.params.iter() {
            if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::I64)) {
                scrutinee_candidates.push(param.name.clone());
            }
        }
        if scrutinee_candidates.is_empty() {
            return None;
        }

        // Step 2: Find a capturable numeric variable (i64 or i32) that is
        // different from the scrutinee, to use inside the closure arms.
        let mut capture_candidates: Vec<(String, PrimitiveType)> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            match ty {
                TypeInfo::Primitive(p @ (PrimitiveType::I64 | PrimitiveType::I32)) => {
                    capture_candidates.push((name.clone(), *p));
                }
                _ => {}
            }
        }
        for param in ctx.params.iter() {
            match &param.param_type {
                TypeInfo::Primitive(p @ (PrimitiveType::I64 | PrimitiveType::I32)) => {
                    capture_candidates.push((param.name.clone(), *p));
                }
                _ => {}
            }
        }
        if capture_candidates.is_empty() {
            return None;
        }

        // Pick the scrutinee
        let scr_idx = self.rng.gen_range(0..scrutinee_candidates.len());
        let scrutinee = scrutinee_candidates[scr_idx].clone();

        // Pick a capture variable (prefer one different from the scrutinee)
        let non_scrutinee_captures: Vec<&(String, PrimitiveType)> = capture_candidates
            .iter()
            .filter(|(name, _)| *name != scrutinee)
            .collect();
        let (capture_var, capture_prim) = if !non_scrutinee_captures.is_empty() {
            let idx = self.rng.gen_range(0..non_scrutinee_captures.len());
            non_scrutinee_captures[idx].clone()
        } else {
            // Fall back to using the same variable (still valid, just less interesting)
            let idx = self.rng.gen_range(0..capture_candidates.len());
            capture_candidates[idx].clone()
        };

        // The closure parameter type and return type match the capture type.
        // We use i64 for the closure param type since all scrutinees are i64;
        // the closure body uses the capture variable which may be i64 or i32.
        // To keep type consistency, we make the closure always i64 -> i64 or
        // i32 -> i32 based on the capture variable type.
        let closure_prim = capture_prim;
        let closure_type_name = match closure_prim {
            PrimitiveType::I64 => "i64",
            PrimitiveType::I32 => "i32",
            _ => "i64",
        };

        // Generate 2-3 literal arms plus a wildcard, each producing a closure
        let arm_count = self.rng.gen_range(2..=3);
        let indent = "    ".repeat(self.indent + 1);
        let close_indent = "    ".repeat(self.indent);

        let mut arms = Vec::new();
        let mut used_values = std::collections::HashSet::new();

        // Closure operations pool: each arm captures the same variable but
        // applies a different operation.
        let operations = [
            ("n + {}", "add"),
            ("n * {}", "mul"),
            ("n - {}", "sub"),
            ("{} - n", "rsub"),
            ("{} + n", "radd"),
        ];

        for _ in 0..arm_count {
            let mut lit_val: i64 = self.rng.gen_range(0..10);
            while used_values.contains(&lit_val) {
                lit_val = self.rng.gen_range(0..10);
            }
            used_values.insert(lit_val);

            // Pick a random operation for this arm
            let op_idx = self.rng.gen_range(0..operations.len());
            let (op_template, _) = operations[op_idx];
            let body = op_template.replace("{}", &capture_var);

            arms.push(format!(
                "{}{} => (n: {}) => {}",
                indent, lit_val, closure_type_name, body
            ));
        }

        // Wildcard arm — always present, with a default operation
        let wildcard_op_idx = self.rng.gen_range(0..operations.len());
        let (wildcard_template, _) = operations[wildcard_op_idx];
        let wildcard_body = wildcard_template.replace("{}", &capture_var);
        arms.push(format!(
            "{}_ => (n: {}) => {}",
            indent, closure_type_name, wildcard_body
        ));

        let fn_name = ctx.new_local_name();
        let closure_type = TypeInfo::Function {
            param_types: vec![TypeInfo::Primitive(closure_prim)],
            return_type: Box::new(TypeInfo::Primitive(closure_prim)),
        };

        let match_stmt = format!(
            "let {} = match {} {{\n{}\n{}}}",
            fn_name,
            scrutinee,
            arms.join("\n"),
            close_indent,
        );

        // Now decide how to use the closure: Pattern A (invoke) or Pattern B (iterator chain)
        let expr_ctx = ctx.to_expr_context();
        let array_vars = expr_ctx.array_vars();

        // Filter to arrays whose element type matches the closure type
        let matching_arrays: Vec<&(String, TypeInfo)> = array_vars
            .iter()
            .filter(|(_, elem_ty)| matches!(elem_ty, TypeInfo::Primitive(p) if *p == closure_prim))
            .collect();

        // 40% chance to use iterator chain if matching arrays are available
        let use_iter = !matching_arrays.is_empty() && self.rng.gen_bool(0.4);

        if use_iter {
            // Pattern B: arr.iter().map(f).collect()
            let arr_idx = self.rng.gen_range(0..matching_arrays.len());
            let (arr_name, _) = matching_arrays[arr_idx];

            let result_name = ctx.new_local_name();
            let result_type = TypeInfo::Array(Box::new(TypeInfo::Primitive(closure_prim)));

            ctx.add_local(fn_name.clone(), closure_type, false);
            ctx.add_local(result_name.clone(), result_type, false);

            // Optionally add a .filter() after the .map() (~30%)
            let chain_suffix = if self.rng.gen_bool(0.3) {
                let pred = self.generate_filter_closure_body_param(closure_prim, "y");
                format!(".filter((y: {}) => {})", closure_type_name, pred)
            } else {
                String::new()
            };

            let iter_stmt = format!(
                "let {} = {}.iter().map({}){}.collect()",
                result_name, arr_name, fn_name, chain_suffix
            );
            Some(format!(
                "{}\n{}{}",
                match_stmt,
                "    ".repeat(self.indent),
                iter_stmt
            ))
        } else {
            // Pattern A: immediate invocation f(arg)
            let result_name = ctx.new_local_name();
            let result_type = TypeInfo::Primitive(closure_prim);

            // Generate a simple argument for the closure call
            let arg = match closure_prim {
                PrimitiveType::I64 => {
                    let n = self.rng.gen_range(1..=20);
                    format!("{}", n)
                }
                PrimitiveType::I32 => {
                    let n = self.rng.gen_range(1..=20);
                    format!("{}_i32", n)
                }
                _ => "0".to_string(),
            };

            ctx.add_local(fn_name.clone(), closure_type, false);
            ctx.add_local(result_name.clone(), result_type, false);

            let call_stmt = format!("let {} = {}({})", result_name, fn_name, arg);
            Some(format!(
                "{}\n{}{}",
                match_stmt,
                "    ".repeat(self.indent),
                call_stmt
            ))
        }
    }

    /// Try to generate a closure that captures a field value from a class/struct
    /// instance in scope.
    ///
    /// Finds a class-typed or struct-typed local variable, extracts a primitive
    /// field value from it, then creates a closure that captures the field value.
    /// The closure is either immediately invoked or passed to an iterator `.map()`
    /// chain on a small literal array.
    ///
    /// This exercises the interaction between:
    /// - Field access on class/struct instances (`instance.field`)
    /// - Closure capture of the extracted field value
    /// - Higher-order usage (direct invocation or `.map()` on array)
    ///
    /// Generated output shapes (Pattern A - direct invocation):
    /// ```vole
    /// let field_val = instance.field1
    /// let closure = (x: i64) -> i64 => x + field_val
    /// let result = closure(5)
    /// ```
    ///
    /// Generated output shapes (Pattern B - iterator chain):
    /// ```vole
    /// let field_val = instance.field1
    /// let result = [1, 2, 3].iter().map((x: i64) -> i64 => x + field_val).collect()
    /// ```
    ///
    /// Returns `None` if no class/struct-typed local with primitive fields is in scope.
    fn try_generate_field_closure_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Guard: closures that capture variables inside generic class methods hit a
        // compiler bug ("Captured variable not found"). Skip this pattern entirely
        // when we're generating a method body for a generic class.
        if let Some((cls_mod, cls_sym)) = ctx.current_class_sym_id {
            if let Some(symbol) = ctx.table.get_symbol(cls_mod, cls_sym) {
                if let SymbolKind::Class(info) = &symbol.kind {
                    if !info.type_params.is_empty() {
                        return None;
                    }
                }
            }
        }

        let _module_id = ctx.module_id?;

        // Collect class/struct-typed locals that have at least one primitive field.
        // For each candidate, store (local_name, field_name, field_prim_type).
        let mut candidates: Vec<(String, String, PrimitiveType)> = Vec::new();

        for (name, ty, _) in &ctx.locals {
            match ty {
                TypeInfo::Class(mod_id, sym_id) => {
                    if let Some(sym) = ctx.table.get_symbol(*mod_id, *sym_id) {
                        if let SymbolKind::Class(ref info) = sym.kind {
                            // Only non-generic classes (generic field types are unresolved)
                            if info.type_params.is_empty() {
                                for field in &info.fields {
                                    if let TypeInfo::Primitive(p) = &field.field_type {
                                        // Only types the closure body can handle
                                        if matches!(p, PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64 | PrimitiveType::String | PrimitiveType::Bool) {
                                            candidates.push((name.clone(), field.name.clone(), *p));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                TypeInfo::Struct(mod_id, sym_id) => {
                    if let Some(sym) = ctx.table.get_symbol(*mod_id, *sym_id) {
                        if let SymbolKind::Struct(ref info) = sym.kind {
                            for field in &info.fields {
                                if let TypeInfo::Primitive(p) = &field.field_type {
                                    // Only types the closure body can handle
                                    if matches!(p, PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64 | PrimitiveType::String | PrimitiveType::Bool) {
                                        candidates.push((name.clone(), field.name.clone(), *p));
                                    }
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        if candidates.is_empty() {
            return None;
        }

        // Pick a random candidate field
        let idx = self.rng.gen_range(0..candidates.len());
        let (instance_name, field_name, field_prim) = candidates[idx].clone();

        // Step 1: Extract the field value into a local
        let field_local = ctx.new_local_name();
        ctx.add_local(field_local.clone(), TypeInfo::Primitive(field_prim), false);
        let field_stmt = format!("let {} = {}.{}", field_local, instance_name, field_name);

        // Step 2: Determine the closure's numeric type.
        // For numeric fields (i64, i32, f64), the closure operates on that type.
        // For non-numeric fields (string, bool), fall back to i64.
        let (closure_prim, closure_type_name) = match field_prim {
            PrimitiveType::I64 => (PrimitiveType::I64, "i64"),
            PrimitiveType::I32 => (PrimitiveType::I32, "i32"),
            PrimitiveType::F64 => (PrimitiveType::F64, "f64"),
            _ => (PrimitiveType::I64, "i64"),
        };

        // Operations that combine the closure parameter with the captured field value.
        // For numeric types, use arithmetic. For string fields captured as i64 proxy,
        // only use addition (safe default).
        let is_numeric_field = matches!(
            field_prim,
            PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64
        );

        let op = if is_numeric_field {
            // Direct arithmetic with the captured field value
            match self.rng.gen_range(0..4) {
                0 => format!("x + {}", field_local),
                1 => format!("x * {}", field_local),
                2 => format!("x - {}", field_local),
                _ => format!("{} + x", field_local),
            }
        } else if matches!(field_prim, PrimitiveType::String) {
            // String field: closure returns the string length plus x
            // We can't directly use the string in an i64 closure, so
            // use a simple captured literal derived from scope.
            // Actually, let's just produce an i64 closure that ignores
            // the string but still captures it to exercise the capture path.
            format!("x + {}.length()", field_local)
        } else if matches!(field_prim, PrimitiveType::Bool) {
            // Bool field: convert to i64 via when expression
            format!(
                "x + when {{\n{indent}    {} => 1\n{indent}    _ => 0\n{indent}    }}",
                field_local,
                indent = "    ".repeat(self.indent)
            )
        } else {
            // Candidate filtering above ensures only i64/i32/f64/string/bool reach here
            unreachable!("unexpected field type in field-closure-let: {:?}", field_prim)
        };

        let indent = "    ".repeat(self.indent);

        // Decide usage pattern: Pattern A (direct invocation) or Pattern B (iterator chain)
        let use_iter = self.rng.gen_bool(0.5);

        if use_iter {
            // Pattern B: build a small literal array, map with inline closure
            let arr_size = self.rng.gen_range(2..=4);
            let arr_elems: Vec<String> = (0..arr_size)
                .map(|_| match closure_prim {
                    PrimitiveType::I32 => {
                        let n = self.rng.gen_range(1..=10);
                        format!("{}_i32", n)
                    }
                    PrimitiveType::F64 => {
                        let n: f64 = self.rng.gen_range(1.0..=10.0);
                        format!("{:.1}", n)
                    }
                    _ => {
                        let n = self.rng.gen_range(1..=10);
                        format!("{}", n)
                    }
                })
                .collect();

            let result_name = ctx.new_local_name();
            let result_type = TypeInfo::Array(Box::new(TypeInfo::Primitive(closure_prim)));
            ctx.add_local(result_name.clone(), result_type, false);

            let iter_stmt = format!(
                "let {} = [{}].iter().map((x: {}) -> {} => {}).collect()",
                result_name,
                arr_elems.join(", "),
                closure_type_name,
                closure_type_name,
                op,
            );

            Some(format!("{}\n{}{}", field_stmt, indent, iter_stmt))
        } else {
            // Pattern A: bind closure to a local, then invoke it
            let fn_name = ctx.new_local_name();
            let closure_type = TypeInfo::Function {
                param_types: vec![TypeInfo::Primitive(closure_prim)],
                return_type: Box::new(TypeInfo::Primitive(closure_prim)),
            };

            let closure_stmt = format!(
                "let {} = (x: {}) -> {} => {}",
                fn_name, closure_type_name, closure_type_name, op,
            );

            let result_name = ctx.new_local_name();
            let result_type = TypeInfo::Primitive(closure_prim);

            // Generate a simple argument
            let arg = match closure_prim {
                PrimitiveType::I64 => {
                    let n = self.rng.gen_range(1..=20);
                    format!("{}", n)
                }
                PrimitiveType::I32 => {
                    let n = self.rng.gen_range(1..=20);
                    format!("{}_i32", n)
                }
                PrimitiveType::F64 => {
                    let n: f64 = self.rng.gen_range(1.0..=20.0);
                    format!("{:.1}", n)
                }
                _ => "0".to_string(),
            };

            ctx.add_local(fn_name.clone(), closure_type, false);
            ctx.add_local(result_name.clone(), result_type, false);

            let call_stmt = format!("let {} = {}({})", result_name, fn_name, arg);
            Some(format!(
                "{}\n{}{}\n{}{}",
                field_stmt, indent, closure_stmt, indent, call_stmt
            ))
        }
    }

    /// Try to generate a match expression let-binding on a string variable.
    ///
    /// Finds a string-typed variable in scope and generates:
    /// ```vole
    /// let result = match str_var {
    ///     "alpha" => <expr>
    ///     "beta" => <expr>
    ///     _ => <expr>
    /// }
    /// ```
    ///
    /// Returns `None` if no string-typed variable is in scope.
    fn try_generate_string_match_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find string-typed variables in scope (locals + params)
        let mut candidates: Vec<String> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if matches!(ty, TypeInfo::Primitive(PrimitiveType::String)) {
                candidates.push(name.clone());
            }
        }
        for param in ctx.params.iter() {
            if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::String)) {
                candidates.push(param.name.clone());
            }
        }
        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let scrutinee = &candidates[idx];

        // Decide if we want to use unreachable in the default arm
        let use_unreachable = self
            .rng
            .gen_bool(self.config.expr_config.unreachable_probability);

        // Pick a result type for all arms (same type to keep it simple)
        let result_type = self.random_primitive_type();
        let result_name = ctx.new_local_name();

        // Generate 2-3 string literal arms plus a wildcard
        let arm_count = self.rng.gen_range(2..=3);
        let indent = "    ".repeat(self.indent + 1);

        let expr_ctx = ctx.to_expr_context();
        let mut arms = Vec::new();

        // Pool of short distinct string patterns to pick from
        let patterns = [
            "alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta", "iota", "kappa",
        ];

        if use_unreachable {
            // Pick a known string literal to match on so the wildcard is dead code
            let known_idx = self.rng.gen_range(0..patterns.len());
            let known_pattern = patterns[known_idx];

            // First arm matches the known literal
            let arm_expr = self.generate_match_arm_value(&result_type, &expr_ctx);
            arms.push(format!("{}\"{}\" => {}", indent, known_pattern, arm_expr));

            // Additional non-matching arms (dead code but syntactically valid)
            let mut used_indices = std::collections::HashSet::new();
            used_indices.insert(known_idx);
            for _ in 1..arm_count {
                let mut pi = self.rng.gen_range(0..patterns.len());
                while used_indices.contains(&pi) {
                    pi = self.rng.gen_range(0..patterns.len());
                }
                used_indices.insert(pi);

                let arm_expr = self.generate_match_arm_value(&result_type, &expr_ctx);
                arms.push(format!("{}\"{}\" => {}", indent, patterns[pi], arm_expr));
            }

            // Wildcard arm with unreachable
            arms.push(format!("{}_ => unreachable", indent));

            let close_indent = "    ".repeat(self.indent);
            ctx.add_local(result_name.clone(), result_type, false);

            Some(format!(
                "let {} = match \"{}\" {{\n{}\n{}}}",
                result_name,
                known_pattern,
                arms.join("\n"),
                close_indent,
            ))
        } else {
            // Pick distinct string patterns
            let mut used_indices = std::collections::HashSet::new();
            for _ in 0..arm_count {
                let mut pi = self.rng.gen_range(0..patterns.len());
                while used_indices.contains(&pi) {
                    pi = self.rng.gen_range(0..patterns.len());
                }
                used_indices.insert(pi);

                let arm_expr = self.generate_match_arm_value(&result_type, &expr_ctx);
                arms.push(format!("{}\"{}\" => {}", indent, patterns[pi], arm_expr));
            }

            // Sometimes generate a guarded wildcard arm before the bare wildcard
            if self
                .rng
                .gen_bool(self.config.expr_config.match_guard_probability)
            {
                let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                let guard_cond = expr_gen.generate_guard_condition(Some(&expr_ctx), 0);
                let guarded_expr = self.generate_match_arm_value(&result_type, &expr_ctx);
                arms.push(format!("{}_ if {} => {}", indent, guard_cond, guarded_expr));
            }

            // Wildcard arm
            let wildcard_expr = self.generate_match_arm_value(&result_type, &expr_ctx);
            arms.push(format!("{}_ => {}", indent, wildcard_expr));

            let close_indent = "    ".repeat(self.indent);
            ctx.add_local(result_name.clone(), result_type, false);

            Some(format!(
                "let {} = match {} {{\n{}\n{}}}",
                result_name,
                scrutinee,
                arms.join("\n"),
                close_indent,
            ))
        }
    }

    /// Try to generate a when-expression let-binding.
    ///
    /// Generates a multiline `when` expression used as a let initializer:
    /// ```vole
    /// let result = when {
    ///     <bool_cond> => <expr>
    ///     <bool_cond> => <expr>
    ///     _ => <expr>
    /// }
    /// ```
    ///
    /// Unlike the inline when expressions generated by `ExprGenerator`, this
    /// produces a multiline block form that exercises the when-as-initializer
    /// pattern in the compiler.
    fn try_generate_when_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Pick a result type for all arms (same type to keep it simple)
        let result_type = self.random_primitive_type();
        let result_name = ctx.new_local_name();

        // Decide if we want to use unreachable in the default arm
        let use_unreachable = self
            .rng
            .gen_bool(self.config.expr_config.unreachable_probability);

        // Decide arm count: either 2 (simple) or 3-4 (multi-arm)
        let arm_count = if self
            .rng
            .gen_bool(self.config.expr_config.multi_arm_when_probability)
        {
            // Multi-arm: 3-4 total arms (2-3 conditions + wildcard)
            self.rng.gen_range(3..=4)
        } else {
            // Simple: 2 total arms (1 condition + wildcard)
            2
        };
        let indent = "    ".repeat(self.indent + 1);

        let expr_ctx = ctx.to_expr_context();
        let mut arms = Vec::new();

        if use_unreachable {
            // First arm uses `true` so the wildcard is provably dead code
            let arm_expr = self.generate_match_arm_value(&result_type, &expr_ctx);
            arms.push(format!("{}true => {}", indent, arm_expr));

            // Additional arms (dead code but syntactically valid)
            for _ in 1..arm_count {
                let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                let cond =
                    expr_gen.generate_simple(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx);
                let arm_expr = self.generate_match_arm_value(&result_type, &expr_ctx);
                arms.push(format!("{}{} => {}", indent, cond, arm_expr));
            }

            // Wildcard arm with unreachable
            arms.push(format!("{}_ => unreachable", indent));
        } else {
            for _ in 0..arm_count {
                // ~20% chance to use a method-based bool condition (string contains/starts_with
                // or iterator any/all) when such variables are in scope.
                let cond = if self.rng.gen_bool(0.20) {
                    let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                    if let Some(method_cond) = expr_gen.try_generate_method_bool_atom(&expr_ctx) {
                        method_cond
                    } else {
                        expr_gen
                            .generate_simple(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx)
                    }
                } else {
                    let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                    expr_gen.generate_simple(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx)
                };
                let arm_expr = self.generate_match_arm_value(&result_type, &expr_ctx);
                arms.push(format!("{}{} => {}", indent, cond, arm_expr));
            }

            // Wildcard arm
            let wildcard_expr = self.generate_match_arm_value(&result_type, &expr_ctx);
            arms.push(format!("{}_ => {}", indent, wildcard_expr));
        }

        let close_indent = "    ".repeat(self.indent);
        ctx.add_local(result_name.clone(), result_type, false);

        Some(format!(
            "let {} = when {{\n{}\n{}}}",
            result_name,
            arms.join("\n"),
            close_indent,
        ))
    }

    /// Try to generate a match expression let-binding on a union-typed variable.
    ///
    /// Finds a union-typed variable in scope and generates:
    /// ```vole
    /// let result = match union_var {
    ///     i32 => <expr>
    ///     string => <expr>
    ///     bool => <expr>
    /// }
    /// ```
    ///
    /// Each variant gets its own type-pattern arm. Only primitive variants
    /// are supported (class/interface variants are skipped to keep things simple).
    ///
    /// Returns `None` if no union-typed variable with all-primitive variants
    /// is in scope.
    fn try_generate_union_match_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find union-typed variables in scope (locals + params) with all-primitive variants
        let mut candidates: Vec<(String, Vec<TypeInfo>)> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Union(variants) = ty {
                if variants.iter().all(|v| matches!(v, TypeInfo::Primitive(_))) {
                    candidates.push((name.clone(), variants.clone()));
                }
            }
        }
        for param in ctx.params.iter() {
            if let TypeInfo::Union(variants) = &param.param_type {
                if variants.iter().all(|v| matches!(v, TypeInfo::Primitive(_))) {
                    candidates.push((param.name.clone(), variants.clone()));
                }
            }
        }
        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (scrutinee, variants) = &candidates[idx];
        let scrutinee = scrutinee.clone();
        let variants = variants.clone();

        // Pick a result type for all arms (same type to keep it simple)
        let result_type = self.random_primitive_type();
        let result_name = ctx.new_local_name();

        let indent = "    ".repeat(self.indent + 1);
        let close_indent = "    ".repeat(self.indent);
        let expr_ctx = ctx.to_expr_context();

        // ~35% chance: generate `when { x is Type => ... }` instead of match
        if self.rng.gen_bool(0.35) {
            // Pick one variant to check with `is`
            let prim_variants: Vec<_> = variants
                .iter()
                .filter_map(|v| {
                    if let TypeInfo::Primitive(p) = v {
                        Some(*p)
                    } else {
                        None
                    }
                })
                .collect();
            if !prim_variants.is_empty() {
                let check_type = prim_variants[self.rng.gen_range(0..prim_variants.len())];
                let is_branch_expr = self.generate_match_arm_value(&result_type, &expr_ctx);
                let else_branch_expr = self.generate_match_arm_value(&result_type, &expr_ctx);

                ctx.add_local(result_name.clone(), result_type, false);

                return Some(format!(
                    "let {} = when {{\n{}{} is {} => {}\n{}_ => {}\n{}}}",
                    result_name,
                    indent,
                    scrutinee,
                    check_type.as_str(),
                    is_branch_expr,
                    indent,
                    else_branch_expr,
                    close_indent,
                ));
            }
        }

        let mut arms = Vec::new();

        // Generate one arm per variant type
        for variant in &variants {
            if let TypeInfo::Primitive(prim) = variant {
                let arm_expr = self.generate_match_arm_value(&result_type, &expr_ctx);
                arms.push(format!("{}{} => {}", indent, prim.as_str(), arm_expr));
            }
        }

        if arms.is_empty() {
            return None;
        }

        ctx.add_local(result_name.clone(), result_type, false);

        Some(format!(
            "let {} = match {} {{\n{}\n{}}}",
            result_name,
            scrutinee,
            arms.join("\n"),
            close_indent,
        ))
    }

    /// Try to generate a sentinel union let-binding.
    ///
    /// Creates a union type combining a primitive type with a sentinel type,
    /// assigns either a primitive value or the sentinel, then follows up with
    /// either a match expression or an `is`-check on the union.
    ///
    /// Pattern 1 (match):
    /// ```vole
    /// let x: i64 | Sent1 = Sent1
    /// let result = match x {
    ///     i64 => "value"
    ///     Sent1 => "sentinel"
    /// }
    /// ```
    ///
    /// Pattern 2 (is-check):
    /// ```vole
    /// let x: i64 | Sent1 = 42
    /// let result = if x is Sent1 { "sentinel" } else { "value" }
    /// ```
    ///
    /// Returns `None` if no sentinel types are available in the current module.
    fn try_generate_sentinel_union_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let module_id = ctx.module_id?;
        let module = ctx.table.get_module(module_id)?;

        // Collect sentinel symbols from the current module
        let sentinels: Vec<_> = module.sentinels().collect();
        if sentinels.is_empty() {
            return None;
        }

        // Pick sentinel(s) — 30% chance of multi-sentinel union when 2+ available
        let use_multi = sentinels.len() >= 2 && self.rng.gen_bool(0.3);

        let sentinel_idx = self.rng.gen_range(0..sentinels.len());
        let sentinel_sym = &sentinels[sentinel_idx];
        let sentinel_name = sentinel_sym.name.clone();
        let sentinel_sym_id = sentinel_sym.id;

        let second_sentinel = if use_multi {
            // Pick a different sentinel for the second variant
            let mut idx2 = self.rng.gen_range(0..sentinels.len());
            while idx2 == sentinel_idx {
                idx2 = self.rng.gen_range(0..sentinels.len());
            }
            Some((sentinels[idx2].name.clone(), sentinels[idx2].id))
        } else {
            None
        };

        // Pick a primitive type for the other union variant
        let prim_type = PrimitiveType::random_expr_type(self.rng);
        let prim_type_info = TypeInfo::Primitive(prim_type);

        // Build the union type: PrimType | Sentinel [| Sentinel2]
        let sentinel_type_info = TypeInfo::Sentinel(module_id, sentinel_sym_id);
        let mut union_members = vec![prim_type_info.clone(), sentinel_type_info.clone()];
        let mut union_type_parts = vec![prim_type.as_str().to_string(), sentinel_name.clone()];

        if let Some((ref name2, sym_id2)) = second_sentinel {
            union_members.push(TypeInfo::Sentinel(module_id, sym_id2));
            union_type_parts.push(name2.clone());
        }
        let union_type = TypeInfo::Union(union_members);
        let union_type_syntax = union_type_parts.join(" | ");

        // Union variable name
        let union_var_name = ctx.new_local_name();

        // Randomly choose initial value
        let init_choice = if second_sentinel.is_some() {
            self.rng.gen_range(0..3) // 0=prim, 1=sent1, 2=sent2
        } else {
            self.rng.gen_range(0..2) // 0=prim, 1=sent1
        };

        let init_value = match init_choice {
            0 => {
                let expr_ctx = ctx.to_expr_context();
                let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                expr_gen.generate_simple(&prim_type_info, &expr_ctx)
            }
            1 => sentinel_name.clone(),
            _ => second_sentinel.as_ref().unwrap().0.clone(),
        };

        let let_stmt = format!(
            "let {}: {} = {}",
            union_var_name, union_type_syntax, init_value
        );

        // Register the union variable
        ctx.add_local(union_var_name.clone(), union_type, false);

        // Choose follow-up: match (60%) or is-check (40%)
        let use_match = self.rng.gen_bool(0.6);

        if use_match {
            // Generate a match expression on the union
            let result_type = self.random_primitive_type();
            let result_name = ctx.new_local_name();

            let indent = "    ".repeat(self.indent + 1);
            let close_indent = "    ".repeat(self.indent);
            let expr_ctx = ctx.to_expr_context();

            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            let prim_arm_expr = expr_gen.generate_simple(&result_type, &expr_ctx);
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            let sentinel_arm_expr = expr_gen.generate_simple(&result_type, &expr_ctx);

            let mut match_arms = format!(
                "{}{} => {}\n{}{} => {}",
                indent, prim_type.as_str(), prim_arm_expr,
                indent, sentinel_name, sentinel_arm_expr,
            );

            if let Some((ref name2, _)) = second_sentinel {
                let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                let sent2_arm_expr = expr_gen.generate_simple(&result_type, &expr_ctx);
                match_arms.push_str(&format!("\n{}{} => {}", indent, name2, sent2_arm_expr));
            }

            let match_stmt = format!(
                "let {} = match {} {{\n{}\n{}}}",
                result_name, union_var_name, match_arms, close_indent,
            );

            ctx.add_local(result_name, result_type, false);

            Some(format!("{}\n{}", let_stmt, match_stmt))
        } else {
            // Generate an is-check using when expression (if is not an expression in vole):
            // let result = when { x is Sentinel => expr, _ => expr }
            let result_type = self.random_primitive_type();
            let result_name = ctx.new_local_name();

            let expr_ctx = ctx.to_expr_context();
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            let sentinel_branch_expr = expr_gen.generate_simple(&result_type, &expr_ctx);
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            let else_branch_expr = expr_gen.generate_simple(&result_type, &expr_ctx);

            let indent = "    ".repeat(self.indent + 1);
            let close_indent = "    ".repeat(self.indent);
            let is_stmt = format!(
                "let {} = when {{\n{}{} is {} => {}\n{}_ => {}\n{}}}",
                result_name,
                indent,
                union_var_name,
                sentinel_name,
                sentinel_branch_expr,
                indent,
                else_branch_expr,
                close_indent,
            );

            ctx.add_local(result_name, result_type, false);

            Some(format!("{}\n{}", let_stmt, is_stmt))
        }
    }

    /// Try to generate an optional destructure match let-binding.
    ///
    /// Finds a non-generic class or struct with at least one primitive field,
    /// creates an optional variable (`ClassName?` or `StructName?`), and generates
    /// a match expression with destructuring:
    /// ```vole
    /// let varN: ClassName? = ClassName { field1: val1, field2: val2 }
    /// let resultN = match varN {
    ///     ClassName { field1: a, field2: b } => a + b
    ///     nil => 0
    /// }
    /// ```
    ///
    /// Returns `None` if no suitable class or struct is available in the current module.
    fn try_generate_optional_destructure_match(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        let module_id = ctx.module_id?;
        let module = ctx.table.get_module(module_id)?;

        // Collect non-generic classes with at least one primitive field
        let class_candidates: Vec<_> = module
            .classes()
            .filter_map(|sym| {
                if let SymbolKind::Class(ref info) = sym.kind {
                    if info.type_params.is_empty() && has_primitive_field(info) {
                        return Some((sym.id, sym.name.clone(), info.fields.clone(), true));
                    }
                }
                None
            })
            .collect();

        // Collect structs with at least one primitive field
        let struct_candidates: Vec<_> = module
            .structs()
            .filter_map(|sym| {
                if let SymbolKind::Struct(ref info) = sym.kind {
                    if info.fields.iter().any(|f| f.field_type.is_primitive()) {
                        return Some((sym.id, sym.name.clone(), info.fields.clone(), false));
                    }
                }
                None
            })
            .collect();

        let all_candidates: Vec<_> = class_candidates
            .into_iter()
            .chain(struct_candidates)
            .collect();

        if all_candidates.is_empty() {
            return None;
        }

        // Pick a random candidate
        let idx = self.rng.gen_range(0..all_candidates.len());
        let (sym_id, type_name, fields, is_class) = &all_candidates[idx];
        let sym_id = *sym_id;
        let type_name = type_name.clone();
        let fields = fields.clone();
        let is_class = *is_class;

        // Determine the base type and optional type
        let base_type = if is_class {
            TypeInfo::Class(module_id, sym_id)
        } else {
            TypeInfo::Struct(module_id, sym_id)
        };
        let optional_type = TypeInfo::Optional(Box::new(base_type));

        // Create the optional variable name
        let opt_var_name = ctx.new_local_name();

        // Randomly (50%) assign nil or a constructed instance
        let assign_nil = self.rng.gen_bool(0.5);

        let init_value = if assign_nil {
            "nil".to_string()
        } else {
            let field_values = self.generate_field_values(&fields, ctx);
            format!("{} {{ {} }}", type_name, field_values)
        };

        let let_stmt = format!(
            "let {}: {}? = {}",
            opt_var_name, type_name, init_value
        );

        // Register the optional variable
        ctx.add_local(opt_var_name.clone(), optional_type, false);

        // Collect primitive fields for the destructure arm body
        let primitive_fields: Vec<_> = fields
            .iter()
            .filter(|f| f.field_type.is_primitive())
            .collect();

        if primitive_fields.is_empty() {
            return None;
        }

        // Generate renamed bindings for each field in the destructure pattern
        let mut pattern_parts = Vec::new();
        let mut binding_names = Vec::new();
        let mut binding_types = Vec::new();

        for field in &fields {
            let binding = ctx.new_local_name();
            pattern_parts.push(format!("{}: {}", field.name, binding));
            binding_names.push(binding);
            binding_types.push(field.field_type.clone());
        }

        // Build the destructure arm body expression.
        // Find numeric fields for arithmetic, or fall back to string .length()
        let numeric_bindings: Vec<(String, &TypeInfo)> = binding_names
            .iter()
            .zip(binding_types.iter())
            .filter(|(_, ty)| {
                matches!(
                    ty,
                    TypeInfo::Primitive(
                        PrimitiveType::I64
                            | PrimitiveType::I32
                            | PrimitiveType::F64
                            | PrimitiveType::I8
                            | PrimitiveType::I16
                            | PrimitiveType::I128
                            | PrimitiveType::U8
                            | PrimitiveType::U16
                            | PrimitiveType::U32
                            | PrimitiveType::U64
                            | PrimitiveType::F32
                    )
                )
            })
            .map(|(name, ty)| (name.clone(), ty))
            .collect();

        let string_bindings: Vec<String> = binding_names
            .iter()
            .zip(binding_types.iter())
            .filter(|(_, ty)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(name, _)| name.clone())
            .collect();

        let bool_bindings: Vec<String> = binding_names
            .iter()
            .zip(binding_types.iter())
            .filter(|(_, ty)| matches!(ty, TypeInfo::Primitive(PrimitiveType::Bool)))
            .map(|(name, _)| name.clone())
            .collect();

        // Build the arm body expression (result type is i64)
        // Filter numeric bindings to only i64/i32 (both widen to i64 implicitly)
        let i64_compatible: Vec<&(String, &TypeInfo)> = numeric_bindings
            .iter()
            .filter(|(_, ty)| {
                matches!(
                    ty,
                    TypeInfo::Primitive(PrimitiveType::I64)
                        | TypeInfo::Primitive(PrimitiveType::I32)
                )
            })
            .collect();

        let arm_body = if !i64_compatible.is_empty() {
            // Combine i64/i32 fields with arithmetic
            let ops = [" + ", " * ", " - "];
            let op = ops[self.rng.gen_range(0..ops.len())];
            let parts: Vec<&str> = i64_compatible
                .iter()
                .take(3)
                .map(|(name, _)| name.as_str())
                .collect();
            let expr = parts.join(op);
            // If any field is i32, add `+ 0_i64` to force widening to i64
            // (otherwise the nil arm type i64 won't match the i32 arm)
            let has_i32 = i64_compatible
                .iter()
                .any(|(_, ty)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I32)));
            if has_i32 {
                format!("{} + 0_i64", expr)
            } else {
                expr
            }
        } else if !string_bindings.is_empty() {
            // Use .length() on the first string field
            format!("{}.length()", string_bindings[0])
        } else if !bool_bindings.is_empty() {
            // Convert bool to i64 using when expression (if is not an expression in vole)
            format!(
                "when {{ {} => 1_i64, _ => 0_i64 }}",
                bool_bindings[0]
            )
        } else {
            // Fallback: just return 1
            "1_i64".to_string()
        };

        // Generate the nil arm default value
        let nil_values = ["-1_i64", "0_i64", "42_i64"];
        let nil_value = nil_values[self.rng.gen_range(0..nil_values.len())];

        // Build the match expression
        let result_name = ctx.new_local_name();
        let indent = "    ".repeat(self.indent + 1);
        let close_indent = "    ".repeat(self.indent);

        let match_stmt = format!(
            "let {} = match {} {{\n{}{} {{ {} }} => {}\n{}nil => {}\n{}}}",
            result_name,
            opt_var_name,
            indent,
            type_name,
            pattern_parts.join(", "),
            arm_body,
            indent,
            nil_value,
            close_indent,
        );

        // Register the result local as i64
        ctx.add_local(
            result_name,
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        Some(format!("{}\n{}", let_stmt, match_stmt))
    }

    /// Try to generate a closure that captures a sentinel union variable.
    ///
    /// Creates a `PrimType | Sentinel` union local, then a closure `(x: i64) -> i64`
    /// that captures the union variable and uses `when { captured is Sentinel => ..., _ => ... }`
    /// inside. The closure is immediately invoked with a literal argument.
    ///
    /// Example:
    /// ```vole
    /// let local0: i64 | Sent1 = Sent1
    /// let local1 = ((x: i64) -> i64 => when { local0 is Sent1 => x + 1, _ => x })(10)
    /// ```
    fn try_generate_sentinel_closure_capture(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let module_id = ctx.module_id?;
        let module = ctx.table.get_module(module_id)?;

        let sentinels: Vec<_> = module.sentinels().collect();
        if sentinels.is_empty() {
            return None;
        }

        let sentinel_idx = self.rng.gen_range(0..sentinels.len());
        let sentinel_name = sentinels[sentinel_idx].name.clone();
        let sentinel_sym_id = sentinels[sentinel_idx].id;

        // Create the union variable: i64 | Sentinel
        let union_var = ctx.new_local_name();
        let assign_sentinel = self.rng.gen_bool(0.5);
        let init_value = if assign_sentinel {
            sentinel_name.clone()
        } else {
            let n = self.rng.gen_range(-100..=100);
            format!("{}_i64", n)
        };
        let union_stmt = format!("let {}: i64 | {} = {}", union_var, sentinel_name, init_value);
        ctx.add_local(
            union_var.clone(),
            TypeInfo::Union(vec![
                TypeInfo::Primitive(PrimitiveType::I64),
                TypeInfo::Sentinel(module_id, sentinel_sym_id),
            ]),
            false,
        );

        // Create a closure that captures the union variable
        let result_var = ctx.new_local_name();
        let sentinel_val = self.rng.gen_range(1..=100);
        let arg_val = self.rng.gen_range(1..=50);

        let closure_expr = format!(
            "((x: i64) -> i64 => when {{ {} is {} => x + {}_i64, _ => x }})({})",
            union_var, sentinel_name, sentinel_val, arg_val
        );

        let result_stmt = format!("let {} = {}", result_var, closure_expr);
        ctx.add_local(
            result_var,
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        Some(format!("{}\n{}", union_stmt, result_stmt))
    }

    /// Try to generate a closure that captures a whole struct variable and accesses
    /// multiple fields inside the closure body. This exercises the interaction between
    /// struct value capture in closure environments and field access through captured
    /// aggregate types.
    ///
    /// Pattern A (direct invocation):
    /// ```vole
    /// let result = ((x: i64) -> i64 => x + my_struct.fieldA + my_struct.fieldB)(5)
    /// ```
    ///
    /// Pattern B (iterator chain):
    /// ```vole
    /// let result = [1, 2, 3].iter().map((x: i64) -> i64 => x + my_struct.fieldA).collect()
    /// ```
    fn try_generate_closure_struct_capture(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Guard: skip in generic class method contexts (same issue as field_closure_let)
        if let Some((cls_mod, cls_sym)) = ctx.current_class_sym_id {
            if let Some(symbol) = ctx.table.get_symbol(cls_mod, cls_sym) {
                if let SymbolKind::Class(info) = &symbol.kind {
                    if !info.type_params.is_empty() {
                        return None;
                    }
                }
            }
        }

        let _module_id = ctx.module_id?;

        // Find struct-typed locals with at least 2 numeric fields (i64 or i32)
        // so we can access multiple fields inside the closure
        let mut candidates: Vec<(String, Vec<(String, PrimitiveType)>)> = Vec::new();

        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Struct(mod_id, sym_id) = ty {
                if let Some(sym) = ctx.table.get_symbol(*mod_id, *sym_id) {
                    if let SymbolKind::Struct(ref info) = sym.kind {
                        let numeric_fields: Vec<(String, PrimitiveType)> = info
                            .fields
                            .iter()
                            .filter_map(|f| {
                                if let TypeInfo::Primitive(p) = &f.field_type {
                                    if matches!(p, PrimitiveType::I64 | PrimitiveType::I32) {
                                        return Some((f.name.clone(), *p));
                                    }
                                }
                                None
                            })
                            .collect();
                        if numeric_fields.len() >= 2 {
                            candidates.push((name.clone(), numeric_fields));
                        }
                    }
                }
            }
        }

        // Also check params
        for p in ctx.params {
            if let TypeInfo::Struct(mod_id, sym_id) = &p.param_type {
                if let Some(sym) = ctx.table.get_symbol(*mod_id, *sym_id) {
                    if let SymbolKind::Struct(ref info) = sym.kind {
                        let numeric_fields: Vec<(String, PrimitiveType)> = info
                            .fields
                            .iter()
                            .filter_map(|f| {
                                if let TypeInfo::Primitive(pt) = &f.field_type {
                                    if matches!(pt, PrimitiveType::I64 | PrimitiveType::I32) {
                                        return Some((f.name.clone(), *pt));
                                    }
                                }
                                None
                            })
                            .collect();
                        if numeric_fields.len() >= 2 {
                            candidates.push((p.name.clone(), numeric_fields));
                        }
                    }
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (struct_name, numeric_fields) = candidates[idx].clone();

        // Pick 2-3 fields to use inside the closure
        let num_fields = std::cmp::min(
            numeric_fields.len(),
            self.rng.gen_range(2..=3),
        );
        let mut chosen_fields = numeric_fields;
        // Shuffle and take first num_fields
        for i in (1..chosen_fields.len()).rev() {
            let j = self.rng.gen_range(0..=i);
            chosen_fields.swap(i, j);
        }
        chosen_fields.truncate(num_fields);

        // Check if any chosen field is i32 - if so we need to widen to i64
        let has_i32 = chosen_fields.iter().any(|(_, p)| matches!(p, PrimitiveType::I32));

        // Build the closure body expression: x + struct.field1 + struct.field2 [+ 0_i64]
        let mut body_parts: Vec<String> = vec!["x".to_string()];
        for (field_name, _) in &chosen_fields {
            body_parts.push(format!("{}.{}", struct_name, field_name));
        }
        let mut body_expr = body_parts.join(" + ");
        if has_i32 {
            body_expr = format!("{} + 0_i64", body_expr);
        }

        let use_iter = self.rng.gen_bool(0.4);
        if use_iter {
            // Pattern B: iterator chain with closure capturing struct
            let arr_size = self.rng.gen_range(2..=4);
            let arr_elems: Vec<String> = (0..arr_size)
                .map(|_| {
                    let n = self.rng.gen_range(1..=20);
                    format!("{}", n)
                })
                .collect();

            let result_name = ctx.new_local_name();
            ctx.add_local(
                result_name.clone(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                false,
            );

            Some(format!(
                "let {} = [{}].iter().map((x: i64) -> i64 => {}).collect()",
                result_name,
                arr_elems.join(", "),
                body_expr,
            ))
        } else {
            // Pattern A: direct invocation of closure
            let arg_val = self.rng.gen_range(1..=50);
            let result_name = ctx.new_local_name();
            ctx.add_local(
                result_name.clone(),
                TypeInfo::Primitive(PrimitiveType::I64),
                false,
            );

            Some(format!(
                "let {} = ((x: i64) -> i64 => {})({})",
                result_name, body_expr, arg_val,
            ))
        }
    }

    /// Try to generate a nested closure capture pattern where one closure captures
    /// and invokes another closure that's already in scope.
    ///
    /// Pattern:
    /// ```vole
    /// let f = (x: i64) -> i64 => x + 1
    /// let g = (y: i64) -> i64 => f(y) + 2
    /// let result = g(5)
    /// ```
    ///
    /// Returns `None` if no suitable closure-typed local is in scope.
    fn try_generate_nested_closure_capture(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Guard: skip in generic class method contexts (capture bug)
        if let Some((cls_mod, cls_sym)) = ctx.current_class_sym_id {
            if let Some(symbol) = ctx.table.get_symbol(cls_mod, cls_sym) {
                if let SymbolKind::Class(info) = &symbol.kind {
                    if !info.type_params.is_empty() {
                        return None;
                    }
                }
            }
        }

        // Find closure-typed locals that take one i64 param and return i64
        let mut candidates: Vec<String> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Function {
                param_types,
                return_type,
            } = ty
            {
                if param_types.len() == 1
                    && matches!(param_types[0], TypeInfo::Primitive(PrimitiveType::I64))
                    && matches!(return_type.as_ref(), TypeInfo::Primitive(PrimitiveType::I64))
                {
                    candidates.push(name.clone());
                }
            }
        }

        // Also check params
        for p in ctx.params {
            if let TypeInfo::Function {
                param_types,
                return_type,
            } = &p.param_type
            {
                if param_types.len() == 1
                    && matches!(param_types[0], TypeInfo::Primitive(PrimitiveType::I64))
                    && matches!(return_type.as_ref(), TypeInfo::Primitive(PrimitiveType::I64))
                {
                    candidates.push(p.name.clone());
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let inner_fn = candidates[idx].clone();

        // Create the outer closure that captures the inner closure
        let outer_fn = ctx.new_local_name();
        let offset_val = self.rng.gen_range(1..=20);
        let op = match self.rng.gen_range(0..3) {
            0 => format!("{}(y) + {}", inner_fn, offset_val),
            1 => format!("{}(y) * {}", inner_fn, offset_val),
            _ => format!("{}(y + {})", inner_fn, offset_val),
        };

        let outer_closure = format!("let {} = (y: i64) -> i64 => {}", outer_fn, op);
        ctx.add_local(
            outer_fn.clone(),
            TypeInfo::Function {
                param_types: vec![TypeInfo::Primitive(PrimitiveType::I64)],
                return_type: Box::new(TypeInfo::Primitive(PrimitiveType::I64)),
            },
            false,
        );

        // Invoke the outer closure
        let result_name = ctx.new_local_name();
        let arg_val = self.rng.gen_range(1..=50);
        let call_stmt = format!("let {} = {}({})", result_name, outer_fn, arg_val);
        ctx.add_local(
            result_name,
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        let indent = "    ".repeat(self.indent);
        Some(format!("{}\n{}{}", outer_closure, indent, call_stmt))
    }

    /// Try to generate a string interpolation let-binding.
    ///
    /// Creates strings with `{expr}` interpolations using variables in scope.
    /// Exercises the parser's handling of nested expressions inside strings
    /// and the codegen for string formatting/concatenation.
    ///
    /// Patterns:
    /// ```vole
    /// let s = "value: {x}"
    /// let s = "{x} + {y} = {x + y}"
    /// let s = "length: {arr.length()}"
    /// ```
    fn try_generate_string_interpolation_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Collect variables suitable for interpolation (numeric, string, bool)
        let mut candidates: Vec<(String, PrimitiveType)> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Primitive(p) = ty {
                if matches!(
                    p,
                    PrimitiveType::I64
                        | PrimitiveType::I32
                        | PrimitiveType::F64
                        | PrimitiveType::String
                        | PrimitiveType::Bool
                ) {
                    candidates.push((name.clone(), *p));
                }
            }
        }
        for p in ctx.params {
            if let TypeInfo::Primitive(pt) = &p.param_type {
                if matches!(
                    pt,
                    PrimitiveType::I64
                        | PrimitiveType::I32
                        | PrimitiveType::F64
                        | PrimitiveType::String
                        | PrimitiveType::Bool
                ) {
                    candidates.push((p.name.clone(), *pt));
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        // Pick 1-3 interpolation segments
        let num_segments = std::cmp::min(candidates.len(), self.rng.gen_range(1..=3));

        // Shuffle candidates for variety
        for i in (1..candidates.len()).rev() {
            let j = self.rng.gen_range(0..=i);
            candidates.swap(i, j);
        }

        let prefixes = ["val: ", "result: ", "x=", "", "data: ", "v="];
        let separators = [", ", " | ", " + ", " and ", " / "];

        let mut parts: Vec<String> = Vec::new();
        for i in 0..num_segments {
            let (name, prim) = &candidates[i];

            // Decide what expression to interpolate
            let expr = match self.rng.gen_range(0..6) {
                0 => {
                    // Simple variable reference
                    name.clone()
                }
                1 if matches!(prim, PrimitiveType::I64 | PrimitiveType::I32) => {
                    // Arithmetic expression
                    let n = self.rng.gen_range(1..=10);
                    format!("{} + {}", name, n)
                }
                2 if matches!(prim, PrimitiveType::String) => {
                    // String length method
                    format!("{}.length()", name)
                }
                3 if matches!(prim, PrimitiveType::I64 | PrimitiveType::I32) => {
                    // When expression inside interpolation (feature interaction):
                    // "text {when { var > 5 => var * 2, _ => 0 }}"
                    let threshold = self.rng.gen_range(0..=10);
                    let suffix = if matches!(prim, PrimitiveType::I32) {
                        "_i32"
                    } else {
                        ""
                    };
                    format!(
                        "when {{ {} > {}{} => {} * 2{}, _ => 0{} }}",
                        name, threshold, suffix, name, suffix, suffix
                    )
                }
                4 if matches!(prim, PrimitiveType::Bool) => {
                    // When expression on bool inside interpolation:
                    // "text {when { flag => 1, _ => 0 }}"
                    format!("when {{ {} => 1, _ => 0 }}", name)
                }
                5 if matches!(
                    prim,
                    PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64
                ) =>
                {
                    // .to_string() inside interpolation (feature interaction):
                    // "text {num.to_string()}"
                    format!("{}.to_string()", name)
                }
                _ => {
                    // Simple variable reference (fallback)
                    name.clone()
                }
            };

            if i == 0 {
                let prefix_idx = self.rng.gen_range(0..prefixes.len());
                parts.push(format!("{}{{{}}}", prefixes[prefix_idx], expr));
            } else {
                let sep_idx = self.rng.gen_range(0..separators.len());
                parts.push(format!("{}{{{}}}", separators[sep_idx], expr));
            }
        }

        let interpolated_string = parts.join("");
        let result_name = ctx.new_local_name();
        ctx.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        Some(format!("let {} = \"{}\"", result_name, interpolated_string))
    }

    /// Generate a `let parts = "a,b,c".split(",").collect()` statement.
    ///
    /// Creates a string literal with known delimiters, splits it, and collects
    /// into a `[string]` array. Optionally chains an iterator operation on the
    /// result (e.g., `.count()`, `.first()`).
    fn generate_string_split_let(&mut self, ctx: &mut StmtContext) -> String {
        let words: Vec<&str> = vec![
            "alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta",
        ];
        let delimiters = [",", ";", "::", "-", "_"];
        let delim = delimiters[self.rng.gen_range(0..delimiters.len())];

        // Pick 2-4 words
        let word_count = self.rng.gen_range(2..=4);
        let mut selected: Vec<&str> = Vec::new();
        for _ in 0..word_count {
            selected.push(words[self.rng.gen_range(0..words.len())]);
        }
        let joined = selected.join(delim);

        let name = ctx.new_local_name();

        // 70% collect to [string], 15% count (i64), 15% first (string?)
        let choice = self.rng.gen_range(0..20);
        if choice < 14 {
            // Collect to [string]
            ctx.add_local(
                name.clone(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                false,
            );
            format!(
                "let {} = \"{}\".split(\"{}\").collect()",
                name, joined, delim
            )
        } else if choice < 17 {
            // Count → i64
            ctx.add_local(
                name.clone(),
                TypeInfo::Primitive(PrimitiveType::I64),
                false,
            );
            format!(
                "let {} = \"{}\".split(\"{}\").count()",
                name, joined, delim
            )
        } else {
            // First → string? (use ?? to unwrap to string)
            ctx.add_local(
                name.clone(),
                TypeInfo::Primitive(PrimitiveType::String),
                false,
            );
            format!(
                "let {} = \"{}\".split(\"{}\").first() ?? \"\"",
                name, joined, delim
            )
        }
    }

    /// Try to generate an iterator predicate let-binding.
    ///
    /// Finds a numeric array in scope and generates:
    /// - `let b = arr.iter().any((x) => x > 0)` → bool
    /// - `let b = arr.iter().all((x) => x > 0)` → bool
    fn try_generate_iter_predicate_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find numeric arrays in scope (i64, i32, f64)
        let mut array_vars: Vec<(String, PrimitiveType)> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Array(inner) = ty {
                if let TypeInfo::Primitive(
                    p @ (PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64),
                ) = inner.as_ref()
                {
                    array_vars.push((name.clone(), *p));
                }
            }
        }
        if array_vars.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..array_vars.len());
        let (arr_name, elem_prim) = &array_vars[idx];
        let result_name = ctx.new_local_name();

        let suffix = match elem_prim {
            PrimitiveType::I32 => "_i32",
            PrimitiveType::F64 => "_f64",
            _ => "",
        };

        // Pick any() or all()
        let method = if self.rng.gen_bool(0.5) { "any" } else { "all" };

        // Generate a simple predicate closure
        let threshold = self.rng.gen_range(0..=5);
        let op = match self.rng.gen_range(0..3) {
            0 => ">",
            1 => "<",
            _ => ">=",
        };

        let call_expr = format!(
            "{}.iter().{}((x) => x {} {}{})",
            arr_name, method, op, threshold, suffix
        );

        ctx.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );
        Some(format!("let {} = {}", result_name, call_expr))
    }

    /// Try to generate an iterator chunks/windows let-binding.
    ///
    /// Finds a primitive array in scope and generates one of:
    /// - `.chunks(N).count()` → i64
    /// - `.windows(N).count()` → i64
    /// - `.chunks(N).flatten().collect()` → [T] (original element type array)
    /// - `.windows(N).flatten().collect()` → [T]
    fn try_generate_iter_chunks_windows_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Find arrays with primitive element types
        let mut array_vars: Vec<(String, PrimitiveType)> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Array(inner) = ty {
                if let TypeInfo::Primitive(p) = inner.as_ref() {
                    match p {
                        PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64
                        | PrimitiveType::Bool | PrimitiveType::String => {
                            array_vars.push((name.clone(), *p));
                        }
                        _ => {}
                    }
                }
            }
        }
        if array_vars.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..array_vars.len());
        let (arr_name, elem_prim) = &array_vars[idx];
        let elem_prim = *elem_prim;
        let arr_name = arr_name.clone();
        let result_name = ctx.new_local_name();

        // Pick chunks or windows
        let method = if self.rng.gen_bool(0.5) {
            "chunks"
        } else {
            "windows"
        };

        // Chunk/window size: 1, 2, or 3
        let size = self.rng.gen_range(1..=3);

        // Optional prefix: ~20% chance to add .filter() or .sorted() before chunks/windows
        let is_numeric = matches!(elem_prim, PrimitiveType::I64 | PrimitiveType::F64);
        let prefix = if self.rng.gen_bool(0.20) && is_numeric {
            match self.rng.gen_range(0..2) {
                0 => ".sorted()".to_string(),
                _ => {
                    let pred = self.generate_filter_closure_body(elem_prim);
                    format!(".filter((x) => {})", pred)
                }
            }
        } else {
            String::new()
        };

        // Pick terminal: count() (50%), flatten().collect() (50%)
        let (terminal, result_type) = if self.rng.gen_bool(0.5) {
            (
                ".count()".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            )
        } else {
            (
                ".flatten().collect()".to_string(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_prim))),
            )
        };

        ctx.add_local(result_name.clone(), result_type, false);
        Some(format!(
            "let {} = {}.iter(){}.{}({}){}",
            result_name, arr_name, prefix, method, size, terminal
        ))
    }

    /// Try to generate a `for_each` iterator statement.
    ///
    /// Produces: `arr.iter()[.chain].for_each((x) => { let y = expr })`
    fn try_generate_for_each_stmt(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let mut array_vars: Vec<(String, PrimitiveType)> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Array(inner) = ty {
                if let TypeInfo::Primitive(p) = inner.as_ref() {
                    match p {
                        PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::String => {
                            array_vars.push((name.clone(), *p));
                        }
                        _ => {}
                    }
                }
            }
        }
        for param in ctx.params.iter() {
            if let TypeInfo::Array(inner) = &param.param_type {
                if let TypeInfo::Primitive(p) = inner.as_ref() {
                    match p {
                        PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::String => {
                            array_vars.push((param.name.clone(), *p));
                        }
                        _ => {}
                    }
                }
            }
        }
        if array_vars.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..array_vars.len());
        let (arr_name, elem_prim) = &array_vars[idx];
        let arr_name = arr_name.clone();
        let elem_prim = *elem_prim;

        // Optional prefix chain (~30% chance)
        let prefix = if self.rng.gen_bool(0.30)
            && matches!(elem_prim, PrimitiveType::I64 | PrimitiveType::I32)
        {
            let pred = self.generate_filter_closure_body(elem_prim);
            format!(".filter((x) => {})", pred)
        } else {
            String::new()
        };

        // Body: a simple let binding inside the closure
        let body = match elem_prim {
            PrimitiveType::I64 | PrimitiveType::I32 => {
                match self.rng.gen_range(0..3) {
                    0 => "let y = x * 2".to_string(),
                    1 => "let y = x + 1".to_string(),
                    _ => "let y = x".to_string(),
                }
            }
            PrimitiveType::String => "let y = x".to_string(),
            _ => "let y = x".to_string(),
        };

        Some(format!(
            "{}.iter(){}.for_each((x) => {{ {} }})",
            arr_name, prefix, body
        ))
    }

    /// Try to generate an `nth` iterator call with match on the optional result.
    ///
    /// Produces:
    /// ```vole
    /// let r = arr.iter()[.chain].nth(0)
    /// let v = match r {
    ///     T => expr
    ///     nil => default
    /// }
    /// ```
    fn try_generate_nth_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let mut array_vars: Vec<(String, PrimitiveType)> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Array(inner) = ty {
                if let TypeInfo::Primitive(p) = inner.as_ref() {
                    match p {
                        PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::String
                        | PrimitiveType::Bool => {
                            array_vars.push((name.clone(), *p));
                        }
                        _ => {}
                    }
                }
            }
        }
        for param in ctx.params.iter() {
            if let TypeInfo::Array(inner) = &param.param_type {
                if let TypeInfo::Primitive(p) = inner.as_ref() {
                    match p {
                        PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::String
                        | PrimitiveType::Bool => {
                            array_vars.push((param.name.clone(), *p));
                        }
                        _ => {}
                    }
                }
            }
        }
        if array_vars.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..array_vars.len());
        let (arr_name, elem_prim) = &array_vars[idx];
        let arr_name = arr_name.clone();
        let elem_prim = *elem_prim;

        let nth_name = ctx.new_local_name();
        let result_name = ctx.new_local_name();

        // Use index 0 (safe - arrays always have at least 1 element)
        let nth_idx = 0;

        // Optional prefix chain
        let prefix = if self.rng.gen_bool(0.25)
            && matches!(elem_prim, PrimitiveType::I64 | PrimitiveType::I32)
        {
            match self.rng.gen_range(0..2) {
                0 => {
                    let pred = self.generate_filter_closure_body(elem_prim);
                    format!(".filter((x) => {})", pred)
                }
                _ => ".sorted()".to_string(),
            }
        } else {
            String::new()
        };

        // The result of nth is optional (T | nil), we match on it
        let indent = "    ".repeat(self.indent + 1);
        let close_indent = "    ".repeat(self.indent);

        // Default value for nil case
        let default_expr = match elem_prim {
            PrimitiveType::I64 => "0".to_string(),
            PrimitiveType::I32 => "0_i32".to_string(),
            PrimitiveType::String => "\"\"".to_string(),
            PrimitiveType::Bool => "false".to_string(),
            _ => "0".to_string(),
        };

        // Register the result variable as the element type
        let result_type = TypeInfo::Primitive(elem_prim);
        ctx.add_local(result_name.clone(), result_type, false);

        // ~40% chance: use `when { r is Type => ... }` instead of match
        if self.rng.gen_bool(0.40) {
            Some(format!(
                "let {} = {}.iter(){}.nth({})\n\
                 let {} = when {{\n\
                 {}{} is {} => {}\n\
                 {}_ => {}\n\
                 {}}}",
                nth_name,
                arr_name,
                prefix,
                nth_idx,
                result_name,
                indent,
                nth_name,
                elem_prim.as_str(),
                nth_name,
                indent,
                default_expr,
                close_indent,
            ))
        } else {
            Some(format!(
                "let {} = {}.iter(){}.nth({})\n\
                 let {} = match {} {{\n\
                 {}{} => {}\n\
                 {}nil => {}\n\
                 {}}}",
                nth_name,
                arr_name,
                prefix,
                nth_idx,
                result_name,
                nth_name,
                indent,
                elem_prim.as_str(),
                nth_name,
                indent,
                default_expr,
                close_indent,
            ))
        }
    }

    /// Try to generate a string iteration let-binding.
    ///
    /// Finds a string variable and chains an iterator operation on it:
    /// - `str.iter().count()` → i64
    /// - `str.iter().collect()` → [string]
    /// - `str.iter().filter((c) => c != " ").count()` → i64
    /// - `str.iter().any((c) => c == "a")` → bool
    fn try_generate_string_iter_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find string variables in scope
        let mut string_vars: Vec<String> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if matches!(ty, TypeInfo::Primitive(PrimitiveType::String)) {
                string_vars.push(name.clone());
            }
        }
        for param in ctx.params.iter() {
            if matches!(&param.param_type, TypeInfo::Primitive(PrimitiveType::String)) {
                string_vars.push(param.name.clone());
            }
        }
        if string_vars.is_empty() {
            return None;
        }

        let str_name = &string_vars[self.rng.gen_range(0..string_vars.len())];
        let str_name = str_name.clone();
        let result_name = ctx.new_local_name();

        // ~30% chance: chain a string method before iteration
        let method_prefix = if self.rng.gen_bool(0.30) {
            let methods = [".to_upper()", ".to_lower()", ".trim()"];
            methods[self.rng.gen_range(0..methods.len())].to_string()
        } else {
            String::new()
        };

        match self.rng.gen_range(0..5) {
            0 => {
                // str[.method()].iter().count() → i64
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                Some(format!(
                    "let {} = {}{}.iter().count()",
                    result_name, str_name, method_prefix
                ))
            }
            1 => {
                // str[.method()].iter().collect() → [string]
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                    false,
                );
                Some(format!(
                    "let {} = {}{}.iter().collect()",
                    result_name, str_name, method_prefix
                ))
            }
            2 => {
                // str[.method()].iter().filter((c) => c != " ").count() → i64
                let filter_chars = [" ", "a", "e", "o"];
                let fc = filter_chars[self.rng.gen_range(0..filter_chars.len())];
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                Some(format!(
                    "let {} = {}{}.iter().filter((c) => c != \"{}\").count()",
                    result_name, str_name, method_prefix, fc
                ))
            }
            3 => {
                // str[.method()].iter().any/all((c) => c == "x") → bool
                let check_chars = ["a", "e", " ", "x", "1"];
                let cc = check_chars[self.rng.gen_range(0..check_chars.len())];
                let method = if self.rng.gen_bool(0.5) { "any" } else { "all" };
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                    false,
                );
                Some(format!(
                    "let {} = {}{}.iter().{}((c) => c == \"{}\")",
                    result_name, str_name, method_prefix, method, cc
                ))
            }
            _ => {
                // str[.method()].iter().map((c) => c + "!").collect() → [string]
                let suffixes = ["!", "?", "_", "+"];
                let sf = suffixes[self.rng.gen_range(0..suffixes.len())];
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                    false,
                );
                Some(format!(
                    "let {} = {}{}.iter().map((c) => c + \"{}\").collect()",
                    result_name, str_name, method_prefix, sf
                ))
            }
        }
    }

    /// Try to generate a string method call let-binding.
    ///
    /// Finds a string-typed variable in scope and calls a random method on it:
    /// - `.length()` → i64
    /// - `.contains("literal")` → bool
    /// Try to generate a re-iteration let-binding.
    ///
    /// Finds an existing array-typed local variable and chains a new iterator
    /// operation on it. This exercises the codegen path of iterating over
    /// dynamically-created arrays (results of prior .collect() calls).
    fn try_generate_reiterate_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find i64 array locals in scope
        let mut i64_array_vars: Vec<String> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Array(inner) = ty {
                if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::I64)) {
                    i64_array_vars.push(name.clone());
                }
            }
        }
        if i64_array_vars.is_empty() {
            return None;
        }

        let arr_name = &i64_array_vars[self.rng.gen_range(0..i64_array_vars.len())];
        let result_name = ctx.new_local_name();

        // Pick a chain + terminal combination
        let (chain, result_type) = match self.rng.gen_range(0..5) {
            0 => {
                // .iter().map((x) => x * 2).collect()
                let body = self.generate_map_closure_body(PrimitiveType::I64);
                (
                    format!(".iter().map((x) => {}).collect()", body),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                )
            }
            1 => {
                // .iter().filter((x) => PRED).count()
                let pred = self.generate_filter_closure_body(PrimitiveType::I64);
                (
                    format!(".iter().filter((x) => {}).count()", pred),
                    TypeInfo::Primitive(PrimitiveType::I64),
                )
            }
            2 => {
                // .iter().sorted().collect()
                (
                    ".iter().sorted().collect()".to_string(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                )
            }
            3 => {
                // .iter().enumerate().count()
                (
                    ".iter().enumerate().count()".to_string(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                )
            }
            _ => {
                // .iter().sum()
                (
                    ".iter().sum()".to_string(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                )
            }
        };

        ctx.add_local(result_name.clone(), result_type, false);
        Some(format!("let {} = {}{}", result_name, arr_name, chain))
    }

    /// - `.starts_with("literal")` → bool
    /// - `.ends_with("literal")` → bool
    /// - `.trim()` → string
    /// - `.to_upper()` → string
    /// - `.to_lower()` → string
    fn try_generate_string_method_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find a string-typed variable in scope
        let mut string_vars: Vec<String> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if matches!(ty, TypeInfo::Primitive(PrimitiveType::String)) {
                string_vars.push(name.clone());
            }
        }
        for param in ctx.params {
            if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::String)) {
                string_vars.push(param.name.clone());
            }
        }
        if string_vars.is_empty() {
            return None;
        }

        let var_name = &string_vars[self.rng.gen_range(0..string_vars.len())];
        let result_name = ctx.new_local_name();

        // Pick a random method
        let method = self.rng.gen_range(0..7);
        let (call_expr, result_type) = match method {
            0 => {
                // .length() → i64
                (
                    format!("{}.length()", var_name),
                    TypeInfo::Primitive(PrimitiveType::I64),
                )
            }
            1 => {
                // .contains("literal") → bool
                let needle = Self::random_short_string(&mut self.rng);
                (
                    format!("{}.contains(\"{}\")", var_name, needle),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                )
            }
            2 => {
                // .starts_with("literal") → bool
                let needle = Self::random_short_string(&mut self.rng);
                (
                    format!("{}.starts_with(\"{}\")", var_name, needle),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                )
            }
            3 => {
                // .ends_with("literal") → bool
                let needle = Self::random_short_string(&mut self.rng);
                (
                    format!("{}.ends_with(\"{}\")", var_name, needle),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                )
            }
            4 => {
                // .trim() → string
                (
                    format!("{}.trim()", var_name),
                    TypeInfo::Primitive(PrimitiveType::String),
                )
            }
            5 => {
                // .to_upper() → string
                (
                    format!("{}.to_upper()", var_name),
                    TypeInfo::Primitive(PrimitiveType::String),
                )
            }
            _ => {
                // .to_lower() → string
                (
                    format!("{}.to_lower()", var_name),
                    TypeInfo::Primitive(PrimitiveType::String),
                )
            }
        };

        // ~30% chance to chain an additional method when current result is string.
        // This produces patterns like str.trim().to_upper() or
        // str.to_lower().contains("x") which stress multi-step method dispatch.
        let (call_expr, result_type) =
            if matches!(result_type, TypeInfo::Primitive(PrimitiveType::String))
                && self.rng.gen_bool(0.30)
            {
                let chain = self.rng.gen_range(0..6);
                match chain {
                    0 => (
                        format!("{}.length()", call_expr),
                        TypeInfo::Primitive(PrimitiveType::I64),
                    ),
                    1 => {
                        let needle = Self::random_short_string(&mut self.rng);
                        (
                            format!("{}.contains(\"{}\")", call_expr, needle),
                            TypeInfo::Primitive(PrimitiveType::Bool),
                        )
                    }
                    2 => (
                        format!("{}.trim()", call_expr),
                        TypeInfo::Primitive(PrimitiveType::String),
                    ),
                    3 => (
                        format!("{}.to_upper()", call_expr),
                        TypeInfo::Primitive(PrimitiveType::String),
                    ),
                    4 => (
                        format!("{}.to_lower()", call_expr),
                        TypeInfo::Primitive(PrimitiveType::String),
                    ),
                    _ => {
                        let needle = Self::random_short_string(&mut self.rng);
                        (
                            format!("{}.starts_with(\"{}\")", call_expr, needle),
                            TypeInfo::Primitive(PrimitiveType::Bool),
                        )
                    }
                }
            } else {
                (call_expr, result_type)
            };

        ctx.add_local(result_name.clone(), result_type, false);
        Some(format!("let {} = {}", result_name, call_expr))
    }

    /// Generate a short random string for string method arguments.
    /// Includes empty string and escape sequences to stress edge cases.
    fn random_short_string<R2: Rng>(rng: &mut R2) -> String {
        let words = [
            "hello", "world", "test", "foo", "bar", "abc", "xyz", "str",
            "", "\\n", "\\t", " ", "a",
        ];
        words[rng.gen_range(0..words.len())].to_string()
    }

    /// Generate a checked/wrapping/saturating arithmetic call using `std:lowlevel` intrinsics.
    ///
    /// Picks two numeric values of the same type and applies a random operation:
    /// - wrapping_add/sub/mul: returns T (wraps on overflow)
    /// - saturating_add/sub/mul: returns T (clamps on overflow)
    /// - checked_add/sub/mul/div: returns T? (nil on overflow), unwrapped with ??
    ///
    /// Requires `ctx.has_lowlevel_import` to be true.
    fn generate_checked_arithmetic_let(&mut self, ctx: &mut StmtContext) -> String {
        // Pick a random integer type to work with
        let int_types = [
            PrimitiveType::I32,
            PrimitiveType::I64,
            PrimitiveType::I8,
            PrimitiveType::I16,
        ];
        let prim_type = int_types[self.rng.gen_range(0..int_types.len())];
        let type_info = TypeInfo::Primitive(prim_type);
        let type_suffix = match prim_type {
            PrimitiveType::I8 => "_i8",
            PrimitiveType::I16 => "_i16",
            PrimitiveType::I32 => "_i32",
            PrimitiveType::I64 => "_i64",
            _ => "_i64",
        };

        // Find existing locals/params of the matching type
        let mut operand_names: Vec<String> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if *ty == type_info {
                operand_names.push(name.clone());
            }
        }
        for param in ctx.params {
            if param.param_type == type_info {
                operand_names.push(param.name.clone());
            }
        }

        // Generate operand expressions: use existing vars or fresh literals
        let (a_expr, b_expr) = if operand_names.len() >= 2 {
            let idx_a = self.rng.gen_range(0..operand_names.len());
            let mut idx_b = self.rng.gen_range(0..operand_names.len());
            // Allow same var for both operands (wrapping_add(x, x) is valid)
            if operand_names.len() > 2 {
                while idx_b == idx_a {
                    idx_b = self.rng.gen_range(0..operand_names.len());
                }
            }
            (operand_names[idx_a].clone(), operand_names[idx_b].clone())
        } else if operand_names.len() == 1 {
            // Use the one var + a literal
            let lit = self.rng.gen_range(1..=50);
            (
                operand_names[0].clone(),
                format!("{}{}", lit, type_suffix),
            )
        } else {
            // Generate two fresh literals
            let a = self.rng.gen_range(-50..=50);
            let b = self.rng.gen_range(1..=50);
            (
                format!("{}{}", a, type_suffix),
                format!("{}{}", b, type_suffix),
            )
        };

        // Pick operation category: 40% wrapping, 30% saturating, 30% checked
        let category = self.rng.gen_range(0..10);
        let (func_name, is_checked) = if category < 4 {
            // Wrapping
            let ops = ["wrapping_add", "wrapping_sub", "wrapping_mul"];
            (ops[self.rng.gen_range(0..ops.len())], false)
        } else if category < 7 {
            // Saturating
            let ops = ["saturating_add", "saturating_sub", "saturating_mul"];
            (ops[self.rng.gen_range(0..ops.len())], false)
        } else {
            // Checked (returns T?)
            let ops = [
                "checked_add",
                "checked_sub",
                "checked_mul",
                "checked_div",
            ];
            (ops[self.rng.gen_range(0..ops.len())], true)
        };

        let name = ctx.new_local_name();

        if is_checked {
            // checked_* returns T?, use ?? to unwrap
            let default_val = format!("0{}", type_suffix);
            ctx.add_local(name.clone(), type_info, false);
            format!(
                "let {} = {}({}, {}) ?? {}",
                name, func_name, a_expr, b_expr, default_val
            )
        } else {
            // wrapping_*/saturating_* returns T directly
            ctx.add_local(name.clone(), type_info, false);
            format!("let {} = {}({}, {})", name, func_name, a_expr, b_expr)
        }
    }

    /// Try to generate a match expression on the result of a method call.
    ///
    /// Finds a class instance in scope with a method returning i64, calls it,
    /// and matches on the result with 2-3 literal arms + wildcard.
    ///
    /// ```vole
    /// let result = match instance.method(args) {
    ///     0 => 100
    ///     1 => 200
    ///     _ => 300
    /// }
    /// ```
    fn try_generate_match_on_method_result(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let _ = ctx.module_id?;

        // Skip in method bodies to avoid mutual recursion
        if ctx.current_class_sym_id.is_some() {
            return None;
        }

        // Find class-typed locals with methods that return i64
        let mut candidates: Vec<(String, String, Vec<ParamInfo>)> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Class(mod_id, sym_id) = ty {
                if let Some(sym) = ctx.table.get_symbol(*mod_id, *sym_id) {
                    if let SymbolKind::Class(ref info) = sym.kind {
                        if info.type_params.is_empty() {
                            for method in &info.methods {
                                if matches!(method.return_type, TypeInfo::Primitive(PrimitiveType::I64))
                                {
                                    candidates.push((
                                        name.clone(),
                                        method.name.clone(),
                                        method.params.clone(),
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (instance_name, method_name, params) = candidates[idx].clone();

        // Generate arguments
        let expr_ctx = ctx.to_expr_context();
        let args: Vec<String> = params
            .iter()
            .map(|p| {
                let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                expr_gen.generate_arg_expr(&p.param_type, &expr_ctx)
            })
            .collect();

        let call_expr = format!("{}.{}({})", instance_name, method_name, args.join(", "));

        // Generate 2-3 match arms + wildcard
        let num_arms = self.rng.gen_range(2..=3);
        let indent = "    ".repeat(self.indent + 1);
        let close_indent = "    ".repeat(self.indent);

        let result_type = TypeInfo::Primitive(PrimitiveType::I64);
        let mut arms = Vec::new();
        let mut used_values = std::collections::HashSet::new();
        for _ in 0..num_arms {
            let val = loop {
                let v = self.rng.gen_range(-5..=20);
                if used_values.insert(v) {
                    break v;
                }
            };
            let arm_expr = self.generate_match_arm_value(&result_type, &expr_ctx);
            arms.push(format!("{}{} => {}", indent, val, arm_expr));
        }
        // Wildcard arm
        let wildcard_expr = self.generate_match_arm_value(&result_type, &expr_ctx);
        arms.push(format!("{}_ => {}", indent, wildcard_expr));

        let result_name = ctx.new_local_name();
        ctx.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        Some(format!(
            "let {} = match {} {{\n{}\n{}}}",
            result_name,
            call_expr,
            arms.join("\n"),
            close_indent,
        ))
    }

    /// Try to generate an iterator map that calls a class method inside the closure.
    ///
    /// Requires both an i64 array variable and a non-generic class instance with
    /// a method that takes a single i64 param and returns i64.
    ///
    /// Pattern A (collect):
    /// ```vole
    /// let result = arr.iter().map((x: i64) -> i64 => instance.method(x)).collect()
    /// ```
    ///
    /// Pattern B (sum):
    /// ```vole
    /// let result = arr.iter().map((x: i64) -> i64 => instance.method(x)).sum()
    /// ```
    ///
    /// Skipped in method bodies to avoid mutual recursion.
    /// Returns `None` if no suitable array + class instance combination is in scope.
    fn try_generate_iter_method_map(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Skip in method bodies to avoid mutual recursion
        if ctx.current_class_sym_id.is_some() {
            return None;
        }

        // Find i64 array variables in scope (locals + params)
        let mut array_candidates: Vec<String> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Array(elem) = ty {
                if matches!(elem.as_ref(), TypeInfo::Primitive(PrimitiveType::I64)) {
                    array_candidates.push(name.clone());
                }
            }
        }
        for param in ctx.params.iter() {
            if let TypeInfo::Array(elem) = &param.param_type {
                if matches!(elem.as_ref(), TypeInfo::Primitive(PrimitiveType::I64)) {
                    array_candidates.push(param.name.clone());
                }
            }
        }
        if array_candidates.is_empty() {
            return None;
        }

        // Find class instances with methods returning i64 that take 0 or 1 numeric params.
        // Find class instances (from locals AND params) with methods returning i64,
        // all-primitive params, and at least one i64 param (to pass `x` into).
        // Tracks (instance_name, method_name, params_vec).
        let mut method_candidates: Vec<(String, String, Vec<ParamInfo>)> = Vec::new();

        // Helper: scan a class type for suitable methods
        let mut scan_class = |name: &str, mod_id: ModuleId, sym_id: SymbolId| {
            if let Some(sym) = ctx.table.get_symbol(mod_id, sym_id) {
                if let SymbolKind::Class(ref info) = sym.kind {
                    if info.type_params.is_empty() {
                        for method in &info.methods {
                            if !matches!(
                                method.return_type,
                                TypeInfo::Primitive(PrimitiveType::I64)
                            ) {
                                continue;
                            }
                            let has_i64 = method.params.iter().any(|p| {
                                matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64))
                            });
                            if has_i64 && !method.params.is_empty() {
                                method_candidates.push((
                                    name.to_string(),
                                    method.name.clone(),
                                    method.params.clone(),
                                ));
                            }
                        }
                    }
                }
            }
        };

        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Class(mod_id, sym_id) = ty {
                scan_class(name, *mod_id, *sym_id);
            }
        }
        for param in ctx.params.iter() {
            if let TypeInfo::Class(mod_id, sym_id) = &param.param_type {
                scan_class(&param.name, *mod_id, *sym_id);
            }
        }
        if method_candidates.is_empty() {
            return None;
        }

        let arr_idx = self.rng.gen_range(0..array_candidates.len());
        let arr_name = &array_candidates[arr_idx];

        let meth_idx = self.rng.gen_range(0..method_candidates.len());
        let (instance_name, method_name, params) = &method_candidates[meth_idx];

        // Build argument list: pick the first i64 param to receive `x`,
        // generate simple literals for all other params.
        let mut x_used = false;
        let args: Vec<String> = params
            .iter()
            .map(|p| {
                if !x_used
                    && matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64))
                {
                    x_used = true;
                    "x".to_string()
                } else {
                    let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                    let expr_ctx = ctx.to_expr_context();
                    expr_gen.generate_simple(&p.param_type, &expr_ctx)
                }
            })
            .collect();
        let closure_body = format!("{}.{}({})", instance_name, method_name, args.join(", "));

        let result_name = ctx.new_local_name();
        let use_sum = self.rng.gen_bool(0.4);

        let stmt = if use_sum {
            ctx.add_local(
                result_name.clone(),
                TypeInfo::Primitive(PrimitiveType::I64),
                false,
            );
            format!(
                "let {} = {}.iter().map((x: i64) -> i64 => {}).sum()",
                result_name, arr_name, closure_body
            )
        } else {
            ctx.add_local(
                result_name.clone(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                false,
            );
            format!(
                "let {} = {}.iter().map((x: i64) -> i64 => {}).collect()",
                result_name, arr_name, closure_body
            )
        };

        Some(stmt)
    }

    /// Try to generate a widening let statement.
    ///
    /// Looks for existing narrow-typed variables in scope and generates a let
    /// that assigns them to a wider-typed variable, exercising Vole's implicit
    /// numeric widening.
    ///
    /// Example: If `narrow_var: i32` is in scope, generates `let wide: i64 = narrow_var`.
    ///
    /// Returns `None` if no suitable widening source is in scope.
    /// Generate an assert statement with a tautological condition.
    ///
    /// Picks a variable in scope and generates conditions like:
    /// ```vole
    /// assert(x == x)
    /// assert(x >= 0 || x < 0)  // always true for integers
    /// assert(true)
    /// ```
    fn try_generate_assert_stmt(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Collect primitive candidates
        let prim_candidates: Vec<(String, TypeInfo)> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(_)))
            .map(|(name, ty, _)| (name.clone(), ty.clone()))
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(_)))
                    .map(|p| (p.name.clone(), p.param_type.clone())),
            )
            .collect();

        // Collect array candidates for iterator-based assertions
        let array_candidates: Vec<(String, TypeInfo)> = ctx
            .params
            .iter()
            .filter(|p| matches!(p.param_type, TypeInfo::Array(_)))
            .map(|p| (p.name.clone(), p.param_type.clone()))
            .collect();

        // Collect string candidates
        let string_candidates: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        let variant = self.rng.gen_range(0..7u32);

        let condition = match variant {
            0 if !prim_candidates.is_empty() => {
                // x == x (reflexive equality)
                let (name, _) = &prim_candidates[self.rng.gen_range(0..prim_candidates.len())];
                format!("{} == {}", name, name)
            }
            1 if !prim_candidates.is_empty() => {
                let (name, ty) = &prim_candidates[self.rng.gen_range(0..prim_candidates.len())];
                match ty {
                    TypeInfo::Primitive(PrimitiveType::I64) => {
                        format!("{} >= 0 || {} < 0", name, name)
                    }
                    TypeInfo::Primitive(PrimitiveType::I32) => {
                        format!("{} >= 0_i32 || {} < 0_i32", name, name)
                    }
                    TypeInfo::Primitive(PrimitiveType::Bool) => {
                        format!("{} || !{}", name, name)
                    }
                    TypeInfo::Primitive(PrimitiveType::String) => {
                        format!("{}.length() >= 0", name)
                    }
                    _ => "true".to_string(),
                }
            }
            2 => "true".to_string(),
            3 if !array_candidates.is_empty() => {
                // assert(arr.iter().count() >= 0)
                let (name, _) = &array_candidates[self.rng.gen_range(0..array_candidates.len())];
                format!("{}.iter().count() >= 0", name)
            }
            4 if !string_candidates.is_empty() => {
                // assert(str.trim().length() >= 0)
                let name = &string_candidates[self.rng.gen_range(0..string_candidates.len())];
                let chain = match self.rng.gen_range(0..3u32) {
                    0 => format!("{}.trim().length() >= 0", name),
                    1 => format!("{}.to_upper().length() == {}.length()", name, name),
                    _ => format!("{}.length() >= 0", name),
                };
                chain
            }
            5 if !array_candidates.is_empty() => {
                // assert(arr.iter().all((x) => x == x))
                let (name, elem_ty) =
                    &array_candidates[self.rng.gen_range(0..array_candidates.len())];
                if let TypeInfo::Array(inner) = elem_ty {
                    if matches!(inner.as_ref(), TypeInfo::Primitive(_)) {
                        format!("{}.iter().all((x) => x == x)", name)
                    } else {
                        "true".to_string()
                    }
                } else {
                    "true".to_string()
                }
            }
            _ => {
                if !prim_candidates.is_empty() {
                    let (name, _) =
                        &prim_candidates[self.rng.gen_range(0..prim_candidates.len())];
                    format!("{} == {}", name, name)
                } else {
                    "true".to_string()
                }
            }
        };

        Some(format!("assert({})", condition))
    }

    /// Generate a variable shadow — re-declare an existing variable with a new value.
    ///
    /// Picks a primitive-typed local and generates:
    /// ```vole
    /// let x = x + 1   // shadows previous x
    /// ```
    ///
    /// Exercises the compiler's variable shadowing and scope resolution.
    /// Generate a match on a boolean variable.
    ///
    /// ```vole
    /// let result = match flag {
    ///     true => expr1
    ///     false => expr2
    /// }
    /// ```
    /// Generate a dead-code assertion: `if false { assert(false) }`.
    ///
    /// Tests the compiler's handling of unreachable code with assertions.
    fn generate_dead_code_assert(&mut self) -> String {
        let variant = self.rng.gen_range(0..3u32);
        match variant {
            0 => "if false {\n    assert(false)\n}".to_string(),
            1 => "if true { } else {\n    assert(false)\n}".to_string(),
            _ => {
                // if false { panic("unreachable") } — but use assert for safety
                "if false {\n    assert(false)\n}".to_string()
            }
        }
    }

    /// Generate a zero-range or single-iteration for loop.
    ///
    /// ```vole
    /// for i in 0..0 { let x = 0 }    // zero iterations
    /// for i in 0..1 { let x = i }    // single iteration
    /// ```
    fn generate_edge_case_for_loop(&mut self, ctx: &mut StmtContext, depth: usize) -> String {
        let iter_name = ctx.new_local_name();
        let range = if self.rng.gen_bool(0.5) {
            "0..0".to_string() // zero iterations
        } else {
            "0..1".to_string() // single iteration
        };

        let was_in_loop = ctx.in_loop;
        let was_in_while_loop = ctx.in_while_loop;
        ctx.in_loop = true;
        ctx.in_while_loop = false;

        let locals_before = ctx.locals.len();
        ctx.add_local(
            iter_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        let body_stmts = self.generate_block(ctx, depth + 1);
        ctx.locals.truncate(locals_before);
        ctx.in_loop = was_in_loop;
        ctx.in_while_loop = was_in_while_loop;

        let body_block = self.format_block(&body_stmts);
        format!("for {} in {} {}", iter_name, range, body_block)
    }

    /// Generate an empty array iterator operation.
    ///
    /// Tests the compiler's handling of zero-length arrays with iterators:
    /// ```vole
    /// let arr: [i64] = []
    /// let n = arr.iter().count()           // 0
    /// let s = arr.iter().sum()             // 0
    /// ```
    fn generate_empty_array_iter(&mut self, ctx: &mut StmtContext) -> String {
        let arr_name = ctx.new_local_name();
        let result_name = ctx.new_local_name();

        let (elem_type, type_str) = match self.rng.gen_range(0..3u32) {
            0 => (PrimitiveType::I64, "i64"),
            1 => (PrimitiveType::I32, "i32"),
            _ => (PrimitiveType::String, "string"),
        };

        ctx.add_local(
            arr_name.clone(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_type))),
            false,
        );

        let terminal = match self.rng.gen_range(0..3u32) {
            0 => {
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                format!("let {} = {}.iter().count()", result_name, arr_name)
            }
            1 if !matches!(elem_type, PrimitiveType::String) => {
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(elem_type),
                    false,
                );
                format!("let {} = {}.iter().sum()", result_name, arr_name)
            }
            _ => {
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_type))),
                    false,
                );
                format!(
                    "let {} = {}.iter().filter((x) => x == x).collect()",
                    result_name, arr_name
                )
            }
        };

        format!(
            "let {}: [{}] = []\n{}{}",
            arr_name,
            type_str,
            "    ".repeat(self.indent),
            terminal
        )
    }

    /// Generate an edge-case string split operation.
    ///
    /// Tests the compiler with degenerate split results:
    /// ```vole
    /// let parts = "".split(",").collect()           // [""]
    /// let parts = "a".split("a").collect()          // ["", ""]
    /// let n = ",,".split(",").collect().iter().count()  // 3
    /// ```
    fn generate_edge_case_split(&mut self, ctx: &mut StmtContext) -> String {
        let result_name = ctx.new_local_name();

        let (input, delim) = match self.rng.gen_range(0..4u32) {
            0 => ("\"\"", "\",\""),        // empty string
            1 => ("\"a\"", "\"a\""),       // delimiter == entire string
            2 => ("\",,\"", "\",\""),      // consecutive delimiters
            _ => ("\"a,b,c\"", "\",\""),   // normal case for safety
        };

        let terminal = match self.rng.gen_range(0..3u32) {
            0 => {
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                format!(
                    "let {} = {}.split({}).collect().iter().count()",
                    result_name, input, delim
                )
            }
            1 => {
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                    false,
                );
                format!(
                    "let {} = {}.split({}).collect()",
                    result_name, input, delim
                )
            }
            _ => {
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                format!(
                    "let {} = {}.split({}).count()",
                    result_name, input, delim
                )
            }
        };

        terminal
    }

    /// Generate a while-loop that runs an iterator terminal each iteration and
    /// accumulates the result.  Stresses iterator alloc/dealloc across loop
    /// iterations — the same pattern that exposed the chunks/windows RC bug.
    fn try_generate_iter_while_accum(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let expr_ctx = ctx.to_expr_context();
        let array_vars = expr_ctx.array_vars();
        let prim_arrays: Vec<(String, PrimitiveType)> = array_vars
            .into_iter()
            .filter_map(|(name, elem_ty)| {
                if let TypeInfo::Primitive(prim) = elem_ty {
                    if matches!(prim, PrimitiveType::I64 | PrimitiveType::I32) {
                        return Some((name, prim));
                    }
                }
                None
            })
            .collect();

        if prim_arrays.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..prim_arrays.len());
        let (arr_name, elem_prim) = &prim_arrays[idx];
        let arr_name = arr_name.clone();
        let elem_prim = *elem_prim;

        let acc_name = ctx.new_local_name();
        let counter_name = ctx.new_local_name();
        let guard_name = ctx.new_local_name();
        let limit = self.rng.gen_range(2..=4);
        let guard_limit = limit * 10;

        // Pick the iterator chain + terminal.
        // Variant 0: .filter((x) => x > counter).count()
        // Variant 1: .map((x) => x * 2).sum()  (ignores counter but still allocs per iter)
        // Variant 2: .filter((x) => x > 0).collect().length()
        let (iter_expr, uses_counter) = match self.rng.gen_range(0..3u32) {
            0 => {
                let filter_body = self.generate_filter_closure_body(elem_prim);
                (format!("{}.iter().filter((x) => {}).count()", arr_name, filter_body), false)
            }
            1 => {
                let map_body = self.generate_map_closure_body(elem_prim);
                (format!("{}.iter().map((x) => {}).sum()", arr_name, map_body), false)
            }
            _ => {
                // Use counter as threshold — tests that loop variable is correctly
                // captured in the filter closure across iterations.
                (format!(
                    "{}.iter().filter((x) => x > {}).count()",
                    arr_name, counter_name
                ), true)
            }
        };
        let _ = uses_counter;

        ctx.add_local(acc_name.clone(), TypeInfo::Primitive(PrimitiveType::I64), true);
        ctx.add_local(counter_name.clone(), TypeInfo::Primitive(PrimitiveType::I64), true);
        ctx.add_local(guard_name.clone(), TypeInfo::Primitive(PrimitiveType::I64), true);

        ctx.protected_vars.push(counter_name.clone());
        ctx.protected_vars.push(guard_name.clone());
        ctx.protected_vars.push(acc_name.clone());
        ctx.protected_vars.push(arr_name.clone());

        let indent = self.indent_str();
        let inner = format!("{}    ", indent);

        let result = format!(
            "let mut {} = 0\n\
             {}let mut {} = 0\n\
             {}let mut {} = 0\n\
             {}while {} < {} {{\n\
             {}{} = {} + 1\n\
             {}if {} > {} {{ break }}\n\
             {}{} = {} + {}\n\
             {}{} = {} + 1\n\
             {}}}",
            acc_name,
            indent, counter_name,
            indent, guard_name,
            indent, counter_name, limit,
            inner, guard_name, guard_name,
            inner, guard_name, guard_limit,
            inner, acc_name, acc_name, iter_expr,
            inner, counter_name, counter_name,
            indent,
        );

        Some(result)
    }

    /// Generate a for-in loop with match on the iteration variable.
    /// Combines iterator chain + for loop + match expression on loop variable.
    fn try_generate_for_in_match_accum(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let expr_ctx = ctx.to_expr_context();
        let array_vars = expr_ctx.array_vars();
        let i64_arrays: Vec<String> = array_vars
            .into_iter()
            .filter_map(|(name, elem_ty)| {
                if matches!(elem_ty, TypeInfo::Primitive(PrimitiveType::I64)) {
                    Some(name)
                } else {
                    None
                }
            })
            .collect();

        if i64_arrays.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..i64_arrays.len());
        let arr_name = i64_arrays[idx].clone();

        let iter_name = ctx.new_local_name();
        let acc_name = ctx.new_local_name();

        // Optional filter prefix: ~40% chance
        let chain = if self.rng.gen_bool(0.40) {
            let pred = self.generate_filter_closure_body(PrimitiveType::I64);
            format!(".filter((x) => {})", pred)
        } else {
            String::new()
        };

        // Generate match arms: 2-3 literal arms + wildcard
        let num_arms = self.rng.gen_range(2..=3);
        let mut arm_values: Vec<i64> = Vec::new();
        for _ in 0..num_arms {
            let v = self.rng.gen_range(0..=10);
            if !arm_values.contains(&v) {
                arm_values.push(v);
            }
        }

        // Build match arms with different result expressions
        let mut arms = Vec::new();
        for v in &arm_values {
            let result = self.rng.gen_range(0..=20);
            arms.push(format!("{} => {}", v, result));
        }
        // Wildcard arm uses the iteration variable itself
        arms.push(format!("_ => {}", iter_name));
        let arms_str = arms.join(", ");

        ctx.add_local(acc_name.clone(), TypeInfo::Primitive(PrimitiveType::I64), true);
        ctx.protected_vars.push(arr_name.clone());
        ctx.protected_vars.push(acc_name.clone());

        let match_name = ctx.new_local_name();
        let indent = self.indent_str();
        let inner = format!("{}    ", indent);
        let inner2 = format!("{}        ", indent);

        let result = format!(
            "let mut {} = 0\n\
             {}for {} in {}.iter(){} {{\n\
             {}let {} = match {} {{\n\
             {}{}\n\
             {}}}\n\
             {}{} = {} + {}\n\
             {}}}",
            acc_name,
            indent, iter_name, arr_name, chain,
            inner, match_name, iter_name,
            inner2, arms_str,
            inner,
            inner, acc_name, acc_name, match_name,
            indent,
        );

        // Clean up protected vars
        ctx.protected_vars.pop();
        ctx.protected_vars.pop();

        Some(result)
    }

    /// Generate a string concatenation let-binding using the `+` operator.
    /// Combines in-scope string variables and/or literals.
    fn try_generate_string_concat_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find string-typed variables in scope
        let string_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if string_vars.is_empty() {
            return None;
        }

        let name = ctx.new_local_name();

        // Pick 2-3 parts to concatenate
        let num_parts = self.rng.gen_range(2..=3);
        let mut parts: Vec<String> = Vec::new();
        for _ in 0..num_parts {
            if !string_vars.is_empty() && self.rng.gen_bool(0.6) {
                let idx = self.rng.gen_range(0..string_vars.len());
                parts.push(string_vars[idx].clone());
            } else {
                // String literal
                let lit = match self.rng.gen_range(0..4u32) {
                    0 => "\" \"".to_string(),
                    1 => "\",\"".to_string(),
                    2 => "\"-\"".to_string(),
                    _ => "\"_\"".to_string(),
                };
                parts.push(lit);
            }
        }

        let expr = parts.join(" + ");
        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        Some(format!("let {} = {}", name, expr))
    }

    /// Generate a let-binding using `.to_string()` on a numeric variable,
    /// optionally concatenated with a string prefix/suffix.
    fn try_generate_to_string_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find numeric variables in scope
        let numeric_vars: Vec<(String, PrimitiveType)> = ctx
            .locals
            .iter()
            .filter_map(|(name, ty, _)| {
                if let TypeInfo::Primitive(p) = ty {
                    if matches!(p, PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64) {
                        return Some((name.clone(), *p));
                    }
                }
                None
            })
            .chain(ctx.params.iter().filter_map(|p| {
                if let TypeInfo::Primitive(pt) = &p.param_type {
                    if matches!(pt, PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64) {
                        return Some((p.name.clone(), *pt));
                    }
                }
                None
            }))
            .collect();

        if numeric_vars.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..numeric_vars.len());
        let (var_name, _) = &numeric_vars[idx];
        let name = ctx.new_local_name();

        // Variant: plain .to_string(), or with prefix/suffix
        let expr = match self.rng.gen_range(0..3u32) {
            0 => {
                // Plain: num.to_string()
                format!("{}.to_string()", var_name)
            }
            1 => {
                // With prefix: "val=" + num.to_string()
                let prefix = match self.rng.gen_range(0..3u32) {
                    0 => "\"n=\"",
                    1 => "\"val:\"",
                    _ => "\"x=\"",
                };
                format!("{} + {}.to_string()", prefix, var_name)
            }
            _ => {
                // With suffix: num.to_string() + "!"
                format!("{}.to_string() + \"!\"", var_name)
            }
        };

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        Some(format!("let {} = {}", name, expr))
    }

    /// Generate `arr.iter().map((el) => el.to_string()).reduce("", (acc, el) => acc + el + sep)`.
    /// Converts a numeric array to a joined string via map+reduce.
    fn try_generate_map_tostring_reduce(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let expr_ctx = ctx.to_expr_context();
        let array_vars = expr_ctx.array_vars();
        let i64_arrays: Vec<String> = array_vars
            .into_iter()
            .filter_map(|(name, elem_ty)| {
                if matches!(elem_ty, TypeInfo::Primitive(PrimitiveType::I64)) {
                    Some(name)
                } else {
                    None
                }
            })
            .collect();

        if i64_arrays.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..i64_arrays.len());
        let arr_name = i64_arrays[idx].clone();
        let name = ctx.new_local_name();
        let sep = match self.rng.gen_range(0..3u32) {
            0 => ",",
            1 => "-",
            _ => " ",
        };

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        Some(format!(
            "let {} = {}.iter().map((el) => el.to_string()).reduce(\"\", (acc, el) => acc + el + \"{}\")",
            name, arr_name, sep
        ))
    }

    /// Generate string interpolation using a struct field access.
    /// E.g., `let s = "value: {instance.field_name}"`
    fn try_generate_struct_field_interpolation(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Find struct-typed locals with numeric or string fields
        let mut candidates: Vec<(String, String, PrimitiveType)> = Vec::new();

        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Struct(mod_id, sym_id) = ty {
                if let Some(sym) = ctx.table.get_symbol(*mod_id, *sym_id) {
                    if let SymbolKind::Struct(ref info) = sym.kind {
                        for f in &info.fields {
                            if let TypeInfo::Primitive(p) = &f.field_type {
                                if matches!(
                                    p,
                                    PrimitiveType::I64
                                        | PrimitiveType::I32
                                        | PrimitiveType::F64
                                        | PrimitiveType::String
                                        | PrimitiveType::Bool
                                ) {
                                    candidates.push((
                                        name.clone(),
                                        f.name.clone(),
                                        *p,
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, field_name, _prim) = &candidates[idx];

        let result_name = ctx.new_local_name();
        let prefix = match self.rng.gen_range(0..3u32) {
            0 => "val=",
            1 => "",
            _ => "f:",
        };

        ctx.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        Some(format!(
            "let {} = \"{}{{{}.{}}}\"",
            result_name, prefix, var_name, field_name
        ))
    }

    /// Generate a when expression with an iterator predicate as condition.
    /// E.g., `let x = when { arr.iter().any((el) => el > 0) => "yes", _ => "no" }`
    fn try_generate_when_iter_predicate(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let expr_ctx = ctx.to_expr_context();
        let array_vars = expr_ctx.array_vars();
        let prim_arrays: Vec<(String, PrimitiveType)> = array_vars
            .into_iter()
            .filter_map(|(name, elem_ty)| {
                if let TypeInfo::Primitive(prim) = elem_ty {
                    if matches!(
                        prim,
                        PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64
                    ) {
                        return Some((name, prim));
                    }
                }
                None
            })
            .collect();

        if prim_arrays.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..prim_arrays.len());
        let (arr_name, elem_prim) = &prim_arrays[idx];
        let arr_name = arr_name.clone();
        let elem_prim = *elem_prim;

        let result_name = ctx.new_local_name();

        // Pick predicate: .any() or .all()
        let predicate = if self.rng.gen_bool(0.5) { "any" } else { "all" };
        let filter_body = self.generate_filter_closure_body(elem_prim);

        // Pick result type: i64 or string
        let (true_val, false_val, result_ty) = if self.rng.gen_bool(0.5) {
            let t = self.rng.gen_range(1..=100);
            let f = self.rng.gen_range(1..=100);
            (
                format!("{}", t),
                format!("{}", f),
                TypeInfo::Primitive(PrimitiveType::I64),
            )
        } else {
            (
                "\"yes\"".to_string(),
                "\"no\"".to_string(),
                TypeInfo::Primitive(PrimitiveType::String),
            )
        };

        ctx.add_local(result_name.clone(), result_ty, false);

        Some(format!(
            "let {} = when {{ {}.iter().{}((x) => {}) => {}, _ => {} }}",
            result_name, arr_name, predicate, filter_body, true_val, false_val
        ))
    }

    /// Generate a closure that returns a numeric value, then use the result
    /// in a string concatenation: `let s = "result=" + f(x).to_string()`.
    fn try_generate_closure_result_concat(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find i64 variables in scope for the lambda argument
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if i64_vars.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..i64_vars.len());
        let arg_var = i64_vars[idx].clone();

        let fn_name = ctx.new_local_name();
        let result_name = ctx.new_local_name();

        // Generate a simple lambda: (a: i64) -> i64 => a * N + M
        let mult = self.rng.gen_range(1..=5);
        let add = self.rng.gen_range(0..=10);

        let lambda_expr = format!("(a: i64) -> i64 => a * {} + {}", mult, add);
        let call_expr = format!("{}({})", fn_name, arg_var);

        // Pick variant: .to_string() concat or string interpolation
        let str_expr = if self.rng.gen_bool(0.5) {
            // "result=" + f(x).to_string()
            format!("\"result=\" + {}.to_string()", call_expr)
        } else {
            // "result={f(x)}" via interpolation
            format!("\"result={{{}}}\"", call_expr)
        };

        ctx.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let indent = self.indent_str();
        Some(format!(
            "let {} = {}\n{}let {} = {}",
            fn_name, lambda_expr, indent, result_name, str_expr
        ))
    }

    /// Generate a for-in loop over a split string result.
    /// `let parts = "a,b,c".split(",").collect()`
    /// `for word in parts.iter() { ... }`
    fn generate_split_for_loop(&mut self, ctx: &mut StmtContext) -> String {
        let parts_name = ctx.new_local_name();
        let iter_name = ctx.new_local_name();
        let acc_name = ctx.new_local_name();

        // Generate a known string to split
        let words: Vec<&str> = vec!["alpha", "beta", "gamma", "delta"];
        let num_words = self.rng.gen_range(2..=4);
        let selected: Vec<&str> = words[..num_words].to_vec();
        let input = selected.join(",");

        // Accumulate string lengths
        ctx.add_local(
            parts_name.clone(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
            false,
        );
        ctx.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );

        ctx.protected_vars.push(parts_name.clone());
        ctx.protected_vars.push(acc_name.clone());

        let indent = self.indent_str();
        let inner = format!("{}    ", indent);

        let result = format!(
            "let {} = \"{}\".split(\",\").collect()\n\
             {}let mut {} = 0\n\
             {}for {} in {}.iter() {{\n\
             {}{} = {} + {}.length()\n\
             {}}}",
            parts_name, input,
            indent, acc_name,
            indent, iter_name, parts_name,
            inner, acc_name, acc_name, iter_name,
            indent,
        );

        ctx.protected_vars.pop();
        ctx.protected_vars.pop();

        result
    }

    /// Iterate over an array, push transformed values into a mutable result array.
    /// ```vole
    /// let source = [1, 2, 3]
    /// let mut result: [i64] = []
    /// for item in source.iter() {
    ///     result.push(item * 2 + 1)
    /// }
    /// ```
    fn try_generate_for_push_collect(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let expr_ctx = ctx.to_expr_context();
        let array_vars = expr_ctx.array_vars();
        let i64_arrays: Vec<String> = array_vars
            .into_iter()
            .filter_map(|(name, elem_ty)| {
                if matches!(elem_ty, TypeInfo::Primitive(PrimitiveType::I64)) {
                    Some(name)
                } else {
                    None
                }
            })
            .collect();

        if i64_arrays.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..i64_arrays.len());
        let source_name = i64_arrays[idx].clone();

        let result_name = ctx.new_local_name();
        let iter_name = ctx.new_local_name();

        // Generate transformation: item * N + M, item + N, or abs-like when
        let transform = match self.rng.gen_range(0..3u32) {
            0 => {
                let mult = self.rng.gen_range(2..=5);
                let add = self.rng.gen_range(0..=10);
                format!("{} * {} + {}", iter_name, mult, add)
            }
            1 => {
                let add = self.rng.gen_range(1..=20);
                format!("{} + {}", iter_name, add)
            }
            _ => {
                // when { item > 0 => item, _ => 0 - item }
                format!(
                    "when {{ {} > 0 => {}, _ => 0 - {} }}",
                    iter_name, iter_name, iter_name
                )
            }
        };

        ctx.add_local(
            result_name.clone(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            true,
        );
        ctx.protected_vars.push(source_name.clone());
        ctx.protected_vars.push(result_name.clone());

        let indent = self.indent_str();
        let inner = format!("{}    ", indent);

        let result = format!(
            "let mut {}: [i64] = []\n\
             {}for {} in {}.iter() {{\n\
             {}{}.push({})\n\
             {}}}",
            result_name,
            indent, iter_name, source_name,
            inner, result_name, transform,
            indent,
        );

        ctx.protected_vars.pop();
        ctx.protected_vars.pop();

        Some(result)
    }

    /// Generate an array literal whose elements are in-scope variables.
    /// E.g., `let arr = [x, y, x + y]` where x, y are i64 locals.
    fn try_generate_array_from_vars(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find i64-typed variables
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if i64_vars.len() < 2 {
            return None;
        }

        let name = ctx.new_local_name();
        let num_elems = self.rng.gen_range(2..=4);

        let mut elems: Vec<String> = Vec::new();
        for _ in 0..num_elems {
            let var_idx = self.rng.gen_range(0..i64_vars.len());
            let var = &i64_vars[var_idx];
            // 50% chance: use variable directly, 50%: small arithmetic
            if self.rng.gen_bool(0.5) {
                elems.push(var.clone());
            } else {
                let op = if self.rng.gen_bool(0.5) { "+" } else { "*" };
                let n = self.rng.gen_range(1..=5);
                elems.push(format!("{} {} {}", var, op, n));
            }
        }

        ctx.add_local(
            name.clone(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );

        Some(format!("let {} = [{}]", name, elems.join(", ")))
    }

    /// Generate multiple .push() calls on a mutable array in sequence.
    fn try_generate_multi_push(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let mut_arrays: Vec<(String, PrimitiveType)> = ctx
            .locals
            .iter()
            .filter(|(name, ty, is_mut)| {
                *is_mut
                    && !ctx.protected_vars.contains(name)
                    && matches!(
                        ty,
                        TypeInfo::Array(elem) if matches!(elem.as_ref(), TypeInfo::Primitive(PrimitiveType::I64))
                    )
            })
            .map(|(name, _, _)| (name.clone(), PrimitiveType::I64))
            .collect();

        if mut_arrays.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..mut_arrays.len());
        let (arr_name, _) = &mut_arrays[idx];
        let arr_name = arr_name.clone();

        let num_pushes = self.rng.gen_range(2..=4);
        let indent = self.indent_str();
        let mut stmts = Vec::new();

        for _ in 0..num_pushes {
            let val = self.rng.gen_range(-50..=50);
            stmts.push(format!("{}.push({})", arr_name, val));
        }

        Some(stmts.join(&format!("\n{}", indent)))
    }

    /// Generate a method call directly on a literal value.
    ///
    /// Tests the compiler's handling of method dispatch on temporaries/immediates:
    /// ```vole
    /// let n = "hello world".length()        // 11
    /// let s = 42.to_string()                // "42"
    /// let b = "hello".contains("ell")       // true
    /// let c = "a,b,c".split(",").count()    // 3
    /// let t = "  hello  ".trim()            // "hello"
    /// ```
    fn generate_literal_method_call(&mut self, ctx: &mut StmtContext) -> String {
        let result_name = ctx.new_local_name();

        let variant = self.rng.gen_range(0..7u32);
        match variant {
            0 => {
                // "literal".length()
                let lit = match self.rng.gen_range(0..4u32) {
                    0 => "\"hello\"",
                    1 => "\"\"",
                    2 => "\"a\"",
                    _ => "\"hello world\"",
                };
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                format!("let {} = {}.length()", result_name, lit)
            }
            1 => {
                // numeric.to_string()
                // Only use non-negative literals: -50.to_string() parses as -(50.to_string())
                let num = self.rng.gen_range(0..=200);
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                format!("let {} = {}.to_string()", result_name, num)
            }
            2 => {
                // "literal".contains("sub")
                let (lit, sub, _expected) = match self.rng.gen_range(0..3u32) {
                    0 => ("\"hello world\"", "\"world\"", true),
                    1 => ("\"abcdef\"", "\"xyz\"", false),
                    _ => ("\"test\"", "\"es\"", true),
                };
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                    false,
                );
                format!("let {} = {}.contains({})", result_name, lit, sub)
            }
            3 => {
                // "a,b,c".split(",").count()
                let (lit, delim) = match self.rng.gen_range(0..3u32) {
                    0 => ("\"a,b,c\"", "\",\""),
                    1 => ("\"one-two-three\"", "\"-\""),
                    _ => ("\"x\"", "\",\""),
                };
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                format!("let {} = {}.split({}).count()", result_name, lit, delim)
            }
            4 => {
                // "  hello  ".trim()
                let lit = match self.rng.gen_range(0..3u32) {
                    0 => "\"  hello  \"",
                    1 => "\"  \"",
                    _ => "\"no-spaces\"",
                };
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                format!("let {} = {}.trim()", result_name, lit)
            }
            5 => {
                // "HELLO".to_lower()
                let lit = match self.rng.gen_range(0..3u32) {
                    0 => "\"HELLO\"",
                    1 => "\"World\"",
                    _ => "\"ABC\"",
                };
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                format!("let {} = {}.to_lower()", result_name, lit)
            }
            _ => {
                // "hello".to_upper()
                let lit = match self.rng.gen_range(0..3u32) {
                    0 => "\"hello\"",
                    1 => "\"world\"",
                    _ => "\"abc\"",
                };
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                format!("let {} = {}.to_upper()", result_name, lit)
            }
        }
    }

    /// Generate a nested when-in-when expression.
    ///
    /// Tests the compiler's handling of nested conditional expressions:
    /// ```vole
    /// let x = when {
    ///     cond1 => when { cond2 => a, _ => b },
    ///     _ => c
    /// }
    /// ```
    fn try_generate_nested_when(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Need at least 2 bool-producing expressions
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if i64_vars.is_empty() {
            return None;
        }

        let result_name = ctx.new_local_name();

        // Pick comparison values for conditions
        let cond1_var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let cond1_thresh = self.rng.gen_range(-10..=10);
        let cond1_op = match self.rng.gen_range(0..3u32) {
            0 => ">",
            1 => "<",
            _ => ">=",
        };

        let cond2_var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let cond2_thresh = self.rng.gen_range(-10..=10);
        let cond2_op = match self.rng.gen_range(0..3u32) {
            0 => ">",
            1 => "<=",
            _ => "==",
        };

        let indent = self.indent_str();

        // Choose between i64 result and string result
        if self.rng.gen_bool(0.5) {
            // i64 result
            let vals: Vec<i64> = (0..3).map(|_| self.rng.gen_range(-20..=20)).collect();
            ctx.add_local(
                result_name.clone(),
                TypeInfo::Primitive(PrimitiveType::I64),
                false,
            );
            Some(format!(
                "let {} = when {{\n{indent}    {} {} {} => when {{ {} {} {} => {}, _ => {} }},\n{indent}    _ => {}\n{indent}}}",
                result_name,
                cond1_var, cond1_op, cond1_thresh,
                cond2_var, cond2_op, cond2_thresh,
                vals[0], vals[1], vals[2],
                indent = indent,
            ))
        } else {
            // string result
            let strs = ["\"big\"", "\"medium\"", "\"small\"", "\"tiny\"", "\"zero\""];
            let s0 = strs[self.rng.gen_range(0..strs.len())];
            let s1 = strs[self.rng.gen_range(0..strs.len())];
            let s2 = strs[self.rng.gen_range(0..strs.len())];
            ctx.add_local(
                result_name.clone(),
                TypeInfo::Primitive(PrimitiveType::String),
                false,
            );
            Some(format!(
                "let {} = when {{\n{indent}    {} {} {} => when {{ {} {} {} => {}, _ => {} }},\n{indent}    _ => {}\n{indent}}}",
                result_name,
                cond1_var, cond1_op, cond1_thresh,
                cond2_var, cond2_op, cond2_thresh,
                s0, s1, s2,
                indent = indent,
            ))
        }
    }

    /// Generate a match expression on a method call result.
    ///
    /// Tests codegen for method call temporaries used as match scrutinees:
    /// ```vole
    /// let r = match str_var.length() { 0 => "empty", _ => "non-empty" }
    /// let r = match str_var.to_upper() { "HELLO" => 1, _ => 0 }
    /// let r = match num_var.to_string() { "0" => true, _ => false }
    /// ```
    fn try_generate_match_on_method(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let result_name = ctx.new_local_name();

        // Collect string vars for .length() / .to_upper() match
        let string_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        // Collect i64 vars for .to_string() match
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if string_vars.is_empty() && i64_vars.is_empty() {
            return None;
        }

        let variant = self.rng.gen_range(0..3u32);
        match variant {
            0 if !string_vars.is_empty() => {
                // match str.length() { 0 => ..., 5 => ..., _ => ... }
                let var = &string_vars[self.rng.gen_range(0..string_vars.len())];
                let val0 = self.rng.gen_range(-5..=5);
                let val1 = self.rng.gen_range(-5..=5);
                let val_default = self.rng.gen_range(-5..=5);
                let arm_len = self.rng.gen_range(0..=10);
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                Some(format!(
                    "let {} = match {}.length() {{ {} => {}, _ => {} }}",
                    result_name, var, arm_len, val0,
                    if self.rng.gen_bool(0.5) {
                        format!("{}", val_default)
                    } else {
                        format!("{}", val1)
                    }
                ))
            }
            1 if !i64_vars.is_empty() => {
                // match num.to_string() { "0" => ..., "1" => ..., _ => ... }
                let var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
                let strs = ["\"0\"", "\"1\"", "\"-1\"", "\"42\""];
                let arm_str = strs[self.rng.gen_range(0..strs.len())];
                let val_true = self.rng.gen_range(-10..=10);
                let val_false = self.rng.gen_range(-10..=10);
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                Some(format!(
                    "let {} = match {}.to_string() {{ {} => {}, _ => {} }}",
                    result_name, var, arm_str, val_true, val_false
                ))
            }
            _ if !string_vars.is_empty() => {
                // match str.trim() { "" => ..., _ => ... }
                let var = &string_vars[self.rng.gen_range(0..string_vars.len())];
                let method = match self.rng.gen_range(0..3u32) {
                    0 => "trim",
                    1 => "to_lower",
                    _ => "to_upper",
                };
                let match_str = match self.rng.gen_range(0..3u32) {
                    0 => "\"\"",
                    1 => "\"hello\"",
                    _ => "\"test\"",
                };
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                    false,
                );
                Some(format!(
                    "let {} = match {}.{}() {{ {} => true, _ => false }}",
                    result_name, var, method, match_str
                ))
            }
            _ => None,
        }
    }

    /// Generate a struct construction using iterator terminal results as field values.
    ///
    /// Tests codegen for iterator chains inside struct literal fields:
    /// ```vole
    /// let s = MyStruct { count_field: arr.iter().count(), sum_field: arr.iter().sum() }
    /// ```
    fn try_generate_struct_with_iter_fields(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let module_id = ctx.module_id?;
        let module = ctx.table.get_module(module_id)?;

        // Find arrays of numeric type in scope
        let numeric_arrays: Vec<(String, PrimitiveType)> = ctx
            .locals
            .iter()
            .filter_map(|(name, ty, _)| {
                if let TypeInfo::Array(elem) = ty {
                    if let TypeInfo::Primitive(prim) = elem.as_ref() {
                        if matches!(prim, PrimitiveType::I64 | PrimitiveType::I32) {
                            return Some((name.clone(), *prim));
                        }
                    }
                }
                None
            })
            .chain(ctx.params.iter().filter_map(|p| {
                if let TypeInfo::Array(elem) = &p.param_type {
                    if let TypeInfo::Primitive(prim) = elem.as_ref() {
                        if matches!(prim, PrimitiveType::I64 | PrimitiveType::I32) {
                            return Some((p.name.clone(), *prim));
                        }
                    }
                }
                None
            }))
            .collect();

        if numeric_arrays.is_empty() {
            return None;
        }

        // Find structs with numeric fields (i64 specifically)
        let struct_candidates: Vec<_> = module
            .structs()
            .filter_map(|sym| {
                if let SymbolKind::Struct(ref info) = sym.kind {
                    // Need at least one i64 field
                    let i64_fields: Vec<_> = info
                        .fields
                        .iter()
                        .filter(|f| matches!(f.field_type, TypeInfo::Primitive(PrimitiveType::I64)))
                        .collect();
                    if !i64_fields.is_empty() {
                        Some((sym.id, sym.name.clone(), info.clone()))
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect();

        if struct_candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..struct_candidates.len());
        let (sym_id, struct_name, struct_info) = &struct_candidates[idx];
        let arr_idx = self.rng.gen_range(0..numeric_arrays.len());
        let (arr_name, _) = &numeric_arrays[arr_idx];

        let result_name = ctx.new_local_name();

        // Generate field values — for i64 fields, use iterator terminals; for others, use regular expr gen
        let expr_ctx = ctx.to_expr_context();
        let field_strs: Vec<String> = struct_info
            .fields
            .iter()
            .map(|f| {
                if matches!(f.field_type, TypeInfo::Primitive(PrimitiveType::I64)) {
                    // Use an iterator terminal for this field
                    let terminal = match self.rng.gen_range(0..3u32) {
                        0 => format!("{}.iter().count()", arr_name),
                        1 => format!("{}.iter().sum()", arr_name),
                        _ => format!(
                            "{}.iter().filter((x) => x > {}).count()",
                            arr_name,
                            self.rng.gen_range(-10..=10)
                        ),
                    };
                    format!("{}: {}", f.name, terminal)
                } else {
                    // Regular expression generation for non-i64 fields
                    let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                    let value = expr_gen.generate(&f.field_type, &expr_ctx, 0);
                    format!("{}: {}", f.name, value)
                }
            })
            .collect();

        ctx.add_local(
            result_name.clone(),
            TypeInfo::Struct(module_id, *sym_id),
            false,
        );

        Some(format!(
            "let {} = {} {{ {} }}",
            result_name,
            struct_name,
            field_strs.join(", ")
        ))
    }

    /// Generate an iterator terminal result chained with a further method call.
    ///
    /// Tests codegen for method dispatch on temporary values from iterator terminals:
    /// ```vole
    /// let s = arr.iter().count().to_string()   // "5"
    /// let s = arr.iter().sum().to_string()      // "15"
    /// ```
    fn try_generate_iter_terminal_chain(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let expr_ctx = ctx.to_expr_context();
        let array_vars = expr_ctx.array_vars();
        let prim_arrays: Vec<(String, PrimitiveType)> = array_vars
            .into_iter()
            .filter_map(|(name, elem_ty)| {
                if let TypeInfo::Primitive(prim) = elem_ty {
                    if matches!(prim, PrimitiveType::I64 | PrimitiveType::I32) {
                        return Some((name, prim));
                    }
                }
                None
            })
            .collect();

        if prim_arrays.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..prim_arrays.len());
        let (arr_name, _) = &prim_arrays[idx];
        let result_name = ctx.new_local_name();

        let variant = self.rng.gen_range(0..4u32);
        match variant {
            0 => {
                // arr.iter().count().to_string()
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!(
                    "let {} = {}.iter().count().to_string()",
                    result_name, arr_name
                ))
            }
            1 => {
                // arr.iter().sum().to_string()
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!(
                    "let {} = {}.iter().sum().to_string()",
                    result_name, arr_name
                ))
            }
            2 => {
                // arr.iter().filter(...).count().to_string()
                let thresh = self.rng.gen_range(-10..=10);
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!(
                    "let {} = {}.iter().filter((x) => x > {}).count().to_string()",
                    result_name, arr_name, thresh
                ))
            }
            _ => {
                // "count=" + arr.iter().count().to_string()
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!(
                    "let {} = \"count=\" + {}.iter().count().to_string()",
                    result_name, arr_name
                ))
            }
        }
    }

    /// Generate a when expression where conditions use string method calls.
    ///
    /// Tests codegen for method calls in when arm conditions:
    /// ```vole
    /// let r = when {
    ///     str.contains("x") => "has x",
    ///     str.length() > 5 => "long",
    ///     _ => "other"
    /// }
    /// ```
    fn try_generate_when_string_method_conds(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let string_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if string_vars.is_empty() {
            return None;
        }

        let var = &string_vars[self.rng.gen_range(0..string_vars.len())];
        let result_name = ctx.new_local_name();
        let indent = self.indent_str();

        // Generate 2-3 string method conditions
        let num_arms = self.rng.gen_range(2..=3);
        let mut arms = Vec::new();

        let method_conds = [
            |var: &str, rng: &mut dyn FnMut() -> i64| {
                let subs = ["\"a\"", "\"e\"", "\"hello\"", "\"test\"", "\" \""];
                let sub = subs[rng() as usize % subs.len()];
                format!("{}.contains({})", var, sub)
            },
            |var: &str, rng: &mut dyn FnMut() -> i64| {
                let thresh = (rng() % 15).abs();
                format!("{}.length() > {}", var, thresh)
            },
            |var: &str, _rng: &mut dyn FnMut() -> i64| {
                format!("{}.length() == 0", var)
            },
            |var: &str, rng: &mut dyn FnMut() -> i64| {
                let prefixes = ["\"a\"", "\"test\"", "\"h\""];
                let prefix = prefixes[rng() as usize % prefixes.len()];
                format!("{}.starts_with({})", var, prefix)
            },
        ];

        // Result is i64
        for i in 0..num_arms {
            let cond_idx = (i as usize) % method_conds.len();
            let mut rng_fn = || self.rng.gen_range(0..1000i64);
            let cond = method_conds[cond_idx](var, &mut rng_fn);
            let val = self.rng.gen_range(-20..=20);
            arms.push(format!("{}    {} => {}", indent, cond, val));
        }

        let default_val = self.rng.gen_range(-20..=20);
        arms.push(format!("{}    _ => {}", indent, default_val));

        ctx.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        Some(format!(
            "let {} = when {{\n{}\n{}}}",
            result_name,
            arms.join(",\n"),
            indent,
        ))
    }

    /// Generate operations on a single-element array.
    ///
    /// Tests codegen for arrays with exactly 1 element, a boundary case for
    /// iterator operations and array access:
    /// ```vole
    /// let arr = [42]
    /// let s = arr.iter().sum()       // 42
    /// let c = arr.iter().count()     // 1
    /// let first = arr[0]             // 42
    /// ```
    fn generate_single_elem_array_ops(&mut self, ctx: &mut StmtContext) -> String {
        let arr_name = ctx.new_local_name();
        let result_name = ctx.new_local_name();
        let indent = self.indent_str();

        let (elem_type, elem_str, val) = match self.rng.gen_range(0..3u32) {
            0 => (PrimitiveType::I64, "i64", format!("{}", self.rng.gen_range(-100..=100))),
            1 => (PrimitiveType::I32, "i32", format!("{}_i32", self.rng.gen_range(-100..=100))),
            _ => (
                PrimitiveType::String,
                "string",
                format!("\"{}\"", ["hello", "world", "test", "a"][self.rng.gen_range(0..4)]),
            ),
        };

        ctx.add_local(
            arr_name.clone(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_type))),
            false,
        );

        let op = match self.rng.gen_range(0..4u32) {
            0 => {
                // arr.iter().count()
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                format!("let {} = {}.iter().count()", result_name, arr_name)
            }
            1 if !matches!(elem_type, PrimitiveType::String) => {
                // arr.iter().sum()
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(elem_type),
                    false,
                );
                format!("let {} = {}.iter().sum()", result_name, arr_name)
            }
            2 => {
                // arr[0]
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(elem_type),
                    false,
                );
                format!("let {} = {}[0]", result_name, arr_name)
            }
            _ => {
                // arr.iter().filter((x) => true).collect()
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_type))),
                    false,
                );
                format!(
                    "let {} = {}.iter().filter((x) => true).collect()",
                    result_name, arr_name
                )
            }
        };

        // Use type annotation to disambiguate empty array types
        let _ = elem_str;
        format!("let {} = [{}]\n{}{}", arr_name, val, indent, op)
    }

    /// Generate a when expression with tautological or self-referential conditions.
    ///
    /// Tests codegen for always-true/always-false conditions:
    /// ```vole
    /// let r = when { x == x => "same", _ => "diff" }
    /// let r = when { arr.length() >= 0 => a, _ => b }
    /// ```
    fn try_generate_tautological_when(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if i64_vars.is_empty() {
            return None;
        }

        let result_name = ctx.new_local_name();
        let var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let indent = self.indent_str();

        let val_true = self.rng.gen_range(-20..=20);
        let val_false = self.rng.gen_range(-20..=20);

        let cond = match self.rng.gen_range(0..4u32) {
            0 => format!("{} == {}", var, var),           // always true
            1 => format!("{} >= {}", var, var),           // always true
            2 => format!("{} <= {}", var, var),           // always true
            _ => format!("{} * 0 == 0", var),             // always true (wrapping)
        };

        ctx.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        Some(format!(
            "let {} = when {{\n{indent}    {} => {},\n{indent}    _ => {}\n{indent}}}",
            result_name, cond, val_true, val_false,
            indent = indent,
        ))
    }

    /// Generate empty string concatenation edge cases.
    ///
    /// Tests codegen for string concat with empty strings:
    /// ```vole
    /// let s = "" + str_var        // prepend empty
    /// let s = str_var + ""        // append empty
    /// let s = "" + "" + str_var   // double empty prepend
    /// ```
    fn try_generate_empty_string_concat(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let string_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if string_vars.is_empty() {
            return None;
        }

        let var = &string_vars[self.rng.gen_range(0..string_vars.len())];
        let result_name = ctx.new_local_name();

        let expr = match self.rng.gen_range(0..4u32) {
            0 => format!("\"\" + {}", var),
            1 => format!("{} + \"\"", var),
            2 => format!("\"\" + \"\" + {}", var),
            _ => format!("\"\" + {} + \"\"", var),
        };

        ctx.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        Some(format!("let {} = {}", result_name, expr))
    }

    /// Generate last-element array access via computed index.
    ///
    /// Tests codegen for runtime-computed index expressions:
    /// ```vole
    /// let last = arr[arr.length() - 1]
    /// ```
    fn try_generate_last_elem_access(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find non-empty parameter arrays (params are always non-empty by contract)
        let param_arrays: Vec<(String, TypeInfo)> = ctx
            .params
            .iter()
            .filter(|p| matches!(p.param_type, TypeInfo::Array(_)))
            .map(|p| (p.name.clone(), p.param_type.clone()))
            .collect();

        if param_arrays.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..param_arrays.len());
        let (arr_name, arr_type) = &param_arrays[idx];
        let elem_type = if let TypeInfo::Array(elem) = arr_type {
            elem.as_ref().clone()
        } else {
            return None;
        };

        let result_name = ctx.new_local_name();

        let expr = match self.rng.gen_range(0..2u32) {
            0 => {
                // arr[arr.length() - 1] — last element
                format!("{}[{}.length() - 1]", arr_name, arr_name)
            }
            _ => {
                // arr[arr.length() - arr.length()] — first element (index 0)
                format!("{}[{}.length() - {}.length()]", arr_name, arr_name, arr_name)
            }
        };

        ctx.add_local(result_name.clone(), elem_type, false);

        Some(format!("let {} = {}", result_name, expr))
    }

    /// Generate a for-loop that iterates 0..arr.length() and accesses arr[i].
    ///
    /// Tests codegen for dynamic range bound + index access:
    /// ```vole
    /// let mut acc = 0
    /// for i in 0..arr.length() {
    ///     acc = acc + arr[i]
    /// }
    /// ```
    fn try_generate_for_length_indexed(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find parameter arrays (guaranteed non-empty)
        let param_arrays: Vec<(String, PrimitiveType)> = ctx
            .params
            .iter()
            .filter_map(|p| {
                if let TypeInfo::Array(elem) = &p.param_type {
                    if let TypeInfo::Primitive(prim) = elem.as_ref() {
                        if matches!(prim, PrimitiveType::I64 | PrimitiveType::I32) {
                            return Some((p.name.clone(), *prim));
                        }
                    }
                }
                None
            })
            .collect();

        if param_arrays.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..param_arrays.len());
        let (arr_name, _prim) = &param_arrays[idx];
        let acc_name = ctx.new_local_name();
        let iter_name = ctx.new_local_name();
        let indent = self.indent_str();

        // Protect the accumulator
        ctx.protected_vars.push(acc_name.clone());
        ctx.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );

        let body_op = match self.rng.gen_range(0..3u32) {
            0 => format!("{} = {} + {}[{}]", acc_name, acc_name, arr_name, iter_name),
            1 => format!(
                "{} = {} + when {{ {}[{}] > 0 => 1, _ => 0 }}",
                acc_name, acc_name, arr_name, iter_name
            ),
            _ => format!(
                "if {}[{}] > 0 {{ {} = {} + 1 }}",
                arr_name, iter_name, acc_name, acc_name
            ),
        };

        Some(format!(
            "let mut {} = 0\n{indent}for {} in 0..{}.length() {{\n{indent}    {}\n{indent}}}",
            acc_name, iter_name, arr_name, body_op,
            indent = indent,
        ))
    }

    /// Generate a while-loop that builds a string up to a length limit.
    ///
    /// Tests codegen for string building in loops with method condition:
    /// ```vole
    /// let mut s = "x"
    /// while s.length() < 10 {
    ///     s = s + "x"
    /// }
    /// ```
    fn generate_while_string_build(&mut self, ctx: &mut StmtContext) -> String {
        let str_name = ctx.new_local_name();
        let indent = self.indent_str();

        let (init, append) = match self.rng.gen_range(0..3u32) {
            0 => ("\"x\"", "\"x\""),
            1 => ("\"ab\"", "\"cd\""),
            _ => ("\"!\"", "\"!\""),
        };
        let limit = self.rng.gen_range(5..=15);

        ctx.protected_vars.push(str_name.clone());
        ctx.add_local(
            str_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            true,
        );

        format!(
            "let mut {} = {}\n{indent}while {}.length() < {} {{\n{indent}    {} = {} + {}\n{indent}}}",
            str_name, init,
            str_name, limit,
            str_name, str_name, append,
            indent = indent,
        )
    }

    /// Generate a compound boolean expression from numeric comparisons.
    ///
    /// Tests codegen for chained && / || with comparison operators:
    /// ```vole
    /// let b = x > y && y > z
    /// let b = x >= 0 || y < 10
    /// let b = !(x < 0) && y > 0
    /// ```
    fn try_generate_compound_bool_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if i64_vars.len() < 2 {
            return None;
        }

        let result_name = ctx.new_local_name();
        let ops = [">", "<", ">=", "<=", "==", "!="];
        let logic = ["&&", "||"];

        let var1 = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let var2 = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let op1 = ops[self.rng.gen_range(0..ops.len())];
        let op2 = ops[self.rng.gen_range(0..ops.len())];
        let logic_op = logic[self.rng.gen_range(0..logic.len())];
        let thresh1 = self.rng.gen_range(-20..=20);
        let thresh2 = self.rng.gen_range(-20..=20);

        let expr = if self.rng.gen_bool(0.3) {
            // Three-way chain: var1 op var2 && var2 op thresh
            format!(
                "{} {} {} {} {} {} {}",
                var1, op1, var2, logic_op, var2, op2, thresh2
            )
        } else {
            // Two comparisons: var1 op thresh1 && var2 op thresh2
            format!(
                "{} {} {} {} {} {} {}",
                var1, op1, thresh1, logic_op, var2, op2, thresh2
            )
        };

        ctx.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );

        Some(format!("let {} = {}", result_name, expr))
    }

    /// Generate a boolean from length comparisons on arrays/strings.
    ///
    /// Tests codegen for method-call results in boolean expressions:
    /// ```vole
    /// let b = arr.length() > 3
    /// let b = str.length() > 0 && arr.length() < 10
    /// ```
    fn try_generate_length_comparison_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Collect arrays and strings for .length() calls
        let length_sources: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| {
                matches!(ty, TypeInfo::Array(_) | TypeInfo::Primitive(PrimitiveType::String))
            })
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| {
                        matches!(
                            p.param_type,
                            TypeInfo::Array(_) | TypeInfo::Primitive(PrimitiveType::String)
                        )
                    })
                    .map(|p| p.name.clone()),
            )
            .collect();

        if length_sources.is_empty() {
            return None;
        }

        let result_name = ctx.new_local_name();
        let var1 = &length_sources[self.rng.gen_range(0..length_sources.len())];
        let thresh1 = self.rng.gen_range(0..=10);
        let op = match self.rng.gen_range(0..4u32) {
            0 => ">",
            1 => ">=",
            2 => "<",
            _ => "==",
        };

        let expr = if length_sources.len() >= 2 && self.rng.gen_bool(0.4) {
            let var2 = &length_sources[self.rng.gen_range(0..length_sources.len())];
            let thresh2 = self.rng.gen_range(0..=10);
            let op2 = match self.rng.gen_range(0..3u32) {
                0 => ">",
                1 => ">=",
                _ => "<",
            };
            let logic = if self.rng.gen_bool(0.5) { "&&" } else { "||" };
            format!(
                "{}.length() {} {} {} {}.length() {} {}",
                var1, op, thresh1, logic, var2, op2, thresh2
            )
        } else {
            format!("{}.length() {} {}", var1, op, thresh1)
        };

        ctx.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );

        Some(format!("let {} = {}", result_name, expr))
    }

    /// Generate a string interpolation containing an iterator terminal.
    ///
    /// Tests codegen for iterator chains inside string interpolation braces:
    /// ```vole
    /// let s = "count: {arr.iter().count()}"
    /// let s = "sum={arr.iter().sum()}"
    /// let s = "filtered: {arr.iter().filter((x) => x > 0).count()}"
    /// ```
    fn try_generate_interpolation_with_iter(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let expr_ctx = ctx.to_expr_context();
        let array_vars = expr_ctx.array_vars();
        let prim_arrays: Vec<(String, PrimitiveType)> = array_vars
            .into_iter()
            .filter_map(|(name, elem_ty)| {
                if let TypeInfo::Primitive(prim) = elem_ty {
                    if matches!(prim, PrimitiveType::I64 | PrimitiveType::I32) {
                        return Some((name, prim));
                    }
                }
                None
            })
            .collect();

        if prim_arrays.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..prim_arrays.len());
        let (arr_name, _) = &prim_arrays[idx];
        let result_name = ctx.new_local_name();

        let prefix = match self.rng.gen_range(0..4u32) {
            0 => "count:",
            1 => "sum=",
            2 => "n=",
            _ => "result:",
        };

        let iter_expr = match self.rng.gen_range(0..3u32) {
            0 => format!("{}.iter().count()", arr_name),
            1 => format!("{}.iter().sum()", arr_name),
            _ => {
                let thresh = self.rng.gen_range(-5..=5);
                format!("{}.iter().filter((x) => x > {}).count()", arr_name, thresh)
            }
        };

        ctx.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        Some(format!(
            "let {} = \"{} {{{}}}\"",
            result_name, prefix, iter_expr
        ))
    }

    /// Generate a reassignment to a mutable variable from a when expression.
    ///
    /// Tests codegen for when expressions as assignment sources:
    /// ```vole
    /// r = when { x > 3 => x * 2, _ => x }
    /// ```
    fn try_generate_reassign_from_when(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find mutable i64 variables (not protected)
        let mut_i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(name, ty, is_mut)| {
                *is_mut
                    && !ctx.protected_vars.contains(name)
                    && matches!(ty, TypeInfo::Primitive(PrimitiveType::I64))
            })
            .map(|(name, _, _)| name.clone())
            .collect();

        if mut_i64_vars.is_empty() {
            return None;
        }

        // Find i64 variables for conditions
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if i64_vars.is_empty() {
            return None;
        }

        let target = &mut_i64_vars[self.rng.gen_range(0..mut_i64_vars.len())];
        let cond_var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let thresh = self.rng.gen_range(-10..=10);
        let op = match self.rng.gen_range(0..3u32) {
            0 => ">",
            1 => "<",
            _ => ">=",
        };
        let val_true = self.rng.gen_range(-20..=20);
        let val_false = self.rng.gen_range(-20..=20);

        Some(format!(
            "{} = when {{ {} {} {} => {}, _ => {} }}",
            target, cond_var, op, thresh, val_true, val_false
        ))
    }

    /// Generate identity arithmetic edge cases: x + 0, x * 1, x - 0, 0 + x, 1 * x, x - x.
    /// These test that the compiler handles trivial arithmetic correctly.
    fn try_generate_identity_arithmetic(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if i64_vars.is_empty() {
            return None;
        }

        let var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let name = ctx.new_local_name();

        let expr = match self.rng.gen_range(0..6u32) {
            0 => format!("{} + 0", var),      // x + 0 == x
            1 => format!("{} * 1", var),      // x * 1 == x
            2 => format!("{} - 0", var),      // x - 0 == x
            3 => format!("0 + {}", var),      // 0 + x == x
            4 => format!("1 * {}", var),      // 1 * x == x
            _ => {
                // x - x == 0
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                return Some(format!("let {} = {} - {}", name, var, var));
            }
        };

        ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
        Some(format!("let {} = {}", name, expr))
    }

    /// Generate string equality edge cases: s == s, "" == "", s.length() == s.length().
    /// These test string comparison and method-call-in-comparison codegen.
    fn try_generate_string_equality_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let string_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| {
                        matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String))
                    })
                    .map(|p| p.name.clone()),
            )
            .collect();

        let name = ctx.new_local_name();

        let expr = match self.rng.gen_range(0..5u32) {
            0 if !string_vars.is_empty() => {
                // s == s (always true)
                let var = &string_vars[self.rng.gen_range(0..string_vars.len())];
                format!("{} == {}", var, var)
            }
            1 => {
                // "" == "" (always true)
                "\"\" == \"\"".to_string()
            }
            2 if !string_vars.is_empty() => {
                // s.length() == s.length() (always true)
                let var = &string_vars[self.rng.gen_range(0..string_vars.len())];
                format!("{}.length() == {}.length()", var, var)
            }
            3 if !string_vars.is_empty() => {
                // s + "" == s (always true)
                let var = &string_vars[self.rng.gen_range(0..string_vars.len())];
                format!("{} + \"\" == {}", var, var)
            }
            _ => {
                // "hello" == "hello" (always true)
                let s = match self.rng.gen_range(0..3u32) {
                    0 => "hello",
                    1 => "test",
                    _ => "abc",
                };
                format!("\"{}\" == \"{}\"", s, s)
            }
        };

        ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::Bool), false);
        Some(format!("let {} = {}", name, expr))
    }

    /// Generate modulo edge cases: N % 1 (always 0), N % N (always 0 for non-zero),
    /// x % large_prime, etc. Tests division/modulo codegen paths.
    fn generate_modulo_edge_case(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();

        let expr = match self.rng.gen_range(0..4u32) {
            0 => {
                // literal % 1 == 0
                let val = self.rng.gen_range(1..=100);
                format!("{} % 1", val)
            }
            1 => {
                // literal % itself == 0
                let val = self.rng.gen_range(1..=100);
                format!("{} % {}", val, val)
            }
            2 => {
                // 0 % literal == 0
                let val = self.rng.gen_range(1..=100);
                format!("0 % {}", val)
            }
            _ => {
                // known modulo: a % b where a and b are known
                let b = self.rng.gen_range(2..=10);
                let a = b * self.rng.gen_range(1..=5) + self.rng.gen_range(0..b);
                format!("{} % {}", a, b)
            }
        };

        ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
        format!("let {} = {}", name, expr)
    }

    /// Generate uniform array operations: arrays where all elements are the same value,
    /// then perform iterator operations on them. Tests iter sum/count on uniform data.
    fn generate_array_uniform_ops(&mut self, ctx: &mut StmtContext) -> String {
        let val = self.rng.gen_range(0..=20);
        let count = self.rng.gen_range(1..=5);
        let elems = vec![val.to_string(); count];
        let arr_literal = format!("[{}]", elems.join(", "));

        let arr_name = ctx.new_local_name();
        let result_name = ctx.new_local_name();

        match self.rng.gen_range(0..3u32) {
            0 => {
                // [v, v, v].iter().sum()
                ctx.add_local(
                    arr_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                    false,
                );
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                format!(
                    "let {} = {}\nlet {} = {}.iter().sum()",
                    arr_name, arr_literal, result_name, arr_name
                )
            }
            1 => {
                // [v, v, v].iter().count()
                ctx.add_local(
                    arr_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                    false,
                );
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                format!(
                    "let {} = {}\nlet {} = {}.iter().count()",
                    arr_name, arr_literal, result_name, arr_name
                )
            }
            _ => {
                // [v, v, v].length()
                ctx.add_local(
                    arr_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                    false,
                );
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                format!(
                    "let {} = {}\nlet {} = {}.length()",
                    arr_name, arr_literal, result_name, arr_name
                )
            }
        }
    }

    /// Generate a for-loop that accumulates using when expressions:
    /// `let mut acc = 0; for item in arr { acc = acc + when { item > 0 => item, _ => 0 } }`
    fn try_generate_for_when_accumulate(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find i64 array parameters (guaranteed non-empty)
        let array_params: Vec<String> = ctx
            .params
            .iter()
            .filter(|p| {
                matches!(
                    &p.param_type,
                    TypeInfo::Array(inner) if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::I64))
                )
            })
            .map(|p| p.name.clone())
            .collect();

        if array_params.is_empty() {
            return None;
        }

        let arr = &array_params[self.rng.gen_range(0..array_params.len())];
        let acc_name = ctx.new_local_name();
        let item_name = ctx.new_local_name();
        let indent = "    ".repeat(self.indent + 1);

        let thresh = self.rng.gen_range(-5..=10);
        let op = match self.rng.gen_range(0..3u32) {
            0 => ">",
            1 => ">=",
            _ => "<",
        };
        let fallback = self.rng.gen_range(0..=5);

        ctx.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );
        ctx.protected_vars.push(acc_name.clone());

        Some(format!(
            "let mut {} = 0\n{}for {} in {} {{\n{}{} = {} + when {{ {} {} {} => {}, _ => {} }}\n{}}}",
            acc_name,
            indent,
            item_name,
            arr,
            indent,
            acc_name,
            acc_name,
            item_name,
            op,
            thresh,
            item_name,
            fallback,
            indent,
        ))
    }

    /// Generate when expression with iterator terminals as arm values:
    /// `let r = when { x > 0 => arr.iter().count(), _ => arr.iter().sum() }`
    fn try_generate_iter_in_when_arms(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Need an i64 variable for condition and an i64 array for iterator
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        let array_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| {
                matches!(
                    ty,
                    TypeInfo::Array(inner) if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::I64))
                )
            })
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| {
                        matches!(
                            &p.param_type,
                            TypeInfo::Array(inner) if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::I64))
                        )
                    })
                    .map(|p| p.name.clone()),
            )
            .collect();

        if i64_vars.is_empty() || array_vars.is_empty() {
            return None;
        }

        let cond_var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let arr = &array_vars[self.rng.gen_range(0..array_vars.len())];
        let name = ctx.new_local_name();
        let thresh = self.rng.gen_range(-5..=10);

        let terminals = ["count()", "sum()"];
        let t1 = terminals[self.rng.gen_range(0..terminals.len())];
        let t2 = terminals[self.rng.gen_range(0..terminals.len())];

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        Some(format!(
            "let {} = when {{ {} > {} => {}.iter().{}, _ => {}.iter().{} }}",
            name, cond_var, thresh, arr, t1, arr, t2
        ))
    }

    /// Generate when expression with 4+ boolean condition arms.
    /// Tests the compiler's handling of larger when expressions.
    fn try_generate_multi_arm_when(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if i64_vars.is_empty() {
            return None;
        }

        let var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let name = ctx.new_local_name();
        let num_arms = self.rng.gen_range(4..=7);
        let indent = "    ".repeat(self.indent + 1);

        let mut arms = Vec::new();
        for i in 0..num_arms {
            let thresh = (i as i64) * 10;
            let result = self.rng.gen_range(-20..=20);
            let op = match self.rng.gen_range(0..3u32) {
                0 => ">",
                1 => "<",
                _ => ">=",
            };
            arms.push(format!("{}{} {} {} => {}", indent, var, op, thresh, result));
        }
        let default_val = self.rng.gen_range(-10..=10);
        arms.push(format!("{}_ => {}", indent, default_val));

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        Some(format!(
            "let {} = when {{\n{}\n{}}}",
            name,
            arms.join("\n"),
            "    ".repeat(self.indent),
        ))
    }

    /// Generate match where arm values involve arithmetic computation.
    /// `match x { 0 => a + b, 1 => c * 2, _ => d - 1 }`
    fn try_generate_match_with_computation(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if i64_vars.len() < 2 {
            return None;
        }

        let scrutinee = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let name = ctx.new_local_name();
        let indent = "    ".repeat(self.indent + 1);
        let num_arms = self.rng.gen_range(2..=4);

        let mut arms = Vec::new();
        let mut used_values = std::collections::HashSet::new();
        for _ in 0..num_arms {
            let mut val = self.rng.gen_range(-5..=10);
            while used_values.contains(&val) {
                val = self.rng.gen_range(-5..=10);
            }
            used_values.insert(val);

            let v1 = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
            let op = match self.rng.gen_range(0..3u32) {
                0 => "+",
                1 => "-",
                _ => "*",
            };
            let operand = self.rng.gen_range(1..=10);
            arms.push(format!("{}{} => {} {} {}", indent, val, v1, op, operand));
        }
        // Default arm with computation
        let v_default = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let default_op = match self.rng.gen_range(0..3u32) {
            0 => "+",
            1 => "-",
            _ => "*",
        };
        let default_operand = self.rng.gen_range(1..=5);
        arms.push(format!(
            "{}_ => {} {} {}",
            indent, v_default, default_op, default_operand
        ));

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        Some(format!(
            "let {} = match {} {{\n{}\n{}}}",
            name,
            scrutinee,
            arms.join("\n"),
            "    ".repeat(self.indent),
        ))
    }

    /// Generate string .replace() or .replace_all() calls.
    /// E.g., `let s = "hello world".replace("world", "there")`
    fn try_generate_string_replace_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let string_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| {
                        matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String))
                    })
                    .map(|p| p.name.clone()),
            )
            .collect();

        let name = ctx.new_local_name();
        let method = if self.rng.gen_bool(0.5) {
            "replace"
        } else {
            "replace_all"
        };

        let expr = if !string_vars.is_empty() && self.rng.gen_bool(0.5) {
            // Use variable
            let var = &string_vars[self.rng.gen_range(0..string_vars.len())];
            let (old, new) = match self.rng.gen_range(0..3u32) {
                0 => ("a", "b"),
                1 => ("hello", "hi"),
                _ => (" ", "_"),
            };
            format!("{}.{}(\"{}\", \"{}\")", var, method, old, new)
        } else {
            // Use literal
            let (src, old, new) = match self.rng.gen_range(0..3u32) {
                0 => ("hello world", "world", "there"),
                1 => ("aabaa", "a", "x"),
                _ => ("foo bar baz", " ", "-"),
            };
            format!("\"{}\".{}(\"{}\", \"{}\")", src, method, old, new)
        };

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!("let {} = {}", name, expr))
    }

    /// Generate nested match: match inside match arm.
    /// `let r = match x { 0 => match y { 0 => a, _ => b }, _ => c }`
    fn try_generate_nested_match_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if i64_vars.len() < 2 {
            return None;
        }

        let outer_var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let inner_var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let name = ctx.new_local_name();
        let indent = "    ".repeat(self.indent + 1);
        let indent2 = "    ".repeat(self.indent + 2);

        let outer_val = self.rng.gen_range(0..=5);
        let inner_val = self.rng.gen_range(0..=5);
        let result_a = self.rng.gen_range(-10..=10);
        let result_b = self.rng.gen_range(-10..=10);
        let result_c = self.rng.gen_range(-10..=10);

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        Some(format!(
            "let {} = match {} {{\n{}{} => match {} {{\n{}{} => {}\n{}_ => {}\n{}}}\n{}_ => {}\n{}}}",
            name,
            outer_var,
            indent, outer_val,
            inner_var,
            indent2, inner_val, result_a,
            indent2, result_b,
            indent,
            indent, result_c,
            "    ".repeat(self.indent),
        ))
    }

    /// Generate string .length() on literal strings of known lengths.
    /// Tests string-length codegen with edge cases: empty string, single char, etc.
    fn generate_string_length_edge_cases(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();
        let expr = match self.rng.gen_range(0..5u32) {
            0 => "\"\".length()".to_string(),           // 0
            1 => "\"a\".length()".to_string(),           // 1
            2 => "\"hello\".length()".to_string(),       // 5
            3 => "\"hello world\".length()".to_string(), // 11
            _ => {
                // Variable .length()
                let string_vars: Vec<String> = ctx
                    .locals
                    .iter()
                    .filter(|(_, ty, _)| {
                        matches!(ty, TypeInfo::Primitive(PrimitiveType::String))
                    })
                    .map(|(name, _, _)| name.clone())
                    .chain(
                        ctx.params
                            .iter()
                            .filter(|p| {
                                matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String))
                            })
                            .map(|p| p.name.clone()),
                    )
                    .collect();
                if !string_vars.is_empty() {
                    let var = &string_vars[self.rng.gen_range(0..string_vars.len())];
                    format!("{}.length()", var)
                } else {
                    "\"test\".length()".to_string() // 4
                }
            }
        };
        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );
        format!("let {} = {}", name, expr)
    }

    /// Generate range-checking booleans: `x > lo && x < hi`, `x >= 0 && x <= 100`.
    fn try_generate_range_check_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if i64_vars.is_empty() {
            return None;
        }

        let var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let name = ctx.new_local_name();

        let lo = self.rng.gen_range(-10..=0);
        let hi = self.rng.gen_range(10..=100);
        let (lo_op, hi_op) = match self.rng.gen_range(0..3u32) {
            0 => (">", "<"),
            1 => (">=", "<="),
            _ => (">=", "<"),
        };

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );
        Some(format!(
            "let {} = {} {} {} && {} {} {}",
            name, var, lo_op, lo, var, hi_op, hi
        ))
    }

    /// Generate for-loop that builds a string using match on the loop variable.
    /// `let mut s = ""; for i in 0..N { s = s + match i { 0 => "a", 1 => "b", _ => "c" } }`
    fn generate_for_string_build_with_match(&mut self, ctx: &mut StmtContext) -> String {
        let s_name = ctx.new_local_name();
        let i_name = ctx.new_local_name();
        let n = self.rng.gen_range(2..=5);
        let indent = "    ".repeat(self.indent + 1);
        let match_indent = "    ".repeat(self.indent + 2);

        let suffixes: Vec<&str> = vec!["a", "b", "c", "d", "x"];
        let num_arms = self.rng.gen_range(2..=3).min(n);
        let mut arms = Vec::new();
        for j in 0..num_arms {
            arms.push(format!(
                "{}{} => \"{}\"",
                match_indent,
                j,
                suffixes[j as usize % suffixes.len()]
            ));
        }
        arms.push(format!(
            "{}_ => \"{}\"",
            match_indent,
            suffixes[num_arms as usize % suffixes.len()]
        ));

        ctx.add_local(
            s_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            true,
        );
        ctx.protected_vars.push(s_name.clone());

        format!(
            "let mut {} = \"\"\n{}for {} in 0..{} {{\n{}{} = {} + match {} {{\n{}\n{}}}\n{}}}",
            s_name,
            indent,
            i_name,
            n,
            indent,
            s_name,
            s_name,
            i_name,
            arms.join("\n"),
            indent,
            indent,
        )
    }

    /// Generate when with string concatenation as arm values.
    /// `let s = when { x > 0 => str + " positive", _ => str + " negative" }`
    fn try_generate_when_with_string_concat_arms(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        let string_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| {
                        matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String))
                    })
                    .map(|p| p.name.clone()),
            )
            .collect();

        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if string_vars.is_empty() || i64_vars.is_empty() {
            return None;
        }

        let str_var = &string_vars[self.rng.gen_range(0..string_vars.len())];
        let cond_var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let name = ctx.new_local_name();
        let thresh = self.rng.gen_range(-5..=10);

        let suffix_true = match self.rng.gen_range(0..3u32) {
            0 => " yes",
            1 => " positive",
            _ => "_true",
        };
        let suffix_false = match self.rng.gen_range(0..3u32) {
            0 => " no",
            1 => " negative",
            _ => "_false",
        };

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        Some(format!(
            "let {} = when {{ {} > {} => {} + \"{}\", _ => {} + \"{}\" }}",
            name, cond_var, thresh, str_var, suffix_true, str_var, suffix_false
        ))
    }

    /// Generate boolean negation: `!true`, `!false`, `!(x > 0)`, `!b`.
    /// Tests the `!` operator codegen on various boolean expressions.
    fn try_generate_bool_negation_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let name = ctx.new_local_name();

        let expr = match self.rng.gen_range(0..5u32) {
            0 => "!true".to_string(),
            1 => "!false".to_string(),
            2 => {
                // !(x > 0)
                let i64_vars: Vec<String> = ctx
                    .locals
                    .iter()
                    .filter(|(_, ty, _)| {
                        matches!(ty, TypeInfo::Primitive(PrimitiveType::I64))
                    })
                    .map(|(name, _, _)| name.clone())
                    .chain(
                        ctx.params
                            .iter()
                            .filter(|p| {
                                matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64))
                            })
                            .map(|p| p.name.clone()),
                    )
                    .collect();
                if i64_vars.is_empty() {
                    return None;
                }
                let var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
                let thresh = self.rng.gen_range(-5..=10);
                format!("!({} > {})", var, thresh)
            }
            3 => {
                // !b where b is a bool variable
                let bool_vars: Vec<String> = ctx
                    .locals
                    .iter()
                    .filter(|(_, ty, _)| {
                        matches!(ty, TypeInfo::Primitive(PrimitiveType::Bool))
                    })
                    .map(|(name, _, _)| name.clone())
                    .chain(
                        ctx.params
                            .iter()
                            .filter(|p| {
                                matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::Bool))
                            })
                            .map(|p| p.name.clone()),
                    )
                    .collect();
                if bool_vars.is_empty() {
                    return None;
                }
                let var = &bool_vars[self.rng.gen_range(0..bool_vars.len())];
                format!("!{}", var)
            }
            _ => {
                // !(x == y)
                let i64_vars: Vec<String> = ctx
                    .locals
                    .iter()
                    .filter(|(_, ty, _)| {
                        matches!(ty, TypeInfo::Primitive(PrimitiveType::I64))
                    })
                    .map(|(name, _, _)| name.clone())
                    .chain(
                        ctx.params
                            .iter()
                            .filter(|p| {
                                matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64))
                            })
                            .map(|p| p.name.clone()),
                    )
                    .collect();
                if i64_vars.len() < 2 {
                    return None;
                }
                let v1 = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
                let v2 = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
                format!("!({} == {})", v1, v2)
            }
        };

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );
        Some(format!("let {} = {}", name, expr))
    }

    /// Generate chained method calls on literal strings.
    /// E.g., `"hello world".split(" ").count()`, `"abc".length().to_string()`
    fn generate_chained_literal_method(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();

        match self.rng.gen_range(0..4u32) {
            0 => {
                // "hello world".split(" ").count() -> i64
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                format!("let {} = \"hello world\".split(\" \").count()", name)
            }
            1 => {
                // "abc".length().to_string() -> string
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                format!("let {} = \"abc\".length().to_string()", name)
            }
            2 => {
                // "a,b,c".split(",").count() -> i64
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                format!("let {} = \"a,b,c\".split(\",\").count()", name)
            }
            _ => {
                // "HELLO".to_lower().length() -> i64
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                format!("let {} = \"HELLO\".to_lower().length()", name)
            }
        }
    }

    /// Generate method call on a when expression result.
    /// `let r = when { x > 0 => "hello", _ => "world" }.length()`
    fn try_generate_when_result_method(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if i64_vars.is_empty() {
            return None;
        }

        let cond_var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let thresh = self.rng.gen_range(-5..=10);
        let name = ctx.new_local_name();

        match self.rng.gen_range(0..3u32) {
            0 => {
                // when { ... => "hello", _ => "world" }.length() -> i64
                let s1 = match self.rng.gen_range(0..3u32) {
                    0 => "hello",
                    1 => "abc",
                    _ => "test",
                };
                let s2 = match self.rng.gen_range(0..3u32) {
                    0 => "world",
                    1 => "xyz",
                    _ => "foo",
                };
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                Some(format!(
                    "let {} = when {{ {} > {} => \"{}\", _ => \"{}\" }}.length()",
                    name, cond_var, thresh, s1, s2
                ))
            }
            1 => {
                // when { ... => "HELLO", _ => "world" }.to_upper() -> string
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!(
                    "let {} = when {{ {} > {} => \"hello\", _ => \"world\" }}.to_upper()",
                    name, cond_var, thresh
                ))
            }
            _ => {
                // when { ... => 42, _ => 0 }.to_string() -> string
                let v1 = self.rng.gen_range(0..=100);
                let v2 = self.rng.gen_range(0..=100);
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!(
                    "let {} = when {{ {} > {} => {}, _ => {} }}.to_string()",
                    name, cond_var, thresh, v1, v2
                ))
            }
        }
    }

    /// Generate for-loop that builds a string using when in the body.
    /// `for item in arr { s = s + when { item > 0 => "+", _ => "-" } }`
    fn try_generate_for_iter_when_string_body(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Find i64 array parameters
        let array_params: Vec<String> = ctx
            .params
            .iter()
            .filter(|p| {
                matches!(
                    &p.param_type,
                    TypeInfo::Array(inner) if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::I64))
                )
            })
            .map(|p| p.name.clone())
            .collect();

        if array_params.is_empty() {
            return None;
        }

        let arr = &array_params[self.rng.gen_range(0..array_params.len())];
        let s_name = ctx.new_local_name();
        let item_name = ctx.new_local_name();
        let indent = "    ".repeat(self.indent + 1);
        let thresh = self.rng.gen_range(-5..=10);

        let (s_true, s_false) = match self.rng.gen_range(0..3u32) {
            0 => ("+", "-"),
            1 => ("y", "n"),
            _ => ("1", "0"),
        };

        ctx.add_local(
            s_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            true,
        );
        ctx.protected_vars.push(s_name.clone());

        Some(format!(
            "let mut {} = \"\"\n{}for {} in {} {{\n{}{} = {} + when {{ {} > {} => \"{}\", _ => \"{}\" }}\n{}}}",
            s_name,
            indent,
            item_name,
            arr,
            indent,
            s_name,
            s_name,
            item_name,
            thresh,
            s_true,
            s_false,
            indent,
        ))
    }

    /// Generate `while false { ... }` — dead loop body.
    /// Tests that the compiler handles unreachable while body correctly.
    fn generate_while_false_deadcode(&mut self, ctx: &mut StmtContext) -> String {
        let indent = "    ".repeat(self.indent + 1);
        let var_name = ctx.new_local_name();
        // Declare a mutable variable before the loop, then modify inside
        // the dead body. The modification should never execute.
        ctx.add_local(
            var_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );
        ctx.protected_vars.push(var_name.clone());
        format!(
            "let mut {} = 42\n{}while false {{\n{}{} = 0\n{}}}",
            var_name, indent, indent, var_name, indent,
        )
    }

    /// Generate division by power of 2: `x / 2`, `x / 4`, `x / 8`.
    /// Common optimization path in codegen (strength reduction).
    fn try_generate_power_of_two_div(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if i64_vars.is_empty() {
            return None;
        }

        let var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let name = ctx.new_local_name();
        let divisor = match self.rng.gen_range(0..4u32) {
            0 => 2,
            1 => 4,
            2 => 8,
            _ => 16,
        };

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );
        Some(format!("let {} = {} / {}", name, var, divisor))
    }

    /// Generate a string predicate call: `s.contains("sub")`, `s.starts_with("hel")`, `s.ends_with("rld")`
    /// Returns a bool-typed let binding.
    fn try_generate_string_predicate_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let string_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        let name = ctx.new_local_name();

        // Pick method and argument
        let method = match self.rng.gen_range(0..3u32) {
            0 => "contains",
            1 => "starts_with",
            _ => "ends_with",
        };

        let search_strs = ["hello", "world", "a", "str", "test", "", "xyz", "lo"];
        let search = search_strs[self.rng.gen_range(0..search_strs.len())];

        let expr = if string_vars.is_empty() {
            // Use a string literal as receiver
            let literals = ["\"hello world\"", "\"testing\"", "\"abcdef\"", "\"vole lang\""];
            let lit = literals[self.rng.gen_range(0..literals.len())];
            format!("{}.{}(\"{}\")", lit, method, search)
        } else {
            let var = &string_vars[self.rng.gen_range(0..string_vars.len())];
            format!("{}.{}(\"{}\")", var, method, search)
        };

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );
        Some(format!("let {} = {}", name, expr))
    }

    /// Generate a string interpolation with complex embedded expressions.
    /// E.g.: `"sum={a + b}"`, `"len={arr.length()}"`, `"upper={s.to_upper()}"`
    fn try_generate_interpolation_expr_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Collect typed variables for interpolation expressions
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        let string_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        let array_vars: Vec<String> = ctx
            .params
            .iter()
            .filter(|p| matches!(p.param_type, TypeInfo::Array(_)))
            .map(|p| p.name.clone())
            .collect();

        // Need at least some variables to make interesting interpolations
        if i64_vars.is_empty() && string_vars.is_empty() && array_vars.is_empty() {
            return None;
        }

        let name = ctx.new_local_name();
        let mut parts: Vec<String> = Vec::new();

        // Generate 2-3 interpolation segments
        let num_segments = self.rng.gen_range(2..=3);
        for _ in 0..num_segments {
            let choice = self.rng.gen_range(0..5u32);
            match choice {
                0 if !i64_vars.is_empty() => {
                    // Arithmetic: {a + b} or {a * 2}
                    let var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
                    let n = self.rng.gen_range(1..=10);
                    let op = match self.rng.gen_range(0..3u32) {
                        0 => "+",
                        1 => "-",
                        _ => "*",
                    };
                    parts.push(format!("{{{} {} {}}}", var, op, n));
                }
                1 if !string_vars.is_empty() => {
                    // String method: {s.to_upper()} or {s.length()} or {s.trim()}
                    let var = &string_vars[self.rng.gen_range(0..string_vars.len())];
                    let method = match self.rng.gen_range(0..3u32) {
                        0 => ".to_upper()",
                        1 => ".length()",
                        _ => ".trim()",
                    };
                    parts.push(format!("{{{}{}}}", var, method));
                }
                2 if !array_vars.is_empty() => {
                    // Array method: {arr.length()}
                    let var = &array_vars[self.rng.gen_range(0..array_vars.len())];
                    parts.push(format!("{{{}.length()}}", var));
                }
                3 if !i64_vars.is_empty() => {
                    // Simple variable
                    let var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
                    parts.push(format!("{{{}}}", var));
                }
                _ if !string_vars.is_empty() => {
                    // Simple string variable
                    let var = &string_vars[self.rng.gen_range(0..string_vars.len())];
                    parts.push(format!("{{{}}}", var));
                }
                _ => {
                    // Literal text fallback
                    parts.push("ok".to_string());
                }
            }
        }

        let labels = ["val", "result", "out", "x", "data"];
        let label = labels[self.rng.gen_range(0..labels.len())];
        let sep = match self.rng.gen_range(0..3u32) {
            0 => ", ",
            1 => " | ",
            _ => " ",
        };

        let interp_str = format!("\"{}={}\"", label, parts.join(sep));

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!("let {} = {}", name, interp_str))
    }

    /// Generate a match on string length: `match s.length() { 0 => "empty", 1 => "one", _ => "many" }`
    fn try_generate_match_string_length(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let string_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if string_vars.is_empty() {
            return None;
        }

        let var = &string_vars[self.rng.gen_range(0..string_vars.len())];
        let name = ctx.new_local_name();

        // Generate match arms on length values
        let result_strs = ["\"empty\"", "\"one\"", "\"short\"", "\"medium\"", "\"long\""];
        let num_arms = self.rng.gen_range(2..=3);

        let mut arms = Vec::new();
        let mut used_values = std::collections::HashSet::new();
        for i in 0..num_arms {
            let val = i as i64;
            used_values.insert(val);
            arms.push(format!(
                "    {} => {}",
                val,
                result_strs[i % result_strs.len()]
            ));
        }
        // Default arm
        let default = result_strs[num_arms % result_strs.len()];
        arms.push(format!("    _ => {}", default));

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = match {}.length() {{\n{}\n}}",
            name,
            var,
            arms.join("\n")
        ))
    }

    /// Generate a safe array access with length guard:
    /// `when { arr.length() > 0 => arr[0], _ => default_val }`
    fn try_generate_array_length_guard(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find array parameters (safe to index — params are always non-empty from test harness)
        let array_params: Vec<(String, PrimitiveType)> = ctx
            .params
            .iter()
            .filter_map(|p| match &p.param_type {
                TypeInfo::Array(inner) => match inner.as_ref() {
                    TypeInfo::Primitive(prim) => Some((p.name.clone(), *prim)),
                    _ => None,
                },
                _ => None,
            })
            .collect();

        if array_params.is_empty() {
            return None;
        }

        let (arr_name, elem_prim) = &array_params[self.rng.gen_range(0..array_params.len())];
        let name = ctx.new_local_name();

        let default_val = match elem_prim {
            PrimitiveType::I64 => "0".to_string(),
            PrimitiveType::I32 => "0_i32".to_string(),
            PrimitiveType::F64 => "0.0_f64".to_string(),
            PrimitiveType::Bool => "false".to_string(),
            PrimitiveType::String => "\"\"".to_string(),
            PrimitiveType::I8 => "0_i8".to_string(),
            _ => return None,
        };

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(*elem_prim),
            false,
        );
        Some(format!(
            "let {} = when {{\n    {}.length() > 0 => {}[0]\n    _ => {}\n}}",
            name, arr_name, arr_name, default_val
        ))
    }

    /// Generate a repeat literal: `let arr: [i64; 5] = [0; 5]`
    /// Note: Fixed-size arrays [T; N] don't support .iter()/.length() in Vole,
    /// so we don't register the local to avoid downstream generators using it.
    fn generate_repeat_literal_let(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();
        let count = self.rng.gen_range(2..=8);

        // Pick element type and value
        let (type_str, val) = match self.rng.gen_range(0..4u32) {
            0 => {
                let v = self.rng.gen_range(-50..=50);
                ("i64".to_string(), format!("{}", v))
            }
            1 => {
                let v = self.rng.gen_range(-50..=50);
                ("i32".to_string(), format!("{}_i32", v))
            }
            2 => {
                let strs = ["\"hello\"", "\"test\"", "\"\"", "\"vole\""];
                let s = strs[self.rng.gen_range(0..strs.len())];
                ("string".to_string(), s.to_string())
            }
            _ => {
                let b = if self.rng.gen_bool(0.5) {
                    "true"
                } else {
                    "false"
                };
                ("bool".to_string(), b.to_string())
            }
        };

        // Don't add to ctx.locals — fixed-size arrays lack .iter()/.length()
        format!(
            "let {}: [{}; {}] = [{}; {}]",
            name, type_str, count, val, count
        )
    }

    /// Generate an iter().reduce() call on an array parameter.
    /// E.g.: `let sum = arr.iter().reduce(0, (acc, x) => acc + x)`
    fn try_generate_iter_reduce_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find array params with numeric element types
        let numeric_array_params: Vec<(String, PrimitiveType)> = ctx
            .params
            .iter()
            .filter_map(|p| match &p.param_type {
                TypeInfo::Array(inner) => match inner.as_ref() {
                    TypeInfo::Primitive(prim @ (PrimitiveType::I64 | PrimitiveType::I32)) => {
                        Some((p.name.clone(), *prim))
                    }
                    _ => None,
                },
                _ => None,
            })
            .collect();

        // Also find string array params for string reduce
        let string_array_params: Vec<String> = ctx
            .params
            .iter()
            .filter_map(|p| match &p.param_type {
                TypeInfo::Array(inner) => match inner.as_ref() {
                    TypeInfo::Primitive(PrimitiveType::String) => Some(p.name.clone()),
                    _ => None,
                },
                _ => None,
            })
            .collect();

        if numeric_array_params.is_empty() && string_array_params.is_empty() {
            return None;
        }

        let name = ctx.new_local_name();

        // 60% numeric reduce, 40% string reduce
        if !numeric_array_params.is_empty() && (string_array_params.is_empty() || self.rng.gen_bool(0.6))
        {
            let (arr_name, prim) = &numeric_array_params
                [self.rng.gen_range(0..numeric_array_params.len())];
            let suffix = if matches!(prim, PrimitiveType::I32) {
                "_i32"
            } else {
                ""
            };
            let type_annot = if matches!(prim, PrimitiveType::I32) {
                "i32"
            } else {
                "i64"
            };

            let (init, op) = match self.rng.gen_range(0..3u32) {
                0 => (format!("0{}", suffix), "+"),
                1 => (format!("1{}", suffix), "*"),
                _ => (format!("0{}", suffix), "+"),
            };

            ctx.add_local(
                name.clone(),
                TypeInfo::Primitive(*prim),
                false,
            );
            Some(format!(
                "let {} = {}.iter().reduce({}, (acc: {}, x: {}) -> {} => acc {} x)",
                name, arr_name, init, type_annot, type_annot, type_annot, op
            ))
        } else {
            let arr_name =
                &string_array_params[self.rng.gen_range(0..string_array_params.len())];
            let seps = [", ", " ", "-", "; "];
            let sep = seps[self.rng.gen_range(0..seps.len())];

            ctx.add_local(
                name.clone(),
                TypeInfo::Primitive(PrimitiveType::String),
                false,
            );
            Some(format!(
                "let {} = {}.iter().reduce(\"\", (acc, x) => acc + x + \"{}\")",
                name, arr_name, sep
            ))
        }
    }

    /// Generate i32 operations near the boundary values.
    /// E.g.: `let x = 2147483647_i32 - 1_i32`, `let y = -2147483648_i32 + 1_i32`
    fn generate_i32_boundary_safe(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();

        let expr = match self.rng.gen_range(0..6u32) {
            0 => "2147483647_i32 - 1_i32".to_string(),
            1 => "(-2147483647_i32 + 1_i32)".to_string(),
            2 => "(2147483646_i32 + 1_i32)".to_string(),
            3 => "(1073741823_i32 * 2_i32)".to_string(),
            4 => "(2147483647_i32 / 2_i32)".to_string(),
            _ => "(2147483647_i32 % 100_i32)".to_string(),
        };

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::I32),
            false,
        );
        format!("let {} = {}", name, expr)
    }

    /// Generate operations on empty strings to test edge cases.
    /// E.g.: `"".length()`, `"".to_upper()`, `"".trim()`, `"".split(",").count()`
    fn generate_empty_string_ops(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();

        let (expr, ty) = match self.rng.gen_range(0..6u32) {
            0 => ("\"\"".to_string() + ".length()", TypeInfo::Primitive(PrimitiveType::I64)),
            1 => ("\"\"".to_string() + ".to_upper()", TypeInfo::Primitive(PrimitiveType::String)),
            2 => ("\"\"".to_string() + ".trim()", TypeInfo::Primitive(PrimitiveType::String)),
            3 => (
                "\"\"".to_string() + ".split(\",\").count()",
                TypeInfo::Primitive(PrimitiveType::I64),
            ),
            4 => (
                "\"\"".to_string() + ".contains(\"\")",
                TypeInfo::Primitive(PrimitiveType::Bool),
            ),
            _ => (
                "\"\"".to_string() + ".starts_with(\"\")",
                TypeInfo::Primitive(PrimitiveType::Bool),
            ),
        };

        ctx.add_local(name.clone(), ty, false);
        format!("let {} = {}", name, expr)
    }

    /// Generate a manual for-loop reduce pattern:
    /// `let mut acc = 0; for x in arr.iter() { acc = acc + x }`
    fn try_generate_for_reduce_pattern(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find numeric array parameters
        let array_params: Vec<(String, PrimitiveType)> = ctx
            .params
            .iter()
            .filter_map(|p| match &p.param_type {
                TypeInfo::Array(inner) => match inner.as_ref() {
                    TypeInfo::Primitive(prim @ (PrimitiveType::I64 | PrimitiveType::I32)) => {
                        Some((p.name.clone(), *prim))
                    }
                    _ => None,
                },
                _ => None,
            })
            .collect();

        if array_params.is_empty() {
            return None;
        }

        let (arr_name, prim) = &array_params[self.rng.gen_range(0..array_params.len())];
        let acc_name = ctx.new_local_name();
        let iter_name = ctx.new_local_name();

        let suffix = if matches!(prim, PrimitiveType::I32) {
            "_i32"
        } else {
            ""
        };

        let op = match self.rng.gen_range(0..2u32) {
            0 => "+",
            _ => "+", // keep it simple — multiplication can overflow
        };

        // Protect the accumulator from compound assignment modifications
        ctx.protected_vars.push(acc_name.clone());

        ctx.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(*prim),
            true,
        );

        Some(format!(
            "let mut {} = 0{}\nfor {} in {}.iter() {{\n    {} = {} {} {}\n}}",
            acc_name, suffix, iter_name, arr_name, acc_name, acc_name, op, iter_name
        ))
    }

    /// Generate a when expression with a match inside an arm:
    /// `when { cond => match x { 0 => a, _ => b }, _ => default }`
    fn try_generate_when_match_combo(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Need an i32 or i64 variable for match scrutinee
        let int_vars: Vec<(String, PrimitiveType)> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| {
                matches!(
                    ty,
                    TypeInfo::Primitive(PrimitiveType::I64 | PrimitiveType::I32)
                )
            })
            .map(|(name, ty, _)| {
                (
                    name.clone(),
                    match ty {
                        TypeInfo::Primitive(p) => *p,
                        _ => unreachable!(),
                    },
                )
            })
            .chain(ctx.params.iter().filter_map(|p| match &p.param_type {
                TypeInfo::Primitive(prim @ (PrimitiveType::I64 | PrimitiveType::I32)) => {
                    Some((p.name.clone(), *prim))
                }
                _ => None,
            }))
            .collect();

        if int_vars.is_empty() {
            return None;
        }

        let (var, _prim) = &int_vars[self.rng.gen_range(0..int_vars.len())];
        let name = ctx.new_local_name();

        // Result type is string — simple and safe
        let match_val0 = self.rng.gen_range(0..=5);
        let match_val1 = match_val0 + 1 + self.rng.gen_range(0..=3);

        let strs = ["\"a\"", "\"b\"", "\"c\"", "\"d\"", "\"e\""];

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = when {{\n    true => match {} {{\n        {} => {}\n        {} => {}\n        _ => {}\n    }}\n    _ => {}\n}}",
            name,
            var,
            match_val0,
            strs[0],
            match_val1,
            strs[1],
            strs[2],
            strs[3],
        ))
    }

    /// Generate a for loop over split string:
    /// `let parts = "a,b,c".split(",").collect(); let mut s = ""; for p in parts.iter() { s = s + p }`
    fn generate_string_split_for(&mut self, ctx: &mut StmtContext) -> String {
        let parts_name = ctx.new_local_name();
        let acc_name = ctx.new_local_name();
        let iter_name = ctx.new_local_name();

        let strings = [
            ("\"alpha,beta,gamma\"", "\",\""),
            ("\"hello world foo\"", "\" \""),
            ("\"a-b-c-d\"", "\"-\""),
            ("\"one;two;three\"", "\";\""),
        ];
        let (s, delim) = strings[self.rng.gen_range(0..strings.len())];

        // Protect accumulator
        ctx.protected_vars.push(acc_name.clone());

        ctx.add_local(
            parts_name.clone(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
            false,
        );
        ctx.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            true,
        );

        format!(
            "let {} = {}.split({}).collect()\nlet mut {} = \"\"\nfor {} in {}.iter() {{\n    {} = {} + {}\n}}",
            parts_name, s, delim, acc_name, iter_name, parts_name, acc_name, acc_name, iter_name
        )
    }

    /// Generate a nested when expression with string result:
    /// `when { a > 0 => when { b > 0 => "both", _ => "b_neg" }, _ => "a_neg" }`
    fn try_generate_nested_when_string_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if i64_vars.len() < 2 {
            return None;
        }

        let var_a = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let var_b = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let name = ctx.new_local_name();

        let thresh_a = self.rng.gen_range(0..=10);
        let thresh_b = self.rng.gen_range(0..=10);

        let strs = ["\"both_pos\"", "\"b_neg\"", "\"a_neg\""];

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = when {{\n    {} > {} => when {{\n        {} > {} => {}\n        _ => {}\n    }}\n    _ => {}\n}}",
            name, var_a, thresh_a, var_b, thresh_b, strs[0], strs[1], strs[2]
        ))
    }

    /// Generate `.to_string()` on numeric variables or literals (simple form).
    /// E.g.: `let s = 42.to_string()`, `let s = var.to_string()`
    fn try_generate_numeric_to_string_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        let name = ctx.new_local_name();

        let expr = if !i64_vars.is_empty() && self.rng.gen_bool(0.6) {
            let var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
            format!("{}.to_string()", var)
        } else {
            // Use a non-negative literal (negative literals can't have methods called on them)
            let val = self.rng.gen_range(0..=999);
            format!("{}.to_string()", val)
        };

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!("let {} = {}", name, expr))
    }

    /// Generate `.substring(start, end)` on strings.
    /// E.g.: `let s = "hello world".substring(0, 5)`, `let s = var.substring(0, 3)`
    fn try_generate_substring_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let string_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        let name = ctx.new_local_name();

        // Use known-length literals to avoid out-of-bounds
        let (receiver, max_len) = if !string_vars.is_empty() && self.rng.gen_bool(0.4) {
            // For variables, use conservative indices (0..3)
            (string_vars[self.rng.gen_range(0..string_vars.len())].clone(), 3)
        } else {
            let literals = [
                ("\"hello world\"", 11),
                ("\"testing\"", 7),
                ("\"abcdefghij\"", 10),
                ("\"vole lang\"", 9),
            ];
            let (lit, len) = literals[self.rng.gen_range(0..literals.len())];
            (lit.to_string(), len)
        };

        let start = self.rng.gen_range(0..max_len.min(4) as i32);
        let end = self.rng.gen_range(start..=max_len as i32);

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = {}.substring({}, {})",
            name, receiver, start, end
        ))
    }

    /// Generate a match where arm values use `.to_string()`:
    /// `match x { 0 => 0.to_string(), 1 => 1.to_string(), _ => x.to_string() }`
    fn try_generate_match_to_string_arms(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if i64_vars.is_empty() {
            return None;
        }

        let var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let name = ctx.new_local_name();

        let num_arms = self.rng.gen_range(2..=3);
        let mut arms = Vec::new();
        for i in 0..num_arms {
            arms.push(format!("    {} => {}.to_string()", i, i));
        }
        arms.push(format!("    _ => {}.to_string()", var));

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = match {} {{\n{}\n}}",
            name,
            var,
            arms.join("\n")
        ))
    }

    /// Generate a for loop building a string with interpolation:
    /// `let mut s = ""; for i in 0..N { s = s + "item {i} " }`
    fn generate_for_interpolation_concat(&mut self, ctx: &mut StmtContext) -> String {
        let acc_name = ctx.new_local_name();
        let iter_name = ctx.new_local_name();
        let n = self.rng.gen_range(2..=5);

        let prefixes = ["item", "val", "x", "n", "elem"];
        let prefix = prefixes[self.rng.gen_range(0..prefixes.len())];

        // Protect accumulator
        ctx.protected_vars.push(acc_name.clone());

        ctx.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            true,
        );

        format!(
            "let mut {} = \"\"\nfor {} in 0..{} {{\n    {} = {} + \"{}={{{}}} \"\n}}",
            acc_name, iter_name, n, acc_name, acc_name, prefix, iter_name
        )
    }

    /// Generate a complex boolean chain: `(a > 0) && (b < 10) || !c`
    fn try_generate_bool_chain_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let bool_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::Bool)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::Bool)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if bool_vars.is_empty() && i64_vars.is_empty() {
            return None;
        }

        let name = ctx.new_local_name();
        let mut parts = Vec::new();

        let num_parts = self.rng.gen_range(2..=4);
        for _ in 0..num_parts {
            let part = match self.rng.gen_range(0..4u32) {
                0 if !bool_vars.is_empty() => {
                    bool_vars[self.rng.gen_range(0..bool_vars.len())].clone()
                }
                1 if !bool_vars.is_empty() => {
                    format!("!{}", bool_vars[self.rng.gen_range(0..bool_vars.len())])
                }
                2 if !i64_vars.is_empty() => {
                    let var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
                    let n = self.rng.gen_range(0..=10);
                    let op = match self.rng.gen_range(0..3u32) {
                        0 => ">",
                        1 => "<",
                        _ => "==",
                    };
                    format!("({} {} {})", var, op, n)
                }
                _ => {
                    if self.rng.gen_bool(0.5) {
                        "true".to_string()
                    } else {
                        "false".to_string()
                    }
                }
            };
            parts.push(part);
        }

        // Join with && and ||
        let mut expr = parts[0].clone();
        for i in 1..parts.len() {
            let op = if self.rng.gen_bool(0.6) { "&&" } else { "||" };
            expr = format!("({} {} {})", expr, op, parts[i]);
        }

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );
        Some(format!("let {} = {}", name, expr))
    }

    /// Generate a comparison chain: `(a > b) == (c > d)`, `(a != 0) && (b != 0)`
    fn try_generate_comparison_chain_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if i64_vars.len() < 2 {
            return None;
        }

        let name = ctx.new_local_name();

        let a = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let b = &i64_vars[self.rng.gen_range(0..i64_vars.len())];

        let expr = match self.rng.gen_range(0..4u32) {
            0 => format!("({} > 0) == ({} > 0)", a, b),
            1 => format!("({} != 0) && ({} != 0)", a, b),
            2 => format!("({} >= 0) || ({} >= 0)", a, b),
            _ => {
                let n = self.rng.gen_range(1..=10);
                format!("({} > {}) == ({} > {})", a, n, b, n)
            }
        };

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );
        Some(format!("let {} = {}", name, expr))
    }

    /// Generate when with string predicate:
    /// `when { s.contains("x") => "found", _ => "not found" }`
    fn try_generate_when_with_contains(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let string_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if string_vars.is_empty() {
            return None;
        }

        let var = &string_vars[self.rng.gen_range(0..string_vars.len())];
        let name = ctx.new_local_name();

        let method = match self.rng.gen_range(0..3u32) {
            0 => "contains",
            1 => "starts_with",
            _ => "ends_with",
        };
        let needles = ["hello", "test", "a", "str", ""];
        let needle = needles[self.rng.gen_range(0..needles.len())];

        let results = ["\"found\"", "\"yes\"", "\"match\"", "\"true\""];
        let defaults = ["\"not found\"", "\"no\"", "\"miss\"", "\"false\""];
        let idx = self.rng.gen_range(0..results.len());

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = when {{\n    {}.{}(\"{}\") => {}\n    _ => {}\n}}",
            name, var, method, needle, results[idx], defaults[idx]
        ))
    }

    /// Generate match on array length:
    /// `match arr.length() { 0 => "empty", 1 => "one", _ => "many" }`
    fn try_generate_match_array_length(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let array_params: Vec<String> = ctx
            .params
            .iter()
            .filter(|p| matches!(p.param_type, TypeInfo::Array(_)))
            .map(|p| p.name.clone())
            .collect();

        if array_params.is_empty() {
            return None;
        }

        let arr = &array_params[self.rng.gen_range(0..array_params.len())];
        let name = ctx.new_local_name();

        let labels = ["\"empty\"", "\"one\"", "\"two\"", "\"few\"", "\"many\""];

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = match {}.length() {{\n    0 => {}\n    1 => {}\n    2 => {}\n    _ => {}\n}}",
            name, arr, labels[0], labels[1], labels[2], labels[4]
        ))
    }

    /// Generate `.iter().sorted().collect()` on a numeric array parameter.
    fn try_generate_sorted_collect_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let numeric_array_params: Vec<(String, TypeInfo)> = ctx
            .params
            .iter()
            .filter_map(|p| match &p.param_type {
                TypeInfo::Array(inner) => match inner.as_ref() {
                    TypeInfo::Primitive(PrimitiveType::I64 | PrimitiveType::I32) => {
                        Some((p.name.clone(), p.param_type.clone()))
                    }
                    _ => None,
                },
                _ => None,
            })
            .collect();

        if numeric_array_params.is_empty() {
            return None;
        }

        let (arr_name, arr_type) =
            &numeric_array_params[self.rng.gen_range(0..numeric_array_params.len())];
        let name = ctx.new_local_name();

        ctx.add_local(name.clone(), arr_type.clone(), false);
        Some(format!(
            "let {} = {}.iter().sorted().collect()",
            name, arr_name
        ))
    }

    /// Generate `.iter().reverse().collect()` on an array parameter.
    fn try_generate_reverse_collect_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let array_params: Vec<(String, TypeInfo)> = ctx
            .params
            .iter()
            .filter_map(|p| match &p.param_type {
                TypeInfo::Array(inner) => match inner.as_ref() {
                    TypeInfo::Primitive(
                        PrimitiveType::I64
                        | PrimitiveType::I32
                        | PrimitiveType::String
                        | PrimitiveType::F64,
                    ) => Some((p.name.clone(), p.param_type.clone())),
                    _ => None,
                },
                _ => None,
            })
            .collect();

        if array_params.is_empty() {
            return None;
        }

        let (arr_name, arr_type) = &array_params[self.rng.gen_range(0..array_params.len())];
        let name = ctx.new_local_name();

        ctx.add_local(name.clone(), arr_type.clone(), false);
        Some(format!(
            "let {} = {}.iter().reverse().collect()",
            name, arr_name
        ))
    }

    /// Generate a guarded division: `when { b != 0 => a / b, _ => 0 }`
    /// Exercises safe division pattern with zero-check guard.
    fn try_generate_zero_division_guard(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find two numeric variables of the same type
        let numeric_vars: Vec<(String, PrimitiveType)> = ctx
            .locals
            .iter()
            .filter_map(|(name, ty, _)| match ty {
                TypeInfo::Primitive(p @ (PrimitiveType::I64 | PrimitiveType::I32)) => {
                    Some((name.clone(), *p))
                }
                _ => None,
            })
            .collect();

        if numeric_vars.len() < 2 {
            return None;
        }

        let idx_a = self.rng.gen_range(0..numeric_vars.len());
        let mut idx_b = self.rng.gen_range(0..numeric_vars.len());
        while idx_b == idx_a {
            idx_b = self.rng.gen_range(0..numeric_vars.len());
        }

        let (a_name, a_prim) = &numeric_vars[idx_a];
        let (b_name, b_prim) = &numeric_vars[idx_b];

        // Both must be same type for division
        if a_prim != b_prim {
            return None;
        }

        let name = ctx.new_local_name();
        let zero = match a_prim {
            PrimitiveType::I64 => "0",
            PrimitiveType::I32 => "0_i32",
            _ => return None,
        };

        // Choose division or modulo
        let op = if self.rng.gen_bool(0.5) { "/" } else { "%" };

        ctx.add_local(name.clone(), TypeInfo::Primitive(*a_prim), false);
        Some(format!(
            "let {} = when {{ {} != {} => {} {} {}, _ => {} }}",
            name, b_name, zero, a_name, op, b_name, zero
        ))
    }

    /// Generate operations on single-character strings.
    /// Tests edge behavior of string methods on minimal inputs.
    fn generate_single_char_string_ops(&mut self, ctx: &mut StmtContext) -> String {
        let chars = ["a", "Z", "0", " ", "x", "M"];
        let ch = chars[self.rng.gen_range(0..chars.len())];
        let name = ctx.new_local_name();

        match self.rng.gen_range(0..6) {
            0 => {
                // "x".to_upper()
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::String), false);
                format!("let {} = \"{}\".to_upper()", name, ch)
            }
            1 => {
                // "x".to_lower()
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::String), false);
                format!("let {} = \"{}\".to_lower()", name, ch)
            }
            2 => {
                // "x".length()
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                format!("let {} = \"{}\".length()", name, ch)
            }
            3 => {
                // "x".contains("x")
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::Bool), false);
                format!("let {} = \"{}\".contains(\"{}\")", name, ch, ch)
            }
            4 => {
                // "x".trim()
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::String), false);
                format!("let {} = \"{}\".trim()", name, ch)
            }
            _ => {
                // "x".substring(0, 1)
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::String), false);
                format!("let {} = \"{}\".substring(0, 1)", name, ch)
            }
        }
    }

    /// Generate f64 literal arithmetic operations.
    /// Tests floating-point codegen paths with known-safe values.
    fn generate_f64_literal_ops_let(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();
        let literals = [
            "0.0", "1.0", "0.5", "2.5", "3.14", "100.0", "0.1", "99.9",
        ];
        let a = literals[self.rng.gen_range(0..literals.len())];
        let b = literals[self.rng.gen_range(0..literals.len())];

        // Find f64 variables
        let f64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::F64)))
            .map(|(name, _, _)| name.clone())
            .collect();

        match self.rng.gen_range(0..5) {
            0 => {
                // f64 addition: 1.5 + 2.3
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::F64), false);
                format!("let {} = {} + {}", name, a, b)
            }
            1 => {
                // f64 multiplication: 3.14 * 2.0
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::F64), false);
                format!("let {} = {} * {}", name, a, b)
            }
            2 => {
                // f64 subtraction with variable if available
                if let Some(var) = f64_vars.first() {
                    ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::F64), false);
                    format!("let {} = {} - {}", name, var, a)
                } else {
                    ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::F64), false);
                    format!("let {} = {} - {}", name, a, b)
                }
            }
            3 => {
                // f64 comparison: a > b
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::Bool), false);
                if let Some(var) = f64_vars.first() {
                    format!("let {} = {} > {}", name, var, a)
                } else {
                    format!("let {} = {} > {}", name, a, b)
                }
            }
            _ => {
                // f64 division by non-zero literal
                let divisors = ["1.0", "2.0", "0.5", "3.14", "10.0"];
                let d = divisors[self.rng.gen_range(0..divisors.len())];
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::F64), false);
                if let Some(var) = f64_vars.first() {
                    format!("let {} = {} / {}", name, var, d)
                } else {
                    format!("let {} = {} / {}", name, a, d)
                }
            }
        }
    }

    /// Generate `.iter().take(N).collect()` or `.iter().skip(N).collect()` on parameter arrays.
    /// Uses parameter arrays with known length to avoid empty-array issues.
    fn try_generate_iter_take_skip_collect_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Only use parameter arrays (guaranteed non-empty with known min length)
        let array_params: Vec<(String, TypeInfo)> = ctx
            .params
            .iter()
            .filter_map(|p| match &p.param_type {
                TypeInfo::Array(_) => Some((p.name.clone(), p.param_type.clone())),
                _ => None,
            })
            .collect();

        if array_params.is_empty() {
            return None;
        }

        let (arr_name, arr_type) = &array_params[self.rng.gen_range(0..array_params.len())];
        let name = ctx.new_local_name();

        // Use small N values (1-3) to keep results meaningful
        let n = self.rng.gen_range(1..=3);

        ctx.add_local(name.clone(), arr_type.clone(), false);
        if self.rng.gen_bool(0.5) {
            Some(format!(
                "let {} = {}.iter().take({}).collect()",
                name, arr_name, n
            ))
        } else {
            Some(format!(
                "let {} = {}.iter().skip({}).collect()",
                name, arr_name, n
            ))
        }
    }

    /// Generate f64 equality/comparison edge cases.
    /// Tests floating-point equality semantics: `0.0 == 0.0`, `1.0 != 2.0`, etc.
    fn generate_f64_comparison_edge_let(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();
        ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::Bool), false);

        match self.rng.gen_range(0..5) {
            0 => format!("let {} = 0.0 == 0.0", name),
            1 => format!("let {} = 1.0 != 2.0", name),
            2 => format!("let {} = 0.0 < 1.0", name),
            3 => {
                // Compare two f64 vars if available
                let f64_vars: Vec<String> = ctx
                    .locals
                    .iter()
                    .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::F64)))
                    .map(|(n, _, _)| n.clone())
                    .collect();
                if f64_vars.len() >= 2 {
                    format!("let {} = {} >= {}", name, f64_vars[0], f64_vars[1])
                } else {
                    format!("let {} = 3.14 > 2.71", name)
                }
            }
            _ => format!("let {} = 1.0 <= 1.0", name),
        }
    }

    /// Generate operations on strings with repeated characters.
    /// Tests string method behavior on uniform content: "aaa", "   ", "111".
    fn generate_repeated_string_ops(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();
        let repeated_strings = ["aaa", "   ", "111", "xxx", "ZZZ"];
        let s = repeated_strings[self.rng.gen_range(0..repeated_strings.len())];

        match self.rng.gen_range(0..5) {
            0 => {
                // "aaa".length()
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                format!("let {} = \"{}\".length()", name, s)
            }
            1 => {
                // "aaa".contains("a")
                let ch = &s[0..1];
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::Bool), false);
                format!("let {} = \"{}\".contains(\"{}\")", name, s, ch)
            }
            2 => {
                // "aaa".replace("a", "b")
                let ch = &s[0..1];
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::String), false);
                format!("let {} = \"{}\".replace(\"{}\", \"b\")", name, s, ch)
            }
            3 => {
                // "   ".trim()
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::String), false);
                format!("let {} = \"{}\".trim()", name, s)
            }
            _ => {
                // "aaa".to_upper()
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::String), false);
                format!("let {} = \"{}\".to_upper()", name, s)
            }
        }
    }

    /// Generate a when expression with f64 variable conditions.
    /// E.g.: `when { x > 1.0 => "big", x > 0.0 => "small", _ => "zero" }`
    fn try_generate_when_f64_cond_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let f64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::F64)))
            .map(|(name, _, _)| name.clone())
            .collect();

        if f64_vars.is_empty() {
            return None;
        }

        let var = &f64_vars[self.rng.gen_range(0..f64_vars.len())];
        let name = ctx.new_local_name();
        let thresholds = ["100.0", "10.0", "1.0", "0.0"];

        // Build 2-3 arms + wildcard
        let num_arms = self.rng.gen_range(2..=3);
        let mut arms = Vec::new();
        let labels = ["\"high\"", "\"medium\"", "\"low\"", "\"zero\""];

        for i in 0..num_arms {
            if i < thresholds.len() && i < labels.len() {
                arms.push(format!("{} > {} => {}", var, thresholds[i], labels[i]));
            }
        }
        arms.push(format!("_ => {}", labels[num_arms.min(labels.len() - 1)]));

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = when {{ {} }}",
            name,
            arms.join(", ")
        ))
    }

    /// Generate a for-range loop that builds a string from index.to_string().
    /// E.g.: `let mut s = ""; for i in 0..5 { s = s + i.to_string() }`
    fn generate_for_range_tostring_build(&mut self, ctx: &mut StmtContext) -> String {
        let acc_name = ctx.new_local_name();
        let iter_var = ctx.new_local_name();
        let n = self.rng.gen_range(2..=5);

        ctx.protected_vars.push(acc_name.clone());
        ctx.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            true,
        );
        let indent = self.indent;
        format!(
            "let mut {} = \"\"\n{}for {} in 0..{} {{\n{}  {} = {} + {}.to_string()\n{}}}",
            acc_name,
            " ".repeat(indent * 2),
            iter_var,
            n,
            " ".repeat((indent + 1) * 2),
            acc_name,
            acc_name,
            iter_var,
            " ".repeat(indent * 2),
        )
    }

    /// Generate match with when expression in arm values.
    /// E.g.: `match x { 0 => when { y > 0 => "pos", _ => "neg" }, _ => "other" }`
    fn try_generate_match_when_arm_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Need an i64 or i32 variable for match scrutinee
        let numeric_vars: Vec<(String, PrimitiveType)> = ctx
            .locals
            .iter()
            .filter_map(|(name, ty, _)| match ty {
                TypeInfo::Primitive(p @ (PrimitiveType::I64 | PrimitiveType::I32)) => {
                    Some((name.clone(), *p))
                }
                _ => None,
            })
            .collect();

        if numeric_vars.len() < 2 {
            return None;
        }

        let (scrutinee, prim) = &numeric_vars[0];
        let (cond_var, _) = &numeric_vars[1];
        let name = ctx.new_local_name();
        let suffix = if *prim == PrimitiveType::I32 {
            "_i32"
        } else {
            ""
        };

        let val = self.rng.gen_range(0..=3);
        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = match {} {{ {}{} => when {{ {} > 0{} => \"match_pos\", _ => \"match_neg\" }}, _ => \"other\" }}",
            name, scrutinee, val, suffix, cond_var, suffix
        ))
    }

    /// Generate sorted iteration with accumulation.
    /// E.g.: `let sorted = arr.iter().sorted().collect(); let mut acc = 0; for x in sorted.iter() { acc = acc + x }`
    fn try_generate_sorted_iter_accum(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Need a numeric array parameter
        let array_params: Vec<(String, PrimitiveType)> = ctx
            .params
            .iter()
            .filter_map(|param| match &param.param_type {
                TypeInfo::Array(inner) => match inner.as_ref() {
                    TypeInfo::Primitive(prim @ (PrimitiveType::I64 | PrimitiveType::I32)) => {
                        Some((param.name.clone(), *prim))
                    }
                    _ => None,
                },
                _ => None,
            })
            .collect();

        if array_params.is_empty() {
            return None;
        }

        let (arr_name, elem_prim) = &array_params[self.rng.gen_range(0..array_params.len())];
        let sorted_name = ctx.new_local_name();
        let acc_name = ctx.new_local_name();
        let iter_var = ctx.new_local_name();
        let indent = self.indent;

        let zero = if *elem_prim == PrimitiveType::I32 {
            "0_i32"
        } else {
            "0"
        };

        let arr_type = TypeInfo::Array(Box::new(TypeInfo::Primitive(*elem_prim)));
        ctx.add_local(sorted_name.clone(), arr_type, false);
        ctx.protected_vars.push(acc_name.clone());
        ctx.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(*elem_prim),
            true,
        );

        Some(format!(
            "let {} = {}.iter().sorted().collect()\n{}let mut {} = {}\n{}for {} in {}.iter() {{\n{}  {} = {} + {}\n{}}}",
            sorted_name,
            arr_name,
            " ".repeat(indent * 2),
            acc_name,
            zero,
            " ".repeat(indent * 2),
            iter_var,
            sorted_name,
            " ".repeat((indent + 1) * 2),
            acc_name,
            acc_name,
            iter_var,
            " ".repeat(indent * 2),
        ))
    }

    /// Generate filter-collect then iterate converting to string.
    /// E.g.: `let pos = arr.iter().filter(x => x > 0).collect(); let mut s = ""; for x in pos.iter() { s = s + x.to_string() }`
    fn try_generate_filter_iter_tostring(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Need a numeric array parameter (i64)
        let i64_arrays: Vec<String> = ctx
            .params
            .iter()
            .filter_map(|p| match &p.param_type {
                TypeInfo::Array(inner)
                    if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::I64)) =>
                {
                    Some(p.name.clone())
                }
                _ => None,
            })
            .collect();

        if i64_arrays.is_empty() {
            return None;
        }

        let arr_name = &i64_arrays[self.rng.gen_range(0..i64_arrays.len())];
        let filtered_name = ctx.new_local_name();
        let acc_name = ctx.new_local_name();
        let iter_var = ctx.new_local_name();
        let indent = self.indent;

        let threshold = self.rng.gen_range(0..=5);

        ctx.add_local(
            filtered_name.clone(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );
        ctx.protected_vars.push(acc_name.clone());
        ctx.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            true,
        );

        Some(format!(
            "let {} = {}.iter().filter((x) => x > {}).collect()\n{}let mut {} = \"\"\n{}for {} in {}.iter() {{\n{}  {} = {} + {}.to_string()\n{}}}",
            filtered_name,
            arr_name,
            threshold,
            " ".repeat(indent * 2),
            acc_name,
            " ".repeat(indent * 2),
            iter_var,
            filtered_name,
            " ".repeat((indent + 1) * 2),
            acc_name,
            acc_name,
            iter_var,
            " ".repeat(indent * 2),
        ))
    }

    /// Generate when expression comparing lengths of array and string.
    /// E.g.: `when { arr.length() > s.length() => "arr_bigger", _ => "str_bigger" }`
    fn try_generate_when_length_compare(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Need at least one array and one string variable
        let array_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Array(_)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Array(_)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        let string_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| {
                        matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String))
                    })
                    .map(|p| p.name.clone()),
            )
            .collect();

        if array_vars.is_empty() || string_vars.is_empty() {
            return None;
        }

        let arr = &array_vars[self.rng.gen_range(0..array_vars.len())];
        let s = &string_vars[self.rng.gen_range(0..string_vars.len())];
        let name = ctx.new_local_name();

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = when {{ {}.length() > {}.length() => \"arr_longer\", _ => \"str_longer\" }}",
            name, arr, s
        ))
    }

    /// Generate character extraction via substring on known-length strings.
    /// E.g.: `let ch = "hello".substring(2, 3)` — extracts single character.
    fn generate_string_char_at_let(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();
        let strings = [
            ("hello", 5),
            ("world", 5),
            ("test", 4),
            ("abc", 3),
            ("vole", 4),
        ];
        let (s, len) = strings[self.rng.gen_range(0..strings.len())];
        let idx = self.rng.gen_range(0..len);

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        format!(
            "let {} = \"{}\".substring({}, {})",
            name, s, idx, idx + 1
        )
    }

    /// Generate range-based iterator with map and collect.
    /// E.g.: `let arr = (0..5).iter().map((x) => x * 2).collect()`
    fn generate_range_iter_map_collect(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();
        let n = self.rng.gen_range(2..=8);
        let multiplier = self.rng.gen_range(1..=5);

        let map_op = match self.rng.gen_range(0..3) {
            0 => format!("x * {}", multiplier),
            1 => format!("x + {}", multiplier),
            _ => format!("x * {} + 1", multiplier),
        };

        ctx.add_local(
            name.clone(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );
        format!(
            "let {} = (0..{}).iter().map((x) => {}).collect()",
            name, n, map_op
        )
    }

    /// Generate match on interpolated string length.
    /// E.g.: `match "val={x}".length() { 4 => "short", 5 => "medium", _ => "long" }`
    fn try_generate_match_interpolation_length(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Need a variable to interpolate
        let vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| {
                matches!(
                    ty,
                    TypeInfo::Primitive(
                        PrimitiveType::I64
                            | PrimitiveType::I32
                            | PrimitiveType::String
                            | PrimitiveType::Bool
                    )
                )
            })
            .map(|(name, _, _)| name.clone())
            .collect();

        if vars.is_empty() {
            return None;
        }

        let var = &vars[self.rng.gen_range(0..vars.len())];
        let name = ctx.new_local_name();
        let prefix = ["val", "x", "result", "out"];
        let pfx = prefix[self.rng.gen_range(0..prefix.len())];

        use std::collections::HashSet;
        let mut used_vals = HashSet::new();
        let mut arms = Vec::new();
        for _ in 0..self.rng.gen_range(2..=3) {
            let v = self.rng.gen_range(1..=20) as i64;
            if used_vals.insert(v) {
                let labels = ["\"short\"", "\"medium\"", "\"exact\""];
                let label = labels[arms.len().min(labels.len() - 1)];
                arms.push(format!("{} => {}", v, label));
            }
        }
        arms.push("_ => \"other\"".to_string());

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = match \"{}={{{}}}\".length() {{ {} }}",
            name,
            pfx,
            var,
            arms.join(", ")
        ))
    }

    /// Generate range for-loop with when body accumulating strings.
    /// E.g.: `let mut s = ""; for i in 0..5 { s = s + when { i > 2 => "big", _ => "small" } }`
    fn generate_for_range_when_accum(&mut self, ctx: &mut StmtContext) -> String {
        let acc_name = ctx.new_local_name();
        let iter_var = ctx.new_local_name();
        let n = self.rng.gen_range(3..=6);
        let threshold = self.rng.gen_range(1..n);
        let indent = self.indent;

        ctx.protected_vars.push(acc_name.clone());
        ctx.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            true,
        );
        format!(
            "let mut {} = \"\"\n{}for {} in 0..{} {{\n{}  {} = {} + when {{ {} > {} => \"hi\", _ => \"lo\" }}\n{}}}",
            acc_name,
            " ".repeat(indent * 2),
            iter_var,
            n,
            " ".repeat((indent + 1) * 2),
            acc_name,
            acc_name,
            iter_var,
            threshold,
            " ".repeat(indent * 2),
        )
    }

    /// Generate when with to_string in arm values.
    /// E.g.: `when { x > 0 => x.to_string(), _ => "negative" }`
    fn try_generate_when_tostring_arms(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let i64_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .collect();

        if i64_vars.is_empty() {
            return None;
        }

        let var = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let name = ctx.new_local_name();
        let threshold = self.rng.gen_range(0..=10);

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = when {{ {} > {} => {}.to_string(), _ => \"default\" }}",
            name, var, threshold, var
        ))
    }

    /// Generate match on sorted array length.
    /// E.g.: `match arr.iter().sorted().collect().length() { 0 => "empty", _ => "has items" }`
    fn try_generate_match_sorted_length(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Need a numeric array parameter
        let array_params: Vec<String> = ctx
            .params
            .iter()
            .filter_map(|p| match &p.param_type {
                TypeInfo::Array(inner) => match inner.as_ref() {
                    TypeInfo::Primitive(
                        PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64,
                    ) => Some(p.name.clone()),
                    _ => None,
                },
                _ => None,
            })
            .collect();

        if array_params.is_empty() {
            return None;
        }

        let arr = &array_params[self.rng.gen_range(0..array_params.len())];
        let name = ctx.new_local_name();

        use std::collections::HashSet;
        let mut used = HashSet::new();
        let mut arms = Vec::new();
        let labels = ["\"empty\"", "\"one\"", "\"two\"", "\"few\""];
        for i in 0..self.rng.gen_range(2..=3) {
            let v = i as i64;
            if used.insert(v) {
                arms.push(format!("{} => {}", v, labels[i.min(labels.len() - 1)]));
            }
        }
        arms.push("_ => \"many\"".to_string());

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = match {}.iter().sorted().collect().length() {{ {} }}",
            name,
            arr,
            arms.join(", ")
        ))
    }

    /// Generate single-element range operations.
    /// E.g.: `(5..6).iter().collect()` — range with exactly one element.
    fn generate_single_elem_range_let(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();
        let start = self.rng.gen_range(0..=10);

        match self.rng.gen_range(0..3) {
            0 => {
                // Collect single-element range
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                    false,
                );
                format!("let {} = ({}..{}).iter().collect()", name, start, start + 1)
            }
            1 => {
                // Sum of single-element range
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                format!("let {} = ({}..{}).iter().sum()", name, start, start + 1)
            }
            _ => {
                // Count of single-element range
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                format!("let {} = ({}..{}).iter().count()", name, start, start + 1)
            }
        }
    }

    /// Generate operations on whitespace-heavy strings.
    /// Tests trim and other string methods on strings with leading/trailing/only whitespace.
    fn generate_whitespace_string_ops(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();
        let ws_strings = [
            "  hello  ",
            "  ",
            " x ",
            "\thello\t",
            "  spaces  here  ",
        ];
        let s = ws_strings[self.rng.gen_range(0..ws_strings.len())];

        match self.rng.gen_range(0..4) {
            0 => {
                // trim
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::String), false);
                format!("let {} = \"{}\".trim()", name, s)
            }
            1 => {
                // length
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                format!("let {} = \"{}\".trim().length()", name, s)
            }
            2 => {
                // contains space
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::Bool), false);
                format!("let {} = \"{}\".contains(\" \")", name, s)
            }
            _ => {
                // replace spaces
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::String), false);
                format!("let {} = \"{}\".replace(\" \", \"\")", name, s)
            }
        }
    }

    fn try_generate_bool_match_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find a bool-typed variable
        let bool_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::Bool)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::Bool)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        // Collect array params for computed bool scrutinee
        let array_params: Vec<(String, TypeInfo)> = ctx
            .params
            .iter()
            .filter(|p| matches!(p.param_type, TypeInfo::Array(_)))
            .map(|p| (p.name.clone(), p.param_type.clone()))
            .collect();

        // Collect string candidates for computed bool scrutinee
        let string_vars: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(name, _, _)| name.clone())
            .chain(
                ctx.params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        // ~35% chance: use a computed bool expression as scrutinee
        // (iterator predicate or string method) instead of a plain bool variable
        let use_computed = self.rng.gen_bool(0.35);
        let scrutinee: String;

        if use_computed {
            let computed = self.try_computed_bool_scrutinee(&array_params, &string_vars);
            if let Some(expr) = computed {
                scrutinee = expr;
            } else if !bool_vars.is_empty() {
                scrutinee = bool_vars[self.rng.gen_range(0..bool_vars.len())].clone();
            } else {
                return None;
            }
        } else if !bool_vars.is_empty() {
            scrutinee = bool_vars[self.rng.gen_range(0..bool_vars.len())].clone();
        } else {
            return None;
        }

        let result_type = self.random_primitive_type();
        let result_name = ctx.new_local_name();

        let expr_ctx = ctx.to_expr_context();
        let true_val = {
            let mut eg = ExprGenerator::new(self.rng, &self.config.expr_config);
            eg.generate(&result_type, &expr_ctx, 0)
        };
        let false_val = {
            let mut eg = ExprGenerator::new(self.rng, &self.config.expr_config);
            eg.generate(&result_type, &expr_ctx, 0)
        };

        let indent = "    ".repeat(self.indent + 1);
        let close_indent = "    ".repeat(self.indent);

        ctx.add_local(result_name.clone(), result_type, false);

        // Use true + wildcard pattern since Vole doesn't recognize
        // true/false as exhaustive coverage for booleans.
        Some(format!(
            "let {} = match {} {{\n{}true => {}\n{}_ => {}\n{}}}",
            result_name, scrutinee, indent, true_val, indent, false_val, close_indent,
        ))
    }

    /// Generate a computed bool expression for use as a match scrutinee.
    /// Returns expressions like `arr.iter().any((x) => x > 0)` or `str.contains("a")`.
    fn try_computed_bool_scrutinee(
        &mut self,
        array_params: &[(String, TypeInfo)],
        string_vars: &[String],
    ) -> Option<String> {
        // Build a list of possible computed expressions
        let mut options: Vec<String> = Vec::new();

        for (name, elem_ty) in array_params {
            if let TypeInfo::Array(inner) = elem_ty {
                if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::I64)) {
                    options.push(format!("{}.iter().any((x) => x > 0)", name));
                    options.push(format!("{}.iter().all((x) => x == x)", name));
                } else if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::I32)) {
                    options.push(format!("{}.iter().any((x) => x > 0_i32)", name));
                    options.push(format!("{}.iter().all((x) => x == x)", name));
                } else if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::Bool)) {
                    options.push(format!("{}.iter().any((x) => x)", name));
                }
            }
        }

        for name in string_vars {
            options.push(format!("{}.contains(\"a\")", name));
            options.push(format!("{}.starts_with(\"\")", name));
            options.push(format!("{}.length() > 0", name));
        }

        if options.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..options.len());
        Some(options.swap_remove(idx))
    }

    fn try_generate_variable_shadow(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Collect primitive locals that can be shadowed (preserve mutability).
        // Skip protected variables (while-loop counters/guards).
        let candidates: Vec<(String, TypeInfo, bool)> = ctx
            .locals
            .iter()
            .filter(|(name, ty, _)| {
                matches!(ty, TypeInfo::Primitive(_)) && !ctx.protected_vars.contains(name)
            })
            .map(|(name, ty, is_mut)| (name.clone(), ty.clone(), *is_mut))
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (name, ty, was_mutable) = candidates[idx].clone();

        // Pre-roll all random decisions before creating ExprGenerator
        let use_self_ref = self.rng.gen_bool(0.7);
        let offset_i64 = self.rng.gen_range(1..=10i64);
        let offset_i32 = self.rng.gen_range(1..=10i32);

        let new_value = match &ty {
            TypeInfo::Primitive(PrimitiveType::I64) => {
                if use_self_ref {
                    format!("{} + {}", name, offset_i64)
                } else {
                    let expr_ctx = ctx.to_expr_context();
                    let mut eg = ExprGenerator::new(self.rng, &self.config.expr_config);
                    eg.generate(&ty, &expr_ctx, 0)
                }
            }
            TypeInfo::Primitive(PrimitiveType::I32) => {
                if use_self_ref {
                    format!("{} + {}_i32", name, offset_i32)
                } else {
                    let expr_ctx = ctx.to_expr_context();
                    let mut eg = ExprGenerator::new(self.rng, &self.config.expr_config);
                    eg.generate(&ty, &expr_ctx, 0)
                }
            }
            TypeInfo::Primitive(PrimitiveType::Bool) => {
                if use_self_ref {
                    format!("!{}", name)
                } else {
                    let expr_ctx = ctx.to_expr_context();
                    let mut eg = ExprGenerator::new(self.rng, &self.config.expr_config);
                    eg.generate(&ty, &expr_ctx, 0)
                }
            }
            TypeInfo::Primitive(PrimitiveType::String) => {
                if use_self_ref {
                    format!("{} + \"_s\"", name)
                } else {
                    let expr_ctx = ctx.to_expr_context();
                    let mut eg = ExprGenerator::new(self.rng, &self.config.expr_config);
                    eg.generate(&ty, &expr_ctx, 0)
                }
            }
            TypeInfo::Primitive(PrimitiveType::F64) => {
                if use_self_ref {
                    format!("{} + 1.0", name)
                } else {
                    let expr_ctx = ctx.to_expr_context();
                    let mut eg = ExprGenerator::new(self.rng, &self.config.expr_config);
                    eg.generate(&ty, &expr_ctx, 0)
                }
            }
            _ => return None,
        };

        // Preserve mutability — if the original was mutable, the shadow
        // must also be mutable so later reassignment code doesn't break.
        ctx.add_local(name.clone(), ty.clone(), was_mutable);

        let decl = if was_mutable { "let mut" } else { "let" };

        // ~30% chance: add explicit type annotation on the shadow
        let use_annotation = self.rng.gen_bool(0.30);
        if use_annotation {
            let type_str = ty.to_vole_syntax(ctx.table);
            Some(format!("{} {}: {} = {}", decl, name, type_str, new_value))
        } else {
            Some(format!("{} {} = {}", decl, name, new_value))
        }
    }

    fn try_generate_widening_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find all widenable (source_name, source_type, target_type) candidates
        let mut candidates: Vec<(String, PrimitiveType, PrimitiveType)> = Vec::new();

        for (name, ty, _mutable) in &ctx.locals {
            if let TypeInfo::Primitive(narrow_type) = ty {
                // Find all types this can widen to
                let widen_targets = Self::widening_targets(*narrow_type);
                for wide_type in widen_targets {
                    candidates.push((name.clone(), *narrow_type, wide_type));
                }
            }
        }

        for param in ctx.params {
            if let TypeInfo::Primitive(narrow_type) = &param.param_type {
                let widen_targets = Self::widening_targets(*narrow_type);
                for wide_type in widen_targets {
                    candidates.push((param.name.clone(), *narrow_type, wide_type));
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        // Pick a random candidate
        let idx = self.rng.gen_range(0..candidates.len());
        let (source_name, _narrow_type, wide_type) = &candidates[idx];

        let name = ctx.new_local_name();
        let wide_ty = TypeInfo::Primitive(*wide_type);

        // Add the variable with the wide type to scope
        ctx.add_local(name.clone(), wide_ty, false);

        // Format: let name: wide_type = narrow_var
        Some(format!(
            "let {}: {} = {}",
            name,
            wide_type.as_str(),
            source_name
        ))
    }

    /// Returns types that the given narrow type can widen to.
    fn widening_targets(narrow: PrimitiveType) -> Vec<PrimitiveType> {
        match narrow {
            PrimitiveType::I8 => vec![
                PrimitiveType::I16,
                PrimitiveType::I32,
                PrimitiveType::I64,
                PrimitiveType::I128,
            ],
            PrimitiveType::I16 => vec![PrimitiveType::I32, PrimitiveType::I64, PrimitiveType::I128],
            PrimitiveType::I32 => vec![PrimitiveType::I64, PrimitiveType::I128],
            PrimitiveType::I64 => vec![PrimitiveType::I128],
            PrimitiveType::U8 => vec![
                PrimitiveType::U16,
                PrimitiveType::U32,
                PrimitiveType::U64,
                PrimitiveType::I16,
                PrimitiveType::I32,
                PrimitiveType::I64,
                PrimitiveType::I128,
            ],
            PrimitiveType::U16 => vec![
                PrimitiveType::U32,
                PrimitiveType::U64,
                PrimitiveType::I32,
                PrimitiveType::I64,
                PrimitiveType::I128,
            ],
            PrimitiveType::U32 => vec![PrimitiveType::U64, PrimitiveType::I64, PrimitiveType::I128],
            PrimitiveType::U64 => vec![PrimitiveType::I128],
            PrimitiveType::F32 => vec![PrimitiveType::F64],
            _ => vec![],
        }
    }

    /// Generate a let statement binding a lambda expression.
    fn generate_lambda_let(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();

        // Pick 0-2 random primitive param types
        let param_count = self.rng.gen_range(0..=2);
        let param_types: Vec<TypeInfo> = (0..param_count)
            .map(|_| self.random_primitive_type())
            .collect();

        // Pick a random return type (any primitive now that vol-pz4y is fixed)
        let return_type = self.random_lambda_return_type();

        let expr_ctx = ctx.to_expr_context();
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let depth = self.config.expr_config.max_depth.saturating_sub(1);
        let value = expr_gen.generate_lambda(&param_types, &return_type, &expr_ctx, depth);

        // Lambda variables are not tracked for reuse since their function
        // type doesn't match primitive type expectations in the generator.

        format!("let {} = {}", name, value)
    }

    /// Generate an if statement.
    ///
    /// May generate else-if chains based on `config.else_if_probability`.
    /// When an else-if chain is generated, it produces:
    /// ```vole
    /// if cond1 { ... } else if cond2 { ... } else if cond3 { ... } else { ... }
    /// ```
    fn generate_if_statement(&mut self, ctx: &mut StmtContext, depth: usize) -> String {
        let locals_before = ctx.locals.len();

        // Generate the initial condition
        let cond = self.generate_bool_condition(ctx);

        // Generate then branch
        let then_stmts = self.generate_block(ctx, depth + 1);
        ctx.locals.truncate(locals_before);
        let then_block = self.format_block(&then_stmts);

        // Decide whether to generate else-if chains
        let use_else_if = self.rng.gen_bool(self.config.else_if_probability);

        let else_part = if use_else_if {
            // Generate 1-3 else-if arms
            let arm_count = self.rng.gen_range(1..=3);
            let mut else_if_parts = Vec::new();

            for _ in 0..arm_count {
                let else_if_cond = self.generate_bool_condition(ctx);
                let else_if_stmts = self.generate_block(ctx, depth + 1);
                ctx.locals.truncate(locals_before);
                let else_if_block = self.format_block(&else_if_stmts);
                let else_if_part = format!(" else if {} {}", else_if_cond, else_if_block);
                else_if_parts.push(else_if_part);
            }

            // Always end with a plain else block for safety
            let else_stmts = self.generate_block(ctx, depth + 1);
            ctx.locals.truncate(locals_before);
            let else_block = self.format_block(&else_stmts);

            format!("{} else {}", else_if_parts.join(""), else_block)
        } else if self.rng.gen_bool(0.5) {
            // 50% chance of simple else branch (no else-if)
            let else_stmts = self.generate_block(ctx, depth + 1);
            ctx.locals.truncate(locals_before);
            let else_block = self.format_block(&else_stmts);
            format!(" else {}", else_block)
        } else {
            String::new()
        };

        format!("if {} {}{}", cond, then_block, else_part)
    }

    /// Generate a boolean condition for if/else-if statements.
    ///
    /// Has a 30% chance to use an `is` expression if union-typed variables exist.
    fn generate_bool_condition(&mut self, ctx: &mut StmtContext) -> String {
        let expr_ctx = ctx.to_expr_context();
        let try_is = self.rng.gen_bool(0.3);
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        if try_is {
            expr_gen.generate_is_expr(&expr_ctx).unwrap_or_else(|| {
                expr_gen.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx, 0)
            })
        } else {
            expr_gen.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx, 0)
        }
    }

    /// Generate a while statement.
    ///
    /// Emits a guard variable before the loop that increments unconditionally
    /// at the top of the loop body (before any generated statements). This
    /// guarantees termination even when `continue` skips the manual counter
    /// increment at the end of the body.
    fn generate_while_statement(&mut self, ctx: &mut StmtContext, depth: usize) -> String {
        // Generate a simple bounded condition to prevent infinite loops
        // We'll use a pattern like: counter < limit
        let counter_name = ctx.new_local_name();
        let guard_name = ctx.new_local_name();
        let limit = self.rng.gen_range(1..=5);
        let guard_limit = limit * 10;

        // Pre-statement to initialize counter (this stays in outer scope)
        ctx.add_local(
            counter_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );
        // Guard variable also lives in outer scope
        ctx.add_local(
            guard_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );

        // Protect both counter and guard from compound assignments.
        // These variables control loop termination and must not be modified
        // by generated statements inside the loop body.
        ctx.protected_vars.push(counter_name.clone());
        ctx.protected_vars.push(guard_name.clone());

        let was_in_loop = ctx.in_loop;
        let was_in_while_loop = ctx.in_while_loop;
        ctx.in_loop = true;
        ctx.in_while_loop = true;

        // Generate body (save and restore locals for scoping)
        let locals_before = ctx.locals.len();
        let user_stmts = self.generate_block(ctx, depth + 1);
        ctx.locals.truncate(locals_before);
        // Note: We intentionally do NOT remove counter and guard from protected_vars here.
        // They remain protected for any subsequent statements in the outer scope, since
        // they're still in scope (in ctx.locals) and must not be modified by compound
        // assignments in sibling statements or nested loops.

        // Build the full loop body: guard increment + break check, then
        // user statements, then counter increment at the end.
        let mut body_stmts = Vec::with_capacity(user_stmts.len() + 3);
        body_stmts.push(format!("{guard_name} = {guard_name} + 1"));
        body_stmts.push(format!("if {guard_name} > {guard_limit} {{ break }}"));
        body_stmts.extend(user_stmts);
        body_stmts.push(format!("{counter_name} = {counter_name} + 1"));

        ctx.in_loop = was_in_loop;
        ctx.in_while_loop = was_in_while_loop;

        let body_block = self.format_block(&body_stmts);

        format!(
            "let mut {} = 0\n{}let mut {} = 0\n{}while {} < {} {}",
            counter_name,
            self.indent_str(),
            guard_name,
            self.indent_str(),
            counter_name,
            limit,
            body_block
        )
    }

    /// Generate a for statement.
    ///
    /// Randomly chooses between:
    /// - Iterator chain iteration: `for x in arr.iter().filter/map/sorted/take(...) { ... }`
    ///   (~20% when primitive array variables are in scope)
    /// - Array iteration: `for elem in arr { ... }` (~40% when array variables are in scope)
    /// - Numeric range iteration: `for x in start..end { ... }` (fallback)
    ///
    /// For numeric ranges, randomly picks exclusive (`start..end`) or inclusive
    /// (`start..=end`) syntax with ~50/50 probability, optionally using a local
    /// i64 variable as the upper bound.
    fn generate_for_statement(&mut self, ctx: &mut StmtContext, depth: usize) -> String {
        let expr_ctx = ctx.to_expr_context();
        let array_vars = expr_ctx.array_vars();

        // Filter to arrays with primitive element types suitable for closures
        let prim_array_vars: Vec<(String, PrimitiveType)> = array_vars
            .iter()
            .filter_map(|(name, elem_ty)| {
                if let TypeInfo::Primitive(prim) = elem_ty {
                    match prim {
                        PrimitiveType::I64
                        | PrimitiveType::F64
                        | PrimitiveType::Bool
                        | PrimitiveType::String => Some((name.clone(), *prim)),
                        _ => None,
                    }
                } else {
                    None
                }
            })
            .collect();

        // ~8% chance for enumerate for-in loop (needs i64 arrays for pair arithmetic)
        if !prim_array_vars.is_empty() && self.rng.gen_bool(0.08) {
            let i64_arrays: Vec<_> = prim_array_vars
                .iter()
                .filter(|(_, p)| matches!(p, PrimitiveType::I64))
                .cloned()
                .collect();
            if !i64_arrays.is_empty() {
                return self.generate_for_in_enumerate(ctx, depth, &i64_arrays);
            }
        }

        // ~6% chance for zip for-in loop (needs 2+ i64 arrays)
        if prim_array_vars.len() >= 2 && self.rng.gen_bool(0.06) {
            let i64_arrays: Vec<_> = prim_array_vars
                .iter()
                .filter(|(_, p)| matches!(p, PrimitiveType::I64))
                .cloned()
                .collect();
            if i64_arrays.len() >= 2 {
                return self.generate_for_in_zip(ctx, depth, &i64_arrays);
            }
        }

        // Check if we can iterate over an iterator chain (~20% when primitive arrays available)
        if !prim_array_vars.is_empty() && self.rng.gen_bool(0.2) {
            return self.generate_for_in_iterator(ctx, depth, &prim_array_vars);
        }

        // Check if we can iterate over an array variable (~40% when available)
        if !array_vars.is_empty() && self.rng.gen_bool(0.4) {
            return self.generate_for_in_array(ctx, depth, &array_vars);
        }

        self.generate_for_in_range(ctx, depth)
    }

    /// Generate a for-in-range statement: `for x in start..end { ... }`.
    fn generate_for_in_range(&mut self, ctx: &mut StmtContext, depth: usize) -> String {
        let iter_name = ctx.new_local_name();

        // Generate range with randomly chosen syntax
        let use_inclusive = self.rng.gen_bool(0.5);
        let range = self.generate_range(ctx, use_inclusive);

        let was_in_loop = ctx.in_loop;
        let was_in_while_loop = ctx.in_while_loop;
        ctx.in_loop = true;
        ctx.in_while_loop = false;

        // Save locals before block (loop variable is scoped to body)
        let locals_before = ctx.locals.len();

        // Add loop variable to context (scoped to body)
        ctx.add_local(
            iter_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        let body_stmts = self.generate_block(ctx, depth + 1);

        // Restore locals (removes loop variable and body locals)
        ctx.locals.truncate(locals_before);
        ctx.in_loop = was_in_loop;
        ctx.in_while_loop = was_in_while_loop;

        let body_block = self.format_block(&body_stmts);
        format!("for {} in {} {}", iter_name, range, body_block)
    }

    /// Generate a for-in-array statement: `for elem in arr { ... }`.
    ///
    /// The loop variable gets the array's element type. Picks a random
    /// array-typed variable from the provided candidates.
    fn generate_for_in_array(
        &mut self,
        ctx: &mut StmtContext,
        depth: usize,
        array_vars: &[(String, TypeInfo)],
    ) -> String {
        let iter_name = ctx.new_local_name();

        let idx = self.rng.gen_range(0..array_vars.len());
        let (arr_name, elem_type) = &array_vars[idx];

        let was_in_loop = ctx.in_loop;
        let was_in_while_loop = ctx.in_while_loop;
        ctx.in_loop = true;
        ctx.in_while_loop = false;

        let locals_before = ctx.locals.len();

        // Add loop variable with the array's element type
        ctx.add_local(iter_name.clone(), elem_type.clone(), false);

        // Protect the iterated array from reassignment inside the loop body.
        // Shrinking the array while iterating causes out-of-bounds panics.
        ctx.protected_vars.push(arr_name.clone());

        let body_stmts = self.generate_block(ctx, depth + 1);

        ctx.protected_vars.pop();
        ctx.locals.truncate(locals_before);
        ctx.in_loop = was_in_loop;
        ctx.in_while_loop = was_in_while_loop;

        let body_block = self.format_block(&body_stmts);
        format!("for {} in {} {}", iter_name, arr_name, body_block)
    }

    /// Generate a for-in-iterator statement: `for x in arr.iter().chain(...) { ... }`.
    ///
    /// Iterates over an iterator chain instead of a plain array. The chain is one of:
    /// - `.filter((x) => PRED)` — element type stays the same
    /// - `.map((x) => EXPR)` — element type preserved (same-type expressions only)
    /// - `.sorted()` — for numeric element types only (i64, f64)
    /// - `.take(N)` — take first N elements
    ///
    /// Only applies to arrays with primitive element types (i64, f64, bool, string).
    fn generate_for_in_iterator(
        &mut self,
        ctx: &mut StmtContext,
        depth: usize,
        prim_array_vars: &[(String, PrimitiveType)],
    ) -> String {
        let iter_name = ctx.new_local_name();

        let idx = self.rng.gen_range(0..prim_array_vars.len());
        let (arr_name, elem_prim) = &prim_array_vars[idx];
        let elem_prim = *elem_prim;
        let arr_name = arr_name.clone();

        let is_numeric = matches!(elem_prim, PrimitiveType::I64 | PrimitiveType::F64);

        // Pick a random iterator chain operation.
        // Weights: filter ~30%, map ~30%, sorted ~20% (numeric only), take ~20%
        // For non-numeric types, sorted's weight is redistributed to filter/map/take.
        let chain_expr = if is_numeric {
            match self.rng.gen_range(0..10) {
                0..3 => {
                    // .filter((x) => PRED)
                    let pred = self.generate_filter_closure_body(elem_prim);
                    format!(".filter((x) => {})", pred)
                }
                3..6 => {
                    // .map((x) => EXPR) — same type
                    let body = self.generate_map_closure_body(elem_prim);
                    format!(".map((x) => {})", body)
                }
                6..8 => {
                    // .sorted() — numeric only
                    ".sorted()".to_string()
                }
                _ => {
                    // .take(N)
                    let n = self.rng.gen_range(1..=3);
                    format!(".take({})", n)
                }
            }
        } else {
            match self.rng.gen_range(0..10) {
                0..4 => {
                    // .filter((x) => PRED)
                    let pred = self.generate_filter_closure_body(elem_prim);
                    format!(".filter((x) => {})", pred)
                }
                4..7 => {
                    // .map((x) => EXPR) — same type
                    let body = self.generate_map_closure_body(elem_prim);
                    format!(".map((x) => {})", body)
                }
                _ => {
                    // .take(N)
                    let n = self.rng.gen_range(1..=3);
                    format!(".take({})", n)
                }
            }
        };

        // ~25% chance to append a second chain operation for multi-chain iterators
        // e.g. .filter(...).sorted(), .map(...).filter(...), .sorted().take(N)
        let chain_expr = if self.rng.gen_bool(0.25) {
            let second = if is_numeric {
                match self.rng.gen_range(0..4) {
                    0 => {
                        let pred = self.generate_filter_closure_body(elem_prim);
                        format!(".filter((x) => {})", pred)
                    }
                    1 => ".sorted()".to_string(),
                    2 => ".reverse()".to_string(),
                    _ => {
                        let n = self.rng.gen_range(1..=3);
                        format!(".take({})", n)
                    }
                }
            } else {
                match self.rng.gen_range(0..3) {
                    0 => {
                        let pred = self.generate_filter_closure_body(elem_prim);
                        format!(".filter((x) => {})", pred)
                    }
                    1 => ".reverse()".to_string(),
                    _ => {
                        let n = self.rng.gen_range(1..=3);
                        format!(".take({})", n)
                    }
                }
            };
            format!("{}{}", chain_expr, second)
        } else {
            chain_expr
        };

        // The element type is always preserved (filter/sorted/take don't change it,
        // and we only use same-type map expressions).
        let elem_type = TypeInfo::Primitive(elem_prim);

        let was_in_loop = ctx.in_loop;
        let was_in_while_loop = ctx.in_while_loop;
        ctx.in_loop = true;
        ctx.in_while_loop = false;

        let locals_before = ctx.locals.len();

        // Add loop variable with the element type
        ctx.add_local(iter_name.clone(), elem_type, false);

        // Protect the iterated array from reassignment inside the loop body
        ctx.protected_vars.push(arr_name.clone());

        let body_stmts = self.generate_block(ctx, depth + 1);

        ctx.protected_vars.pop();
        ctx.locals.truncate(locals_before);
        ctx.in_loop = was_in_loop;
        ctx.in_while_loop = was_in_while_loop;

        let body_block = self.format_block(&body_stmts);
        format!(
            "for {} in {}.iter(){} {}",
            iter_name, arr_name, chain_expr, body_block
        )
    }

    /// Generate a for-in-enumerate loop: `for pair in arr.iter().enumerate() { ... }`.
    ///
    /// The loop body uses `pair[0]` (index, i64) and `pair[1]` (element value, i64).
    /// Generates an accumulator pattern: `let mut acc = 0` before, then `acc = acc + pair[0] + pair[1]` inside.
    fn generate_for_in_enumerate(
        &mut self,
        ctx: &mut StmtContext,
        _depth: usize,
        i64_arrays: &[(String, PrimitiveType)],
    ) -> String {
        let pair_name = ctx.new_local_name();
        let acc_name = ctx.new_local_name();

        let idx = self.rng.gen_range(0..i64_arrays.len());
        let (arr_name, _) = &i64_arrays[idx];
        let arr_name = arr_name.clone();

        // Optional prefix chain: ~20% chance to add .filter() or .take() before enumerate
        let prefix = if self.rng.gen_bool(0.20) {
            match self.rng.gen_range(0..2) {
                0 => {
                    let n = self.rng.gen_range(1..=3);
                    format!(".take({})", n)
                }
                _ => {
                    let pred = self.generate_filter_closure_body(PrimitiveType::I64);
                    format!(".filter((x) => {})", pred)
                }
            }
        } else {
            String::new()
        };

        // Pick accumulation body: add indices, add values, or multiply-accumulate
        let body_expr = match self.rng.gen_range(0..3) {
            0 => format!(
                "{} = {} + {}[0] + {}[1]",
                acc_name, acc_name, pair_name, pair_name
            ),
            1 => format!("{} = {} + {}[0]", acc_name, acc_name, pair_name),
            _ => format!("{} = {} + {}[1]", acc_name, acc_name, pair_name),
        };

        ctx.protected_vars.push(arr_name.clone());
        // acc is mutable i64 declared before the loop
        ctx.add_local(acc_name.clone(), TypeInfo::Primitive(PrimitiveType::I64), true);

        let indent = self.indent_str();
        let inner_indent = format!("{}    ", indent);
        format!(
            "let mut {} = 0\n{}for {} in {}.iter(){}.enumerate() {{\n{}{}\n{}}}",
            acc_name,
            indent,
            pair_name,
            arr_name,
            prefix,
            inner_indent,
            body_expr,
            indent
        )
    }

    /// Generate a for-in-zip loop: `for pair in a.iter().zip(b.iter()) { ... }`.
    ///
    /// Combines two i64 arrays. The loop body uses `pair[0]` and `pair[1]`,
    /// each being i64 elements from the respective arrays.
    fn generate_for_in_zip(
        &mut self,
        ctx: &mut StmtContext,
        _depth: usize,
        i64_arrays: &[(String, PrimitiveType)],
    ) -> String {
        let pair_name = ctx.new_local_name();
        let acc_name = ctx.new_local_name();

        // Pick two distinct arrays
        let idx_a = self.rng.gen_range(0..i64_arrays.len());
        let mut idx_b = self.rng.gen_range(0..i64_arrays.len());
        if idx_b == idx_a {
            idx_b = (idx_a + 1) % i64_arrays.len();
        }
        let (arr_a, _) = &i64_arrays[idx_a];
        let (arr_b, _) = &i64_arrays[idx_b];
        let arr_a = arr_a.clone();
        let arr_b = arr_b.clone();

        // Pick accumulation body
        let body_expr = match self.rng.gen_range(0..3) {
            0 => format!(
                "{} = {} + {}[0] + {}[1]",
                acc_name, acc_name, pair_name, pair_name
            ),
            1 => format!(
                "{} = {} + ({}[0] * {}[1])",
                acc_name, acc_name, pair_name, pair_name
            ),
            _ => format!(
                "{} = {} + {}[0] - {}[1]",
                acc_name, acc_name, pair_name, pair_name
            ),
        };

        ctx.protected_vars.push(arr_a.clone());
        ctx.protected_vars.push(arr_b.clone());
        ctx.add_local(acc_name.clone(), TypeInfo::Primitive(PrimitiveType::I64), true);

        let indent = self.indent_str();
        let inner_indent = format!("{}    ", indent);
        format!(
            "let mut {} = 0\n{}for {} in {}.iter().zip({}.iter()) {{\n{}{}\n{}}}",
            acc_name,
            indent,
            pair_name,
            arr_a,
            arr_b,
            inner_indent,
            body_expr,
            indent,
        )
    }

    /// Generate a range expression for a for loop.
    ///
    /// Produces either exclusive (`start..end`) or inclusive (`start..=end`)
    /// syntax. The bounds may reference existing local i64 variables or
    /// simple arithmetic expressions (~30% chance when variables are available).
    fn generate_range(&mut self, ctx: &StmtContext, inclusive: bool) -> String {
        // ~10% chance to generate an edge-case range (empty or single-iteration)
        // to stress loop codegen boundary conditions.
        if self.rng.gen_bool(0.10) {
            let start = self.rng.gen_range(0..3);
            return match self.rng.gen_range(0..3) {
                0 => format!("{}..{}", start, start),         // empty exclusive range
                1 => format!("{}..={}", start, start),        // single-iteration inclusive
                _ => format!("{}..{}", start, start + 1),     // single-iteration exclusive
            };
        }

        // Collect i64 locals that could serve as variable bounds.
        // Only use protected_vars (while-loop counters/guards) which are
        // guaranteed to hold small values. Arbitrary i64 locals can hold
        // huge computed values that would cause for loops to iterate
        // billions of times.
        let i64_locals: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(name, ty, _)| {
                matches!(ty, TypeInfo::Primitive(PrimitiveType::I64))
                    && ctx.protected_vars.contains(name)
            })
            .map(|(name, _, _)| name.clone())
            .collect();

        // Generate start bound: ~20% chance to use a variable/expression
        // when protected i64 locals are available, otherwise use a literal.
        let start_str = if !i64_locals.is_empty() && self.rng.gen_bool(0.2) {
            let idx = self.rng.gen_range(0..i64_locals.len());
            let var = &i64_locals[idx];
            self.generate_range_bound_expr(var)
        } else {
            let start = self.rng.gen_range(0..3);
            format!("{}", start)
        };

        // Generate end bound: ~30% chance to use a variable/expression
        // when protected i64 locals are available, otherwise use a literal.
        if !i64_locals.is_empty() && self.rng.gen_bool(0.3) {
            let idx = self.rng.gen_range(0..i64_locals.len());
            let var = &i64_locals[idx];
            let end_str = self.generate_range_bound_expr(var);
            if inclusive {
                format!("{}..={}", start_str, end_str)
            } else {
                format!("{}..{}", start_str, end_str)
            }
        } else if inclusive {
            // Inclusive literal bound: `start..=end` iterates start through end.
            let end = self.rng.gen_range(0..5);
            format!("{}..={}", start_str, end.max(0))
        } else {
            // Exclusive literal bound: `start..end` iterates start through end-1.
            let end = self.rng.gen_range(1..6);
            format!("{}..{}", start_str, end)
        }
    }

    /// Generate a range bound expression from a protected i64 variable.
    ///
    /// Returns either the variable directly or a simple arithmetic expression
    /// involving the variable (e.g., `var + 1`, `var * 2`). All expressions
    /// are kept small-valued since the input variable is a protected (small)
    /// i64 local.
    fn generate_range_bound_expr(&mut self, var: &str) -> String {
        match self.rng.gen_range(0..5) {
            // Plain variable reference
            0 | 1 => var.to_string(),
            // Addition: var + small_literal
            2 => {
                let offset = self.rng.gen_range(1..=3);
                format!("({} + {})", var, offset)
            }
            // Subtraction: var - small_literal (can go negative, but that
            // just means an empty range which is fine)
            3 => {
                let offset = self.rng.gen_range(1..=2);
                format!("({} - {})", var, offset)
            }
            // Multiplication: var * small_literal
            _ => {
                let factor = self.rng.gen_range(1..=2);
                format!("({} * {})", var, factor)
            }
        }
    }

    /// Generate nested for-loops where the inner loop uses `break` or `continue`.
    ///
    /// Produces patterns like:
    /// ```vole
    /// for i in 0..3 {
    ///     for j in 0..5 {
    ///         if j >= 2 {
    ///             break
    ///         }
    ///         let localN = ...
    ///     }
    /// }
    /// ```
    ///
    /// This exercises complex control flow with multiple loop scopes, ensuring
    /// that break/continue target the correct (inner) loop.
    fn generate_nested_for_loop(&mut self, ctx: &mut StmtContext, depth: usize) -> String {
        let outer_iter = ctx.new_local_name();
        let inner_iter = ctx.new_local_name();

        // Generate small ranges for both loops
        let outer_end = self.rng.gen_range(2..=4);
        let inner_end = self.rng.gen_range(3..=6);

        let outer_inclusive = self.rng.gen_bool(0.3);
        let inner_inclusive = self.rng.gen_bool(0.3);

        let outer_range = if outer_inclusive {
            format!("0..={}", outer_end)
        } else {
            format!("0..{}", outer_end)
        };
        let inner_range = if inner_inclusive {
            format!("0..={}", inner_end)
        } else {
            format!("0..{}", inner_end)
        };

        // Set up the outer loop context
        let was_in_loop = ctx.in_loop;
        let was_in_while_loop = ctx.in_while_loop;
        ctx.in_loop = true;
        ctx.in_while_loop = false;

        let outer_locals_before = ctx.locals.len();
        ctx.add_local(
            outer_iter.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        // Build the inner loop body with break or continue
        let inner_locals_before = ctx.locals.len();
        ctx.add_local(
            inner_iter.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        // Generate the break/continue statement for the inner loop
        let keyword = if self.rng.gen_bool(0.5) {
            "break"
        } else {
            "continue"
        };

        // Build inner body: a conditional break/continue, then optionally a statement
        let mut inner_stmts = Vec::new();

        // Generate condition: use the inner iterator variable for the condition
        let expr_ctx = ctx.to_expr_context();
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let cond = expr_gen.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx, 0);

        let inner_indent = "    ".repeat(self.indent + 2);
        let if_close_indent = "    ".repeat(self.indent + 1);
        inner_stmts.push(format!(
            "if {} {{\n{}{}\n{}}}",
            cond, inner_indent, keyword, if_close_indent
        ));

        // Add 1-2 more statements inside the inner loop body
        let extra_count = self.rng.gen_range(1..=2);
        for _ in 0..extra_count {
            inner_stmts.push(self.generate_statement(ctx, depth + 2));
        }

        // Restore inner loop variable
        ctx.locals.truncate(inner_locals_before);

        // Format the inner loop
        let inner_body = self.format_block(&inner_stmts);
        let inner_loop = format!("for {} in {} {}", inner_iter, inner_range, inner_body);

        // Optionally add a statement before or after the inner loop in the outer body
        let mut outer_stmts = Vec::new();
        if self.rng.gen_bool(0.3) {
            outer_stmts.push(self.generate_statement(ctx, depth + 1));
        }
        outer_stmts.push(inner_loop);
        if self.rng.gen_bool(0.3) {
            outer_stmts.push(self.generate_statement(ctx, depth + 1));
        }

        // Restore outer loop context
        ctx.locals.truncate(outer_locals_before);
        ctx.in_loop = was_in_loop;
        ctx.in_while_loop = was_in_while_loop;

        let outer_body = self.format_block(&outer_stmts);
        format!("for {} in {} {}", outer_iter, outer_range, outer_body)
    }

    /// Generate a break, continue, or early return statement wrapped in a conditional.
    ///
    /// Wraps in `if <condition> { break }` (or `continue` / `return expr`) to
    /// avoid always exiting on the first iteration. Only called when
    /// `ctx.in_loop` is true.
    ///
    /// When the enclosing function has a non-void return type, there is a 20%
    /// chance of generating `return <expr>` instead of break/continue.  This
    /// exercises the compiler's handling of return statements inside nested
    /// control flow (for + if).
    ///
    /// Both `break` and `continue` are allowed in while loops because a
    /// guard variable at the top of the loop body guarantees termination
    /// even when `continue` skips the manual counter increment.
    fn generate_break_continue(&mut self, ctx: &mut StmtContext) -> String {
        let expr_ctx = ctx.to_expr_context();

        // 20% chance of early return from inside a loop when the function
        // has a non-void return type.
        let return_type = ctx.return_type.clone();
        if let Some(ref ret_ty) = return_type {
            if !matches!(ret_ty, TypeInfo::Void) && self.rng.gen_bool(0.20) {
                let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                let cond =
                    expr_gen.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx, 0);

                let return_expr = {
                    let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                    expr_gen.generate(ret_ty, &expr_ctx, 0)
                };

                let indent = "    ".repeat(self.indent + 1);
                return format!(
                    "if {} {{\n{}return {}\n{}}}",
                    cond,
                    indent,
                    return_expr,
                    "    ".repeat(self.indent)
                );
            }
        }

        let keyword = if self.rng.gen_bool(0.5) {
            "break"
        } else {
            "continue"
        };

        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let cond = expr_gen.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx, 0);

        let indent = "    ".repeat(self.indent + 1);
        format!(
            "if {} {{\n{}{}\n{}}}",
            cond,
            indent,
            keyword,
            "    ".repeat(self.indent)
        )
    }

    /// Check if there are any mutable numeric locals in scope that are not protected.
    fn has_mutable_numeric_locals(&self, ctx: &StmtContext) -> bool {
        ctx.locals.iter().any(|(name, ty, is_mut)| {
            *is_mut
                && !ctx.protected_vars.contains(name)
                && matches!(
                    ty,
                    TypeInfo::Primitive(PrimitiveType::I8)
                        | TypeInfo::Primitive(PrimitiveType::I16)
                        | TypeInfo::Primitive(PrimitiveType::I32)
                        | TypeInfo::Primitive(PrimitiveType::I64)
                        | TypeInfo::Primitive(PrimitiveType::I128)
                        | TypeInfo::Primitive(PrimitiveType::U8)
                        | TypeInfo::Primitive(PrimitiveType::U16)
                        | TypeInfo::Primitive(PrimitiveType::U32)
                        | TypeInfo::Primitive(PrimitiveType::U64)
                        | TypeInfo::Primitive(PrimitiveType::F32)
                        | TypeInfo::Primitive(PrimitiveType::F64)
                )
        })
    }

    /// Generate a compound assignment statement (+=, -=, *=).
    ///
    /// Picks a random mutable numeric local, a random compound operator,
    /// and generates a simple numeric literal RHS of the same type.
    /// Avoids /= and %= to prevent division by zero.
    /// Excludes protected variables (e.g., while-loop counters and guards).
    fn generate_compound_assignment(&mut self, ctx: &mut StmtContext) -> String {
        // Collect mutable numeric locals, excluding protected variables
        let candidates: Vec<(String, PrimitiveType)> = ctx
            .locals
            .iter()
            .filter_map(|(name, ty, is_mut)| {
                if !is_mut || ctx.protected_vars.contains(name) {
                    return None;
                }
                match ty {
                    TypeInfo::Primitive(p @ PrimitiveType::I8)
                    | TypeInfo::Primitive(p @ PrimitiveType::I16)
                    | TypeInfo::Primitive(p @ PrimitiveType::I32)
                    | TypeInfo::Primitive(p @ PrimitiveType::I64)
                    | TypeInfo::Primitive(p @ PrimitiveType::I128)
                    | TypeInfo::Primitive(p @ PrimitiveType::U8)
                    | TypeInfo::Primitive(p @ PrimitiveType::U16)
                    | TypeInfo::Primitive(p @ PrimitiveType::U32)
                    | TypeInfo::Primitive(p @ PrimitiveType::U64)
                    | TypeInfo::Primitive(p @ PrimitiveType::F32)
                    | TypeInfo::Primitive(p @ PrimitiveType::F64) => Some((name.clone(), *p)),
                    _ => None,
                }
            })
            .collect();

        // Pick a random candidate (caller guarantees non-empty via has_mutable_numeric_locals)
        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, prim) = &candidates[idx];

        // Pick a random compound operator
        let op = match self.rng.gen_range(0..4) {
            0 => "+=",
            1 => "-=",
            2 => "*=",
            _ => "%=",
        };

        // Generate a simple numeric literal of the same type.
        // For %= use a non-zero literal to avoid division by zero.
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let rhs = if op == "%=" {
            expr_gen.nonzero_literal_for_primitive(*prim)
        } else {
            expr_gen.literal_for_primitive(*prim)
        };

        format!("{} {} {}", var_name, op, rhs)
    }

    /// Check if there are any mutable locals (of any type) that can be reassigned.
    ///
    /// Excludes protected variables (e.g., while-loop counters and guards).
    fn has_mutable_locals(&self, ctx: &StmtContext) -> bool {
        ctx.locals.iter().any(|(name, ty, is_mut)| {
            *is_mut
                && !ctx.protected_vars.contains(name)
                && !matches!(ty, TypeInfo::Void | TypeInfo::TypeParam(_))
        })
    }

    /// Generate a direct variable reassignment statement (x = new_value).
    ///
    /// Picks a random mutable local (excluding protected variables), then
    /// generates a type-compatible RHS expression via `ExprGenerator::generate`.
    fn generate_reassignment(&mut self, ctx: &mut StmtContext) -> String {
        // Collect mutable locals eligible for reassignment
        let candidates: Vec<(String, TypeInfo)> = ctx
            .locals
            .iter()
            .filter(|(name, ty, is_mut)| {
                *is_mut
                    && !ctx.protected_vars.contains(name)
                    && !matches!(ty, TypeInfo::Void | TypeInfo::TypeParam(_))
            })
            .map(|(name, ty, _)| (name.clone(), ty.clone()))
            .collect();

        // Pick a random candidate (caller guarantees non-empty via has_mutable_locals)
        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, var_type) = &candidates[idx];

        // Generate a type-compatible RHS expression
        let expr_ctx = ctx.to_expr_context();
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let rhs = expr_gen.generate(var_type, &expr_ctx, 0);

        format!("{} = {}", var_name, rhs)
    }

    /// Get mutable dynamic arrays in scope that are not protected.
    ///
    /// Returns `(name, element_type)` pairs for locals of type `[T]`
    /// that are mutable and not in `protected_vars`.
    fn mutable_dynamic_arrays(ctx: &StmtContext) -> Vec<(String, TypeInfo)> {
        ctx.locals
            .iter()
            .filter_map(|(name, ty, is_mut)| {
                if *is_mut && !ctx.protected_vars.contains(name) {
                    if let TypeInfo::Array(elem) = ty {
                        return Some((name.clone(), *elem.clone()));
                    }
                }
                None
            })
            .collect()
    }

    /// Generate an array index assignment: `arr[i] = expr`.
    ///
    /// Picks a random mutable dynamic array in scope, generates a bounds-safe
    /// index (0 or 1, since arrays have 2-4 elements), and generates a
    /// type-compatible RHS expression matching the element type.
    fn generate_array_index_assignment(&mut self, ctx: &mut StmtContext) -> String {
        let candidates = Self::mutable_dynamic_arrays(ctx);
        // Caller guarantees non-empty via the check in generate_statement
        let idx = self.rng.gen_range(0..candidates.len());
        let (arr_name, elem_type) = &candidates[idx];

        // Use index 0 — arrays may be single-element after the 15% chance change.
        let index = 0;

        let expr_ctx = ctx.to_expr_context();
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let value = expr_gen.generate_simple(&elem_type, &expr_ctx);

        format!("{}[{}] = {}", arr_name, index, value)
    }

    /// Generate an array push statement: `arr.push(value)`.
    ///
    /// Picks a random mutable dynamic array in scope and generates a
    /// type-compatible value expression matching the element type.
    fn generate_array_push(&mut self, ctx: &mut StmtContext) -> String {
        let candidates = Self::mutable_dynamic_arrays(ctx);
        // Caller guarantees non-empty via the check in generate_statement
        let idx = self.rng.gen_range(0..candidates.len());
        let (arr_name, elem_type) = &candidates[idx];

        let expr_ctx = ctx.to_expr_context();
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let value = expr_gen.generate_simple(&elem_type, &expr_ctx);

        format!("{}.push({})", arr_name, value)
    }

    /// Get mutable dynamic arrays with numeric element types.
    ///
    /// Returns `(name, element_type)` pairs for locals of type `[T]` where T is
    /// a numeric primitive (i8..i128, u8..u64, f32, f64), that are mutable and
    /// not in `protected_vars`. Used for compound assignment on array elements.
    fn mutable_numeric_arrays(ctx: &StmtContext) -> Vec<(String, PrimitiveType)> {
        ctx.locals
            .iter()
            .filter_map(|(name, ty, is_mut)| {
                if *is_mut && !ctx.protected_vars.contains(name) {
                    if let TypeInfo::Array(elem) = ty {
                        if let TypeInfo::Primitive(
                            p @ (PrimitiveType::I8
                            | PrimitiveType::I16
                            | PrimitiveType::I32
                            | PrimitiveType::I64
                            | PrimitiveType::I128
                            | PrimitiveType::U8
                            | PrimitiveType::U16
                            | PrimitiveType::U32
                            | PrimitiveType::U64
                            | PrimitiveType::F32
                            | PrimitiveType::F64),
                        ) = **elem
                        {
                            return Some((name.clone(), p));
                        }
                    }
                }
                None
            })
            .collect()
    }

    /// Generate an array index compound assignment: `arr[i] += expr`.
    ///
    /// Picks a random mutable dynamic array with numeric element type in scope,
    /// generates a bounds-safe index (0 or 1), a compound operator (+=, -=, *=),
    /// and a type-compatible RHS expression.
    fn generate_array_index_compound_assignment(&mut self, ctx: &mut StmtContext) -> String {
        let candidates = Self::mutable_numeric_arrays(ctx);
        // Caller guarantees non-empty via the check in generate_statement
        let idx = self.rng.gen_range(0..candidates.len());
        let (arr_name, elem_type) = &candidates[idx];

        // Use index 0 — arrays may be single-element.
        let index = 0;

        // Pick a random compound operator (avoid /= to prevent division by zero;
        // %= uses a non-zero literal to stay safe)
        let op = match self.rng.gen_range(0..4) {
            0 => "+=",
            1 => "-=",
            2 => "*=",
            _ => "%=",
        };

        let expr_ctx = ctx.to_expr_context();
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let value = if op == "%=" {
            expr_gen.nonzero_literal_for_primitive(*elem_type)
        } else {
            expr_gen.generate_simple(&TypeInfo::Primitive(*elem_type), &expr_ctx)
        };

        format!("{}[{}] {} {}", arr_name, index, op, value)
    }

    /// Try to generate an iterator map or filter let-binding on an array in scope.
    ///
    /// Finds an array-typed variable with a primitive element type and generates
    /// one of:
    /// ```vole
    /// let result = arr.iter().map((x) => x * 2).collect()
    /// let result = arr.iter().filter((x) => x > 0).collect()
    /// ```
    ///
    /// Returns `None` if no suitable array variable is in scope.
    fn try_generate_iter_map_filter_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Collect array-typed variables with element types safe for closure operations.
        // Restrict to i64, f64, bool, and string since these are well-tested with
        // iterator closures in the Vole test suite. Other numeric types may have
        // type inference issues with bare integer literals inside closures.
        let expr_ctx = ctx.to_expr_context();
        let array_vars = expr_ctx.array_vars();
        let prim_array_vars: Vec<(String, PrimitiveType)> = array_vars
            .into_iter()
            .filter_map(|(name, elem_ty)| {
                if let TypeInfo::Primitive(prim) = elem_ty {
                    match prim {
                        PrimitiveType::I64
                        | PrimitiveType::F64
                        | PrimitiveType::Bool
                        | PrimitiveType::String => Some((name, prim)),
                        _ => None,
                    }
                } else {
                    None
                }
            })
            .collect();

        if prim_array_vars.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..prim_array_vars.len());
        let (arr_name, elem_prim) = &prim_array_vars[idx];
        let elem_prim = *elem_prim;
        let arr_name = arr_name.clone();

        let name = ctx.new_local_name();

        // Optionally prepend .sorted(), .reverse(), .unique(), or .skip(N) (~25%).
        // .sorted() requires numeric elements (i64, f64); .unique() skips bool.
        let is_numeric_elem = matches!(elem_prim, PrimitiveType::I64 | PrimitiveType::F64);
        let prefix: String = if self.rng.gen_bool(0.25) {
            match self.rng.gen_range(0..4) {
                0 if is_numeric_elem => ".sorted()".to_string(),
                1 => ".reverse()".to_string(),
                2 if elem_prim != PrimitiveType::Bool => ".unique()".to_string(),
                3 => format!(".skip({})", self.rng.gen_range(0..=1)),
                _ => ".reverse()".to_string(),
            }
        } else {
            String::new()
        };

        // Build the iterator chain: .iter() followed by 1-2 operations, then a terminal.
        // 30% single .map(), 25% single .filter(), 20% chained .map().filter() or .filter().map(),
        // 15% .sorted() intermediate chains (numeric only, else fallback to .map()),
        // ~13% .enumerate() chains
        //
        // enumerate_terminal: when Some, the enumerate chain includes its own terminal
        // and bypasses the normal terminal selection below.
        let chain_choice = self.rng.gen_range(0..23);

        let (chain, enumerate_terminal) = if chain_choice < 6 {
            // Single .map()
            let map_body = self.generate_map_closure_body(elem_prim);
            (format!(".map((x) => {})", map_body), None)
        } else if chain_choice < 11 {
            // Single .filter()
            let filter_body = self.generate_filter_closure_body(elem_prim);
            (format!(".filter((x) => {})", filter_body), None)
        } else if chain_choice < 14 {
            // Chained .map().filter() — map uses 'x', filter uses 'y' to avoid shadowing
            let map_body = self.generate_map_closure_body(elem_prim);
            let filter_body = self.generate_filter_closure_body_param(elem_prim, "y");
            (
                format!(".map((x) => {}).filter((y) => {})", map_body, filter_body),
                None,
            )
        } else if chain_choice < 17 && is_numeric_elem {
            // .sorted() before .map() — numeric only
            let map_body = self.generate_map_closure_body(elem_prim);
            (format!(".sorted().map((x) => {})", map_body), None)
        } else if chain_choice < 20 && is_numeric_elem {
            // .filter() then .sorted() — numeric only
            let filter_body = self.generate_filter_closure_body(elem_prim);
            (format!(".filter((x) => {}).sorted()", filter_body), None)
        } else if chain_choice < 21 {
            // .enumerate().count() — always valid, any element type
            // enumerate wraps each element as [index, value] tuple;
            // .count() avoids type complexity by just returning i64.
            // Terminal is included in the chain; bypasses normal terminal selection.
            (
                ".enumerate().count()".to_string(),
                Some(("".to_string(), TypeInfo::Primitive(PrimitiveType::I64))),
            )
        } else if chain_choice < 23 && is_numeric_elem {
            // .enumerate().filter((e) => e[1] > 0).map((e) => e[1]) — numeric only
            // Filter by original value (e[1]), then map back to original type.
            // Normal terminal selection applies (element type is preserved).
            let pred = match elem_prim {
                PrimitiveType::I64 => "(e) => e[1] > 0_i64",
                PrimitiveType::F64 => "(e) => e[1] > 0.0_f64",
                _ => "(e) => true",
            };
            (
                format!(".enumerate().filter({}).map((e) => e[1])", pred),
                None,
            )
        } else {
            // Chained .filter().map() — filter uses 'x', map uses 'y'
            let filter_body = self.generate_filter_closure_body(elem_prim);
            let map_body = self.generate_map_closure_body_param(elem_prim, "y");
            (
                format!(".filter((x) => {}).map((y) => {})", filter_body, map_body),
                None,
            )
        };

        // If the enumerate chain already includes its terminal, use that directly.
        if let Some((terminal, result_type)) = enumerate_terminal {
            ctx.add_local(name.clone(), result_type, false);
            let stmt = format!(
                "let {} = {}.iter(){}{}{}",
                name, arr_name, prefix, chain, terminal
            );
            return Some(stmt);
        }

        // Pick a terminal operation:
        // 33% .collect() -> [T], 13% .count() -> i64, 13% .sum() -> T (numeric only),
        // 13% .reduce() -> T (two-param closure), 12% .take(N).collect() -> [T],
        // 8% .first() -> T? or T (with ??), 8% .last() -> T? or T (with ??)
        let terminal_choice = self.rng.gen_range(0..24);
        let (terminal, result_type) = if terminal_choice < 8 {
            (
                ".collect()".to_string(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_prim))),
            )
        } else if terminal_choice < 11 {
            (
                ".count()".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            )
        } else if terminal_choice < 14 {
            // .sum() only valid for numeric types
            match elem_prim {
                PrimitiveType::I64 | PrimitiveType::F64 => {
                    (".sum()".to_string(), TypeInfo::Primitive(elem_prim))
                }
                _ => (
                    ".count()".to_string(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                ),
            }
        } else if terminal_choice < 17 {
            // .reduce(init, (acc, x) => expr) - two-param accumulator closure
            // Bool elements can't use reduce (&&/|| has codegen bug, arithmetic
            // has type mismatch). Fall back to .collect() for bool.
            if elem_prim == PrimitiveType::Bool {
                (
                    ".collect()".to_string(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_prim))),
                )
            } else {
                let (init, body, result_ty) = self.generate_reduce_closure(elem_prim);
                (
                    format!(".reduce({}, (acc, el) => {})", init, body),
                    result_ty,
                )
            }
        } else if terminal_choice < 20 {
            let n = self.rng.gen_range(1..=3);
            (
                format!(".take({}).collect()", n),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_prim))),
            )
        } else {
            // .first() or .last() -> T? (optional)
            // ~50% of the time, immediately unwrap with ?? to produce T instead of T?
            // This exercises both optional-typed locals and null coalescing on
            // iterator terminal results.
            let method = if self.rng.gen_bool(0.5) {
                ".first()"
            } else {
                ".last()"
            };
            if self.rng.gen_bool(0.5) {
                // Produce T? — the optional local becomes a candidate for ?? elsewhere
                (
                    method.to_string(),
                    TypeInfo::Optional(Box::new(TypeInfo::Primitive(elem_prim))),
                )
            } else {
                // Immediately unwrap with ?? default — produces T directly
                let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                let default_val = expr_gen.literal_for_primitive(elem_prim);
                (
                    format!("{} ?? {}", method, default_val),
                    TypeInfo::Primitive(elem_prim),
                )
            }
        };

        ctx.add_local(name.clone(), result_type, false);
        let stmt = format!(
            "let {} = {}.iter(){}{}{}",
            name, arr_name, prefix, chain, terminal
        );

        Some(stmt)
    }

    /// Generate a simple closure body for `.map()` that transforms a value.
    ///
    /// The closure parameter is always named `x`. Returns an expression string
    /// that produces the same primitive type as the input.
    /// Only handles i64, f64, bool, and string (the types we restrict to).
    fn generate_map_closure_body(&mut self, elem_prim: PrimitiveType) -> String {
        match elem_prim {
            PrimitiveType::I64 => match self.rng.gen_range(0..3) {
                0 => {
                    let n = self.rng.gen_range(2..=5);
                    format!("x * {}", n)
                }
                1 => {
                    let n = self.rng.gen_range(1..=10);
                    format!("x + {}", n)
                }
                _ => {
                    let n = self.rng.gen_range(1..=3);
                    format!("x - {}", n)
                }
            },
            PrimitiveType::F64 => match self.rng.gen_range(0..2) {
                0 => {
                    let n = self.rng.gen_range(2..=5);
                    format!("x * {}.0", n)
                }
                _ => {
                    let n = self.rng.gen_range(1..=10);
                    format!("x + {}.0", n)
                }
            },
            PrimitiveType::Bool => "!x".to_string(),
            PrimitiveType::String => match self.rng.gen_range(0..3) {
                0 => "x.to_upper()".to_string(),
                1 => "x.to_lower()".to_string(),
                _ => "x.trim()".to_string(),
            },
            // Other types are filtered out by try_generate_iter_map_filter_let
            _ => "x".to_string(),
        }
    }

    /// Generate a simple closure body for `.filter()` that returns a boolean.
    ///
    /// The closure parameter is always named `x`. Returns a boolean expression
    /// suitable for filtering.
    /// Only handles i64, f64, bool, and string (the types we restrict to).
    fn generate_filter_closure_body(&mut self, elem_prim: PrimitiveType) -> String {
        // Use permissive thresholds to avoid producing empty arrays.
        // Source arrays typically have elements in 0..10 or small ranges.
        match elem_prim {
            PrimitiveType::I64 => match self.rng.gen_range(0..3) {
                0 => {
                    let n = self.rng.gen_range(-5..=2);
                    format!("x > {}", n)
                }
                1 => {
                    let n = self.rng.gen_range(5..=20);
                    format!("x < {}", n)
                }
                _ => "x % 2 == 0".to_string(),
            },
            PrimitiveType::F64 => {
                let n = self.rng.gen_range(0..=20);
                format!("x > {}.0", n)
            }
            PrimitiveType::Bool => {
                if self.rng.gen_bool(0.5) {
                    "x".to_string()
                } else {
                    "!x".to_string()
                }
            }
            PrimitiveType::String => {
                let n = self.rng.gen_range(0..=1);
                format!("x.length() > {}", n)
            }
            // Other types are filtered out by try_generate_iter_map_filter_let
            _ => "true".to_string(),
        }
    }

    /// Generate a `.reduce()` closure with initial value and accumulator body.
    ///
    /// Returns `(init_expr, closure_body, result_type)`. The closure params
    /// are always `acc` and `el`. Produces type-safe reduce patterns.
    fn generate_reduce_closure(&mut self, elem_prim: PrimitiveType) -> (String, String, TypeInfo) {
        match elem_prim {
            PrimitiveType::I64 => {
                match self.rng.gen_range(0..4) {
                    0 => (
                        "0".to_string(),
                        "acc + el".to_string(),
                        TypeInfo::Primitive(PrimitiveType::I64),
                    ),
                    1 => {
                        let n = self.rng.gen_range(1..=3);
                        (
                            format!("{}", n),
                            "acc * el".to_string(),
                            TypeInfo::Primitive(PrimitiveType::I64),
                        )
                    }
                    2 => {
                        // Conditional accumulation: when { el > 0 => acc + el, _ => acc }
                        let threshold = self.rng.gen_range(0..=5);
                        (
                            "0".to_string(),
                            format!(
                                "when {{ el > {} => acc + el, _ => acc }}",
                                threshold
                            ),
                            TypeInfo::Primitive(PrimitiveType::I64),
                        )
                    }
                    _ => {
                        // Max-like: when { el > acc => el, _ => acc }
                        (
                            "0".to_string(),
                            "when { el > acc => el, _ => acc }".to_string(),
                            TypeInfo::Primitive(PrimitiveType::I64),
                        )
                    }
                }
            }
            PrimitiveType::F64 => (
                "0.0".to_string(),
                "acc + el".to_string(),
                TypeInfo::Primitive(PrimitiveType::F64),
            ),
            PrimitiveType::String => {
                // String concatenation with separator
                let sep = if self.rng.gen_bool(0.5) { "," } else { " " };
                (
                    format!("\"\""),
                    format!("acc + el + \"{}\"", sep),
                    TypeInfo::Primitive(PrimitiveType::String),
                )
            }
            // Bool is filtered out by the caller (reduce skipped for bool).
            // Fallback: count as i64
            _ => (
                "0".to_string(),
                "acc + 1".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            ),
        }
    }

    /// Generate a closure body for `.map()` with a custom parameter name.
    ///
    /// Used for chained operations where the second closure needs a different
    /// parameter name to avoid shadowing (e.g., `.map((x) => ...).filter((y) => ...)`).
    fn generate_map_closure_body_param(&mut self, elem_prim: PrimitiveType, param: &str) -> String {
        let body = self.generate_map_closure_body(elem_prim);
        body.replace("x", param)
    }

    /// Generate a closure body for `.filter()` with a custom parameter name.
    ///
    /// Used for chained operations where the second closure needs a different
    /// parameter name to avoid shadowing.
    fn generate_filter_closure_body_param(
        &mut self,
        elem_prim: PrimitiveType,
        param: &str,
    ) -> String {
        let body = self.generate_filter_closure_body(elem_prim);
        body.replace("x", param)
    }

    /// Try to generate a generic-closure-interface iterator chain statement.
    ///
    /// Looks for the combination of:
    /// 1. An array-typed variable in scope (with primitive element type)
    /// 2. A function-typed parameter whose signature is `(ElemType) -> ElemType`
    /// 3. A type-param-typed parameter with interface constraints (whose methods
    ///    return a comparable primitive type)
    ///
    /// When all three are present, generates an iterator chain that uses the
    /// closure parameter in `.map(transform)` and calls an interface method on
    /// the constrained type param in `.filter((n: ElemType) => n > criterion.method())`.
    ///
    /// Example output:
    /// ```vole
    /// let local5 = items.iter().map(transform).filter((n: i64) => n > criterion.threshold()).collect()
    /// ```
    ///
    /// Returns `None` if the required combination is not available in scope.
    fn try_generate_generic_closure_interface_chain(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        let expr_ctx = ctx.to_expr_context();

        // Step 1: Find array-typed variables with safe element types
        let array_vars = expr_ctx.array_vars();
        let prim_array_vars: Vec<(String, PrimitiveType)> = array_vars
            .into_iter()
            .filter_map(|(name, elem_ty)| {
                if let TypeInfo::Primitive(prim) = elem_ty {
                    match prim {
                        PrimitiveType::I64 | PrimitiveType::I32 => Some((name, prim)),
                        _ => None,
                    }
                } else {
                    None
                }
            })
            .collect();

        if prim_array_vars.is_empty() {
            return None;
        }

        // Step 2: Find function-typed params that are (PrimType) -> PrimType
        // (single-param closures whose input and output are the same numeric type)
        let fn_params: Vec<(String, PrimitiveType)> = ctx
            .params
            .iter()
            .filter_map(|p| {
                if let TypeInfo::Function {
                    param_types,
                    return_type,
                } = &p.param_type
                {
                    if param_types.len() == 1 {
                        if let (TypeInfo::Primitive(pt), TypeInfo::Primitive(rt)) =
                            (&param_types[0], return_type.as_ref())
                        {
                            if pt == rt && matches!(pt, PrimitiveType::I64 | PrimitiveType::I32) {
                                return Some((p.name.clone(), *pt));
                            }
                        }
                    }
                }
                None
            })
            .collect();

        if fn_params.is_empty() {
            return None;
        }

        // Step 3: Find constrained type param variables with interface methods
        // that return a numeric type suitable for comparison
        let constrained_vars = expr_ctx.constrained_type_param_vars();
        if constrained_vars.is_empty() {
            return None;
        }

        // Find a (var_name, method_name, params, return_type) tuple where the
        // method is callable on the constrained type param instance.
        // We accept any method (including void) — the filter expression adapts:
        //   - Matching numeric (i64/i32): n > criterion.method()
        //   - Bool: criterion.method() || n > 0
        //   - Void/other: call method in a let _ discard, filter uses n > 0
        let mut iface_candidates: Vec<(String, String, Vec<ParamInfo>, TypeInfo)> = Vec::new();
        for (var_name, _tp_name, constraints) in &constrained_vars {
            let methods = crate::expr::get_type_param_constraint_methods(ctx.table, constraints);
            for (_iface_info, method) in methods {
                iface_candidates.push((
                    var_name.clone(),
                    method.name.clone(),
                    method.params.clone(),
                    method.return_type.clone(),
                ));
            }
        }

        if iface_candidates.is_empty() {
            return None;
        }

        // Pick an array variable
        let arr_idx = self.rng.gen_range(0..prim_array_vars.len());
        let (arr_name, elem_prim) = &prim_array_vars[arr_idx];
        let elem_prim = *elem_prim;
        let arr_name = arr_name.clone();

        // Pick a matching function-typed param (must match element type)
        let matching_fn_params: Vec<&(String, PrimitiveType)> = fn_params
            .iter()
            .filter(|(_, pt)| *pt == elem_prim)
            .collect();

        if matching_fn_params.is_empty() {
            return None;
        }
        let fn_idx = self.rng.gen_range(0..matching_fn_params.len());
        let (fn_name, _) = matching_fn_params[fn_idx];
        let fn_name = fn_name.clone();

        // Pick an interface method candidate
        let iface_idx = self.rng.gen_range(0..iface_candidates.len());
        let (iface_var, method_name, method_params, method_return_type) =
            &iface_candidates[iface_idx];
        let iface_var = iface_var.clone();
        let method_name = method_name.clone();
        let method_params = method_params.clone();
        let method_return_type = method_return_type.clone();

        // Generate method call arguments (for the interface method)
        let method_args = if method_params.is_empty() {
            String::new()
        } else {
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            method_params
                .iter()
                .map(|p| expr_gen.generate_simple(&p.param_type, &expr_ctx))
                .collect::<Vec<_>>()
                .join(", ")
        };

        let method_call = format!("{}.{}({})", iface_var, method_name, method_args);

        // Determine how to incorporate the method call in filter predicates.
        // When the method returns the same numeric type as the array element,
        // use direct comparison: n > criterion.method().
        // Otherwise, adapt the filter to still exercise the method call.
        let method_returns_matching_numeric = matches!(
            method_return_type,
            TypeInfo::Primitive(p) if p == elem_prim
        );
        let method_returns_bool =
            matches!(method_return_type, TypeInfo::Primitive(PrimitiveType::Bool));

        // Choose the chain pattern: several variations combining closure + interface dispatch
        let elem_type_name = match elem_prim {
            PrimitiveType::I64 => "i64",
            PrimitiveType::I32 => "i32",
            _ => "i64",
        };

        // Build the filter predicate based on the method return type.
        // When the return type matches the element type, compare directly.
        // For bool returns, combine with a comparison on n.
        // For other types, use a simple n > 0 and prepend a discard statement
        // to exercise the interface dispatch.
        let needs_discard_prefix = !method_returns_matching_numeric && !method_returns_bool;

        let filter_pred = if method_returns_matching_numeric {
            // Direct comparison: n > criterion.method()
            format!("(n: {}) => n > {}", elem_type_name, method_call)
        } else if method_returns_bool {
            // Boolean dispatch: criterion.method() || n > 0
            format!("(n: {}) => {} || n > 0", elem_type_name, method_call)
        } else {
            // Other/void return type: simple predicate (dispatch is in discard stmt)
            format!("(n: {}) => n > 0", elem_type_name)
        };

        let name = ctx.new_local_name();
        let pattern = self.rng.gen_range(0..6);
        let (chain, result_type) = match pattern {
            0 => {
                // .map(transform).filter(pred).collect()
                (
                    format!(".map({}).filter({}).collect()", fn_name, filter_pred),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_prim))),
                )
            }
            1 => {
                // .filter(pred).map(transform).collect()
                (
                    format!(".filter({}).map({}).collect()", filter_pred, fn_name),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_prim))),
                )
            }
            2 => {
                // .map(transform).filter(pred).count()
                (
                    format!(".map({}).filter({}).count()", fn_name, filter_pred),
                    TypeInfo::Primitive(PrimitiveType::I64),
                )
            }
            3 => {
                // .filter(pred).collect()
                // (closure-only map omitted, just interface dispatch in filter)
                (
                    format!(".filter({}).collect()", filter_pred),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_prim))),
                )
            }
            4 => {
                // .map(transform).filter(pred).sum()
                (
                    format!(".map({}).filter({}).sum()", fn_name, filter_pred),
                    TypeInfo::Primitive(elem_prim),
                )
            }
            _ => {
                // .map(transform).filter(pred).take(N).collect()
                let take_n = self.rng.gen_range(1..=3);
                (
                    format!(
                        ".map({}).filter({}).take({}).collect()",
                        fn_name, filter_pred, take_n
                    ),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_prim))),
                )
            }
        };

        ctx.add_local(name.clone(), result_type, false);

        // When the method returns a non-matching/non-bool type, prepend a discard
        // statement to exercise the interface dispatch before the chain.
        let chain_stmt = format!("let {} = {}.iter(){}", name, arr_name, chain);
        if needs_discard_prefix {
            let discard_name = ctx.new_local_name();
            ctx.add_local(discard_name.clone(), method_return_type, false);
            let discard = format!("let {} = {}", discard_name, method_call);
            Some(format!("{}\n    {}", discard, chain_stmt))
        } else {
            Some(chain_stmt)
        }
    }

    /// Try to generate a raise statement in a fallible function body.
    ///
    /// Wraps the raise in `if <condition> { raise ErrorType { ... } }` to avoid
    /// always exiting on the first statement. Only called when `ctx.is_fallible`
    /// is true.
    ///
    /// Returns `None` if the error type can't be resolved.
    fn try_generate_raise_statement(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let _module_id = ctx.module_id?;
        let error_type = ctx.fallible_error_type.as_ref()?;

        // Get the error type's fields
        let (error_name, error_fields) = match error_type {
            TypeInfo::Error(mod_id, sym_id) => {
                let symbol = ctx.table.get_symbol(*mod_id, *sym_id)?;
                if let SymbolKind::Error(ref info) = symbol.kind {
                    (symbol.name.clone(), info.fields.clone())
                } else {
                    return None;
                }
            }
            _ => return None,
        };

        // Generate a simple condition so the raise doesn't always trigger
        // Use a simple expression to avoid multi-line when/match in the if condition
        let expr_ctx = ctx.to_expr_context();
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let cond = expr_gen.generate_simple(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx);

        // Generate simple field values for the error construction (use literals/vars
        // to avoid multi-line expressions that break the single-line raise statement)
        let field_values = if error_fields.is_empty() {
            String::new()
        } else {
            let values: Vec<String> = error_fields
                .iter()
                .map(|f| {
                    let mut eg = ExprGenerator::new(self.rng, &self.config.expr_config);
                    let val = eg.generate_simple(&f.field_type, &expr_ctx);
                    format!("{}: {}", f.name, val)
                })
                .collect();
            format!(" {}", values.join(", "))
        };

        let indent = "    ".repeat(self.indent + 1);
        Some(format!(
            "if {} {{\n{}raise {} {{{}}}\n{}}}",
            cond,
            indent,
            error_name,
            field_values,
            "    ".repeat(self.indent)
        ))
    }

    /// Try to generate a let statement that calls a fallible function with try.
    ///
    /// If the current function is fallible and shares the same error type as the
    /// called function, use `try func()` to propagate errors.
    /// If the current function is NOT fallible, use a `match` expression to
    /// handle the result: `match func() { success x => x, error => default, _ => default }`.
    ///
    /// Excludes the current function from candidates to prevent direct self-recursion.
    /// Wraps the call in a conditional (`when`) to guard against mutual recursion
    /// between functions that call each other without base cases.
    ///
    /// Returns `None` if no fallible functions are available in the module.
    fn try_generate_try_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let module_id = ctx.module_id?;
        let module = ctx.table.get_module(module_id)?;

        // Find fallible functions in this module (non-generic),
        // excluding the current function to prevent direct self-recursion,
        // and only allowing lower-indexed functions to prevent mutual recursion.
        let current_name = ctx.current_function_name.as_deref();
        let current_fn_sym_id = ctx.current_function_sym_id;
        let fallible_funcs: Vec<(String, FunctionInfo)> = module
            .functions()
            .filter_map(|sym| {
                if let SymbolKind::Function(ref info) = sym.kind {
                    if info.type_params.is_empty()
                        && info.return_type.is_fallible()
                        && current_name != Some(sym.name.as_str())
                    {
                        // Only call lower-indexed functions to prevent cycles
                        if let Some(cur_id) = current_fn_sym_id {
                            if sym.id.0 >= cur_id.0 {
                                return None;
                            }
                        }
                        return Some((sym.name.clone(), info.clone()));
                    }
                }
                None
            })
            .collect();

        if fallible_funcs.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..fallible_funcs.len());
        let (func_name, func_info) = fallible_funcs[idx].clone();

        // Generate simple arguments for the call (use literals/vars to avoid multi-line expressions)
        let expr_ctx = ctx.to_expr_context();
        let args: Vec<String> = func_info
            .params
            .iter()
            .map(|p| {
                let mut eg = ExprGenerator::new(self.rng, &self.config.expr_config);
                eg.generate_simple(&p.param_type, &expr_ctx)
            })
            .collect();
        let args_str = args.join(", ");

        let success_type = func_info.return_type.success_type().clone();

        // Generate a default value for the non-call branch
        let default_val = {
            let expr_ctx2 = ctx.to_expr_context();
            let mut eg = ExprGenerator::new(self.rng, &self.config.expr_config);
            eg.generate_simple(&success_type, &expr_ctx2)
        };

        // Use `false` as the guard condition to prevent mutual recursion.
        // The call is syntactically present (exercising the type checker and
        // codegen) but never executes at runtime, preventing infinite mutual
        // recursion between functions that call each other.
        let guard_cond = "false";

        let name = ctx.new_local_name();
        ctx.add_local(name.clone(), success_type, false);

        // Use `match` (not `try`) so the call can sit inside a `when` guard.
        // The `when` condition makes the call conditional, providing a
        // non-recursive default path that prevents infinite mutual recursion.
        let call_expr = format!(
            "match {}({}) {{ success x => x, error => {}, _ => {} }}",
            func_name, args_str, default_val, default_val
        );

        Some(format!(
            "let {} = when {{ {} => {}, _ => {} }}",
            name, guard_cond, call_expr, default_val
        ))
    }

    /// Try to generate a let statement that calls a function-typed parameter.
    ///
    /// Looks for parameters with `TypeInfo::Function` type in the current scope,
    /// generates arguments matching the function's param types, and binds the
    /// result. Returns `None` if no function-typed parameters are in scope.
    fn try_generate_fn_param_call(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find function-typed parameters
        let fn_params: Vec<(String, Vec<TypeInfo>, TypeInfo)> = ctx
            .params
            .iter()
            .filter_map(|p| {
                if let TypeInfo::Function {
                    param_types,
                    return_type,
                } = &p.param_type
                {
                    Some((
                        p.name.clone(),
                        param_types.clone(),
                        return_type.as_ref().clone(),
                    ))
                } else {
                    None
                }
            })
            .collect();

        if fn_params.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..fn_params.len());
        let (fn_name, param_types, return_type) = fn_params[idx].clone();

        // Generate arguments for the function call
        let expr_ctx = ctx.to_expr_context();
        let args: Vec<String> = param_types
            .iter()
            .map(|ty| {
                let mut eg = ExprGenerator::new(self.rng, &self.config.expr_config);
                eg.generate_simple(ty, &expr_ctx)
            })
            .collect();

        let call = format!("{}({})", fn_name, args.join(", "));

        let name = ctx.new_local_name();
        if matches!(return_type, TypeInfo::Void) {
            Some(call)
        } else {
            ctx.add_local(name.clone(), return_type, false);
            Some(format!("let {} = {}", name, call))
        }
    }

    /// Try to generate a discard statement (_ = expr) that discards a function's return value.
    ///
    /// Looks for non-generic functions in the current module that return a non-void,
    /// non-fallible type. Excludes the current function to prevent direct self-recursion.
    /// Wraps the call in a conditional to guard against mutual recursion.
    ///
    /// Returns `None` if no suitable functions are available.
    fn try_generate_discard_statement(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let module_id = ctx.module_id?;
        let module = ctx.table.get_module(module_id)?;

        // Find non-generic functions with non-void, non-fallible return types,
        // excluding the current function to prevent direct self-recursion,
        // and only allowing lower-indexed functions to prevent mutual recursion.
        let current_name = ctx.current_function_name.as_deref();
        let current_fn_sym_id = ctx.current_function_sym_id;
        let candidates: Vec<(String, FunctionInfo)> = module
            .functions()
            .filter_map(|sym| {
                if let SymbolKind::Function(ref info) = sym.kind {
                    // Skip generic functions, void return, fallible return,
                    // never return (diverge), and self
                    if info.type_params.is_empty()
                        && !matches!(info.return_type, TypeInfo::Void | TypeInfo::Never)
                        && !info.return_type.is_fallible()
                        && !info.return_type.is_iterator()
                        && current_name != Some(sym.name.as_str())
                    {
                        // Only call lower-indexed functions to prevent cycles
                        if let Some(cur_id) = current_fn_sym_id {
                            if sym.id.0 >= cur_id.0 {
                                return None;
                            }
                        }
                        return Some((sym.name.clone(), info.clone()));
                    }
                }
                None
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (func_name, func_info) = candidates[idx].clone();

        // Generate simple arguments for the call
        let expr_ctx = ctx.to_expr_context();
        let args: Vec<String> = func_info
            .params
            .iter()
            .map(|p| {
                let mut eg = ExprGenerator::new(self.rng, &self.config.expr_config);
                eg.generate_simple(&p.param_type, &expr_ctx)
            })
            .collect();
        let args_str = args.join(", ");

        // Use `false` as the guard condition to prevent mutual recursion.
        // The discard call is syntactically present (exercising the type checker
        // and codegen) but never executes at runtime, preventing infinite mutual
        // recursion between functions that call each other.
        let guard_cond = "false";

        // Emit a conditional discard: if guard { _ = func(args) }
        let indent = "    ".repeat(self.indent + 1);
        Some(format!(
            "if {} {{\n{}_ = {}({})\n{}}}",
            guard_cond,
            indent,
            func_name,
            args_str,
            "    ".repeat(self.indent)
        ))
    }

    /// Generate a block of statements.
    fn generate_block(&mut self, ctx: &mut StmtContext, depth: usize) -> Vec<String> {
        let count = self.rng.gen_range(1..=2);
        let mut stmts = Vec::new();

        for _ in 0..count {
            stmts.push(self.generate_statement(ctx, depth));
        }

        stmts
    }

    /// Format a block of statements.
    ///
    /// This produces a block with relative indentation:
    /// - Inner statements are indented by 4 spaces from the opening brace
    /// - The closing brace is at the same level as the opening
    ///
    /// When a statement is multi-line (e.g., nested if/else-if chains), each
    /// line of the statement is indented by 4 spaces.
    fn format_block(&self, stmts: &[String]) -> String {
        if stmts.is_empty() {
            return "{ }".to_string();
        }

        // Use a single level of indentation for the block contents.
        // The outer indentation is handled by emit_line.
        let one_indent = "    ";
        let inner: Vec<String> = stmts
            .iter()
            .flat_map(|s| {
                // Split each statement into lines and indent each line
                s.lines()
                    .map(|line| format!("{}{}", one_indent, line))
                    .collect::<Vec<_>>()
            })
            .collect();

        format!("{{\n{}\n}}", inner.join("\n"))
    }

    /// Get the current indentation string.
    fn indent_str(&self) -> String {
        "    ".repeat(self.indent)
    }

    /// Generate a let statement that creates a small array literal.
    ///
    /// Produces `let localN = [elem1, elem2, elem3]` with 2-4 elements of
    /// a random primitive type. The local is added to scope as an array type
    /// so it can be used for array indexing expressions later.
    ///
    /// With `mutable_array_probability`, produces `let mut` bindings to enable
    /// index assignment and push operations on the array.
    fn generate_array_let(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();
        let elem_prim = PrimitiveType::random_array_element_type(self.rng);
        let elem_ty = TypeInfo::Primitive(elem_prim);
        let is_mutable = self.rng.gen_bool(self.config.mutable_array_probability);

        // Array size distribution:
        //   ~15% single-element (boundary condition stress)
        //   ~10% large 6-10 elements (stress iterator codegen with more data)
        //   ~75% standard 2-4 elements
        let elem_count = if self.rng.gen_bool(0.15) {
            1
        } else if self.rng.gen_bool(0.12) {
            self.rng.gen_range(6..=10)
        } else {
            self.rng.gen_range(2..=4)
        };
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);

        let elements: Vec<String> = (0..elem_count)
            .map(|_| expr_gen.literal_for_primitive(elem_prim))
            .collect();

        let array_ty = TypeInfo::Array(Box::new(elem_ty));
        ctx.add_local(name.clone(), array_ty, is_mutable);

        let mutability = if is_mutable { "let mut" } else { "let" };
        format!("{} {} = [{}]", mutability, name, elements.join(", "))
    }

    /// Generate an empty string and run an iterator chain on it.
    ///
    /// Produces a two-statement sequence:
    /// ```vole
    /// let s = ""
    /// let result = s.iter().count()
    /// ```
    fn generate_empty_string_iter_let(&mut self, ctx: &mut StmtContext) -> String {
        let str_name = ctx.new_local_name();
        let result_name = ctx.new_local_name();

        let (chain, result_type) = match self.rng.gen_range(0..5) {
            0 => (
                ".iter().collect()".to_string(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
            ),
            1 => (
                ".iter().count()".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            ),
            2 => (
                ".iter().any((c) => c == \"a\")".to_string(),
                TypeInfo::Primitive(PrimitiveType::Bool),
            ),
            3 => (
                ".iter().all((c) => c != \"x\")".to_string(),
                TypeInfo::Primitive(PrimitiveType::Bool),
            ),
            _ => (
                ".iter().map((c) => c + \"!\").collect()".to_string(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
            ),
        };

        ctx.add_local(
            str_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        ctx.add_local(result_name.clone(), result_type, false);

        format!(
            "let {} = \"\"\nlet {} = {}{}",
            str_name, result_name, str_name, chain
        )
    }

    /// Generate a match expression with only a wildcard arm.
    ///
    /// Produces:
    /// ```vole
    /// let result = match var {
    ///     _ => expr
    /// }
    /// ```
    fn generate_wildcard_only_match(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find any variable in scope to use as scrutinee
        let scrutinee = if !ctx.locals.is_empty() && self.rng.gen_bool(0.7) {
            let idx = self.rng.gen_range(0..ctx.locals.len());
            ctx.locals[idx].0.clone()
        } else if !ctx.params.is_empty() {
            let idx = self.rng.gen_range(0..ctx.params.len());
            ctx.params[idx].name.clone()
        } else {
            return None;
        };

        let result_type = self.random_primitive_type();
        let result_name = ctx.new_local_name();
        let expr_ctx = ctx.to_expr_context();
        let value_expr = self.generate_match_arm_value(&result_type, &expr_ctx);

        let indent = "    ".repeat(self.indent + 1);
        let close_indent = "    ".repeat(self.indent);

        ctx.add_local(result_name.clone(), result_type, false);

        Some(format!(
            "let {} = match {} {{\n{}_ => {}\n{}}}",
            result_name, scrutinee, indent, value_expr, close_indent
        ))
    }

    /// Generate a nested when expression.
    ///
    /// Produces:
    /// ```vole
    /// let result = when {
    ///     cond1 => when {
    ///         cond2 => val1
    ///         _ => val2
    ///     }
    ///     _ => val3
    /// }
    /// ```
    fn try_generate_nested_when_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let result_type = self.random_primitive_type();
        let result_name = ctx.new_local_name();

        let expr_ctx = ctx.to_expr_context();

        // Generate outer condition
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let outer_cond = expr_gen.generate_simple(
            &TypeInfo::Primitive(PrimitiveType::Bool),
            &expr_ctx,
        );

        // Generate inner condition
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let inner_cond = expr_gen.generate_simple(
            &TypeInfo::Primitive(PrimitiveType::Bool),
            &expr_ctx,
        );

        // Generate three values for the three branches
        let val1 = self.generate_match_arm_value(&result_type, &expr_ctx);
        let val2 = self.generate_match_arm_value(&result_type, &expr_ctx);
        let val3 = self.generate_match_arm_value(&result_type, &expr_ctx);

        let indent = "    ".repeat(self.indent + 1);
        let inner_indent = "    ".repeat(self.indent + 2);
        let close_indent = "    ".repeat(self.indent);
        let inner_close = "    ".repeat(self.indent + 1);

        ctx.add_local(result_name.clone(), result_type, false);

        Some(format!(
            "let {} = when {{\n\
             {}{} => when {{\n\
             {}{} => {}\n\
             {}_ => {}\n\
             {}}}\n\
             {}_ => {}\n\
             {}}}",
            result_name,
            indent, outer_cond,
            inner_indent, inner_cond, val1,
            inner_indent, val2,
            inner_close,
            indent, val3,
            close_indent,
        ))
    }

    /// Generate iterator chains that produce empty results from non-empty arrays.
    ///
    /// Uses `.take(0)` or `.skip(large)` to force zero-length iteration.
    fn try_generate_empty_iter_edge(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find arrays with primitive element types
        let mut array_vars: Vec<(String, PrimitiveType)> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Array(inner) = ty {
                if let TypeInfo::Primitive(p) = inner.as_ref() {
                    match p {
                        PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::String => {
                            array_vars.push((name.clone(), *p));
                        }
                        _ => {}
                    }
                }
            }
        }
        for param in ctx.params.iter() {
            if let TypeInfo::Array(inner) = &param.param_type {
                if let TypeInfo::Primitive(p) = inner.as_ref() {
                    match p {
                        PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::String => {
                            array_vars.push((param.name.clone(), *p));
                        }
                        _ => {}
                    }
                }
            }
        }
        if array_vars.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..array_vars.len());
        let (arr_name, elem_prim) = &array_vars[idx];
        let arr_name = arr_name.clone();
        let elem_prim = *elem_prim;
        let result_name = ctx.new_local_name();

        match self.rng.gen_range(0..4) {
            0 => {
                // .take(0).collect() → empty array
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_prim))),
                    false,
                );
                Some(format!(
                    "let {} = {}.iter().take(0).collect()",
                    result_name, arr_name
                ))
            }
            1 => {
                // .take(0).count() → 0
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                Some(format!(
                    "let {} = {}.iter().take(0).count()",
                    result_name, arr_name
                ))
            }
            2 => {
                // .skip(999).collect() → empty array
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_prim))),
                    false,
                );
                Some(format!(
                    "let {} = {}.iter().skip(999).collect()",
                    result_name, arr_name
                ))
            }
            _ => {
                // .skip(999).count() → 0
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                Some(format!(
                    "let {} = {}.iter().skip(999).count()",
                    result_name, arr_name
                ))
            }
        }
    }

    /// Generate chained string method calls.
    /// Generate a match expression on an iterator terminal result.
    ///
    /// Produces:
    /// ```vole
    /// let result = match arr.iter().count() {
    ///     0 => expr1
    ///     1 => expr2
    ///     _ => expr3
    /// }
    /// ```
    fn try_generate_match_iter_terminal(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find i64 array params (guaranteed non-empty)
        let mut array_vars: Vec<String> = Vec::new();
        for param in ctx.params.iter() {
            if let TypeInfo::Array(inner) = &param.param_type {
                if let TypeInfo::Primitive(p) = inner.as_ref() {
                    if matches!(p, PrimitiveType::I64 | PrimitiveType::I32) {
                        array_vars.push(param.name.clone());
                    }
                }
            }
        }
        if array_vars.is_empty() {
            return None;
        }

        let arr_name = &array_vars[self.rng.gen_range(0..array_vars.len())];
        let arr_name = arr_name.clone();
        let result_name = ctx.new_local_name();

        // Iterator terminal that produces i64
        let terminal = match self.rng.gen_range(0..3) {
            0 => ".iter().count()".to_string(),
            1 => ".iter().sum()".to_string(),
            _ => {
                let pred = self.generate_filter_closure_body(PrimitiveType::I64);
                format!(".iter().filter((x) => {}).count()", pred)
            }
        };

        let result_type = self.random_primitive_type();
        let expr_ctx = ctx.to_expr_context();
        let indent = "    ".repeat(self.indent + 1);
        let close_indent = "    ".repeat(self.indent);

        let arm_val1 = self.generate_match_arm_value(&result_type, &expr_ctx);
        let arm_val2 = self.generate_match_arm_value(&result_type, &expr_ctx);
        let wildcard_val = self.generate_match_arm_value(&result_type, &expr_ctx);

        ctx.add_local(result_name.clone(), result_type, false);

        Some(format!(
            "let {} = match {}{} {{\n\
             {}0 => {}\n\
             {}1 => {}\n\
             {}_ => {}\n\
             {}}}",
            result_name,
            arr_name,
            terminal,
            indent, arm_val1,
            indent, arm_val2,
            indent, wildcard_val,
            close_indent,
        ))
    }

    ///
    /// Produces patterns like:
    /// - `let r = str.to_upper().to_lower().length()`
    /// - `let r = str.trim().to_upper().contains("x")`
    fn try_generate_chained_string_methods(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Find string variables in scope
        let mut string_vars: Vec<String> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if matches!(ty, TypeInfo::Primitive(PrimitiveType::String)) {
                string_vars.push(name.clone());
            }
        }
        for param in ctx.params.iter() {
            if matches!(&param.param_type, TypeInfo::Primitive(PrimitiveType::String)) {
                string_vars.push(param.name.clone());
            }
        }
        if string_vars.is_empty() {
            return None;
        }

        let str_name = &string_vars[self.rng.gen_range(0..string_vars.len())];
        let str_name = str_name.clone();
        let result_name = ctx.new_local_name();

        // Build a chain of 2-3 string transforms ending with a terminal
        let transforms = [".to_upper()", ".to_lower()", ".trim()"];
        let chain_len = self.rng.gen_range(2..=3);
        let mut chain = String::new();
        for _ in 0..chain_len {
            chain.push_str(transforms[self.rng.gen_range(0..transforms.len())]);
        }

        // Pick terminal
        let (terminal, result_type) = match self.rng.gen_range(0..3) {
            0 => (
                ".length()".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            ),
            1 => (
                ".contains(\"a\")".to_string(),
                TypeInfo::Primitive(PrimitiveType::Bool),
            ),
            _ => (
                String::new(),
                TypeInfo::Primitive(PrimitiveType::String),
            ),
        };

        ctx.add_local(result_name.clone(), result_type, false);
        Some(format!(
            "let {} = {}{}{}",
            result_name, str_name, chain, terminal
        ))
    }

    /// Generate a match expression on an array element.
    ///
    /// Produces:
    /// ```vole
    /// let result = match arr[0] {
    ///     val1 => expr1
    ///     val2 => expr2
    ///     _ => expr3
    /// }
    /// ```
    fn try_generate_match_array_elem(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Only use parameter arrays (guaranteed non-empty by generator).
        // Local arrays could be from .collect() which may produce empty arrays.
        let mut array_vars: Vec<(String, PrimitiveType)> = Vec::new();
        for param in ctx.params.iter() {
            if let TypeInfo::Array(inner) = &param.param_type {
                if let TypeInfo::Primitive(p) = inner.as_ref() {
                    if matches!(p, PrimitiveType::I64 | PrimitiveType::I32) {
                        array_vars.push((param.name.clone(), *p));
                    }
                }
            }
        }
        if array_vars.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..array_vars.len());
        let (arr_name, elem_prim) = &array_vars[idx];
        let arr_name = arr_name.clone();
        let elem_prim = *elem_prim;

        let result_type = self.random_primitive_type();
        let result_name = ctx.new_local_name();
        let expr_ctx = ctx.to_expr_context();
        let indent = "    ".repeat(self.indent + 1);
        let close_indent = "    ".repeat(self.indent);

        // Generate 2 specific arms + wildcard
        // Pre-generate literals to avoid borrow conflict
        let lit1 = {
            let mut eg = ExprGenerator::new(self.rng, &self.config.expr_config);
            eg.literal_for_primitive(elem_prim)
        };
        let lit2 = {
            let mut eg = ExprGenerator::new(self.rng, &self.config.expr_config);
            eg.literal_for_primitive(elem_prim)
        };
        let arm_val1 = self.generate_match_arm_value(&result_type, &expr_ctx);
        let arm_val2 = self.generate_match_arm_value(&result_type, &expr_ctx);
        let wildcard_val = self.generate_match_arm_value(&result_type, &expr_ctx);

        let arms = vec![
            format!("{}{} => {}", indent, lit1, arm_val1),
            format!("{}{} => {}", indent, lit2, arm_val2),
            format!("{}_ => {}", indent, wildcard_val),
        ];

        ctx.add_local(result_name.clone(), result_type, false);

        Some(format!(
            "let {} = match {}[0] {{\n{}\n{}}}",
            result_name,
            arr_name,
            arms.join("\n"),
            close_indent,
        ))
    }

    /// Generate an empty array and run an iterator chain on it.
    ///
    /// Produces a two-statement sequence:
    /// ```vole
    /// let arrN: [i64] = []
    /// let resN = arrN.iter().map((x) => x * 2_i64).collect()
    /// ```
    ///
    /// This stresses boundary conditions around zero-length collections in the
    /// iterator pipeline: empty .collect(), .count() == 0, .sum() == 0,
    /// .first()/.last() returning none, .reduce() returning only the init value,
    /// .sorted()/.reverse()/.unique() on empty sequences, etc.
    fn generate_empty_array_iter_let(&mut self, ctx: &mut StmtContext) -> String {
        // Restrict to well-tested element types for iterator closures
        let elem_prim = match self.rng.gen_range(0..4) {
            0 => PrimitiveType::I64,
            1 => PrimitiveType::F64,
            2 => PrimitiveType::Bool,
            _ => PrimitiveType::String,
        };
        let elem_ty = TypeInfo::Primitive(elem_prim);
        let array_ty = TypeInfo::Array(Box::new(elem_ty.clone()));
        let type_annotation = array_ty.to_vole_syntax(ctx.table);

        let arr_name = ctx.new_local_name();
        // NOTE: intentionally NOT calling ctx.add_local() for the empty array.
        // Registering it would make it available to try_generate_array_index(),
        // which assumes arrays have 2-4 elements and would generate OOB accesses.

        let result_name = ctx.new_local_name();

        let is_numeric = matches!(elem_prim, PrimitiveType::I64 | PrimitiveType::F64);

        // Optionally prepend a prefix chain stage (~25%).
        let prefix: String = if self.rng.gen_bool(0.25) {
            match self.rng.gen_range(0..4) {
                0 if is_numeric => ".sorted()".to_string(),
                1 => ".reverse()".to_string(),
                2 if elem_prim != PrimitiveType::Bool => ".unique()".to_string(),
                3 => format!(".skip({})", self.rng.gen_range(0..=1)),
                _ => ".reverse()".to_string(),
            }
        } else {
            String::new()
        };

        // Pick a chain + terminal combination.
        // Weight distribution:
        //   0..4  => .map().collect()           -> [T]
        //   4..7  => .filter().collect()         -> [T]
        //   7..9  => .count()                    -> i64
        //   9..11 => .sum() (numeric only)       -> T
        //  11..13 => .first() ?? default         -> T
        //  13..15 => .last() ?? default           -> T
        //  15..17 => .reduce(init, closure)       -> T
        //  17..19 => .take(N).collect()           -> [T]
        //  19..20 => .map().filter().collect()    -> [T]
        //  20..21 => .enumerate().count()         -> i64
        let choice = self.rng.gen_range(0..21);

        let (chain, result_type) = if choice < 4 {
            // .map().collect()
            let map_body = self.generate_map_closure_body(elem_prim);
            (
                format!(".map((x) => {}).collect()", map_body),
                TypeInfo::Array(Box::new(elem_ty.clone())),
            )
        } else if choice < 7 {
            // .filter().collect()
            let filter_body = self.generate_filter_closure_body(elem_prim);
            (
                format!(".filter((x) => {}).collect()", filter_body),
                TypeInfo::Array(Box::new(elem_ty.clone())),
            )
        } else if choice < 9 {
            // .count()
            (
                ".count()".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            )
        } else if choice < 11 && is_numeric {
            // .sum() — numeric only
            (".sum()".to_string(), TypeInfo::Primitive(elem_prim))
        } else if choice < 13 {
            // .first() ?? default
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            let default_val = expr_gen.literal_for_primitive(elem_prim);
            (
                format!(".first() ?? {}", default_val),
                TypeInfo::Primitive(elem_prim),
            )
        } else if choice < 15 {
            // .last() ?? default
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            let default_val = expr_gen.literal_for_primitive(elem_prim);
            (
                format!(".last() ?? {}", default_val),
                TypeInfo::Primitive(elem_prim),
            )
        } else if choice < 17 && elem_prim != PrimitiveType::Bool {
            // .reduce(init, closure) — skip bool (codegen limitation)
            let (init, body, result_ty) = self.generate_reduce_closure(elem_prim);
            (
                format!(".reduce({}, (acc, el) => {})", init, body),
                result_ty,
            )
        } else if choice < 19 {
            // .take(N).collect()
            let n = self.rng.gen_range(1..=3);
            (
                format!(".take({}).collect()", n),
                TypeInfo::Array(Box::new(elem_ty.clone())),
            )
        } else if choice < 20 {
            // .map().filter().collect()
            let map_body = self.generate_map_closure_body(elem_prim);
            let filter_body = self.generate_filter_closure_body_param(elem_prim, "y");
            (
                format!(
                    ".map((x) => {}).filter((y) => {}).collect()",
                    map_body, filter_body
                ),
                TypeInfo::Array(Box::new(elem_ty.clone())),
            )
        } else {
            // .enumerate().count()
            (
                ".enumerate().count()".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            )
        };

        // Only register non-array results (count, sum, first, last, reduce).
        // Array results (.collect()) are also empty and must not be indexed.
        if !matches!(result_type, TypeInfo::Array(_)) {
            ctx.add_local(result_name.clone(), result_type, false);
        }

        let indent = self.indent_str();
        format!(
            "let {}: {} = []\n{}let {} = {}.iter(){}{}",
            arr_name, type_annotation, indent, result_name, arr_name, prefix, chain
        )
    }

    /// Generate a range-based iterator chain let-binding.
    ///
    /// Produces expressions like:
    /// ```vole
    /// let localN = (0..10).iter().map((x) => x * 2).collect()
    /// let localN = (1..=5).iter().filter((x) => x > 2).sum()
    /// let localN = (0..8).iter().sorted().take(3).collect()
    /// ```
    ///
    /// Range iterators always produce i64 elements, so all numeric iterator
    /// operations (.sum(), .sorted(), numeric map/filter closures) apply.
    /// This exercises a different iterator source codegen path compared to
    /// array-based iterators (range source vs array source).
    fn generate_range_iter_let(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();

        // Generate a small, bounded range. Use only literal bounds to avoid
        // accidentally iterating over huge ranges from computed values.
        let use_inclusive = self.rng.gen_bool(0.3);
        let start = self.rng.gen_range(0..3_i64);
        let end = if use_inclusive {
            self.rng.gen_range(start..start + 8)
        } else {
            self.rng.gen_range(start + 1..start + 10)
        };
        let range_expr = if use_inclusive {
            format!("({}..={})", start, end)
        } else {
            format!("({}..{})", start, end)
        };

        // Range elements are always i64.
        let elem_prim = PrimitiveType::I64;

        // Optionally prepend .sorted(), .reverse(), or .skip(N) (~20%).
        let prefix: String = if self.rng.gen_bool(0.20) {
            match self.rng.gen_range(0..3) {
                0 => ".sorted()".to_string(),
                1 => ".reverse()".to_string(),
                _ => format!(".skip({})", self.rng.gen_range(0..=1)),
            }
        } else {
            String::new()
        };

        // Build the iterator chain: .iter() followed by 1-2 operations, then a terminal.
        // Weight distribution:
        //   0..5  => single .map()
        //   5..9  => single .filter()
        //   9..12 => .map().filter()
        //  12..14 => .filter().map()
        //  14..16 => .sorted().map()
        //  16..18 => .filter().sorted()
        let chain_choice = self.rng.gen_range(0..18);

        let chain = if chain_choice < 5 {
            // Single .map()
            let map_body = self.generate_map_closure_body(elem_prim);
            format!(".map((x) => {})", map_body)
        } else if chain_choice < 9 {
            // Single .filter()
            let filter_body = self.generate_filter_closure_body(elem_prim);
            format!(".filter((x) => {})", filter_body)
        } else if chain_choice < 12 {
            // .map().filter()
            let map_body = self.generate_map_closure_body(elem_prim);
            let filter_body = self.generate_filter_closure_body_param(elem_prim, "y");
            format!(".map((x) => {}).filter((y) => {})", map_body, filter_body)
        } else if chain_choice < 14 {
            // .filter().map()
            let filter_body = self.generate_filter_closure_body(elem_prim);
            let map_body = self.generate_map_closure_body_param(elem_prim, "y");
            format!(".filter((x) => {}).map((y) => {})", filter_body, map_body)
        } else if chain_choice < 16 {
            // .sorted().map()
            let map_body = self.generate_map_closure_body(elem_prim);
            format!(".sorted().map((x) => {})", map_body)
        } else {
            // .filter().sorted()
            let filter_body = self.generate_filter_closure_body(elem_prim);
            format!(".filter((x) => {}).sorted()", filter_body)
        };

        // Pick a terminal operation:
        // 30% .collect() -> [i64], 15% .count() -> i64, 15% .sum() -> i64,
        // 12% .reduce() -> i64, 12% .take(N).collect() -> [i64],
        // 8% .first() -> i64? or i64 (with ??), 8% .last() -> i64? or i64 (with ??)
        let terminal_choice = self.rng.gen_range(0..20);
        let (terminal, result_type) = if terminal_choice < 6 {
            (
                ".collect()".to_string(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_prim))),
            )
        } else if terminal_choice < 9 {
            (
                ".count()".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            )
        } else if terminal_choice < 12 {
            (
                ".sum()".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            )
        } else if terminal_choice < 14 {
            // .reduce(init, (acc, el) => expr)
            let (init, body, result_ty) = self.generate_reduce_closure(elem_prim);
            (
                format!(".reduce({}, (acc, el) => {})", init, body),
                result_ty,
            )
        } else if terminal_choice < 17 {
            let n = self.rng.gen_range(1..=3);
            (
                format!(".take({}).collect()", n),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_prim))),
            )
        } else {
            // .first() or .last() -> i64? (optional)
            // ~50% immediately unwrap with ?? to produce i64
            let method = if self.rng.gen_bool(0.5) {
                ".first()"
            } else {
                ".last()"
            };
            if self.rng.gen_bool(0.5) {
                // Produce i64? — the optional local becomes a candidate for ?? elsewhere
                (
                    method.to_string(),
                    TypeInfo::Optional(Box::new(TypeInfo::Primitive(elem_prim))),
                )
            } else {
                // Immediately unwrap with ?? default — produces i64 directly
                let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                let default_val = expr_gen.literal_for_primitive(elem_prim);
                (
                    format!("{} ?? {}", method, default_val),
                    TypeInfo::Primitive(elem_prim),
                )
            }
        };

        ctx.add_local(name.clone(), result_type, false);
        format!(
            "let {} = {}.iter(){}{}{}",
            name, range_expr, prefix, chain, terminal
        )
    }

    /// Generate a tuple let-binding with destructuring.
    ///
    /// Produces a two-statement sequence:
    /// ```vole
    /// let tN: [i64, string] = [42_i64, "hello"]
    /// let [a, b] = tN
    /// ```
    /// Adds each destructured element as a local variable with its
    /// corresponding element type.
    fn generate_tuple_let(&mut self, ctx: &mut StmtContext) -> String {
        let tuple_ty = TypeInfo::random_tuple_type(self.rng);
        let elem_types = match &tuple_ty {
            TypeInfo::Tuple(elems) => elems.clone(),
            _ => unreachable!(),
        };

        // Generate the tuple literal expression
        let expr_ctx = ctx.to_expr_context();
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let value = expr_gen.generate(&tuple_ty, &expr_ctx, 0);

        let tuple_name = ctx.new_local_name();
        let type_annotation = tuple_ty.to_vole_syntax(ctx.table);

        // Add the tuple variable itself to scope so it can be used for tuple indexing
        ctx.add_local(tuple_name.clone(), tuple_ty.clone(), false);

        // Generate destructuring names for each element
        let destruct_names: Vec<String> = elem_types.iter().map(|_| ctx.new_local_name()).collect();

        // Add destructured locals to scope
        for (name, ty) in destruct_names.iter().zip(elem_types.iter()) {
            ctx.add_local(name.clone(), ty.clone(), false);
        }

        let pattern = format!("[{}]", destruct_names.join(", "));
        format!(
            "let {}: {} = {}\n{}let {} = {}",
            tuple_name,
            type_annotation,
            value,
            self.indent_str(),
            pattern,
            tuple_name,
        )
    }

    /// Generate a fixed-size array let-binding with destructuring.
    ///
    /// Produces a two-statement sequence:
    /// ```vole
    /// let arrN: [i64; 3] = [42_i64; 3]
    /// let [a, b, c] = arrN
    /// ```
    /// Adds each destructured element as a local variable with the element type.
    fn generate_fixed_array_let(&mut self, ctx: &mut StmtContext) -> String {
        let fixed_array_ty = TypeInfo::random_fixed_array_type(self.rng);
        let (elem_ty, size) = match &fixed_array_ty {
            TypeInfo::FixedArray(elem, size) => (*elem.clone(), *size),
            _ => unreachable!(),
        };

        // Generate the repeat literal expression
        let expr_ctx = ctx.to_expr_context();
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let value = expr_gen.generate(&fixed_array_ty, &expr_ctx, 0);

        let arr_name = ctx.new_local_name();
        let type_annotation = fixed_array_ty.to_vole_syntax(ctx.table);

        // Generate destructuring names for each element
        let destruct_names: Vec<String> = (0..size).map(|_| ctx.new_local_name()).collect();

        // Add destructured locals to scope with the element type
        for name in &destruct_names {
            ctx.add_local(name.clone(), elem_ty.clone(), false);
        }

        let pattern = format!("[{}]", destruct_names.join(", "));
        format!(
            "let {}: {} = {}\n{}let {} = {}",
            arr_name,
            type_annotation,
            value,
            self.indent_str(),
            pattern,
            arr_name,
        )
    }

    /// Try to generate a let statement that constructs a class instance.
    ///
    /// Returns `None` if no suitable non-generic class is available in the
    /// current module. Only constructs classes with primitive-typed fields
    /// so the resulting local can be used for field access expressions.
    ///
    /// If the class has static methods, there's a chance to use a static method
    /// call instead of direct construction: `let local = ClassName.staticMethod(args)`
    ///
    /// If the class has Self-returning methods (from standalone implement blocks),
    /// there's a chance to chain method calls on the constructed instance:
    /// `let local = ClassName { fields }.selfMethod(args).selfMethod2(args)`
    fn try_generate_class_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let module_id = ctx.module_id?;
        let module = ctx.table.get_module(module_id)?;

        // Collect non-generic classes with at least one primitive field
        let candidates: Vec<_> = module
            .classes()
            .filter_map(|sym| {
                if let SymbolKind::Class(ref info) = sym.kind {
                    if info.type_params.is_empty() && has_primitive_field(info) {
                        return Some((sym.id, sym.name.clone(), info.clone()));
                    }
                }
                None
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (sym_id, class_name, class_info) = &candidates[idx];

        let name = ctx.new_local_name();
        let ty = TypeInfo::Class(module_id, *sym_id);

        // Try using a static method call if available
        if !class_info.static_methods.is_empty()
            && self.rng.gen_bool(self.config.static_call_probability)
        {
            let expr = self.generate_static_call(class_name, &class_info.static_methods, ctx);
            // Add to scope AFTER generating the expression to avoid self-references
            ctx.add_local(name.clone(), ty, false);
            return Some(format!("let {} = {}", name, expr));
        }

        // Generate field values for construction
        let fields = self.generate_field_values(&class_info.fields, ctx);

        // Build the base expression (class construction)
        let mut expr = format!("{} {{ {} }}", class_name, fields);

        // Try to chain Self-returning methods (but not on the class whose method
        // body we're currently generating — the chained methods could call back).
        if ctx.current_class_sym_id != Some((module_id, *sym_id)) {
            let chain = self.try_generate_method_chain(ctx.table, module_id, *sym_id, ctx);
            if !chain.is_empty() {
                expr = format!("{}{}", expr, chain);
            }
        }

        // Add to scope AFTER generating all expressions to avoid self-references
        ctx.add_local(name.clone(), ty, false);

        Some(format!("let {} = {}", name, expr))
    }

    /// Try to generate an instance method call on a class-typed local.
    ///
    /// Finds class-typed locals in scope, picks a non-generic class method,
    /// generates type-correct arguments, and binds the result to a new local
    /// when the return type is primitive or optional.
    ///
    /// Generated output shapes:
    /// - `let local5 = instance.methodName(42_i64, true)` (primitive return)
    /// - `instance.methodName(42_i64)` (void return)
    fn try_generate_method_call(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let _ = ctx.module_id?;

        // Find class-typed locals in scope (non-generic classes only).
        // Exclude instances of the class whose method body we are currently
        // generating — calling any method on the same class risks mutual recursion
        // (e.g. method83 calls method84 on Class18, method84 calls method83).
        let current_class = ctx.current_class_sym_id;
        let class_locals: Vec<_> = ctx
            .locals
            .iter()
            .filter_map(|(name, ty, _)| {
                if let TypeInfo::Class(mod_id, sym_id) = ty {
                    if current_class == Some((*mod_id, *sym_id)) {
                        return None;
                    }
                    let sym = ctx.table.get_symbol(*mod_id, *sym_id)?;
                    if let SymbolKind::Class(ref info) = sym.kind {
                        if info.type_params.is_empty() && !info.methods.is_empty() {
                            return Some((name.clone(), *mod_id, *sym_id, info.methods.clone()));
                        }
                    }
                }
                None
            })
            .collect();

        if class_locals.is_empty() {
            return None;
        }

        // Pick a random class-typed local
        let idx = self.rng.gen_range(0..class_locals.len());
        let (instance_name, _mod_id, _sym_id, methods) = &class_locals[idx];

        // Pick a random method, excluding the current method to prevent self-recursion
        let current_name = ctx.current_function_name.as_deref();
        let eligible: Vec<_> = methods
            .iter()
            .filter(|m| Some(m.name.as_str()) != current_name)
            .collect();
        if eligible.is_empty() {
            return None;
        }
        let method = eligible[self.rng.gen_range(0..eligible.len())];

        // Generate type-correct arguments for non-self parameters
        // (occasionally inline when/if expressions via generate_arg_expr)
        let expr_ctx = ctx.to_expr_context();
        let args: Vec<String> = method
            .params
            .iter()
            .map(|p| {
                let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                expr_gen.generate_arg_expr(&p.param_type, &expr_ctx)
            })
            .collect();

        let call_expr = format!("{}.{}({})", instance_name, method.name, args.join(", "));

        // When we're inside a method body (current_class_sym_id is set), calling
        // methods on *other* classes risks cross-class mutual recursion:
        //   ClassA.methodX -> ClassB.methodY -> ClassA.methodZ -> ...
        // Guard such calls with `if false { }` so they're type-checked but never
        // executed at runtime.  Outside of method bodies (free functions, tests),
        // allow the call to run normally.
        let in_method_body = current_class.is_some();

        if in_method_body {
            // Wrap in `if false { ... }` to prevent cross-class mutual recursion
            let indent = "    ".repeat(self.indent + 1);
            let stmt = match &method.return_type {
                TypeInfo::Void => call_expr,
                _ => format!("_ = {}", call_expr),
            };
            Some(format!(
                "if false {{\n{}{}\n{}}}",
                indent,
                stmt,
                "    ".repeat(self.indent)
            ))
        } else {
            // Bind result to a local when the return type is primitive or optional
            match &method.return_type {
                TypeInfo::Primitive(_) | TypeInfo::Optional(_) => {
                    let name = ctx.new_local_name();
                    let ty = method.return_type.clone();
                    ctx.add_local(name.clone(), ty, false);
                    Some(format!("let {} = {}", name, call_expr))
                }
                TypeInfo::Void => {
                    // Void return (including self-returning placeholders) - bare call
                    Some(call_expr)
                }
                _ => {
                    // Other return types - use discard to avoid unused warnings
                    Some(format!("_ = {}", call_expr))
                }
            }
        }
    }

    /// Try to generate an interface-typed local via upcast from a class instance.
    ///
    /// Finds a non-generic interface with methods in the current module that has
    /// at least one implementing class. Constructs the class and assigns it to a
    /// local with the interface type annotation, e.g.:
    ///   `let local5: IFace1 = MyClass { field1: 42_i64 }`
    ///
    /// Returns `None` if no suitable interface/class pair is available.
    fn try_generate_interface_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let module_id = ctx.module_id?;
        let (iface_sym_id, iface_name, _iface_info, class_name, class_info) =
            self.find_implementor_pair(ctx.table, module_id)?;

        let name = ctx.new_local_name();

        // Generate field values for the class construction
        let fields = self.generate_field_values(&class_info.fields, ctx);
        let expr = format!("{} {{ {} }}", class_name, fields);

        // Register as interface-typed (enables vtable dispatch calls later)
        ctx.add_local(
            name.clone(),
            TypeInfo::Interface(module_id, iface_sym_id),
            false,
        );

        let iface_type_str = iface_name;
        Some(format!("let {}: {} = {}", name, iface_type_str, expr))
    }

    /// Try to generate a method call on an interface-typed variable (vtable dispatch).
    ///
    /// Finds interface-typed locals or params in scope, looks up the interface
    /// methods, and generates a call. This exercises the codegen's vtable
    /// dispatch path.
    ///
    /// Generated output shapes:
    /// - `let local6 = ifaceVar.methodName(42_i64)` (primitive return)
    /// - `ifaceVar.methodName(42_i64)` (void return)
    fn try_generate_interface_method_call(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let expr_ctx = ctx.to_expr_context();
        let iface_vars = expr_ctx.interface_typed_vars();
        if iface_vars.is_empty() {
            return None;
        }

        // Pick a random interface-typed variable
        let idx = self.rng.gen_range(0..iface_vars.len());
        let (var_name, mod_id, sym_id) = &iface_vars[idx];

        // Look up the interface to get its methods
        let sym = ctx.table.get_symbol(*mod_id, *sym_id)?;
        let iface_info = match &sym.kind {
            SymbolKind::Interface(info) => info,
            _ => return None,
        };

        // Pick a random method, excluding the current method to prevent self-recursion
        let current_name = ctx.current_function_name.as_deref();
        let eligible: Vec<_> = iface_info
            .methods
            .iter()
            .filter(|m| Some(m.name.as_str()) != current_name)
            .collect();
        if eligible.is_empty() {
            return None;
        }
        let method = eligible[self.rng.gen_range(0..eligible.len())];

        // Generate type-correct arguments (occasionally inline when/if expressions)
        let args: Vec<String> = method
            .params
            .iter()
            .map(|p| {
                let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                expr_gen.generate_arg_expr(&p.param_type, &expr_ctx)
            })
            .collect();

        let call_expr = format!("{}.{}({})", var_name, method.name, args.join(", "));

        // When inside a method body, interface vtable dispatch can cause
        // cross-class mutual recursion (the implementing class's method may
        // call back into the current class).  Guard with `if false`.
        let in_method_body = ctx.current_class_sym_id.is_some();

        if in_method_body {
            let indent = "    ".repeat(self.indent + 1);
            let stmt = match &method.return_type {
                TypeInfo::Void => call_expr,
                _ => format!("_ = {}", call_expr),
            };
            Some(format!(
                "if false {{\n{}{}\n{}}}",
                indent,
                stmt,
                "    ".repeat(self.indent)
            ))
        } else {
            // Bind result to a local when the return type is primitive or optional
            match &method.return_type {
                TypeInfo::Primitive(_) | TypeInfo::Optional(_) => {
                    let name = ctx.new_local_name();
                    let ty = method.return_type.clone();
                    ctx.add_local(name.clone(), ty, false);
                    Some(format!("let {} = {}", name, call_expr))
                }
                TypeInfo::Void => Some(call_expr),
                _ => Some(format!("_ = {}", call_expr)),
            }
        }
    }

    /// Try to generate a call to a free function that has an interface-typed parameter.
    ///
    /// Finds non-generic functions in the current module that have at least one
    /// `TypeInfo::Interface` parameter, picks one, and generates a call with
    /// all arguments (constructing a class instance for interface-typed params).
    /// This exercises the codegen path where a concrete class is implicitly
    /// upcast to an interface type at the call site.
    ///
    /// Generated output shapes:
    /// - `let local7 = funcName(42_i64, ClassName { field1: 1_i64 })` (non-void return)
    /// - `funcName(42_i64, ClassName { field1: 1_i64 })` (void return)
    fn try_generate_iface_function_call(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let module_id = ctx.module_id?;
        let module = ctx.table.get_module(module_id)?;

        // When generating a method body for a class, collect the interfaces
        // that the class implements.  We must avoid calling any free function
        // that accepts one of these interfaces as a parameter, because the
        // function's body may dispatch a method call on that interface back to
        // the current class, creating mutual recursion at runtime.
        // E.g. Class18.method81 -> func35(IFace12) -> ifaceParam.method81() -> ...
        let current_class_ifaces: Vec<(ModuleId, SymbolId)> =
            if let Some((cls_mod, cls_sym)) = ctx.current_class_sym_id {
                ctx.table
                    .get_symbol(cls_mod, cls_sym)
                    .and_then(|s| match &s.kind {
                        SymbolKind::Class(info) => Some(info.implements.clone()),
                        _ => None,
                    })
                    .unwrap_or_default()
            } else {
                Vec::new()
            };

        // Collect non-generic functions with at least one interface-typed param
        let current_fn_sym_id = ctx.current_function_sym_id;
        let candidates: Vec<(String, Vec<ParamInfo>, TypeInfo)> = module
            .functions()
            .filter_map(|s| {
                if let SymbolKind::Function(ref info) = s.kind {
                    if info.type_params.is_empty()
                        && !matches!(info.return_type, TypeInfo::Never)
                        && info
                            .params
                            .iter()
                            .any(|p| p.param_type.contains_interface())
                        && Some(s.name.as_str()) != ctx.current_function_name.as_deref()
                    {
                        // When inside a free function body, only call functions
                        // with a lower symbol ID to prevent mutual recursion.
                        if let Some(cur_id) = current_fn_sym_id {
                            if s.id.0 >= cur_id.0 {
                                return None;
                            }
                        }

                        // When inside a method body, skip functions whose
                        // interface-typed params overlap with the current
                        // class's implemented interfaces (prevents cross-
                        // function/method mutual recursion).
                        if !current_class_ifaces.is_empty() {
                            let mut func_ifaces = Vec::new();
                            for p in &info.params {
                                p.param_type.collect_interface_ids(&mut func_ifaces);
                            }
                            if func_ifaces
                                .iter()
                                .any(|id| current_class_ifaces.contains(id))
                            {
                                return None;
                            }
                        }

                        Some((
                            s.name.clone(),
                            info.params.clone(),
                            info.return_type.clone(),
                        ))
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (func_name, params, return_type) = &candidates[idx];

        // Generate arguments for each parameter
        let expr_ctx = ctx.to_expr_context();
        let args: Vec<String> = params
            .iter()
            .map(|p| {
                let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                expr_gen.generate_arg_expr(&p.param_type, &expr_ctx)
            })
            .collect();

        let call_expr = format!("{}({})", func_name, args.join(", "));

        // When inside a method body, the called free function's body may
        // construct an instance of the current class and call methods on it,
        // creating mutual recursion:
        //   ClassA.methodX -> func20(IFace) -> ClassA.methodY -> func20(IFace) -> ...
        // Guard such calls with `if false { }` so they're type-checked but
        // never executed at runtime.
        let in_method_body = ctx.current_class_sym_id.is_some();

        if in_method_body {
            let indent = "    ".repeat(self.indent + 1);
            let stmt = match return_type {
                TypeInfo::Void => call_expr,
                _ => format!("_ = {}", call_expr),
            };
            Some(format!(
                "if false {{\n{}{}\n{}}}",
                indent,
                stmt,
                "    ".repeat(self.indent)
            ))
        } else {
            // Outside method bodies, allow the call to run normally
            match return_type {
                TypeInfo::Void => Some(call_expr),
                TypeInfo::Primitive(_) | TypeInfo::Optional(_) => {
                    let name = ctx.new_local_name();
                    let ty = return_type.clone();
                    ctx.add_local(name.clone(), ty, false);
                    Some(format!("let {} = {}", name, call_expr))
                }
                _ => Some(format!("_ = {}", call_expr)),
            }
        }
    }

    /// Find a (interface, implementing class) pair in a module.
    ///
    /// Returns `(iface_sym_id, iface_name, iface_info, class_name, class_info)` for a
    /// randomly chosen non-generic interface that has at least one implementing class.
    fn find_implementor_pair(
        &mut self,
        table: &SymbolTable,
        module_id: ModuleId,
    ) -> Option<(SymbolId, String, InterfaceInfo, String, ClassInfo)> {
        let module = table.get_module(module_id)?;

        // Collect (iface_sym_id, iface_name, iface_info, class_name, class_info) candidates
        let mut candidates: Vec<(SymbolId, String, InterfaceInfo, String, ClassInfo)> = Vec::new();

        for iface_sym in module.interfaces() {
            let iface_info = match &iface_sym.kind {
                SymbolKind::Interface(info)
                    if info.type_params.is_empty() && !info.methods.is_empty() =>
                {
                    info
                }
                _ => continue,
            };

            // Find a non-generic class implementing this interface
            for class_sym in module.classes() {
                if let SymbolKind::Class(ref class_info) = class_sym.kind {
                    if class_info.type_params.is_empty()
                        && class_info
                            .implements
                            .iter()
                            .any(|&(m, s)| m == module_id && s == iface_sym.id)
                    {
                        candidates.push((
                            iface_sym.id,
                            iface_sym.name.clone(),
                            iface_info.clone(),
                            class_sym.name.clone(),
                            class_info.clone(),
                        ));
                    }
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        Some(candidates.swap_remove(idx))
    }

    /// Try to generate a let statement that constructs a struct instance.
    ///
    /// Returns `None` if no suitable struct is available in the current module.
    /// Structs are value types with primitive fields, making them simpler than classes.
    fn try_generate_struct_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let module_id = ctx.module_id?;
        let module = ctx.table.get_module(module_id)?;

        // Collect structs from this module
        let candidates: Vec<_> = module
            .structs()
            .filter_map(|sym| {
                if let SymbolKind::Struct(ref info) = sym.kind {
                    Some((sym.id, sym.name.clone(), info.clone()))
                } else {
                    None
                }
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (sym_id, struct_name, struct_info) = &candidates[idx];

        let name = ctx.new_local_name();
        let ty = TypeInfo::Struct(module_id, *sym_id);

        // Try using a static method call if available
        if !struct_info.static_methods.is_empty()
            && self.rng.gen_bool(self.config.static_call_probability)
        {
            let expr = self.generate_static_call(struct_name, &struct_info.static_methods, ctx);
            ctx.add_local(name.clone(), ty, false);
            return Some(format!("let {} = {}", name, expr));
        }

        // Generate field values for construction BEFORE adding to scope
        // to avoid self-referential field initializers
        let fields = self.generate_field_values(&struct_info.fields, ctx);

        // Add to scope AFTER generating field values
        ctx.add_local(name.clone(), ty, false);

        Some(format!("let {} = {} {{ {} }}", name, struct_name, fields))
    }

    /// Try to generate a struct destructuring statement.
    ///
    /// Looks for struct-typed variables in scope and generates destructuring:
    /// ```vole
    /// let { field1, field2 } = structVar
    /// ```
    /// Adds each destructured field as a new local variable with its field type.
    ///
    /// Returns `None` if no struct-typed variable is in scope.
    fn try_generate_struct_destructure(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Ensure we're in a module context
        let _ = ctx.module_id?;

        // Find struct-typed variables in locals
        let struct_locals: Vec<_> = ctx
            .locals
            .iter()
            .filter_map(|(name, ty, _)| {
                if let TypeInfo::Struct(mod_id, sym_id) = ty {
                    Some((name.clone(), *mod_id, *sym_id))
                } else {
                    None
                }
            })
            .collect();

        // Also check params for struct types
        let struct_params: Vec<_> = ctx
            .params
            .iter()
            .filter_map(|p| {
                if let TypeInfo::Struct(mod_id, sym_id) = &p.param_type {
                    Some((p.name.clone(), *mod_id, *sym_id))
                } else {
                    None
                }
            })
            .collect();

        let all_structs: Vec<_> = struct_locals.into_iter().chain(struct_params).collect();

        if all_structs.is_empty() {
            return None;
        }

        // Pick a random struct-typed variable
        let idx = self.rng.gen_range(0..all_structs.len());
        let (var_name, struct_mod_id, struct_sym_id) = &all_structs[idx];

        // Get the struct info to find field names and types
        let symbol = ctx.table.get_symbol(*struct_mod_id, *struct_sym_id)?;
        let struct_info = match &symbol.kind {
            SymbolKind::Struct(info) => info,
            _ => return None,
        };

        if struct_info.fields.is_empty() {
            return None;
        }

        // Decide whether to do full or partial destructuring
        let do_partial = self.rng.gen_bool(0.3);
        let fields_to_destruct = if do_partial && struct_info.fields.len() > 1 {
            // Partial: pick a random subset (at least 1 field)
            let count = self.rng.gen_range(1..struct_info.fields.len());
            let mut indices: Vec<usize> = (0..struct_info.fields.len()).collect();
            // Shuffle and take first `count`
            for i in (1..indices.len()).rev() {
                let j = self.rng.gen_range(0..=i);
                indices.swap(i, j);
            }
            indices.truncate(count);
            indices.sort(); // Keep original order for readability
            indices
        } else {
            // Full destructuring
            (0..struct_info.fields.len()).collect()
        };

        // Build the pattern and collect new locals.
        // We always use the renamed syntax (field: binding) to avoid name collisions
        // with other variables in scope.
        let mut pattern_parts = Vec::new();
        for &field_idx in &fields_to_destruct {
            let field = &struct_info.fields[field_idx];
            let new_name = ctx.new_local_name();
            pattern_parts.push(format!("{}: {}", field.name, new_name));
            ctx.add_local(new_name, field.field_type.clone(), false);
        }

        let pattern = format!("{{ {} }}", pattern_parts.join(", "));
        Some(format!("let {} = {}", pattern, var_name))
    }

    /// Try to generate a class destructuring statement.
    ///
    /// Looks for class-typed variables in scope and generates destructuring:
    /// ```vole
    /// let { field1: local1, field2: local2 } = classVar
    /// ```
    /// Adds each destructured field as a new local variable with its field type.
    /// Only non-generic classes with at least one primitive field are considered.
    ///
    /// Returns `None` if no class-typed variable is in scope.
    fn try_generate_class_destructure(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Ensure we're in a module context
        let _ = ctx.module_id?;

        // Find class-typed variables in locals
        let class_locals: Vec<_> = ctx
            .locals
            .iter()
            .filter_map(|(name, ty, _)| {
                if let TypeInfo::Class(mod_id, sym_id) = ty {
                    Some((name.clone(), *mod_id, *sym_id))
                } else {
                    None
                }
            })
            .collect();

        // Also check params for class types
        let class_params: Vec<_> = ctx
            .params
            .iter()
            .filter_map(|p| {
                if let TypeInfo::Class(mod_id, sym_id) = &p.param_type {
                    Some((p.name.clone(), *mod_id, *sym_id))
                } else {
                    None
                }
            })
            .collect();

        let all_classes: Vec<_> = class_locals.into_iter().chain(class_params).collect();

        if all_classes.is_empty() {
            return None;
        }

        // Pick a random class-typed variable
        let idx = self.rng.gen_range(0..all_classes.len());
        let (var_name, class_mod_id, class_sym_id) = &all_classes[idx];

        // Get the class info to find field names and types
        let symbol = ctx.table.get_symbol(*class_mod_id, *class_sym_id)?;
        let class_info = match &symbol.kind {
            SymbolKind::Class(info) => info,
            _ => return None,
        };

        // Only destructure non-generic classes with primitive fields
        if !class_info.type_params.is_empty() {
            return None;
        }

        // Filter to primitive-typed fields only (class/interface fields can't
        // be destructured as simply)
        let primitive_fields: Vec<usize> = class_info
            .fields
            .iter()
            .enumerate()
            .filter(|(_, f)| f.field_type.is_primitive())
            .map(|(i, _)| i)
            .collect();

        if primitive_fields.is_empty() {
            return None;
        }

        // Decide whether to do full or partial destructuring
        let do_partial = self.rng.gen_bool(0.3);
        let fields_to_destruct = if do_partial && primitive_fields.len() > 1 {
            // Partial: pick a random subset (at least 1 field)
            let count = self.rng.gen_range(1..primitive_fields.len());
            let mut indices = primitive_fields.clone();
            // Shuffle and take first `count`
            for i in (1..indices.len()).rev() {
                let j = self.rng.gen_range(0..=i);
                indices.swap(i, j);
            }
            indices.truncate(count);
            indices.sort(); // Keep original order for readability
            indices
        } else {
            // Full destructuring (of primitive fields)
            primitive_fields
        };

        // Build the pattern and collect new locals.
        // We always use the renamed syntax (field: binding) to avoid name collisions
        // with other variables in scope.
        let mut pattern_parts = Vec::new();
        for &field_idx in &fields_to_destruct {
            let field = &class_info.fields[field_idx];
            let new_name = ctx.new_local_name();
            pattern_parts.push(format!("{}: {}", field.name, new_name));
            ctx.add_local(new_name, field.field_type.clone(), false);
        }

        let pattern = format!("{{ {} }}", pattern_parts.join(", "));
        Some(format!("let {} = {}", pattern, var_name))
    }

    /// Try to generate a struct copy statement.
    ///
    /// Looks for struct-typed variables in scope and generates a copy:
    /// ```vole
    /// let copy = structVar
    /// ```
    /// This exercises struct value-type copy semantics.
    ///
    /// Returns `None` if no struct-typed variable is in scope.
    fn try_generate_struct_copy(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find struct-typed variables in locals
        let struct_locals: Vec<_> = ctx
            .locals
            .iter()
            .filter_map(|(name, ty, _)| {
                if let TypeInfo::Struct(_mod_id, _sym_id) = ty {
                    Some((name.clone(), ty.clone()))
                } else {
                    None
                }
            })
            .collect();

        // Also check params for struct types
        let struct_params: Vec<_> = ctx
            .params
            .iter()
            .filter_map(|p| {
                if matches!(&p.param_type, TypeInfo::Struct(_, _)) {
                    Some((p.name.clone(), p.param_type.clone()))
                } else {
                    None
                }
            })
            .collect();

        let all_structs: Vec<_> = struct_locals.into_iter().chain(struct_params).collect();

        if all_structs.is_empty() {
            return None;
        }

        // Pick a random struct-typed variable
        let idx = self.rng.gen_range(0..all_structs.len());
        let (var_name, struct_type) = &all_structs[idx];

        // Create a new variable name for the copy
        let copy_name = ctx.new_local_name();
        ctx.add_local(copy_name.clone(), struct_type.clone(), false);

        Some(format!("let {} = {}", copy_name, var_name))
    }

    /// Generate a static method call on a type (class or struct).
    ///
    /// Returns something like `TypeName.staticMethod(arg1, arg2)`.
    fn generate_static_call(
        &mut self,
        type_name: &str,
        static_methods: &[StaticMethodInfo],
        ctx: &mut StmtContext,
    ) -> String {
        // Pick a random static method
        let idx = self.rng.gen_range(0..static_methods.len());
        let static_method = &static_methods[idx];

        // Generate arguments for the static method (occasionally inline when/if expressions)
        let expr_ctx = ctx.to_expr_context();
        let args: Vec<String> = static_method
            .params
            .iter()
            .map(|p| {
                let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                expr_gen.generate_arg_expr(&p.param_type, &expr_ctx)
            })
            .collect();

        format!("{}.{}({})", type_name, static_method.name, args.join(", "))
    }

    /// Try to generate a standalone static method call statement.
    ///
    /// Searches the current module for classes or structs with static methods
    /// and generates `let localN = TypeName.staticMethod(args)`.
    ///
    /// Returns `None` if no type with static methods is available.
    fn try_generate_static_call_statement(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let module_id = ctx.module_id?;
        let module = ctx.table.get_module(module_id)?;

        // Collect all types with static methods: (sym_id, name, statics, type_info_fn)
        let mut candidates: Vec<(SymbolId, String, Vec<StaticMethodInfo>, bool)> = Vec::new();

        // Classes: non-generic with primitive fields and static methods
        for sym in module.classes() {
            if let SymbolKind::Class(ref info) = sym.kind {
                if info.type_params.is_empty()
                    && has_primitive_field(info)
                    && !info.static_methods.is_empty()
                {
                    // is_class = true
                    candidates.push((sym.id, sym.name.clone(), info.static_methods.clone(), true));
                }
            }
        }

        // Structs with static methods
        for sym in module.structs() {
            if let SymbolKind::Struct(ref info) = sym.kind {
                if !info.static_methods.is_empty() {
                    // is_class = false
                    candidates.push((sym.id, sym.name.clone(), info.static_methods.clone(), false));
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (sym_id, type_name, static_methods, is_class) = &candidates[idx];

        let name = ctx.new_local_name();
        let ty = if *is_class {
            TypeInfo::Class(module_id, *sym_id)
        } else {
            TypeInfo::Struct(module_id, *sym_id)
        };

        let expr = self.generate_static_call(type_name, static_methods, ctx);
        ctx.add_local(name.clone(), ty, false);

        Some(format!("let {} = {}", name, expr))
    }

    /// Try to generate a method chain for a class instance.
    ///
    /// Returns a string like `.selfMethod(args).selfMethod2(args)` or empty string
    /// if no chaining is done.
    fn try_generate_method_chain(
        &mut self,
        table: &SymbolTable,
        mod_id: ModuleId,
        class_id: SymbolId,
        ctx: &mut StmtContext,
    ) -> String {
        // Get chainable methods for this class
        let methods = get_chainable_methods(table, mod_id, class_id);

        // Filter to Self-returning methods, excluding the current method to prevent
        // infinite recursion (e.g. selfMethod6 chaining back to selfMethod6).
        let current_name = ctx.current_function_name.as_deref();
        let self_returning: Vec<_> = methods
            .iter()
            .filter(|m| m.returns_self && Some(m.name.as_str()) != current_name)
            .collect();
        if self_returning.is_empty() {
            return String::new();
        }

        // Probabilistically decide whether to chain
        if !self
            .rng
            .gen_bool(self.config.expr_config.method_chain_probability)
        {
            return String::new();
        }

        let expr_ctx = ctx.to_expr_context();
        let mut chain = String::new();
        let max_depth = self.config.expr_config.max_chain_depth;
        let mut depth = 0;

        while depth < max_depth {
            // Pick a random Self-returning method
            let method_idx = self.rng.gen_range(0..self_returning.len());
            let method = self_returning[method_idx];

            // Generate arguments for the method call (occasionally inline when/if)
            let args: Vec<String> = method
                .params
                .iter()
                .map(|p| {
                    let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                    expr_gen.generate_arg_expr(&p.param_type, &expr_ctx)
                })
                .collect();

            chain.push_str(&format!(".{}({})", method.name, args.join(", ")));
            depth += 1;

            // Probabilistically stop chaining
            if !self
                .rng
                .gen_bool(self.config.expr_config.method_chain_probability)
            {
                break;
            }
        }

        chain
    }

    /// Generate field value expressions for class construction.
    fn generate_field_values(
        &mut self,
        fields: &[crate::symbols::FieldInfo],
        ctx: &mut StmtContext,
    ) -> String {
        let expr_ctx = ctx.to_expr_context();
        fields
            .iter()
            .map(|f| {
                let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                let value = expr_gen.generate(&f.field_type, &expr_ctx, 0);
                format!("{}: {}", f.name, value)
            })
            .collect::<Vec<_>>()
            .join(", ")
    }

    /// Generate a random primitive type.
    ///
    /// Uses the same distribution as `PrimitiveType::random_expr_type()`:
    /// core types ~90%, wider types ~10%.
    fn random_primitive_type(&mut self) -> TypeInfo {
        TypeInfo::Primitive(PrimitiveType::random_expr_type(self.rng))
    }

    /// Generate a random return type for lambdas.
    ///
    /// Now uses the full random_primitive_type distribution since the
    /// cross-module lambda codegen bug (vol-pz4y) has been fixed.
    fn random_lambda_return_type(&mut self) -> TypeInfo {
        self.random_primitive_type()
    }

    /// Set the indentation level.
    pub fn set_indent(&mut self, indent: usize) {
        self.indent = indent;
    }

    /// Generate a random usize in the given range.
    pub fn gen_range_usize(&mut self, range: std::ops::Range<usize>) -> usize {
        self.rng.gen_range(range)
    }

    /// Generate a generator function body with a while loop and yield statements.
    ///
    /// Produces a bounded loop pattern:
    /// ```vole
    /// let mut i = 0
    /// while i < N {
    ///     yield <expr>
    ///     i = i + 1
    /// }
    /// ```
    /// where N is a small random limit (2-5) and `<expr>` is a simple expression
    /// of the element type.
    pub fn generate_generator_body(
        &mut self,
        elem_type: &TypeInfo,
        ctx: &StmtContext,
    ) -> Vec<String> {
        let mut lines = Vec::new();
        let limit = self.rng.gen_range(2..=5);

        // Initialize counter
        lines.push("let mut _gi = 0".to_string());

        // Generate the yield expression.
        // IMPORTANT: Use an empty context (no params, no locals) because the vole
        // compiler does not support referencing function parameters inside generator
        // yield expressions (compiler bug: params are lost during state machine
        // transformation). Only literals are safe here.
        let empty_expr_ctx = ExprContext::new(&[], &[], ctx.table);
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let yield_expr = expr_gen.generate_simple(elem_type, &empty_expr_ctx);

        // Build the while loop with yield
        let indent = "    ".repeat(self.indent + 1);
        lines.push(format!("while _gi < {} {{", limit));
        lines.push(format!("{}yield {}", indent, yield_expr));
        lines.push(format!("{}_gi = _gi + 1", indent));
        lines.push("}".to_string());

        lines
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;

    #[test]
    fn test_let_statement() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = StmtConfig::default();
        let mut generator = StmtGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let mut ctx = StmtContext::new(&[], &table);

        let stmt = generator.generate_let_statement(&mut ctx);
        assert!(stmt.starts_with("let "));
    }

    #[test]
    fn test_body_generation() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = StmtConfig::default();
        let mut generator = StmtGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let mut ctx = StmtContext::new(&[], &table);

        let lines = generator.generate_body(&TypeInfo::Primitive(PrimitiveType::I64), &mut ctx, 0);
        assert!(!lines.is_empty());
        // Should end with return
        assert!(lines.last().unwrap().starts_with("return "));
    }

    #[test]
    fn test_if_statement() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = StmtConfig::default();
        let mut generator = StmtGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let mut ctx = StmtContext::new(&[], &table);

        let stmt = generator.generate_if_statement(&mut ctx, 0);
        assert!(stmt.starts_with("if "));
    }

    #[test]
    fn test_for_statement() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = StmtConfig::default();
        let mut generator = StmtGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let mut ctx = StmtContext::new(&[], &table);

        let stmt = generator.generate_for_statement(&mut ctx, 0);
        assert!(stmt.contains("for "));
        assert!(stmt.contains("in "));
    }

    #[test]
    fn test_for_statement_both_range_syntaxes() {
        let table = SymbolTable::new();
        let config = StmtConfig::default();

        let mut found_exclusive = false;
        let mut found_inclusive = false;
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::new(&[], &table);

            let stmt = generator.generate_for_statement(&mut ctx, 0);
            assert!(stmt.contains("for "), "Should contain 'for': {}", stmt);
            assert!(stmt.contains("in "), "Should contain 'in': {}", stmt);

            if stmt.contains("..=") {
                found_inclusive = true;
            } else if stmt.contains("..") {
                found_exclusive = true;
            }

            if found_exclusive && found_inclusive {
                break;
            }
        }
        assert!(
            found_exclusive,
            "Expected exclusive range syntax (a..b) across 500 seeds",
        );
        assert!(
            found_inclusive,
            "Expected inclusive range syntax (a..=b) across 500 seeds",
        );
    }

    #[test]
    fn test_for_statement_variable_bound() {
        let table = SymbolTable::new();
        let config = StmtConfig::default();

        let mut found_var_bound = false;
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::new(&[], &table);

            // Add an i64 local marked as protected (simulating a while-loop counter)
            // so it can be used as a variable bound in for-loop ranges.
            // Only protected i64 locals are eligible as range bounds since they
            // are guaranteed to hold small values.
            ctx.add_local(
                "n".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
                false,
            );
            ctx.protected_vars.push("n".to_string());

            let stmt = generator.generate_for_statement(&mut ctx, 0);
            // Check if the range uses the variable name "n" as a bound
            // (either directly or in an expression like (n + 1))
            if stmt.contains("..n")
                || stmt.contains("..=n")
                || stmt.contains("..(n")
                || stmt.contains("..=(n")
            {
                found_var_bound = true;
                break;
            }
        }
        assert!(
            found_var_bound,
            "Expected variable bound in for-loop range across 500 seeds",
        );
    }

    #[test]
    fn test_for_statement_expression_bound() {
        let table = SymbolTable::new();
        let config = StmtConfig::default();

        let mut found_expr_bound = false;
        let mut found_start_expr = false;
        for seed in 0..2000 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::new(&[], &table);

            ctx.add_local(
                "n".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
                false,
            );
            ctx.protected_vars.push("n".to_string());

            let stmt = generator.generate_for_statement(&mut ctx, 0);
            // Check for arithmetic expression bounds like (n + 1), (n - 1), (n * 2)
            if stmt.contains("(n +") || stmt.contains("(n -") || stmt.contains("(n *") {
                found_expr_bound = true;
            }
            // Check for expression as start bound (before the ..)
            if let Some(in_pos) = stmt.find("in ") {
                let after_in = &stmt[in_pos + 3..];
                if after_in.starts_with('(') || after_in.starts_with('n') {
                    found_start_expr = true;
                }
            }

            if found_expr_bound && found_start_expr {
                break;
            }
        }
        assert!(
            found_expr_bound,
            "Expected arithmetic expression bound (e.g., (n + 1)) in for-loop range across 2000 seeds",
        );
        assert!(
            found_start_expr,
            "Expected variable/expression as start bound in for-loop range across 2000 seeds",
        );
    }

    #[test]
    fn test_compound_assignment() {
        let table = SymbolTable::new();
        let compound_ops = ["+=", "-=", "*="];
        let mut found = std::collections::HashSet::new();

        // Generate across many seeds to find compound assignments
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let config = StmtConfig::default();
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::new(&[], &table);

            // Pre-populate with a mutable numeric local so compound assign can fire
            ctx.add_local(
                "x".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
                true,
            );

            let stmt = generator.generate_statement(&mut ctx, 0);
            for op in &compound_ops {
                if stmt.contains(op) {
                    found.insert(*op);
                }
            }
        }

        // We should find at least all three compound operators across 500 seeds
        assert!(
            found.len() >= 3,
            "Expected all 3 compound ops, found: {:?}",
            found,
        );
    }

    #[test]
    fn test_compound_assignment_respects_type() {
        let table = SymbolTable::new();

        for seed in 0..200 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let config = StmtConfig::default();
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::new(&[], &table);

            // Add mutable locals of different numeric types
            ctx.add_local(
                "xi32".to_string(),
                TypeInfo::Primitive(PrimitiveType::I32),
                true,
            );
            ctx.add_local(
                "xf64".to_string(),
                TypeInfo::Primitive(PrimitiveType::F64),
                true,
            );

            let stmt = generator.generate_compound_assignment(&mut ctx);

            // The RHS suffix should match the variable's type
            if stmt.starts_with("xi32") {
                assert!(
                    stmt.contains("_i32"),
                    "i32 compound assign should have _i32 suffix: {}",
                    stmt,
                );
            } else if stmt.starts_with("xf64") {
                assert!(
                    stmt.contains("_f64"),
                    "f64 compound assign should have _f64 suffix: {}",
                    stmt,
                );
            }
        }
    }

    #[test]
    fn test_compound_assignment_not_generated_without_mutable_numeric() {
        let table = SymbolTable::new();
        // Use a config that disables control flow (which can create mutable
        // numeric locals like while-loop counters) to isolate the test
        let config = StmtConfig {
            if_probability: 0.0,
            while_probability: 0.0,
            for_probability: 0.0,
            break_continue_probability: 0.0,
            compound_assign_probability: 0.15,
            ..StmtConfig::default()
        };

        // With no locals at all, compound assignment should never appear
        for seed in 0..100 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::new(&[], &table);

            let stmt = generator.generate_statement(&mut ctx, 0);
            assert!(
                !stmt.contains("+=") && !stmt.contains("-=") && !stmt.contains("*="),
                "Compound assign should not appear without mutable numeric locals: {}",
                stmt,
            );
        }
    }

    #[test]
    fn test_array_let_generation() {
        let table = SymbolTable::new();
        let config = StmtConfig::default();

        let mut found_array_let = false;
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::new(&[], &table);

            let stmt = generator.generate_let_statement(&mut ctx);
            let last_local = match ctx.locals.last() {
                Some(l) => l,
                None => continue,
            };
            if matches!(last_local.1, TypeInfo::Array(_)) {
                // Verify it looks like an array literal: let localN = [elem1, elem2, ...]
                assert!(
                    stmt.starts_with("let ") && stmt.contains("= ["),
                    "Array let should contain '= [', got: {}",
                    stmt,
                );
                found_array_let = true;
                break;
            }
        }
        assert!(
            found_array_let,
            "Expected at least one array let statement across 500 seeds",
        );
    }

    #[test]
    fn test_array_let_has_sufficient_elements() {
        let table = SymbolTable::new();
        let config = StmtConfig::default();

        // Generate array lets and verify they have 2-4 elements
        for seed in 0..200 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::new(&[], &table);

            let stmt = generator.generate_array_let(&mut ctx);
            assert!(
                stmt.starts_with("let "),
                "Should start with 'let ': {}",
                stmt
            );
            assert!(stmt.contains("= ["), "Should contain '= [': {}", stmt);

            // Count commas to determine element count (N elements = N-1 commas)
            let bracket_start = stmt.find('[').unwrap();
            let bracket_end = stmt.rfind(']').unwrap();
            let inner = &stmt[bracket_start + 1..bracket_end];
            let comma_count = inner.matches(',').count();
            // 2-4 elements means 1-3 commas
            assert!(
                comma_count >= 1 && comma_count <= 3,
                "Expected 2-4 elements (1-3 commas), got {} commas in: {}",
                comma_count,
                stmt,
            );
        }
    }

    #[test]
    fn test_determinism() {
        let config = StmtConfig::default();
        let table = SymbolTable::new();

        let mut rng1 = rand::rngs::StdRng::seed_from_u64(12345);
        let mut gen1 = StmtGenerator::new(&mut rng1, &config);
        let mut ctx1 = StmtContext::new(&[], &table);
        let lines1 = gen1.generate_body(&TypeInfo::Primitive(PrimitiveType::I64), &mut ctx1, 0);

        let mut rng2 = rand::rngs::StdRng::seed_from_u64(12345);
        let mut gen2 = StmtGenerator::new(&mut rng2, &config);
        let mut ctx2 = StmtContext::new(&[], &table);
        let lines2 = gen2.generate_body(&TypeInfo::Primitive(PrimitiveType::I64), &mut ctx2, 0);

        assert_eq!(lines1, lines2);
    }

    #[test]
    fn test_discard_statement_generation() {
        // Set up a symbol table with a module containing a non-generic,
        // non-void-returning function that can be used for discard statements.
        let mut table = SymbolTable::new();
        let module_id = table.add_module("test_mod".to_string(), "test_mod.vole".to_string());

        // Add a function that returns i64 (suitable for discarding)
        {
            let module = table.get_module_mut(module_id).unwrap();
            module.add_symbol(
                "discardable_func".to_string(),
                SymbolKind::Function(FunctionInfo {
                    type_params: vec![],
                    params: vec![ParamInfo {
                        name: "x".to_string(),
                        param_type: TypeInfo::Primitive(PrimitiveType::I64),
                    }],
                    return_type: TypeInfo::Primitive(PrimitiveType::I64),
                }),
            );
        }

        // Use a config with high discard probability to trigger the feature
        let config = StmtConfig {
            discard_probability: 0.99, // Very high to ensure it triggers
            if_probability: 0.0,
            while_probability: 0.0,
            for_probability: 0.0,
            break_continue_probability: 0.0,
            compound_assign_probability: 0.0,
            raise_probability: 0.0,
            try_probability: 0.0,
            tuple_probability: 0.0,
            fixed_array_probability: 0.0,
            ..StmtConfig::default()
        };

        let mut found_discard = false;
        for seed in 0..100 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::with_module(&[], &table, module_id);

            let stmt = generator.generate_statement(&mut ctx, 0);

            // Check if this statement contains a discard pattern
            // Discards are wrapped in: if <cond> { _ = func(...) }
            if stmt.contains("_ = discardable_func") {
                found_discard = true;
                // Verify the format: should be wrapped in an if block
                assert!(
                    stmt.starts_with("if "),
                    "Discard should be wrapped in if: {}",
                    stmt
                );
                assert!(
                    stmt.contains("_ = discardable_func("),
                    "Should contain discard call: {}",
                    stmt
                );
                break;
            }
        }
        assert!(
            found_discard,
            "Expected at least one discard statement across 100 seeds"
        );
    }

    #[test]
    fn test_discard_statement_not_generated_without_functions() {
        // Without any functions in the module, discard statements should not be generated
        let mut table = SymbolTable::new();
        let module_id = table.add_module("empty_mod".to_string(), "empty_mod.vole".to_string());

        let config = StmtConfig {
            discard_probability: 0.99,
            if_probability: 0.0,
            while_probability: 0.0,
            for_probability: 0.0,
            ..StmtConfig::default()
        };

        for seed in 0..50 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::with_module(&[], &table, module_id);

            let stmt = generator.generate_statement(&mut ctx, 0);

            // Should not contain discard pattern since there are no functions
            assert!(
                !stmt.contains("_ =") || stmt.contains("_ =>"),
                "Discard should not appear without callable functions: {}",
                stmt
            );
        }
    }

    #[test]
    fn test_early_return_generation() {
        let table = SymbolTable::new();

        // Use a config with high early_return_probability to ensure it triggers
        let config = StmtConfig {
            early_return_probability: 0.99,
            if_probability: 0.0,
            while_probability: 0.0,
            for_probability: 0.0,
            ..StmtConfig::default()
        };

        let mut found_early_return = false;
        for seed in 0..100 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::new(&[], &table);

            let lines =
                generator.generate_body(&TypeInfo::Primitive(PrimitiveType::I64), &mut ctx, 0);

            // Check if there's an early return (if block containing return before the final return)
            let return_count = lines.iter().filter(|l| l.contains("return ")).count();
            if return_count >= 2 {
                // Should have an "if" block with a return inside it
                let has_if_with_return = lines.iter().any(|l| l.starts_with("if "));
                if has_if_with_return {
                    found_early_return = true;
                    break;
                }
            }
        }
        assert!(
            found_early_return,
            "Expected at least one early return in if block across 100 seeds"
        );
    }

    #[test]
    fn test_early_return_not_generated_for_void() {
        let table = SymbolTable::new();

        let config = StmtConfig {
            early_return_probability: 0.99,
            if_probability: 0.0,
            while_probability: 0.0,
            for_probability: 0.0,
            ..StmtConfig::default()
        };

        for seed in 0..50 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::new(&[], &table);

            let lines = generator.generate_body(&TypeInfo::Void, &mut ctx, 0);

            // Void functions should not have any return statements
            assert!(
                !lines.iter().any(|l| l.contains("return ")),
                "Void functions should not have return statements: {:?}",
                lines
            );
        }
    }

    #[test]
    fn test_early_return_disabled_when_probability_zero() {
        let table = SymbolTable::new();

        let config = StmtConfig {
            early_return_probability: 0.0,
            if_probability: 0.0,
            while_probability: 0.0,
            for_probability: 0.0,
            nested_loop_probability: 0.0,
            ..StmtConfig::default()
        };

        for seed in 0..100 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::new(&[], &table);

            let lines =
                generator.generate_body(&TypeInfo::Primitive(PrimitiveType::I64), &mut ctx, 0);

            // Should have exactly one return statement (the final one)
            let return_count = lines.iter().filter(|l| l.contains("return ")).count();
            assert_eq!(
                return_count, 1,
                "With early_return_probability=0.0, should have exactly 1 return: {:?}",
                lines
            );
        }
    }

    #[test]
    fn test_else_if_chain_generation() {
        let table = SymbolTable::new();

        // Use a config with high else_if_probability to ensure it triggers
        let config = StmtConfig {
            if_probability: 0.99,
            else_if_probability: 0.99,
            while_probability: 0.0,
            for_probability: 0.0,
            break_continue_probability: 0.0,
            compound_assign_probability: 0.0,
            ..StmtConfig::default()
        };

        let mut found_else_if = false;
        for seed in 0..200 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::new(&[], &table);

            let stmt = generator.generate_statement(&mut ctx, 0);

            // Check for else-if pattern: "} else if"
            if stmt.contains("} else if ") {
                found_else_if = true;
                // Verify the syntax is correct: should have multiple else-if arms
                // and end with a plain else
                assert!(
                    stmt.contains("} else {"),
                    "Else-if chain should end with plain else: {}",
                    stmt
                );
                break;
            }
        }
        assert!(
            found_else_if,
            "Expected at least one else-if chain across 200 seeds"
        );
    }

    #[test]
    fn test_else_if_chain_not_generated_when_probability_zero() {
        let table = SymbolTable::new();

        let config = StmtConfig {
            if_probability: 0.99,
            else_if_probability: 0.0,
            while_probability: 0.0,
            for_probability: 0.0,
            break_continue_probability: 0.0,
            compound_assign_probability: 0.0,
            ..StmtConfig::default()
        };

        for seed in 0..100 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::new(&[], &table);

            let stmt = generator.generate_statement(&mut ctx, 0);

            // With else_if_probability=0.0, should never see "else if"
            assert!(
                !stmt.contains("else if"),
                "With else_if_probability=0.0, should not have else-if: {}",
                stmt
            );
        }
    }

    #[test]
    fn test_else_if_chain_syntax_correct() {
        let table = SymbolTable::new();

        let config = StmtConfig {
            if_probability: 0.99,
            else_if_probability: 0.99,
            while_probability: 0.0,
            for_probability: 0.0,
            break_continue_probability: 0.0,
            compound_assign_probability: 0.0,
            ..StmtConfig::default()
        };

        // Test multiple seeds to validate syntax
        for seed in 0..100 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::new(&[], &table);

            let stmt = generator.generate_statement(&mut ctx, 0);

            if stmt.contains("else if") {
                // The "else if" must be on the same line as closing brace
                // Valid: "} else if"
                // Invalid: "}\nelse if"
                assert!(
                    stmt.contains("} else if "),
                    "else-if must follow closing brace on same line: {}",
                    stmt
                );
            }
        }
    }

    #[test]
    fn test_match_let_generation() {
        let table = SymbolTable::new();

        let config = StmtConfig {
            match_probability: 0.99,
            if_probability: 0.0,
            while_probability: 0.0,
            for_probability: 0.0,
            break_continue_probability: 0.0,
            compound_assign_probability: 0.0,
            ..StmtConfig::default()
        };

        let mut found_match = false;
        for seed in 0..200 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            // Provide an i64 param as a match scrutinee
            let i64_params = vec![ParamInfo {
                name: "input".to_string(),
                param_type: TypeInfo::Primitive(PrimitiveType::I64),
            }];
            let mut ctx = StmtContext::new(&i64_params, &table);

            let stmt = generator.generate_let_statement(&mut ctx);

            if stmt.contains("match input") {
                found_match = true;
                // Must have a wildcard arm
                assert!(
                    stmt.contains("_ =>"),
                    "Match must have wildcard arm: {}",
                    stmt
                );
                // Must be a let binding
                assert!(
                    stmt.starts_with("let "),
                    "Match must be a let binding: {}",
                    stmt
                );
                break;
            }
        }
        assert!(
            found_match,
            "Expected at least one match let across 200 seeds"
        );
    }

    #[test]
    fn test_i64_match_not_generated_when_no_i64_in_scope() {
        let table = SymbolTable::new();

        // High i64 match probability, but string match disabled
        let config = StmtConfig {
            match_probability: 0.99,
            string_match_probability: 0.0,
            if_probability: 0.0,
            while_probability: 0.0,
            for_probability: 0.0,
            ..StmtConfig::default()
        };

        // Only string params - no i64 to match on
        let params = vec![ParamInfo {
            name: "text".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::String),
        }];

        // With string_match_probability=0.0 and no i64 in scope,
        // the i64 match path should never trigger on a string variable.
        for seed in 0..50 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::new(&params, &table);

            let stmt = generator.generate_let_statement(&mut ctx);
            // Check the first line only - match-let starts with "let localN = match var {"
            let first_line = stmt.lines().next().unwrap_or("");
            assert!(
                !(first_line.contains("= match text")),
                "Should not generate i64 match-let on string var: {}",
                stmt
            );
        }
    }

    #[test]
    fn test_string_match_let_generation() {
        let table = SymbolTable::new();

        let config = StmtConfig {
            string_match_probability: 0.99,
            match_probability: 0.0,
            if_probability: 0.0,
            while_probability: 0.0,
            for_probability: 0.0,
            break_continue_probability: 0.0,
            compound_assign_probability: 0.0,
            reassign_probability: 0.0,
            ..StmtConfig::default()
        };

        // A string param in scope to match on
        let params = vec![ParamInfo {
            name: "msg".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::String),
        }];

        let mut found_match = false;
        for seed in 0..200 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::new(&params, &table);

            let stmt = generator.generate_let_statement(&mut ctx);
            if stmt.contains("= match msg {") {
                found_match = true;
                // Verify it has string literal arms
                assert!(
                    stmt.contains("\""),
                    "String match should have string literal arms: {}",
                    stmt
                );
                // Verify wildcard arm
                assert!(
                    stmt.contains("_ =>"),
                    "String match should have wildcard arm: {}",
                    stmt
                );
                // Must be a let binding
                assert!(
                    stmt.starts_with("let "),
                    "String match must be a let binding: {}",
                    stmt
                );
                break;
            }
        }
        assert!(
            found_match,
            "Expected at least one string match let across 200 seeds"
        );
    }

    #[test]
    fn test_class_destructure_generation() {
        use crate::symbols::{ClassInfo, FieldInfo};

        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test_mod".to_string(), "test_mod.vole".to_string());

        // Create a class with two primitive fields
        let sym_id = table.get_module_mut(mod_id).unwrap().add_symbol(
            "Point".to_string(),
            SymbolKind::Class(ClassInfo {
                type_params: vec![],
                fields: vec![
                    FieldInfo {
                        name: "x".to_string(),
                        field_type: TypeInfo::Primitive(PrimitiveType::I64),
                    },
                    FieldInfo {
                        name: "y".to_string(),
                        field_type: TypeInfo::Primitive(PrimitiveType::I64),
                    },
                ],
                methods: vec![],
                implements: vec![],
                static_methods: vec![],
            }),
        );

        let config = StmtConfig {
            class_destructure_probability: 0.99,
            // Disable other generation paths so we almost always hit class destructuring
            if_probability: 0.0,
            while_probability: 0.0,
            for_probability: 0.0,
            nested_loop_probability: 0.0,
            ..StmtConfig::default()
        };

        let mut found_destructure = false;
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::with_module(&[], &table, mod_id);

            // Add a class-typed local so destructuring can fire
            ctx.add_local("point".to_string(), TypeInfo::Class(mod_id, sym_id), false);

            let stmt = generator.generate_statement(&mut ctx, 0);

            // Check if this is a class destructuring statement
            if stmt.starts_with("let {") && stmt.contains("= point") {
                // Should reference field names with renamed bindings
                assert!(
                    stmt.contains("x:") || stmt.contains("y:"),
                    "Class destructure should reference field names: {}",
                    stmt
                );
                found_destructure = true;
                break;
            }
        }
        assert!(
            found_destructure,
            "Expected at least one class destructure across 500 seeds"
        );
    }

    #[test]
    fn test_class_destructure_no_classes_returns_none() {
        let table = SymbolTable::new();

        let config = StmtConfig {
            class_destructure_probability: 0.99,
            ..StmtConfig::default()
        };

        // No class-typed variables in scope: destructuring should never appear
        for seed in 0..50 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::new(&[], &table);

            let result = generator.try_generate_class_destructure(&mut ctx);
            assert!(
                result.is_none(),
                "Should return None without class-typed locals, got: {:?}",
                result
            );
        }
    }

    #[test]
    fn test_class_destructure_skips_generic_classes() {
        use crate::symbols::{ClassInfo, FieldInfo, TypeParam};

        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test_mod".to_string(), "test_mod.vole".to_string());

        // Create a generic class (should be skipped)
        let sym_id = table.get_module_mut(mod_id).unwrap().add_symbol(
            "Box".to_string(),
            SymbolKind::Class(ClassInfo {
                type_params: vec![TypeParam {
                    name: "T".to_string(),
                    constraints: vec![],
                }],
                fields: vec![FieldInfo {
                    name: "value".to_string(),
                    field_type: TypeInfo::Primitive(PrimitiveType::I64),
                }],
                methods: vec![],
                implements: vec![],
                static_methods: vec![],
            }),
        );

        let config = StmtConfig {
            class_destructure_probability: 0.99,
            ..StmtConfig::default()
        };

        for seed in 0..50 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::with_module(&[], &table, mod_id);
            ctx.add_local("boxed".to_string(), TypeInfo::Class(mod_id, sym_id), false);

            let result = generator.try_generate_class_destructure(&mut ctx);
            assert!(
                result.is_none(),
                "Should return None for generic class, got: {:?}",
                result
            );
        }
    }

    #[test]
    fn test_iter_first_last_terminal() {
        use rand::SeedableRng;

        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test_mod".to_string(), "test_mod.vole".to_string());

        let config = StmtConfig {
            iter_map_filter_probability: 0.99,
            ..StmtConfig::default()
        };

        let mut found_first = false;
        let mut found_last = false;
        let mut found_optional_type = false;
        let mut found_coalesced = false;

        for seed in 0..2000 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = StmtGenerator::new(&mut rng, &config);
            let mut ctx = StmtContext::with_module(&[], &table, mod_id);
            ctx.add_local(
                "nums".to_string(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                false,
            );

            if let Some(stmt) = generator.try_generate_iter_map_filter_let(&mut ctx) {
                if stmt.contains(".first()") {
                    found_first = true;
                    // Check that the local was registered with the right type
                    let last_local = ctx.locals.last().unwrap();
                    if matches!(last_local.1, TypeInfo::Optional(_)) {
                        found_optional_type = true;
                    }
                }
                if stmt.contains(".last()") {
                    found_last = true;
                }
                if stmt.contains("?? ") {
                    found_coalesced = true;
                }
            }
        }

        assert!(
            found_first,
            "Expected at least one .first() terminal across 2000 seeds",
        );
        assert!(
            found_last,
            "Expected at least one .last() terminal across 2000 seeds",
        );
        assert!(
            found_optional_type,
            "Expected at least one .first()/.last() to produce an Optional type",
        );
        assert!(
            found_coalesced,
            "Expected at least one .first()/.last() with ?? coalescing across 2000 seeds",
        );
    }
}
