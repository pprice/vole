//! Grammar-based statement generation.
//!
//! This module generates type-correct Vole statements using grammar rules.
//! Statements are generated with depth limits and proper control flow.

mod arithmetic;
mod closures;
mod iterators;
mod let_bindings;
mod match_stmts;
mod strings;

#[cfg(test)]
mod tests;

use rand::Rng;
use rand::seq::SliceRandom;

use crate::expr::{ExprConfig, ExprContext, ExprGenerator, get_chainable_methods};
use crate::symbols::{
    ClassInfo, FunctionInfo, InterfaceInfo, ModuleId, ParamInfo, PrimitiveType, StaticMethodInfo,
    SymbolId, SymbolKind, SymbolTable, TypeInfo, TypeParam,
};

/// Configuration for statement generation.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(default)]
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
    ///
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
    ///
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
    ///
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
    ///
    /// Exercises intrinsic function codegen paths across integer types.
    /// Set to 0.0 to disable.
    pub checked_arithmetic_probability: f64,
}

impl Default for StmtConfig {
    fn default() -> Self {
        // Default values match the "full" profile so TOML files only specify overrides.
        Self {
            expr_config: ExprConfig::default(),
            max_depth: 3,
            statements_per_block: (2, 4),
            if_probability: 0.3,
            while_probability: 0.15,
            for_probability: 0.2,
            break_continue_probability: 0.12,
            compound_assign_probability: 0.15,
            reassign_probability: 0.15,
            raise_probability: 0.12,
            try_probability: 0.15,
            tuple_probability: 0.12,
            fixed_array_probability: 0.12,
            struct_destructure_probability: 0.15,
            class_destructure_probability: 0.12,
            discard_probability: 0.05,
            early_return_probability: 0.15,
            else_if_probability: 0.30,
            static_call_probability: 0.30,
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
            union_match_probability: 0.10,
            iter_map_filter_probability: 0.10,
            iface_function_call_probability: 0.10,
            generic_closure_interface_probability: 0.15,
            empty_array_iter_probability: 0.06,
            match_closure_arm_probability: 0.10,
            range_iter_probability: 0.08,
            field_closure_let_probability: 0.08,
            sentinel_union_probability: 0.15,
            optional_destructure_match_probability: 0.12,
            sentinel_closure_capture_probability: 0.10,
            closure_struct_capture_probability: 0.12,
            nested_closure_capture_probability: 0.10,
            string_interpolation_probability: 0.12,
            match_on_method_result_probability: 0.10,
            iter_method_map_probability: 0.10,
            string_split_probability: 0.08,
            string_method_probability: 0.10,
            iter_predicate_probability: 0.08,
            iter_chunks_windows_probability: 0.06,
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

/// Result of a let-dispatch generator call.
///
/// Unifies infallible generators (returning `String`) and fallible generators
/// (returning `Option<String>`) so that the dispatch macro can handle both
/// uniformly.
enum LetResult {
    Hit(String),
    Miss,
}

impl From<String> for LetResult {
    fn from(s: String) -> Self {
        LetResult::Hit(s)
    }
}

impl From<Option<String>> for LetResult {
    fn from(opt: Option<String>) -> Self {
        match opt {
            Some(s) => LetResult::Hit(s),
            None => LetResult::Miss,
        }
    }
}

/// Dispatch table for let-statement generation.
///
/// Shuffles entry order to avoid positional bias, then tries each entry once:
/// check the optional guard, roll against the probability, and call the
/// generator.  The first entry that fires *and* produces a value wins.
///
/// Each entry is `{ prob: <f64-expr>, call: <expr -> impl Into<LetResult>> }`
/// with an optional `guard: <bool-expr>,` before `call:`.
macro_rules! let_dispatch {
    ($self:expr, $ctx:expr, [
        $( { prob: $prob:expr, $( guard: $guard:expr, )? call: $call:expr } ),* $(,)?
    ]) => {{
        // Build index vec without recursive counting.
        let mut _order: Vec<usize> = Vec::new();
        { let mut _n = 0usize; $( let _ = $prob; _order.push(_n); _n += 1; )* }
        _order.shuffle(&mut *$self.rng);

        for _i in _order {
            let mut _idx = 0usize;
            $(
                if _i == _idx {
                    // Evaluate optional guard (defaults to true).
                    let _guarded = true;
                    $( let _guarded = $guard; )?
                    if _guarded && $self.rng.gen_bool($prob) {
                        let _result: LetResult = ($call).into();
                        if let LetResult::Hit(s) = _result {
                            return s;
                        }
                    }
                }
                _idx += 1;
            )*
            let _ = _idx;
        }
    }};
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
            && let Some(early_return_stmt) = self.generate_early_return(ctx)
        {
            lines.push(early_return_stmt);
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
        if ctx.is_fallible
            && self.rng.gen_bool(self.config.raise_probability)
            && let Some(stmt) = self.try_generate_raise_statement(ctx)
        {
            return stmt;
        }

        // Occasionally generate a try expression calling a fallible function
        if self.rng.gen_bool(self.config.try_probability)
            && let Some(stmt) = self.try_generate_try_let(ctx)
        {
            return stmt;
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
        if self.rng.gen_bool(0.20)
            && let Some(stmt) = self.try_generate_fn_param_call(ctx)
        {
            return stmt;
        }

        // Occasionally generate a discard statement (_ = func()) to exercise the syntax
        if self.rng.gen_bool(self.config.discard_probability)
            && let Some(stmt) = self.try_generate_discard_statement(ctx)
        {
            return stmt;
        }

        // Occasionally generate a standalone static method call
        if self.rng.gen_bool(self.config.static_call_probability)
            && let Some(stmt) = self.try_generate_static_call_statement(ctx)
        {
            return stmt;
        }

        // Occasionally generate an instance method call on a class-typed local
        if self.rng.gen_bool(self.config.method_call_probability)
            && let Some(stmt) = self.try_generate_method_call(ctx)
        {
            return stmt;
        }

        // Occasionally generate a method call on an interface-typed variable (vtable dispatch)
        if self
            .rng
            .gen_bool(self.config.interface_dispatch_probability)
            && let Some(stmt) = self.try_generate_interface_method_call(ctx)
        {
            return stmt;
        }

        // Occasionally call a free function that takes an interface-typed parameter
        if self
            .rng
            .gen_bool(self.config.iface_function_call_probability)
            && let Some(stmt) = self.try_generate_iface_function_call(ctx)
        {
            return stmt;
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
    ///
    /// Uses a shuffled dispatch table to avoid positional ordering bias.
    /// Each entry pairs a probability with a generator; the first entry that
    /// fires and produces a value wins. Falls back to a simple primitive
    /// let-binding when no dispatch entry fires.
    fn generate_let_statement(&mut self, ctx: &mut StmtContext) -> String {
        let config = self.config.clone();

        let_dispatch!(self, ctx, [
            // Lambda let-binding (closure exercise)
            { prob: config.expr_config.lambda_probability,
              call: self.generate_lambda_let(ctx) },
            // Class-typed local for field access
            { prob: 0.15,
              call: self.try_generate_class_let(ctx) },
            // Interface-typed local via upcast (vtable dispatch)
            { prob: config.interface_dispatch_probability,
              call: self.try_generate_interface_let(ctx) },
            // Struct-typed local
            { prob: 0.10,
              call: self.try_generate_struct_let(ctx) },
            // Array-typed local
            { prob: 0.12,
              call: self.generate_array_let(ctx) },
            // Iterator map/filter on array variables
            { prob: config.iter_map_filter_probability,
              call: self.try_generate_iter_map_filter_let(ctx) },
            // Empty array through iterator chain
            { prob: config.empty_array_iter_probability,
              call: self.generate_empty_array_iter_let(ctx) },
            // Empty string iteration
            { prob: config.empty_array_iter_probability,
              call: self.generate_empty_string_iter_let(ctx) },
            // Wildcard-only match
            { prob: 0.03,
              call: self.generate_wildcard_only_match(ctx) },
            // Nested when expressions
            { prob: 0.03,
              call: self.try_generate_nested_when_let(ctx) },
            // Zero-take / max-skip empty iterator
            { prob: 0.03,
              call: self.try_generate_empty_iter_edge(ctx) },
            // Chained string method calls
            { prob: 0.04,
              call: self.try_generate_chained_string_methods(ctx) },
            // Match on array element
            { prob: 0.03,
              call: self.try_generate_match_array_elem(ctx) },
            // Match on iterator terminal
            { prob: 0.03,
              call: self.try_generate_match_iter_terminal(ctx) },
            // Range-based iterator chain
            { prob: config.range_iter_probability,
              call: self.generate_range_iter_let(ctx) },
            // Generic closure + interface dispatch in iterator chains
            { prob: config.generic_closure_interface_probability,
              call: self.try_generate_generic_closure_interface_chain(ctx) },
            // Match with closure arms
            { prob: config.match_closure_arm_probability,
              call: self.try_generate_match_closure_arms(ctx) },
            // Field-closure-let (extract field, capture in closure)
            { prob: config.field_closure_let_probability,
              call: self.try_generate_field_closure_let(ctx) },
            // String split to array
            { prob: config.string_split_probability,
              call: self.generate_string_split_let(ctx) },
            // String method call
            { prob: config.string_method_probability,
              call: self.try_generate_string_method_let(ctx) },
            // Checked/wrapping/saturating arithmetic (requires lowlevel import)
            { prob: config.checked_arithmetic_probability,
              guard: ctx.has_lowlevel_import,
              call: self.generate_checked_arithmetic_let(ctx) },
            // Tuple let-binding with destructuring
            { prob: config.tuple_probability,
              call: self.generate_tuple_let(ctx) },
            // Fixed-size array let-binding with destructuring
            { prob: config.fixed_array_probability,
              call: self.generate_fixed_array_let(ctx) },
            // Struct destructuring
            { prob: config.struct_destructure_probability,
              call: self.try_generate_struct_destructure(ctx) },
            // Class destructuring
            { prob: config.class_destructure_probability,
              call: self.try_generate_class_destructure(ctx) },
            // Struct copy
            { prob: 0.08,
              call: self.try_generate_struct_copy(ctx) },
            // Match expression let-binding
            { prob: config.match_probability,
              call: self.try_generate_match_let(ctx) },
            // String match expression let-binding
            { prob: config.string_match_probability,
              call: self.try_generate_string_match_let(ctx) },
            // Union match expression let-binding
            { prob: config.union_match_probability,
              call: self.try_generate_union_match_let(ctx) },
            // Sentinel union let-binding
            { prob: config.sentinel_union_probability,
              call: self.try_generate_sentinel_union_let(ctx) },
            // Optional destructure match
            { prob: config.optional_destructure_match_probability,
              call: self.try_generate_optional_destructure_match(ctx) },
            // Sentinel closure capture
            { prob: config.sentinel_closure_capture_probability,
              call: self.try_generate_sentinel_closure_capture(ctx) },
            // Closure capturing whole struct
            { prob: config.closure_struct_capture_probability,
              call: self.try_generate_closure_struct_capture(ctx) },
            // Nested closure capture
            { prob: config.nested_closure_capture_probability,
              call: self.try_generate_nested_closure_capture(ctx) },
            // String interpolation let-binding
            { prob: config.string_interpolation_probability,
              call: self.try_generate_string_interpolation_let(ctx) },
            // Match on method call result
            { prob: config.match_on_method_result_probability,
              call: self.try_generate_match_on_method_result(ctx) },
            // Iterator map using method call on class instance
            { prob: config.iter_method_map_probability,
              call: self.try_generate_iter_method_map(ctx) },
            // When expression let-binding
            { prob: config.when_let_probability,
              call: self.try_generate_when_let(ctx) },
            // Iterator predicate
            { prob: config.iter_predicate_probability,
              call: self.try_generate_iter_predicate_let(ctx) },
            // Iterator chunks/windows
            { prob: config.iter_chunks_windows_probability,
              call: self.try_generate_iter_chunks_windows_let(ctx) },
            // Re-iterate existing array local
            { prob: 0.08,
              call: self.try_generate_reiterate_let(ctx) },
            // for_each as standalone statement
            { prob: 0.05,
              call: self.try_generate_for_each_stmt(ctx) },
            // nth with match on optional result
            { prob: 0.05,
              call: self.try_generate_nth_let(ctx) },
            // String iteration
            { prob: 0.05,
              call: self.try_generate_string_iter_let(ctx) },
            // Variable shadowing
            { prob: 0.04,
              call: self.try_generate_variable_shadow(ctx) },
            // Assert statement with tautological condition
            { prob: 0.03,
              call: self.try_generate_assert_stmt(ctx) },
            // Match on boolean value
            { prob: 0.03,
              call: self.try_generate_bool_match_let(ctx) },
            // Dead-code assertion
            { prob: 0.02,
              call: self.generate_dead_code_assert() },
            // Zero/single-iteration for loop
            { prob: 0.02,
              call: self.generate_edge_case_for_loop(ctx, 2) },
            // Empty array iterator operation
            { prob: 0.02,
              call: self.generate_empty_array_iter(ctx) },
            // Edge-case string split
            { prob: 0.02,
              call: self.generate_edge_case_split(ctx) },
            // Iterator terminal inside while-loop accumulator
            { prob: 0.02,
              call: self.try_generate_iter_while_accum(ctx) },
            // For-in loop with match on iteration variable
            { prob: 0.02,
              call: self.try_generate_for_in_match_accum(ctx) },
            // String concatenation with + operator
            { prob: 0.03,
              call: self.try_generate_string_concat_let(ctx) },
            // Map-to-string-then-reduce (join pattern)
            { prob: 0.02,
              call: self.try_generate_map_tostring_reduce(ctx) },
            // Numeric .to_string() in string expression
            { prob: 0.02,
              call: self.try_generate_to_string_let(ctx) },
            // Struct field in string interpolation
            { prob: 0.02,
              call: self.try_generate_struct_field_interpolation(ctx) },
            // When with iterator predicate condition
            { prob: 0.02,
              call: self.try_generate_when_iter_predicate(ctx) },
            // Closure result in string concat
            { prob: 0.02,
              call: self.try_generate_closure_result_concat(ctx) },
            // Split result in for-in loop
            { prob: 0.02,
              call: self.generate_split_for_loop(ctx) },
            // For-in loop pushing derived values to mutable array
            { prob: 0.02,
              call: self.try_generate_for_push_collect(ctx) },
            // Array literal with variable elements
            { prob: 0.03,
              call: self.try_generate_array_from_vars(ctx) },
            // Multiple pushes onto a mutable array
            { prob: 0.02,
              call: self.try_generate_multi_push(ctx) },
            // Method call on a literal value
            { prob: 0.02,
              call: self.generate_literal_method_call(ctx) },
            // Nested when-in-when expression
            { prob: 0.02,
              call: self.try_generate_nested_when(ctx) },
            // Match on method call result (small variant)
            { prob: 0.02,
              call: self.try_generate_match_on_method(ctx) },
            // Struct construction with iterator field values
            { prob: 0.02,
              call: self.try_generate_struct_with_iter_fields(ctx) },
            // Iterator terminal + method chain
            { prob: 0.02,
              call: self.try_generate_iter_terminal_chain(ctx) },
            // When with string method conditions
            { prob: 0.02,
              call: self.try_generate_when_string_method_conds(ctx) },
            // Single-element array operations
            { prob: 0.02,
              call: self.generate_single_elem_array_ops(ctx) },
            // Tautological comparison in when
            { prob: 0.02,
              call: self.try_generate_tautological_when(ctx) },
            // Empty string concatenation edge case
            { prob: 0.02,
              call: self.try_generate_empty_string_concat(ctx) },
            // Last element access via computed index
            { prob: 0.02,
              call: self.try_generate_last_elem_access(ctx) },
            // For-loop indexed by array length
            { prob: 0.02,
              call: self.try_generate_for_length_indexed(ctx) },
            // While-loop string building
            { prob: 0.02,
              call: self.generate_while_string_build(ctx) },
            // Compound boolean from numeric comparisons
            { prob: 0.03,
              call: self.try_generate_compound_bool_let(ctx) },
            // Boolean from length comparisons
            { prob: 0.02,
              call: self.try_generate_length_comparison_let(ctx) },
            // String interpolation with iterator terminal
            { prob: 0.02,
              call: self.try_generate_interpolation_with_iter(ctx) },
            // Reassign from when expression
            { prob: 0.02,
              call: self.try_generate_reassign_from_when(ctx) },
            // Identity arithmetic edge case
            { prob: 0.02,
              call: self.try_generate_identity_arithmetic(ctx) },
            // String equality edge case
            { prob: 0.02,
              call: self.try_generate_string_equality_let(ctx) },
            // Modulo edge cases
            { prob: 0.02,
              call: self.generate_modulo_edge_case(ctx) },
            // Uniform array operations
            { prob: 0.02,
              call: self.generate_array_uniform_ops(ctx) },
            // For-loop with when-based accumulation
            { prob: 0.02,
              call: self.try_generate_for_when_accumulate(ctx) },
            // When with iterator terminals as arm values
            { prob: 0.02,
              call: self.try_generate_iter_in_when_arms(ctx) },
            // Multi-arm when (4+ arms)
            { prob: 0.02,
              call: self.try_generate_multi_arm_when(ctx) },
            // Match with computed arm values
            { prob: 0.02,
              call: self.try_generate_match_with_computation(ctx) },
            // String replace/replace_all
            { prob: 0.02,
              call: self.try_generate_string_replace_let(ctx) },
            // Nested match expression
            { prob: 0.02,
              call: self.try_generate_nested_match_let(ctx) },
            // String length on literal edge cases
            { prob: 0.02,
              call: self.generate_string_length_edge_cases(ctx) },
            // Range check boolean
            { prob: 0.02,
              call: self.try_generate_range_check_let(ctx) },
            // For-loop string build with match
            { prob: 0.02,
              call: self.generate_for_string_build_with_match(ctx) },
            // When with string concat arm values
            { prob: 0.02,
              call: self.try_generate_when_with_string_concat_arms(ctx) },
            // Boolean negation edge cases
            { prob: 0.02,
              call: self.try_generate_bool_negation_let(ctx) },
            // Chained methods on literal strings
            { prob: 0.02,
              call: self.generate_chained_literal_method(ctx) },
            // Method call on when result
            { prob: 0.02,
              call: self.try_generate_when_result_method(ctx) },
            // For-loop building string with when body
            { prob: 0.02,
              call: self.try_generate_for_iter_when_string_body(ctx) },
            // While false dead code
            { prob: 0.02,
              call: self.generate_while_false_deadcode(ctx) },
            // Division by power of 2
            { prob: 0.02,
              call: self.try_generate_power_of_two_div(ctx) },
            // String predicate (contains/starts_with/ends_with)
            { prob: 0.02,
              call: self.try_generate_string_predicate_let(ctx) },
            // String interpolation with complex expressions
            { prob: 0.02,
              call: self.try_generate_interpolation_expr_let(ctx) },
            // Match on string length
            { prob: 0.02,
              call: self.try_generate_match_string_length(ctx) },
            // Array length guard (safe indexing)
            { prob: 0.02,
              call: self.try_generate_array_length_guard(ctx) },
            // Repeat literal array
            { prob: 0.02,
              call: self.generate_repeat_literal_let(ctx) },
            // iter().reduce() on array
            { prob: 0.02,
              call: self.try_generate_iter_reduce_let(ctx) },
            // i32 near-boundary operations
            { prob: 0.02,
              call: self.generate_i32_boundary_safe(ctx) },
            // Empty string operations
            { prob: 0.02,
              call: self.generate_empty_string_ops(ctx) },
            // Manual for-loop reduce pattern
            { prob: 0.02,
              call: self.try_generate_for_reduce_pattern(ctx) },
            // When containing match expression
            { prob: 0.02,
              call: self.try_generate_when_match_combo(ctx) },
            // String split iteration
            { prob: 0.02,
              call: self.generate_string_split_for(ctx) },
            // Nested when with string result
            { prob: 0.02,
              call: self.try_generate_nested_when_string_let(ctx) },
            // .to_string() on numeric values
            { prob: 0.02,
              call: self.try_generate_numeric_to_string_let(ctx) },
            // .substring() on strings
            { prob: 0.02,
              call: self.try_generate_substring_let(ctx) },
            // Match with to_string arm values
            { prob: 0.02,
              call: self.try_generate_match_to_string_arms(ctx) },
            // For loop with string interpolation concat
            { prob: 0.02,
              call: self.generate_for_interpolation_concat(ctx) },
            // Boolean chain expression
            { prob: 0.02,
              call: self.try_generate_bool_chain_let(ctx) },
            // Comparison chain expression
            { prob: 0.02,
              call: self.try_generate_comparison_chain_let(ctx) },
            // When with string predicate (contains/starts_with)
            { prob: 0.02,
              call: self.try_generate_when_with_contains(ctx) },
            // Match on array length
            { prob: 0.02,
              call: self.try_generate_match_array_length(ctx) },
            // Sorted collect on array
            { prob: 0.02,
              call: self.try_generate_sorted_collect_let(ctx) },
            // Reverse collect on array
            { prob: 0.02,
              call: self.try_generate_reverse_collect_let(ctx) },
            // Guarded division
            { prob: 0.02,
              call: self.try_generate_zero_division_guard(ctx) },
            // Single-character string operations
            { prob: 0.02,
              call: self.generate_single_char_string_ops(ctx) },
            // f64 literal arithmetic operations
            { prob: 0.02,
              call: self.generate_f64_literal_ops_let(ctx) },
            // f64 equality/comparison edge cases
            { prob: 0.02,
              call: self.generate_f64_comparison_edge_let(ctx) },
            // String with repeated characters operations
            { prob: 0.02,
              call: self.generate_repeated_string_ops(ctx) },
            // Iterator take/skip collect on parameter arrays
            { prob: 0.02,
              call: self.try_generate_iter_take_skip_collect_let(ctx) },
            // When with f64 variable conditions
            { prob: 0.02,
              call: self.try_generate_when_f64_cond_let(ctx) },
            // For-range building string via i.to_string()
            { prob: 0.02,
              call: self.generate_for_range_tostring_build(ctx) },
            // Match with when expression in arm values
            { prob: 0.02,
              call: self.try_generate_match_when_arm_let(ctx) },
            // Sorted iteration with accumulation
            { prob: 0.02,
              call: self.try_generate_sorted_iter_accum(ctx) },
            // Filter-collect then iterate with to_string
            { prob: 0.02,
              call: self.try_generate_filter_iter_tostring(ctx) },
            // When comparing lengths of array and string
            { prob: 0.02,
              call: self.try_generate_when_length_compare(ctx) },
            // Character extraction via substring
            { prob: 0.02,
              call: self.generate_string_char_at_let(ctx) },
            // Range-based iterator with map and collect
            { prob: 0.02,
              call: self.generate_range_iter_map_collect(ctx) },
            // Match on interpolated string length
            { prob: 0.02,
              call: self.try_generate_match_interpolation_length(ctx) },
            // Range for-loop with when body accumulation
            { prob: 0.02,
              call: self.generate_for_range_when_accum(ctx) },
            // When with to_string in arms
            { prob: 0.02,
              call: self.try_generate_when_tostring_arms(ctx) },
            // Match on sorted array length
            { prob: 0.02,
              call: self.try_generate_match_sorted_length(ctx) },
            // Single-element range operations
            { prob: 0.02,
              call: self.generate_single_elem_range_let(ctx) },
            // Whitespace-heavy string operations
            { prob: 0.02,
              call: self.generate_whitespace_string_ops(ctx) },
            // Empty range (N..N) operations
            { prob: 0.02,
              call: self.generate_empty_range_let(ctx) },
            // .to_string().length() chained method
            { prob: 0.02,
              call: self.try_generate_tostring_length_let(ctx) },
            // Chained boolean literal ops
            { prob: 0.02,
              call: self.generate_bool_chain_edge_let(ctx) },
            // Safe array first-element access via length guard
            { prob: 0.02,
              call: self.try_generate_array_length_zero_check(ctx) },
            // When with string replace in arms
            { prob: 0.02,
              call: self.try_generate_when_replace_result(ctx) },
            // Match with .to_string() in arms
            { prob: 0.02,
              call: self.try_generate_match_tostring_arms(ctx) },
            // Manual min/max via when
            { prob: 0.02,
              call: self.try_generate_manual_minmax_let(ctx) },
            // Nested .to_string().length().to_string() chain
            { prob: 0.02,
              call: self.try_generate_nested_tostring_let(ctx) },
            // Widening let statement
            { prob: 0.10,
              call: self.try_generate_widening_let(ctx) },
        ]);

        // Fallback: simple primitive let-binding
        self.generate_primitive_let(ctx)
    }

    /// Fallback: generate a simple primitive let-binding.
    fn generate_primitive_let(&mut self, ctx: &mut StmtContext) -> String {
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
        ctx.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );

        let indent = self.indent_str();
        let inner_indent = format!("{}    ", indent);
        format!(
            "let mut {} = 0\n{}for {} in {}.iter(){}.enumerate() {{\n{}{}\n{}}}",
            acc_name, indent, pair_name, arr_name, prefix, inner_indent, body_expr, indent
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
        ctx.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );

        let indent = self.indent_str();
        let inner_indent = format!("{}    ", indent);
        format!(
            "let mut {} = 0\n{}for {} in {}.iter().zip({}.iter()) {{\n{}{}\n{}}}",
            acc_name, indent, pair_name, arr_a, arr_b, inner_indent, body_expr, indent,
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
                0 => format!("{}..{}", start, start),  // empty exclusive range
                1 => format!("{}..={}", start, start), // single-iteration inclusive
                _ => format!("{}..{}", start, start + 1), // single-iteration exclusive
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
        if let Some(ref ret_ty) = return_type
            && !matches!(ret_ty, TypeInfo::Void)
            && self.rng.gen_bool(0.20)
        {
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            let cond = expr_gen.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx, 0);

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
                if *is_mut
                    && !ctx.protected_vars.contains(name)
                    && let TypeInfo::Array(elem) = ty
                {
                    return Some((name.clone(), *elem.clone()));
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
        let value = expr_gen.generate_simple(elem_type, &expr_ctx);

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
        let value = expr_gen.generate_simple(elem_type, &expr_ctx);

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
                if *is_mut
                    && !ctx.protected_vars.contains(name)
                    && let TypeInfo::Array(elem) = ty
                    && let TypeInfo::Primitive(
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
                if let SymbolKind::Function(ref info) = sym.kind
                    && info.type_params.is_empty()
                    && info.return_type.is_fallible()
                    && current_name != Some(sym.name.as_str())
                {
                    // Only call lower-indexed functions to prevent cycles
                    if let Some(cur_id) = current_fn_sym_id
                        && sym.id.0 >= cur_id.0
                    {
                        return None;
                    }
                    return Some((sym.name.clone(), info.clone()));
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
                        if let Some(cur_id) = current_fn_sym_id
                            && sym.id.0 >= cur_id.0
                        {
                            return None;
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
        //   ~12% large 6-10 elements (stress iterator codegen with more data)
        //   ~88% standard 2-4 elements
        // Note: single-element arrays are covered by generate_single_elem_array_ops.
        let elem_count = if self.rng.gen_bool(0.12) {
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
                if let SymbolKind::Class(ref info) = sym.kind
                    && info.type_params.is_empty()
                    && has_primitive_field(info)
                {
                    return Some((sym.id, sym.name.clone(), info.clone()));
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
                    if let SymbolKind::Class(ref info) = sym.kind
                        && info.type_params.is_empty()
                        && !info.methods.is_empty()
                    {
                        return Some((name.clone(), *mod_id, *sym_id, info.methods.clone()));
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
                        if let Some(cur_id) = current_fn_sym_id
                            && s.id.0 >= cur_id.0
                        {
                            return None;
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
                if let SymbolKind::Class(ref class_info) = class_sym.kind
                    && class_info.type_params.is_empty()
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
            let mut indices = primitive_fields;
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
            if let SymbolKind::Class(ref info) = sym.kind
                && info.type_params.is_empty()
                && has_primitive_field(info)
                && !info.static_methods.is_empty()
            {
                // is_class = true
                candidates.push((sym.id, sym.name.clone(), info.static_methods.clone(), true));
            }
        }

        // Structs with static methods
        for sym in module.structs() {
            if let SymbolKind::Struct(ref info) = sym.kind
                && !info.static_methods.is_empty()
            {
                // is_class = false
                candidates.push((sym.id, sym.name.clone(), info.static_methods.clone(), false));
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
