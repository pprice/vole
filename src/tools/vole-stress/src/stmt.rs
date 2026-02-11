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
            current_class_sym_id: None,
            protected_vars: Vec::new(),
            return_type: None,
            type_params: Vec::new(),
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
            current_class_sym_id: None,
            protected_vars: Vec::new(),
            return_type: None,
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

        // When expression let-binding: let x = when { cond => val, _ => val }
        if self.rng.gen_bool(self.config.when_let_probability) {
            if let Some(stmt) = self.try_generate_when_let(ctx) {
                return stmt;
            }
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

        ctx.add_local(name.clone(), ty, is_mutable);

        let mutability = if is_mutable { "let mut" } else { "let" };
        format!("{} {} = {}", mutability, name, value)
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
    /// Returns `None` if no i64-typed variable is in scope.
    fn try_generate_match_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find i64-typed variables in scope (locals + params)
        let mut candidates: Vec<String> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)) {
                candidates.push(name.clone());
            }
        }
        for param in ctx.params.iter() {
            if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::I64)) {
                candidates.push(param.name.clone());
            }
        }
        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let scrutinee = &candidates[idx];

        // Pick a result type for all arms (same type to keep it simple)
        let result_type = self.random_primitive_type();
        let result_name = ctx.new_local_name();

        // Generate 2-3 literal arms plus a wildcard
        let arm_count = self.rng.gen_range(2..=3);
        let indent = "    ".repeat(self.indent + 1);

        let expr_ctx = ctx.to_expr_context();
        let mut arms = Vec::new();

        // Generate distinct integer literal patterns
        let mut used_values = std::collections::HashSet::new();
        for _ in 0..arm_count {
            let mut val: i64 = self.rng.gen_range(0..20);
            while used_values.contains(&val) {
                val = self.rng.gen_range(0..20);
            }
            used_values.insert(val);

            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            let arm_expr = expr_gen.generate_simple(&result_type, &expr_ctx);
            arms.push(format!("{}{} => {}", indent, val, arm_expr));
        }

        // Wildcard arm
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let wildcard_expr = expr_gen.generate_simple(&result_type, &expr_ctx);
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

        // Pick distinct string patterns
        let mut used_indices = std::collections::HashSet::new();
        for _ in 0..arm_count {
            let mut pi = self.rng.gen_range(0..patterns.len());
            while used_indices.contains(&pi) {
                pi = self.rng.gen_range(0..patterns.len());
            }
            used_indices.insert(pi);

            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            let arm_expr = expr_gen.generate_simple(&result_type, &expr_ctx);
            arms.push(format!("{}\"{}\" => {}", indent, patterns[pi], arm_expr));
        }

        // Wildcard arm
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let wildcard_expr = expr_gen.generate_simple(&result_type, &expr_ctx);
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

        // Generate 2-3 boolean condition arms plus a wildcard
        let arm_count = self.rng.gen_range(2..=3);
        let indent = "    ".repeat(self.indent + 1);

        let expr_ctx = ctx.to_expr_context();
        let mut arms = Vec::new();

        for _ in 0..arm_count {
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            let cond =
                expr_gen.generate_simple(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx);
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            let arm_expr = expr_gen.generate_simple(&result_type, &expr_ctx);
            arms.push(format!("{}{} => {}", indent, cond, arm_expr));
        }

        // Wildcard arm
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let wildcard_expr = expr_gen.generate_simple(&result_type, &expr_ctx);
        arms.push(format!("{}_ => {}", indent, wildcard_expr));

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
        let expr_ctx = ctx.to_expr_context();
        let mut arms = Vec::new();

        // Generate one arm per variant type
        for variant in &variants {
            if let TypeInfo::Primitive(prim) = variant {
                let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                let arm_expr = expr_gen.generate_simple(&result_type, &expr_ctx);
                arms.push(format!("{}{} => {}", indent, prim.as_str(), arm_expr));
            }
        }

        if arms.is_empty() {
            return None;
        }

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

    /// Try to generate a widening let statement.
    ///
    /// Looks for existing narrow-typed variables in scope and generates a let
    /// that assigns them to a wider-typed variable, exercising Vole's implicit
    /// numeric widening.
    ///
    /// Example: If `narrow_var: i32` is in scope, generates `let wide: i64 = narrow_var`.
    ///
    /// Returns `None` if no suitable widening source is in scope.
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

        // Check if we can iterate over an iterator chain (~20% when primitive arrays available)
        if !array_vars.is_empty() && self.rng.gen_bool(0.2) {
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

            if !prim_array_vars.is_empty() {
                return self.generate_for_in_iterator(ctx, depth, &prim_array_vars);
            }
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

    /// Generate a range expression for a for loop.
    ///
    /// Produces either exclusive (`start..end`) or inclusive (`start..=end`)
    /// syntax. The upper bound may reference an existing local i64 variable
    /// (~30% chance when one is available).
    fn generate_range(&mut self, ctx: &StmtContext, inclusive: bool) -> String {
        let start = self.rng.gen_range(0..3);

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

        // Try to use a local i64 variable as the upper bound (~30% chance)
        let var_bound = if !i64_locals.is_empty() && self.rng.gen_bool(0.3) {
            let idx = self.rng.gen_range(0..i64_locals.len());
            Some(i64_locals[idx].clone())
        } else {
            None
        };

        if let Some(var_name) = var_bound {
            // Variable bound: use the variable name directly
            if inclusive {
                format!("{}..={}", start, var_name)
            } else {
                format!("{}..{}", start, var_name)
            }
        } else if inclusive {
            // Inclusive literal bound: `start..=end` iterates start through end.
            let end = start + self.rng.gen_range(0..5);
            format!("{}..={}", start, end.max(start))
        } else {
            // Exclusive literal bound: `start..end` iterates start through end-1.
            let end = start + self.rng.gen_range(1..5);
            format!("{}..{}", start, end)
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

        // Use index 0 or 1 to stay in bounds (arrays have at least 2 elements)
        let index = self.rng.gen_range(0..=1);

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

        // Use index 0 or 1 to stay in bounds (arrays have at least 2 elements)
        let index = self.rng.gen_range(0..=1);

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
        // 40% .collect() -> [T], 15% .count() -> i64, 15% .sum() -> T (numeric only),
        // 15% .reduce() -> T (two-param closure), 15% .take(N).collect() -> [T]
        let terminal_choice = self.rng.gen_range(0..20);
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
        } else {
            let n = self.rng.gen_range(1..=3);
            (
                format!(".take({}).collect()", n),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_prim))),
            )
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
        match elem_prim {
            PrimitiveType::I64 => match self.rng.gen_range(0..3) {
                0 => {
                    let n = self.rng.gen_range(0..=5);
                    format!("x > {}", n)
                }
                1 => {
                    let n = self.rng.gen_range(0..=10);
                    format!("x < {}", n)
                }
                _ => "x % 2 == 0".to_string(),
            },
            PrimitiveType::F64 => {
                let n = self.rng.gen_range(0..=50);
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
                let n = self.rng.gen_range(0..=3);
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
                // Accumulate sum or product
                if self.rng.gen_bool(0.5) {
                    (
                        "0".to_string(),
                        "acc + el".to_string(),
                        TypeInfo::Primitive(PrimitiveType::I64),
                    )
                } else {
                    let n = self.rng.gen_range(1..=3);
                    (
                        format!("{}", n),
                        "acc * el".to_string(),
                        TypeInfo::Primitive(PrimitiveType::I64),
                    )
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
        // excluding the current function to prevent direct self-recursion.
        let current_name = ctx.current_function_name.as_deref();
        let fallible_funcs: Vec<(String, FunctionInfo)> = module
            .functions()
            .filter_map(|sym| {
                if let SymbolKind::Function(ref info) = sym.kind {
                    if info.type_params.is_empty()
                        && info.return_type.is_fallible()
                        && current_name != Some(sym.name.as_str())
                    {
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
        // excluding the current function to prevent direct self-recursion.
        let current_name = ctx.current_function_name.as_deref();
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

        // Generate 2-4 elements so indexing with 0..=2 is safe
        let elem_count = self.rng.gen_range(2..=4);
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
            if stmt.contains("..n") || stmt.contains("..=n") {
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
            if stmt.contains("[") && stmt.contains("]") && stmt.starts_with("let ") {
                // Verify it looks like an array literal: let localN = [elem1, elem2, ...]
                assert!(
                    stmt.contains("= ["),
                    "Array let should contain '= [', got: {}",
                    stmt,
                );
                found_array_let = true;

                // Verify the local was added with an Array type
                let last_local = ctx.locals.last().unwrap();
                assert!(
                    matches!(last_local.1, TypeInfo::Array(_)),
                    "Local should have Array type, got: {:?}",
                    last_local.1,
                );
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
}
