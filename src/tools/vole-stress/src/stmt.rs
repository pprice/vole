//! Grammar-based statement generation.
//!
//! This module generates type-correct Vole statements using grammar rules.
//! Statements are generated with depth limits and proper control flow.

use rand::Rng;

use crate::expr::{ExprConfig, ExprContext, ExprGenerator, get_chainable_methods};
use crate::symbols::{
    ClassInfo, FunctionInfo, ModuleId, ParamInfo, PrimitiveType, SymbolKind, SymbolTable, TypeInfo,
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
    /// Probability of generating a raise statement in fallible functions.
    pub raise_probability: f64,
    /// Probability of generating a try expression when calling fallible functions.
    pub try_probability: f64,
    /// Probability of generating a tuple let-binding with destructuring.
    pub tuple_probability: f64,
    /// Probability of generating a fixed-size array let-binding with destructuring.
    pub fixed_array_probability: f64,
    /// Probability of generating a discard expression (_ = expr) statement.
    pub discard_probability: f64,
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
            raise_probability: 0.10,
            try_probability: 0.12,
            tuple_probability: 0.10,
            fixed_array_probability: 0.10,
            discard_probability: 0.05,
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
    /// Variables that should not be modified by compound assignments.
    /// Used to protect while-loop counter and guard variables from modification.
    pub protected_vars: Vec<String>,
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
            protected_vars: Vec::new(),
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
            protected_vars: Vec::new(),
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

        // Generate statements
        for _ in 0..stmt_count {
            let stmt = self.generate_statement(ctx, depth);
            lines.push(stmt);
        }

        // For fallible functions, use the success type for the return expression
        let effective_return_type = return_type.success_type();

        // Generate return statement
        if !matches!(effective_return_type, TypeInfo::Void) {
            let expr_ctx = ctx.to_expr_context();
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            let return_expr = expr_gen.generate(effective_return_type, &expr_ctx, 0);
            lines.push(format!("return {}", return_expr));
        }

        lines
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

        // ~12% chance to generate an array-typed local for array indexing
        if self.rng.gen_bool(0.12) {
            return self.generate_array_let(ctx);
        }

        // Tuple let-binding with destructuring
        if self.rng.gen_bool(self.config.tuple_probability) {
            return self.generate_tuple_let(ctx);
        }

        // Fixed-size array let-binding with destructuring
        if self.rng.gen_bool(self.config.fixed_array_probability) {
            return self.generate_fixed_array_let(ctx);
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

    /// Generate a let statement binding a lambda expression.
    fn generate_lambda_let(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();

        // Pick 0-2 random primitive param types
        let param_count = self.rng.gen_range(0..=2);
        let param_types: Vec<TypeInfo> = (0..param_count)
            .map(|_| self.random_primitive_type())
            .collect();

        // Pick a random return type (avoiding i32 due to cross-module
        // lambda codegen bug, see vol-pz4y)
        let return_type = self.random_lambda_return_type();

        let expr_ctx = ctx.to_expr_context();
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        // Generate the lambda at a reduced depth so the body is simpler.
        // Complex bodies (when/match) in lambdas trigger a cross-module
        // codegen bug (vol-pz4y), so we keep bodies shallow.
        let depth = self.config.expr_config.max_depth.saturating_sub(1);
        let value = expr_gen.generate_lambda(&param_types, &return_type, &expr_ctx, depth);

        // Lambda variables are not tracked for reuse since their function
        // type doesn't match primitive type expectations in the generator.

        format!("let {} = {}", name, value)
    }

    /// Generate an if statement.
    fn generate_if_statement(&mut self, ctx: &mut StmtContext, depth: usize) -> String {
        let expr_ctx = ctx.to_expr_context();

        // 30% chance to use an `is` expression as the condition if union-typed vars exist
        let try_is = self.rng.gen_bool(0.3);
        let cond = {
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            if try_is {
                expr_gen.generate_is_expr(&expr_ctx).unwrap_or_else(|| {
                    expr_gen.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx, 0)
                })
            } else {
                expr_gen.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx, 0)
            }
        };

        // Generate then branch (save and restore locals for scoping)
        let locals_before = ctx.locals.len();
        let then_stmts = self.generate_block(ctx, depth + 1);
        ctx.locals.truncate(locals_before);
        let then_block = self.format_block(&then_stmts);

        // 50% chance of else branch
        let else_part = if self.rng.gen_bool(0.5) {
            let else_stmts = self.generate_block(ctx, depth + 1);
            ctx.locals.truncate(locals_before);
            let else_block = self.format_block(&else_stmts);
            format!(" else {}", else_block)
        } else {
            String::new()
        };

        format!("if {} {}{}", cond, then_block, else_part)
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
    /// Randomly chooses between exclusive (`start..end`) and inclusive
    /// (`start..=end`) range syntax with ~50/50 probability.
    /// Optionally uses a local i64 variable as the upper bound.
    fn generate_for_statement(&mut self, ctx: &mut StmtContext, depth: usize) -> String {
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

    /// Generate a range expression for a for loop.
    ///
    /// Produces either exclusive (`start..end`) or inclusive (`start..=end`)
    /// syntax. The upper bound may reference an existing local i64 variable
    /// (~30% chance when one is available).
    fn generate_range(&mut self, ctx: &StmtContext, inclusive: bool) -> String {
        let start = self.rng.gen_range(0..3);

        // Collect i64 locals that could serve as variable bounds
        let i64_locals: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
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

    /// Generate a break or continue statement wrapped in a conditional.
    ///
    /// Wraps in `if <condition> { break }` to avoid always exiting on
    /// the first iteration. Only called when `ctx.in_loop` is true.
    ///
    /// Both `break` and `continue` are allowed in while loops because a
    /// guard variable at the top of the loop body guarantees termination
    /// even when `continue` skips the manual counter increment.
    fn generate_break_continue(&mut self, ctx: &mut StmtContext) -> String {
        let keyword = if self.rng.gen_bool(0.5) {
            "break"
        } else {
            "continue"
        };

        let expr_ctx = ctx.to_expr_context();
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
        let op = match self.rng.gen_range(0..3) {
            0 => "+=",
            1 => "-=",
            _ => "*=",
        };

        // Generate a simple numeric literal of the same type
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let rhs = expr_gen.literal_for_primitive(*prim);

        format!("{} {} {}", var_name, op, rhs)
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

        // Generate a simple boolean guard condition to prevent mutual recursion.
        // The call only executes when the condition is true, providing a
        // non-recursive fallback path through the else/default branch.
        let guard_cond = {
            let expr_ctx3 = ctx.to_expr_context();
            let mut eg = ExprGenerator::new(self.rng, &self.config.expr_config);
            eg.generate_simple(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx3)
        };

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
                    // Skip generic functions, void return, fallible return, and self
                    if info.type_params.is_empty()
                        && !matches!(info.return_type, TypeInfo::Void)
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

        // Generate a simple boolean guard condition to prevent mutual recursion
        let guard_cond = {
            let expr_ctx2 = ctx.to_expr_context();
            let mut eg = ExprGenerator::new(self.rng, &self.config.expr_config);
            eg.generate_simple(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx2)
        };

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
    fn format_block(&self, stmts: &[String]) -> String {
        if stmts.is_empty() {
            return "{ }".to_string();
        }

        let indent = "    ".repeat(self.indent + 1);
        let inner: Vec<String> = stmts.iter().map(|s| format!("{}{}", indent, s)).collect();

        format!("{{\n{}\n{}}}", inner.join("\n"), "    ".repeat(self.indent))
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
    fn generate_array_let(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();
        let elem_prim = PrimitiveType::random_array_element_type(self.rng);
        let elem_ty = TypeInfo::Primitive(elem_prim);

        // Generate 2-4 elements so indexing with 0..=2 is safe
        let elem_count = self.rng.gen_range(2..=4);
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);

        let elements: Vec<String> = (0..elem_count)
            .map(|_| expr_gen.literal_for_primitive(elem_prim))
            .collect();

        let array_ty = TypeInfo::Array(Box::new(elem_ty));
        ctx.add_local(name.clone(), array_ty, false);

        format!("let {} = [{}]", name, elements.join(", "))
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

        // Generate field values for construction
        let fields = self.generate_field_values(&class_info.fields, ctx);
        let ty = TypeInfo::Class(module_id, *sym_id);

        ctx.add_local(name.clone(), ty, false);

        // Build the base expression (class construction)
        let mut expr = format!("{} {{ {} }}", class_name, fields);

        // Try to chain Self-returning methods
        let chain = self.try_generate_method_chain(ctx.table, module_id, *sym_id, ctx);
        if !chain.is_empty() {
            expr = format!("{}{}", expr, chain);
        }

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
        class_id: crate::symbols::SymbolId,
        ctx: &mut StmtContext,
    ) -> String {
        // Get chainable methods for this class
        let methods = get_chainable_methods(table, mod_id, class_id);

        // Filter to Self-returning methods only
        let self_returning: Vec<_> = methods.iter().filter(|m| m.returns_self).collect();
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

            // Generate arguments for the method call
            let args: Vec<String> = method
                .params
                .iter()
                .map(|p| {
                    let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
                    expr_gen.generate_simple(&p.param_type, &expr_ctx)
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
    /// Restricted to i64 and string due to a cross-module lambda codegen
    /// bug (vol-pz4y) where non-i64 return types get miscompiled when
    /// the containing module is imported. Expand once fixed.
    fn random_lambda_return_type(&mut self) -> TypeInfo {
        let prim = match self.rng.gen_range(0..2) {
            0 => PrimitiveType::I64,
            _ => PrimitiveType::String,
        };
        TypeInfo::Primitive(prim)
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

            // Add an i64 local so variable bounds can be used
            ctx.add_local(
                "n".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
                false,
            );

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
}
