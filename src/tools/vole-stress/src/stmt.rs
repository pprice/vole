//! Grammar-based statement generation.
//!
//! This module generates type-correct Vole statements using grammar rules.
//! Statements are generated with depth limits and proper control flow.

use rand::Rng;

use crate::expr::{ExprConfig, ExprContext, ExprGenerator};
use crate::symbols::{
    ClassInfo, ModuleId, ParamInfo, PrimitiveType, SymbolKind, SymbolTable, TypeInfo,
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
    /// Whether this function is fallible.
    pub is_fallible: bool,
    /// Counter for generating unique local variable names.
    pub local_counter: usize,
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
            is_fallible: false,
            local_counter: 0,
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
            is_fallible: false,
            local_counter: 0,
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

        // Generate return statement
        if !matches!(return_type, TypeInfo::Void) {
            let expr_ctx = ctx.to_expr_context();
            let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
            let return_expr = expr_gen.generate(return_type, &expr_ctx, 0);
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
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let cond = expr_gen.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx, 0);

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
    fn generate_while_statement(&mut self, ctx: &mut StmtContext, depth: usize) -> String {
        // Generate a simple bounded condition to prevent infinite loops
        // We'll use a pattern like: counter < limit
        let counter_name = ctx.new_local_name();
        let limit = self.rng.gen_range(1..=5);

        // Pre-statement to initialize counter (this stays in outer scope)
        ctx.add_local(
            counter_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );

        let was_in_loop = ctx.in_loop;
        ctx.in_loop = true;

        // Generate body (save and restore locals for scoping)
        let locals_before = ctx.locals.len();
        let mut body_stmts = self.generate_block(ctx, depth + 1);
        ctx.locals.truncate(locals_before);
        // Add increment at end
        body_stmts.push(format!("{} = {} + 1", counter_name, counter_name));

        ctx.in_loop = was_in_loop;

        let body_block = self.format_block(&body_stmts);

        format!(
            "let mut {} = 0\n{}while {} < {} {}",
            counter_name,
            self.indent_str(),
            counter_name,
            limit,
            body_block
        )
    }

    /// Generate a for statement.
    fn generate_for_statement(&mut self, ctx: &mut StmtContext, depth: usize) -> String {
        let iter_name = ctx.new_local_name();

        // Generate range
        let start = self.rng.gen_range(0..3);
        let end = start + self.rng.gen_range(1..5);
        let range = format!("{}..{}", start, end);

        let was_in_loop = ctx.in_loop;
        ctx.in_loop = true;

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

        let body_block = self.format_block(&body_stmts);
        format!("for {} in {} {}", iter_name, range, body_block)
    }

    /// Generate a break or continue statement wrapped in a conditional.
    ///
    /// Wraps in `if <condition> { break }` to avoid always exiting on
    /// the first iteration. Only called when `ctx.in_loop` is true.
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

    /// Try to generate a let statement that constructs a class instance.
    ///
    /// Returns `None` if no suitable non-generic class is available in the
    /// current module. Only constructs classes with primitive-typed fields
    /// so the resulting local can be used for field access expressions.
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

        Some(format!("let {} = {} {{ {} }}", name, class_name, fields))
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
    fn random_primitive_type(&mut self) -> TypeInfo {
        let prim = match self.rng.gen_range(0..5) {
            0 => PrimitiveType::I32,
            1 => PrimitiveType::I64,
            2 => PrimitiveType::F64,
            3 => PrimitiveType::Bool,
            _ => PrimitiveType::String,
        };
        TypeInfo::Primitive(prim)
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
}
