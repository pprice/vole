//! Grammar-based expression generation.
//!
//! This module generates type-correct Vole expressions using grammar rules.
//! Expressions are generated with depth limits to prevent infinite recursion.

use rand::Rng;

use crate::symbols::{ParamInfo, PrimitiveType, SymbolTable, TypeInfo};

/// Configuration for expression generation.
#[derive(Debug, Clone)]
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
}

impl Default for ExprConfig {
    fn default() -> Self {
        Self {
            max_depth: 3,
            binary_probability: 0.4,
            when_probability: 0.1,
            match_probability: 0.1,
            if_expr_probability: 0.15,
            lambda_probability: 0.05,
        }
    }
}

/// Context for expression generation within a scope.
#[allow(dead_code)]
pub struct ExprContext<'a> {
    /// Available parameters in scope.
    pub params: &'a [ParamInfo],
    /// Available local variables (name, type).
    pub locals: &'a [(String, TypeInfo)],
    /// Symbol table for type lookups.
    pub table: &'a SymbolTable,
}

#[allow(dead_code)]
impl<'a> ExprContext<'a> {
    /// Create a new expression context.
    pub fn new(
        params: &'a [ParamInfo],
        locals: &'a [(String, TypeInfo)],
        table: &'a SymbolTable,
    ) -> Self {
        Self {
            params,
            locals,
            table,
        }
    }

    /// Find a variable in scope matching the given type.
    pub fn find_matching_var(&self, target_type: &TypeInfo) -> Option<String> {
        // Check locals first
        for (name, ty) in self.locals {
            if types_compatible(ty, target_type) {
                return Some(name.clone());
            }
        }
        // Check params
        for param in self.params {
            if types_compatible(&param.param_type, target_type) {
                return Some(param.name.clone());
            }
        }
        None
    }

    /// Get all numeric variables in scope.
    pub fn numeric_vars(&self) -> Vec<String> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            if is_numeric_type(ty) {
                vars.push(name.clone());
            }
        }
        for param in self.params {
            if is_numeric_type(&param.param_type) {
                vars.push(param.name.clone());
            }
        }
        vars
    }

    /// Get all boolean variables in scope.
    pub fn bool_vars(&self) -> Vec<String> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            if matches!(ty, TypeInfo::Primitive(PrimitiveType::Bool)) {
                vars.push(name.clone());
            }
        }
        for param in self.params {
            if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::Bool)) {
                vars.push(param.name.clone());
            }
        }
        vars
    }

    /// Get all variables in scope (any type), for use in string interpolation.
    pub fn all_vars(&self) -> Vec<(&str, &TypeInfo)> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            vars.push((name.as_str(), ty));
        }
        for param in self.params {
            vars.push((param.name.as_str(), &param.param_type));
        }
        vars
    }
}

/// Check if two types are compatible for expression generation.
fn types_compatible(actual: &TypeInfo, expected: &TypeInfo) -> bool {
    match (actual, expected) {
        (TypeInfo::Primitive(a), TypeInfo::Primitive(e)) => a == e,
        (TypeInfo::Void, TypeInfo::Void) => true,
        (TypeInfo::Optional(a), TypeInfo::Optional(e)) => types_compatible(a, e),
        (TypeInfo::Array(a), TypeInfo::Array(e)) => types_compatible(a, e),
        _ => false,
    }
}

/// Check if a type is numeric.
#[allow(dead_code)]
fn is_numeric_type(ty: &TypeInfo) -> bool {
    matches!(
        ty,
        TypeInfo::Primitive(PrimitiveType::I32)
            | TypeInfo::Primitive(PrimitiveType::I64)
            | TypeInfo::Primitive(PrimitiveType::F64)
    )
}

/// Expression generator.
pub struct ExprGenerator<'a, R> {
    rng: &'a mut R,
    config: &'a ExprConfig,
}

impl<'a, R: Rng> ExprGenerator<'a, R> {
    /// Create a new expression generator.
    pub fn new(rng: &'a mut R, config: &'a ExprConfig) -> Self {
        Self { rng, config }
    }

    /// Generate an expression of the given type.
    pub fn generate(&mut self, ty: &TypeInfo, ctx: &ExprContext, depth: usize) -> String {
        // At max depth, always return a simple expression
        if depth >= self.config.max_depth {
            return self.generate_simple(ty, ctx);
        }

        match ty {
            TypeInfo::Primitive(prim) => self.generate_primitive(*prim, ctx, depth),
            TypeInfo::Optional(inner) => self.generate_optional(inner, ctx, depth),
            TypeInfo::Void => "nil".to_string(),
            TypeInfo::Array(elem) => self.generate_array(elem, ctx, depth),
            TypeInfo::TypeParam(name) => {
                // For type params, try to find a matching parameter, else use panic
                for param in ctx.params {
                    if let TypeInfo::TypeParam(param_type_name) = &param.param_type
                        && param_type_name == name
                    {
                        return param.name.clone();
                    }
                }
                // No matching parameter found - use panic (this shouldn't happen with good planning)
                "panic(\"unreachable: type parameter has no source\")".to_string()
            }
            _ => self.generate_simple(ty, ctx),
        }
    }

    /// Generate a simple expression (literal or variable reference).
    fn generate_simple(&mut self, ty: &TypeInfo, ctx: &ExprContext) -> String {
        // Try to find a matching variable first
        if let Some(var) = ctx.find_matching_var(ty)
            && self.rng.gen_bool(0.6)
        {
            return var;
        }

        // Otherwise generate a literal
        match ty {
            TypeInfo::Primitive(p) => self.literal_for_primitive(*p),
            TypeInfo::Optional(_) => "nil".to_string(),
            TypeInfo::Void => "nil".to_string(),
            _ => self.literal_for_primitive(PrimitiveType::I64),
        }
    }

    /// Generate a primitive expression.
    fn generate_primitive(
        &mut self,
        prim: PrimitiveType,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        let choice = self.rng.gen_range(0..10);

        match prim {
            PrimitiveType::I32 | PrimitiveType::I64 | PrimitiveType::F64 => {
                match choice {
                    0..=3 => {
                        // Binary arithmetic expression
                        self.generate_binary_arith(prim, ctx, depth)
                    }
                    4 => {
                        // Unary negation - generate a negated literal
                        let suffix = match prim {
                            PrimitiveType::I32 => "_i32",
                            PrimitiveType::I64 => "_i64",
                            PrimitiveType::F64 => "_f64",
                            _ => "",
                        };
                        let val = self.rng.gen_range(1..100);
                        format!("(-{}{})", val, suffix)
                    }
                    5..=6 => {
                        // Multi-arm when expression
                        self.generate_when_expr(&TypeInfo::Primitive(prim), ctx, depth)
                    }
                    7 => {
                        // Match expression
                        let ty = TypeInfo::Primitive(prim);
                        self.generate_match_expr(&ty, &ty, ctx, depth)
                    }
                    8 => {
                        // Two-arm conditional (if-expression equivalent)
                        self.generate_if_expr(&TypeInfo::Primitive(prim), ctx, depth)
                    }
                    _ => self.generate_simple(&TypeInfo::Primitive(prim), ctx),
                }
            }
            PrimitiveType::Bool => {
                match choice {
                    0..=2 => {
                        // Comparison expression
                        self.generate_comparison(ctx, depth)
                    }
                    3..=4 => {
                        // Boolean binary (and/or)
                        self.generate_binary_bool(ctx, depth)
                    }
                    5 => {
                        // Unary not - only negate simple expressions
                        let inner =
                            self.generate_simple(&TypeInfo::Primitive(PrimitiveType::Bool), ctx);
                        format!("(!{})", inner)
                    }
                    6 => {
                        // Match expression
                        let ty = TypeInfo::Primitive(prim);
                        self.generate_match_expr(&ty, &ty, ctx, depth)
                    }
                    7 => {
                        // Two-arm conditional (if-expression equivalent)
                        self.generate_if_expr(&TypeInfo::Primitive(prim), ctx, depth)
                    }
                    _ => self.generate_simple(&TypeInfo::Primitive(prim), ctx),
                }
            }
            PrimitiveType::String => {
                match choice {
                    0..=1 => {
                        // Multi-arm when expression returning string
                        self.generate_when_expr(&TypeInfo::Primitive(prim), ctx, depth)
                    }
                    2..=3 => {
                        // Match expression
                        let ty = TypeInfo::Primitive(prim);
                        self.generate_match_expr(&ty, &ty, ctx, depth)
                    }
                    4..=5 => {
                        // Two-arm conditional (if-expression equivalent)
                        self.generate_if_expr(&TypeInfo::Primitive(prim), ctx, depth)
                    }
                    6..=8 => {
                        // Interpolated string (~30%)
                        self.generate_interpolated_string(ctx)
                    }
                    _ => self.generate_simple(&TypeInfo::Primitive(prim), ctx),
                }
            }
            PrimitiveType::Nil => "nil".to_string(),
        }
    }

    /// Generate a binary arithmetic expression.
    fn generate_binary_arith(
        &mut self,
        prim: PrimitiveType,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        let ty = TypeInfo::Primitive(prim);
        let left = self.generate(&ty, ctx, depth + 1);
        let right = self.generate(&ty, ctx, depth + 1);

        let op = match self.rng.gen_range(0..4) {
            0 => "+",
            1 => "-",
            2 => "*",
            // Avoid division by zero by using addition instead
            _ => "+",
        };

        format!("({} {} {})", left, op, right)
    }

    /// Generate a comparison expression.
    fn generate_comparison(&mut self, ctx: &ExprContext, depth: usize) -> String {
        let prim = match self.rng.gen_range(0..3) {
            0 => PrimitiveType::I32,
            1 => PrimitiveType::I64,
            _ => PrimitiveType::F64,
        };
        let ty = TypeInfo::Primitive(prim);
        let left = self.generate(&ty, ctx, depth + 1);
        let right = self.generate(&ty, ctx, depth + 1);

        let op = match self.rng.gen_range(0..6) {
            0 => "==",
            1 => "!=",
            2 => "<",
            3 => ">",
            4 => "<=",
            _ => ">=",
        };

        format!("({} {} {})", left, op, right)
    }

    /// Generate a binary boolean expression.
    fn generate_binary_bool(&mut self, ctx: &ExprContext, depth: usize) -> String {
        let ty = TypeInfo::Primitive(PrimitiveType::Bool);
        let left = self.generate(&ty, ctx, depth + 1);
        let right = self.generate(&ty, ctx, depth + 1);

        let op = if self.rng.gen_bool(0.5) { "&&" } else { "||" };

        format!("({} {} {})", left, op, right)
    }

    /// Generate a conditional expression using when (Vole's if-expression equivalent).
    ///
    /// Produces a 2-arm when expression: `when { cond => then, _ => else }`.
    /// This is distinct from generate_when_expr which produces 2-4 arms.
    fn generate_if_expr(&mut self, ty: &TypeInfo, ctx: &ExprContext, depth: usize) -> String {
        let cond = self.generate(&TypeInfo::Primitive(PrimitiveType::Bool), ctx, depth + 1);
        let then_expr = self.generate(ty, ctx, depth + 1);
        let else_expr = self.generate(ty, ctx, depth + 1);

        format!("when {{ {} => {}, _ => {} }}", cond, then_expr, else_expr)
    }

    /// Generate a when expression.
    fn generate_when_expr(&mut self, ty: &TypeInfo, ctx: &ExprContext, depth: usize) -> String {
        let arm_count = self.rng.gen_range(2..=4);
        let mut arms = Vec::new();

        for _ in 0..arm_count - 1 {
            let cond = self.generate(&TypeInfo::Primitive(PrimitiveType::Bool), ctx, depth + 1);
            let value = self.generate(ty, ctx, depth + 1);
            arms.push(format!("{} => {}", cond, value));
        }

        // Default arm with wildcard
        let default_value = self.generate(ty, ctx, depth + 1);
        arms.push(format!("_ => {}", default_value));

        format!("when {{ {} }}", arms.join(", "))
    }

    /// Generate an optional expression.
    fn generate_optional(&mut self, inner: &TypeInfo, ctx: &ExprContext, depth: usize) -> String {
        // 50% chance of nil, 50% chance of value
        if self.rng.gen_bool(0.5) {
            "nil".to_string()
        } else {
            self.generate(inner, ctx, depth)
        }
    }

    /// Generate an array expression.
    fn generate_array(&mut self, elem: &TypeInfo, ctx: &ExprContext, depth: usize) -> String {
        let len = self.rng.gen_range(0..=4);
        if len == 0 {
            return "[]".to_string();
        }

        let elements: Vec<String> = (0..len)
            .map(|_| self.generate(elem, ctx, depth + 1))
            .collect();

        format!("[{}]", elements.join(", "))
    }

    /// Generate an interpolated string expression.
    ///
    /// Produces strings like `"value is {param0}"` or `"sum: {a + 1_i64}"`.
    /// Falls back to a plain string literal if no variables are in scope.
    fn generate_interpolated_string(&mut self, ctx: &ExprContext) -> String {
        let vars = ctx.all_vars();
        if vars.is_empty() {
            let id = self.rng.gen_range(0..100);
            return format!("\"str{}\"", id);
        }

        let interp_count = self.rng.gen_range(1..=2.min(vars.len()));
        let mut parts = Vec::new();

        // Optional leading text
        if self.rng.gen_bool(0.6) {
            let prefixes = ["val: ", "result: ", "got ", "x=", ""];
            let idx = self.rng.gen_range(0..prefixes.len());
            let prefix = prefixes[idx];
            if !prefix.is_empty() {
                parts.push(prefix.to_string());
            }
        }

        for i in 0..interp_count {
            let var_idx = self.rng.gen_range(0..vars.len());
            let (name, ty) = vars[var_idx];

            let interp_expr = self.interp_expr_for_var(name, ty);
            parts.push(format!("{{{}}}", interp_expr));

            // Add separator text between interpolations
            if i + 1 < interp_count {
                let seps = [", ", " | ", " and ", " - "];
                let idx = self.rng.gen_range(0..seps.len());
                parts.push(seps[idx].to_string());
            }
        }

        // Optional trailing text
        if self.rng.gen_bool(0.4) {
            let suffixes = [" done", "!", " ok", ""];
            let idx = self.rng.gen_range(0..suffixes.len());
            let suffix = suffixes[idx];
            if !suffix.is_empty() {
                parts.push(suffix.to_string());
            }
        }

        format!("\"{}\"", parts.join(""))
    }

    /// Generate an interpolation expression for a variable.
    ///
    /// For numeric types, sometimes wraps in arithmetic (e.g. `param0 + 1_i64`).
    /// For other types, just references the variable directly.
    fn interp_expr_for_var(&mut self, name: &str, ty: &TypeInfo) -> String {
        match ty {
            TypeInfo::Primitive(PrimitiveType::I32) if self.rng.gen_bool(0.3) => {
                let n = self.rng.gen_range(1..10);
                format!("{} + {}_i32", name, n)
            }
            TypeInfo::Primitive(PrimitiveType::I64) if self.rng.gen_bool(0.3) => {
                let n = self.rng.gen_range(1..10);
                format!("{} + {}_i64", name, n)
            }
            _ => name.to_string(),
        }
    }

    /// Generate a literal for a primitive type.
    pub fn literal_for_primitive(&mut self, prim: PrimitiveType) -> String {
        match prim {
            PrimitiveType::I32 => {
                let val: i32 = self.rng.gen_range(0..100);
                format!("{}_i32", val)
            }
            PrimitiveType::I64 => {
                let val: i64 = self.rng.gen_range(0..1000);
                format!("{}_i64", val)
            }
            PrimitiveType::F64 => {
                let val: f64 = self.rng.gen_range(0.0..100.0);
                format!("{:.2}_f64", val)
            }
            PrimitiveType::Bool => {
                if self.rng.gen_bool(0.5) {
                    "true".to_string()
                } else {
                    "false".to_string()
                }
            }
            PrimitiveType::String => {
                let id = self.rng.gen_range(0..100);
                format!("\"str{}\"", id)
            }
            PrimitiveType::Nil => "nil".to_string(),
        }
    }

    /// Generate a match expression.
    pub fn generate_match_expr(
        &mut self,
        subject_type: &TypeInfo,
        result_type: &TypeInfo,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        let subject = self.generate(subject_type, ctx, depth + 1);
        let arm_count = self.rng.gen_range(2..=4);
        let mut arms = Vec::new();

        // Generate some literal or guarded arms
        for _ in 0..arm_count - 1 {
            let pattern = self.generate_pattern(subject_type);
            let value = self.generate(result_type, ctx, depth + 1);
            arms.push(format!("{} => {}", pattern, value));
        }

        // Always end with wildcard for exhaustiveness
        let default_value = self.generate(result_type, ctx, depth + 1);
        arms.push(format!("_ => {}", default_value));

        format!("match {} {{ {} }}", subject, arms.join(", "))
    }

    /// Generate a match pattern.
    fn generate_pattern(&mut self, ty: &TypeInfo) -> String {
        match ty {
            TypeInfo::Primitive(prim) => {
                match self.rng.gen_range(0..3) {
                    0 => "_".to_string(), // Wildcard
                    1 => {
                        // Literal pattern
                        self.literal_for_primitive(*prim)
                    }
                    _ => {
                        // Guarded wildcard
                        let cond = self.literal_for_primitive(PrimitiveType::Bool);
                        format!("_ if {}", cond)
                    }
                }
            }
            _ => "_".to_string(),
        }
    }

    /// Generate a lambda expression.
    pub fn generate_lambda(
        &mut self,
        param_types: &[TypeInfo],
        return_type: &TypeInfo,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        // Generate parameter names
        let params: Vec<String> = param_types
            .iter()
            .enumerate()
            .map(|(i, ty)| format!("p{}: {}", i, ty.to_vole_syntax(ctx.table)))
            .collect();

        // Create a new context with the lambda parameters
        let lambda_params: Vec<ParamInfo> = param_types
            .iter()
            .enumerate()
            .map(|(i, ty)| ParamInfo {
                name: format!("p{}", i),
                param_type: ty.clone(),
            })
            .collect();

        let lambda_ctx = ExprContext::new(&lambda_params, &[], ctx.table);

        // Generate the body expression
        let body = self.generate(return_type, &lambda_ctx, depth + 1);

        let return_annotation = match return_type {
            TypeInfo::Void => String::new(),
            _ => format!(" -> {}", return_type.to_vole_syntax(ctx.table)),
        };

        format!("({}){} => {}", params.join(", "), return_annotation, body)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;

    #[test]
    fn test_literal_generation() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = ExprConfig::default();
        let mut generator = ExprGenerator::new(&mut rng, &config);

        let i64_lit = generator.literal_for_primitive(PrimitiveType::I64);
        assert!(!i64_lit.is_empty());

        let bool_lit = generator.literal_for_primitive(PrimitiveType::Bool);
        assert!(bool_lit == "true" || bool_lit == "false");

        let str_lit = generator.literal_for_primitive(PrimitiveType::String);
        assert!(str_lit.starts_with('"'));
    }

    #[test]
    fn test_expr_generation() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = ExprConfig::default();
        let mut generator = ExprGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let ctx = ExprContext::new(&[], &[], &table);

        let i64_expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
        assert!(!i64_expr.is_empty());

        let bool_expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &ctx, 0);
        assert!(!bool_expr.is_empty());
    }

    #[test]
    fn test_when_expr_generation() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = ExprConfig::default();
        let mut generator = ExprGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let ctx = ExprContext::new(&[], &[], &table);

        let when_expr =
            generator.generate_when_expr(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
        assert!(when_expr.contains("when"));
        assert!(when_expr.contains("=>"));
    }

    #[test]
    fn test_interpolated_string_generation() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(99);
        let config = ExprConfig::default();
        let mut generator = ExprGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let params = vec![
            ParamInfo {
                name: "count".to_string(),
                param_type: TypeInfo::Primitive(PrimitiveType::I64),
            },
            ParamInfo {
                name: "label".to_string(),
                param_type: TypeInfo::Primitive(PrimitiveType::String),
            },
        ];
        let ctx = ExprContext::new(&params, &[], &table);

        let interp = generator.generate_interpolated_string(&ctx);
        assert!(interp.starts_with('"'));
        assert!(interp.ends_with('"'));
        // Should contain at least one interpolation brace
        assert!(interp.contains('{'));
        assert!(interp.contains('}'));
    }

    #[test]
    fn test_interpolated_string_no_vars_fallback() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = ExprConfig::default();
        let mut generator = ExprGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let ctx = ExprContext::new(&[], &[], &table);

        // With no variables in scope, should fall back to plain string
        let result = generator.generate_interpolated_string(&ctx);
        assert!(result.starts_with('"'));
        assert!(result.ends_with('"'));
        // Should NOT contain interpolation braces (it's a plain "strN" literal)
        assert!(!result.contains('{'));
    }

    #[test]
    fn test_determinism() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let ctx = ExprContext::new(&[], &[], &table);

        let mut rng1 = rand::rngs::StdRng::seed_from_u64(12345);
        let mut gen1 = ExprGenerator::new(&mut rng1, &config);
        let expr1 = gen1.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);

        let mut rng2 = rand::rngs::StdRng::seed_from_u64(12345);
        let mut gen2 = ExprGenerator::new(&mut rng2, &config);
        let expr2 = gen2.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);

        assert_eq!(expr1, expr2);
    }
}
