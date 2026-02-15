//! Control flow expression generation: if, when, match, boolean operators.

use rand::Rng;

use super::{ExprContext, ExprGenerator};
use crate::symbols::{PrimitiveType, TypeInfo};

impl<'a, R: Rng> ExprGenerator<'a, R> {
    /// Generate a binary arithmetic expression.
    pub(super) fn generate_binary_arith(
        &mut self,
        prim: PrimitiveType,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        // For integer types, 25% chance to generate a bitwise op instead
        if matches!(prim, PrimitiveType::I32 | PrimitiveType::I64) && self.rng.gen_bool(0.25) {
            return self.generate_binary_bitwise(prim, ctx, depth);
        }

        let ty = TypeInfo::Primitive(prim);
        let left = self.generate(&ty, ctx, depth + 1);
        let right = self.generate(&ty, ctx, depth + 1);

        // ~20% chance to generate modulo with a safe non-zero RHS
        if self.rng.gen_bool(0.20) {
            let rhs = self.nonzero_literal_for_primitive(prim);
            return format!("({} % {})", left, rhs);
        }

        let op = match self.rng.gen_range(0..4) {
            0 => "+",
            1 => "-",
            2 => "*",
            // Avoid division by zero by using addition instead
            _ => "+",
        };

        format!("({} {} {})", left, op, right)
    }

    /// Generate a binary bitwise expression (integer types only).
    ///
    /// Produces `&`, `|`, `^`, `<<`, or `>>`. For shift operators the RHS
    /// is constrained to a small literal to avoid undefined behaviour.
    pub(super) fn generate_binary_bitwise(
        &mut self,
        prim: PrimitiveType,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        let ty = TypeInfo::Primitive(prim);
        let left = self.generate(&ty, ctx, depth + 1);

        let op = match self.rng.gen_range(0..5) {
            0 => "&",
            1 => "|",
            2 => "^",
            3 => "<<",
            _ => ">>",
        };

        // For shift operators, use a small literal RHS to avoid UB
        let right = if op == "<<" || op == ">>" {
            let max_shift = match prim {
                PrimitiveType::I32 => 15,
                PrimitiveType::I64 => 31,
                _ => unreachable!(),
            };
            let shift_amount = self.rng.gen_range(0..=max_shift);
            let suffix = match prim {
                PrimitiveType::I32 => "_i32",
                PrimitiveType::I64 => "_i64",
                _ => unreachable!(),
            };
            format!("{}{}", shift_amount, suffix)
        } else {
            self.generate(&ty, ctx, depth + 1)
        };

        format!("({} {} {})", left, op, right)
    }

    /// Generate a comparison expression.
    pub(super) fn generate_comparison(&mut self, ctx: &ExprContext, depth: usize) -> String {
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
    pub(super) fn generate_binary_bool(&mut self, ctx: &ExprContext, depth: usize) -> String {
        let ty = TypeInfo::Primitive(PrimitiveType::Bool);
        let left = self.generate(&ty, ctx, depth + 1);
        let right = self.generate(&ty, ctx, depth + 1);

        let op = if self.rng.gen_bool(0.5) { "&&" } else { "||" };

        format!("({} {} {})", left, op, right)
    }

    /// Generate a negated compound boolean expression.
    ///
    /// Produces expressions like `!(a > b)`, `!(a && b)`, or `!(a || b)`.
    /// This exercises the combination of boolean negation with compound
    /// sub-expressions (comparisons and binary boolean operators), which
    /// differs from the simple unary-not case that only negates literals
    /// or variable references.
    pub(super) fn generate_negated_compound_bool(
        &mut self,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        let inner = if self.rng.gen_bool(0.5) {
            // Negate a comparison: !(x > y), !(a == b), etc.
            self.generate_comparison(ctx, depth + 1)
        } else {
            // Negate a binary boolean: !(a && b), !(a || b)
            self.generate_binary_bool(ctx, depth + 1)
        };

        format!("(!{})", inner)
    }

    /// Generate a compound boolean expression with mixed `&&` and `||` operators.
    ///
    /// Produces expressions like `(a > 0 && b < 10) || c`, `(x || y) && (z > 5)`,
    /// or `(a && b) || (c && d)`. This exercises the compiler's short-circuit
    /// evaluation across parenthesized sub-groups with different operators,
    /// which is more complex than the single-operator `generate_binary_bool`.
    pub(super) fn generate_compound_bool(&mut self, ctx: &ExprContext, depth: usize) -> String {
        // Pick the top-level operator; sub-groups use the opposite to ensure mixing.
        let top_op = if self.rng.gen_bool(0.5) { "||" } else { "&&" };
        let inner_op = if top_op == "||" { "&&" } else { "||" };

        // Generate 2-3 sub-groups joined by top_op.
        let group_count = self.rng.gen_range(2..=3_usize);
        let groups: Vec<String> = (0..group_count)
            .map(|_| {
                // Each sub-group is either a parenthesized pair joined by inner_op,
                // or a single boolean atom (comparison or simple bool).
                if self.rng.gen_bool(0.65) {
                    // Parenthesized pair with the inner operator
                    let a = self.generate_bool_atom(ctx, depth + 1);
                    let b = self.generate_bool_atom(ctx, depth + 1);
                    format!("({} {} {})", a, inner_op, b)
                } else {
                    // Single atom (no extra parens needed; generate wraps if needed)
                    self.generate_bool_atom(ctx, depth + 1)
                }
            })
            .collect();

        format!("({})", groups.join(&format!(" {} ", top_op)))
    }

    /// Generate a simple boolean atom for use in compound expressions.
    ///
    /// Produces either a comparison (`x > 5`), a simple bool variable/literal,
    /// or a negated simple bool. Avoids recursive compound generation to keep
    /// the output bounded.
    pub(super) fn generate_bool_atom(&mut self, ctx: &ExprContext, depth: usize) -> String {
        // ~12% chance to use a string method or iterator predicate as a bool atom.
        // This creates feature interactions between compound bools and method dispatch.
        if self.rng.gen_bool(0.12)
            && let Some(expr) = self.try_generate_method_bool_atom(ctx)
        {
            return expr;
        }
        match self.rng.gen_range(0..4_u32) {
            0..=1 => {
                // Comparison: (a > b), (x == y), etc.
                self.generate_comparison(ctx, depth)
            }
            2 => {
                // Simple bool variable or literal
                self.generate_simple(&TypeInfo::Primitive(PrimitiveType::Bool), ctx)
            }
            _ => {
                // Negated simple bool: !x, !true
                let inner = self.generate_simple(&TypeInfo::Primitive(PrimitiveType::Bool), ctx);
                format!("(!{})", inner)
            }
        }
    }

    /// Try to generate a bool-producing method call for use as a bool atom.
    /// Returns string method calls (contains, starts_with) or iterator predicates
    /// (any, all) when suitable variables are in scope.
    pub fn try_generate_method_bool_atom(&mut self, ctx: &ExprContext) -> Option<String> {
        let string_vars = ctx.string_vars();
        let array_vars = ctx.array_vars();

        // Collect options
        let mut options: Vec<String> = Vec::new();
        for name in &string_vars {
            let words = ["hello", "world", "test", "foo", "bar", ""];
            let word = words[self.rng.gen_range(0..words.len())];
            match self.rng.gen_range(0..3) {
                0 => options.push(format!("{}.contains(\"{}\")", name, word)),
                1 => options.push(format!("{}.starts_with(\"{}\")", name, word)),
                _ => options.push(format!("{}.ends_with(\"{}\")", name, word)),
            }
        }
        for (name, elem_ty) in &array_vars {
            if matches!(
                elem_ty,
                TypeInfo::Primitive(PrimitiveType::I64 | PrimitiveType::I32)
            ) {
                let suffix = if matches!(elem_ty, TypeInfo::Primitive(PrimitiveType::I32)) {
                    "_i32"
                } else {
                    ""
                };
                let threshold = self.rng.gen_range(0..=5);
                let method = if self.rng.gen_bool(0.5) { "any" } else { "all" };
                options.push(format!(
                    "{}.iter().{}((x) => x > {}{})",
                    name, method, threshold, suffix
                ));
            }
        }

        if options.is_empty() {
            return None;
        }
        Some(options.remove(self.rng.gen_range(0..options.len())))
    }

    /// Generate a type test (`is`) expression on a union-typed variable.
    ///
    /// Returns `Some("varName is TypeName")` if a union-typed variable is in scope,
    /// or `None` if no union-typed variables are available.
    pub fn generate_is_expr(&mut self, ctx: &ExprContext) -> Option<String> {
        let union_vars = ctx.union_typed_vars();
        if union_vars.is_empty() {
            return None;
        }

        let var_idx = self.rng.gen_range(0..union_vars.len());
        let (var_name, variants) = union_vars[var_idx];

        if variants.is_empty() {
            return None;
        }

        let variant_idx = self.rng.gen_range(0..variants.len());
        let variant = &variants[variant_idx];

        // Only generate `is` for primitive variants (type name is straightforward)
        match variant {
            TypeInfo::Primitive(prim) => Some(format!("({} is {})", var_name, prim.as_str())),
            _ => None,
        }
    }

    /// Generate a conditional expression using when (Vole's if-expression equivalent).
    ///
    /// Produces a 2-arm when expression: `when { cond => then, _ => else }`.
    /// This is distinct from generate_when_expr which produces 2-4 arms.
    pub(super) fn generate_if_expr(
        &mut self,
        ty: &TypeInfo,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        let cond = self.generate(&TypeInfo::Primitive(PrimitiveType::Bool), ctx, depth + 1);
        let then_expr = self.generate(ty, ctx, depth + 1);
        let else_expr = self.generate(ty, ctx, depth + 1);

        format!("when {{ {} => {}, _ => {} }}", cond, then_expr, else_expr)
    }

    /// Generate a when expression.
    ///
    /// Optionally uses `unreachable` in the wildcard arm when one of the
    /// preceding conditions is guaranteed to be true (e.g., `true => ...`).
    pub(super) fn generate_when_expr(
        &mut self,
        ty: &TypeInfo,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        // Decide if we want to use unreachable in the default arm
        let use_unreachable = self.rng.gen_bool(self.config.unreachable_probability);

        // Decide arm count: either 2 (1 condition + wildcard) or 3-4 (multi-arm)
        let arm_count = if self.rng.gen_bool(self.config.multi_arm_when_probability) {
            // Multi-arm: 3-4 total arms (2-3 conditions + wildcard)
            self.rng.gen_range(3..=4)
        } else {
            // Simple: 2 total arms (1 condition + wildcard)
            2
        };
        let mut arms = Vec::new();

        if use_unreachable {
            // Generate a "true" condition to guarantee the default arm is unreachable
            let value = self.generate(ty, ctx, depth + 1);
            arms.push(format!("true => {}", value));

            // Generate additional arms (will never execute, but syntactically valid)
            for _ in 1..arm_count - 1 {
                let cond = self.generate(&TypeInfo::Primitive(PrimitiveType::Bool), ctx, depth + 1);
                let arm_value = self.generate(ty, ctx, depth + 1);
                arms.push(format!("{} => {}", cond, arm_value));
            }

            // Default arm with unreachable
            arms.push("_ => unreachable".to_string());
        } else {
            // Normal when expression
            for _ in 0..arm_count - 1 {
                let cond = self.generate(&TypeInfo::Primitive(PrimitiveType::Bool), ctx, depth + 1);
                let value = self.generate(ty, ctx, depth + 1);
                arms.push(format!("{} => {}", cond, value));
            }

            // Default arm with a value
            let default_value = self.generate(ty, ctx, depth + 1);
            arms.push(format!("_ => {}", default_value));
        }

        format!("when {{ {} }}", arms.join(", "))
    }

    /// Generate a match expression.
    ///
    /// Optionally uses `unreachable` in the wildcard arm when the subject is
    /// a known literal value and one of the preceding patterns matches it.
    pub fn generate_match_expr(
        &mut self,
        subject_type: &TypeInfo,
        result_type: &TypeInfo,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        // Decide if we want to use unreachable in the default arm
        let use_unreachable = self.rng.gen_bool(self.config.unreachable_probability);

        if use_unreachable {
            // Generate a match where the default arm is provably unreachable
            // by matching on a known literal and including a pattern for it
            return self.generate_match_with_unreachable(subject_type, result_type, ctx, depth);
        }

        // Normal match expression
        let subject = self.generate(subject_type, ctx, depth + 1);
        let max_arms = self.config.max_match_arms.max(2);
        let arm_count = self.rng.gen_range(2..=max_arms);
        let mut arms = Vec::new();

        // Generate some literal or guarded arms
        for _ in 0..arm_count - 1 {
            let pattern = self.generate_pattern(subject_type, Some(ctx), depth);
            let value = self.generate(result_type, ctx, depth + 1);
            arms.push(format!("{} => {}", pattern, value));
        }

        // Always end with wildcard for exhaustiveness.
        // Sometimes generate a guarded wildcard arm before the bare wildcard.
        if self.rng.gen_bool(self.config.match_guard_probability) {
            let guard_cond = self.generate_guard_condition(Some(ctx), depth);
            let guarded_value = self.generate(result_type, ctx, depth + 1);
            arms.push(format!("_ if {} => {}", guard_cond, guarded_value));
        }
        let default_value = self.generate(result_type, ctx, depth + 1);
        arms.push(format!("_ => {}", default_value));

        format!("match {} {{ {} }}", subject, arms.join(", "))
    }

    /// Generate a match expression where the default arm uses `unreachable`.
    ///
    /// Creates a pattern like:
    /// ```vole
    /// match 5 {
    ///     5 => "five",
    ///     _ => unreachable
    /// }
    /// ```
    fn generate_match_with_unreachable(
        &mut self,
        subject_type: &TypeInfo,
        result_type: &TypeInfo,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        // Generate a known literal subject for primitive types
        let (subject_literal, pattern) = match subject_type {
            TypeInfo::Primitive(prim) => {
                let lit = self.literal_for_primitive(*prim);
                (lit.clone(), lit)
            }
            _ => {
                // For non-primitive types, fall back to a normal match
                return self.generate_match_expr_normal(subject_type, result_type, ctx, depth);
            }
        };

        let max_arms = self.config.max_match_arms.max(2);
        let arm_count = self.rng.gen_range(2..=max_arms);
        let mut arms = Vec::new();

        // First arm matches the known subject value
        let first_value = self.generate(result_type, ctx, depth + 1);
        arms.push(format!("{} => {}", pattern, first_value));

        // Generate additional non-matching arms (won't execute but valid syntax)
        for _ in 1..arm_count - 1 {
            let other_pattern = self.generate_pattern(subject_type, Some(ctx), depth);
            let value = self.generate(result_type, ctx, depth + 1);
            arms.push(format!("{} => {}", other_pattern, value));
        }

        // Default arm with unreachable
        arms.push("_ => unreachable".to_string());

        format!("match {} {{ {} }}", subject_literal, arms.join(", "))
    }

    /// Generate a normal match expression (internal helper for fallback).
    fn generate_match_expr_normal(
        &mut self,
        subject_type: &TypeInfo,
        result_type: &TypeInfo,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        let subject = self.generate(subject_type, ctx, depth + 1);
        let max_arms = self.config.max_match_arms.max(2);
        let arm_count = self.rng.gen_range(2..=max_arms);
        let mut arms = Vec::new();

        for _ in 0..arm_count - 1 {
            let pattern = self.generate_pattern(subject_type, Some(ctx), depth);
            let value = self.generate(result_type, ctx, depth + 1);
            arms.push(format!("{} => {}", pattern, value));
        }

        // Sometimes generate a guarded wildcard arm before the bare wildcard.
        if self.rng.gen_bool(self.config.match_guard_probability) {
            let guard_cond = self.generate_guard_condition(Some(ctx), depth);
            let guarded_value = self.generate(result_type, ctx, depth + 1);
            arms.push(format!("_ if {} => {}", guard_cond, guarded_value));
        }
        let default_value = self.generate(result_type, ctx, depth + 1);
        arms.push(format!("_ => {}", default_value));

        format!("match {} {{ {} }}", subject, arms.join(", "))
    }

    /// Generate a match pattern.
    ///
    /// Accepts an optional `ExprContext` and `depth` to generate richer guard
    /// expressions that reference variables in scope (comparisons, compound
    /// booleans, `val` patterns). When `ctx` is `None`, falls back to simple
    /// literal guards.
    fn generate_pattern(
        &mut self,
        ty: &TypeInfo,
        ctx: Option<&ExprContext>,
        depth: usize,
    ) -> String {
        match ty {
            TypeInfo::Primitive(prim) => {
                // With context available, we can generate richer patterns
                let range = if ctx.is_some() { 5 } else { 3 };
                match self.rng.gen_range(0..range) {
                    0 => "_".to_string(), // Wildcard
                    1 => {
                        // Literal pattern
                        self.literal_for_primitive(*prim)
                    }
                    2 => {
                        // Guarded wildcard with expression
                        let cond = self.generate_guard_condition(ctx, depth);
                        format!("_ if {}", cond)
                    }
                    3 => {
                        // `val` pattern: compare against an existing variable
                        // in scope of the same type (exercises the val-pattern codepath)
                        if let Some(ctx) = ctx
                            && let Some(var) = ctx.find_matching_var(&TypeInfo::Primitive(*prim))
                        {
                            return format!("val {}", var);
                        }
                        // Fallback to literal
                        self.literal_for_primitive(*prim)
                    }
                    _ => {
                        // `val` pattern with guard: `val x if cond => ...`
                        if let Some(ctx) = ctx
                            && let Some(var) = ctx.find_matching_var(&TypeInfo::Primitive(*prim))
                        {
                            let cond = self.generate_guard_condition(Some(ctx), depth);
                            return format!("val {} if {}", var, cond);
                        }
                        // Fallback to guarded wildcard
                        let cond = self.generate_guard_condition(ctx, depth);
                        format!("_ if {}", cond)
                    }
                }
            }
            _ => "_".to_string(),
        }
    }

    /// Generate a guard condition for a match arm.
    ///
    /// When an `ExprContext` is available, produces comparison-based conditions
    /// referencing numeric variables in scope (e.g. `x > 42`, `x >= 10 && x < 100`).
    /// Falls back to boolean literals when no variables are available.
    pub fn generate_guard_condition(&mut self, ctx: Option<&ExprContext>, depth: usize) -> String {
        if let Some(ctx) = ctx {
            // Use integer-only vars for comparisons with integer literals
            let numeric = ctx.integer_vars();
            if !numeric.is_empty() {
                let var_idx = self.rng.gen_range(0..numeric.len());
                let var = &numeric[var_idx];

                match self.rng.gen_range(0..4) {
                    0 => {
                        // Simple comparison: x > literal
                        let op = match self.rng.gen_range(0..4) {
                            0 => ">",
                            1 => "<",
                            2 => ">=",
                            _ => "<=",
                        };
                        let lit = self.rng.gen_range(0..100);
                        return format!("{} {} {}", var, op, lit);
                    }
                    1 => {
                        // Equality check: x == literal
                        let lit = self.rng.gen_range(0..50);
                        return format!("{} == {}", var, lit);
                    }
                    2 => {
                        // Compound range check: x > low && x < high
                        let low = self.rng.gen_range(0..50);
                        let high = low + self.rng.gen_range(10..100);
                        return format!("{} > {} && {} < {}", var, low, var, high);
                    }
                    _ => {
                        // Inequality: x != literal
                        let lit = self.rng.gen_range(0..50);
                        return format!("{} != {}", var, lit);
                    }
                }
            }

            // Try boolean variables
            let bools = ctx.bool_vars();
            if !bools.is_empty() {
                let var_idx = self.rng.gen_range(0..bools.len());
                let var = &bools[var_idx];
                if self.rng.gen_bool(0.5) {
                    return var.clone();
                } else {
                    return format!("!{}", var);
                }
            }

            // Fall back to a full bool expression generation if we have depth budget
            if depth + 1 < 3 {
                return self.generate(&TypeInfo::Primitive(PrimitiveType::Bool), ctx, depth + 1);
            }
        }

        // Ultimate fallback: literal boolean
        self.literal_for_primitive(PrimitiveType::Bool)
    }
}
