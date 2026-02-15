//! Match and when statement generators.
//!
//! Contains generators for match expressions, when expressions,
//! union match, sentinel union, and optional destructure patterns.

use rand::Rng;

use crate::expr::{ExprContext, ExprGenerator};
use crate::symbols::{ParamInfo, PrimitiveType, SymbolKind, TypeInfo};

use super::{StmtContext, StmtGenerator, has_primitive_field};

impl<'a, R: Rng> StmtGenerator<'a, R> {
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
    pub(super) fn generate_match_arm_value(
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

    pub(super) fn try_generate_match_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
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
    pub(super) fn try_generate_string_match_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn try_generate_when_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
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
    pub(super) fn try_generate_union_match_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find union-typed variables in scope (locals + params) with all-primitive variants
        let mut candidates: Vec<(String, Vec<TypeInfo>)> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Union(variants) = ty
                && variants.iter().all(|v| matches!(v, TypeInfo::Primitive(_)))
            {
                candidates.push((name.clone(), variants.clone()));
            }
        }
        for param in ctx.params.iter() {
            if let TypeInfo::Union(variants) = &param.param_type
                && variants.iter().all(|v| matches!(v, TypeInfo::Primitive(_)))
            {
                candidates.push((param.name.clone(), variants.clone()));
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
    pub(super) fn try_generate_sentinel_union_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
        let mut union_members = vec![prim_type_info.clone(), sentinel_type_info];
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
                indent,
                prim_type.as_str(),
                prim_arm_expr,
                indent,
                sentinel_name,
                sentinel_arm_expr,
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
    pub(super) fn try_generate_optional_destructure_match(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        let module_id = ctx.module_id?;
        let module = ctx.table.get_module(module_id)?;

        // Collect non-generic classes with at least one primitive field
        let class_candidates: Vec<_> = module
            .classes()
            .filter_map(|sym| {
                if let SymbolKind::Class(ref info) = sym.kind
                    && info.type_params.is_empty()
                    && has_primitive_field(info)
                {
                    return Some((sym.id, sym.name.clone(), info.fields.clone(), true));
                }
                None
            })
            .collect();

        // Collect structs with at least one primitive field
        let struct_candidates: Vec<_> = module
            .structs()
            .filter_map(|sym| {
                if let SymbolKind::Struct(ref info) = sym.kind
                    && info.fields.iter().any(|f| f.field_type.is_primitive())
                {
                    return Some((sym.id, sym.name.clone(), info.fields.clone(), false));
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

        let let_stmt = format!("let {}: {}? = {}", opt_var_name, type_name, init_value);

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
            format!("when {{ {} => 1_i64, _ => 0_i64 }}", bool_bindings[0])
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
        ctx.add_local(result_name, TypeInfo::Primitive(PrimitiveType::I64), false);

        Some(format!("{}\n{}", let_stmt, match_stmt))
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
    pub(super) fn try_generate_match_on_method_result(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        let _ = ctx.module_id?;

        // Skip in method bodies to avoid mutual recursion
        if ctx.current_class_sym_id.is_some() {
            return None;
        }

        // Find class-typed locals with methods that return i64
        let mut candidates: Vec<(String, String, Vec<ParamInfo>)> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Class(mod_id, sym_id) = ty
                && let Some(sym) = ctx.table.get_symbol(*mod_id, *sym_id)
                && let SymbolKind::Class(ref info) = sym.kind
                && info.type_params.is_empty()
            {
                for method in &info.methods {
                    if matches!(method.return_type, TypeInfo::Primitive(PrimitiveType::I64)) {
                        candidates.push((name.clone(), method.name.clone(), method.params.clone()));
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
}
