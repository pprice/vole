//! String-related statement generators.
//!
//! Contains generators for string interpolation, string split,
//! string method calls, and string helper utilities.

use rand::Rng;

use crate::symbols::{PrimitiveType, TypeInfo};

use super::{StmtContext, StmtGenerator};

impl<'a, R: Rng> StmtGenerator<'a, R> {
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
    pub(super) fn try_generate_string_interpolation_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Collect variables suitable for interpolation (numeric, string, bool)
        let mut candidates: Vec<(String, PrimitiveType)> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Primitive(p) = ty
                && matches!(
                    p,
                    PrimitiveType::I64
                        | PrimitiveType::I32
                        | PrimitiveType::F64
                        | PrimitiveType::String
                        | PrimitiveType::Bool
                )
            {
                candidates.push((name.clone(), *p));
            }
        }
        for p in ctx.params {
            if let TypeInfo::Primitive(pt) = &p.param_type
                && matches!(
                    pt,
                    PrimitiveType::I64
                        | PrimitiveType::I32
                        | PrimitiveType::F64
                        | PrimitiveType::String
                        | PrimitiveType::Bool
                )
            {
                candidates.push((p.name.clone(), *pt));
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
        for (i, (name, prim)) in candidates.iter().enumerate().take(num_segments) {
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
    pub(super) fn generate_string_split_let(&mut self, ctx: &mut StmtContext) -> String {
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
            ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
            format!("let {} = \"{}\".split(\"{}\").count()", name, joined, delim)
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

    /// Try to generate a string method call let-binding.
    ///
    /// Finds a string-typed variable in scope and calls a random method on it:
    /// - `.length()` -> i64
    /// - `.contains("literal")` -> bool
    /// - `.starts_with("literal")` -> bool
    /// - `.ends_with("literal")` -> bool
    /// - `.trim()` -> string
    /// - `.to_upper()` -> string
    /// - `.to_lower()` -> string
    pub(super) fn try_generate_string_method_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn random_short_string<R2: Rng>(rng: &mut R2) -> String {
        let words = [
            "hello", "world", "test", "foo", "bar", "abc", "xyz", "str", "", "\\n", "\\t", " ", "a",
        ];
        words[rng.gen_range(0..words.len())].to_string()
    }
}
