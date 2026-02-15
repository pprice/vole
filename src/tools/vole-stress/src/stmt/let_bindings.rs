//! Let-binding statement generators.
//!
//! Contains the large collection of edge-case and pattern generators
//! dispatched from `generate_let_statement` in mod.rs. These cover
//! assertions, dead code, edge cases, string operations, boolean chains,
//! numeric operations, array operations, and more.

use rand::Rng;

use crate::expr::ExprGenerator;
use crate::symbols::{PrimitiveType, SymbolKind, TypeInfo};

use super::{StmtContext, StmtGenerator};

impl<'a, R: Rng> StmtGenerator<'a, R> {
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
    pub(super) fn try_generate_assert_stmt(&mut self, ctx: &mut StmtContext) -> Option<String> {
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

                match self.rng.gen_range(0..3u32) {
                    0 => format!("{}.trim().length() >= 0", name),
                    1 => format!("{}.to_upper().length() == {}.length()", name, name),
                    _ => format!("{}.length() >= 0", name),
                }
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
                    let (name, _) = &prim_candidates[self.rng.gen_range(0..prim_candidates.len())];
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
    pub(super) fn generate_dead_code_assert(&mut self) -> String {
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
    pub(super) fn generate_edge_case_for_loop(
        &mut self,
        ctx: &mut StmtContext,
        depth: usize,
    ) -> String {
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
    pub(super) fn generate_empty_array_iter(&mut self, ctx: &mut StmtContext) -> String {
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
                ctx.add_local(result_name.clone(), TypeInfo::Primitive(elem_type), false);
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
    pub(super) fn generate_edge_case_split(&mut self, ctx: &mut StmtContext) -> String {
        let result_name = ctx.new_local_name();

        let (input, delim) = match self.rng.gen_range(0..4u32) {
            0 => ("\"\"", "\",\""),      // empty string
            1 => ("\"a\"", "\"a\""),     // delimiter == entire string
            2 => ("\",,\"", "\",\""),    // consecutive delimiters
            _ => ("\"a,b,c\"", "\",\""), // normal case for safety
        };

        match self.rng.gen_range(0..3u32) {
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
                format!("let {} = {}.split({}).collect()", result_name, input, delim)
            }
            _ => {
                ctx.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                format!("let {} = {}.split({}).count()", result_name, input, delim)
            }
        }
    }

    /// Generate a while-loop that runs an iterator terminal each iteration and
    /// accumulates the result.  Stresses iterator alloc/dealloc across loop
    /// iterations — the same pattern that exposed the chunks/windows RC bug.
    pub(super) fn try_generate_iter_while_accum(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        let expr_ctx = ctx.to_expr_context();
        let array_vars = expr_ctx.array_vars();
        let prim_arrays: Vec<(String, PrimitiveType)> = array_vars
            .into_iter()
            .filter_map(|(name, elem_ty)| {
                if let TypeInfo::Primitive(prim) = elem_ty
                    && matches!(prim, PrimitiveType::I64 | PrimitiveType::I32)
                {
                    return Some((name, prim));
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
                (
                    format!("{}.iter().filter((x) => {}).count()", arr_name, filter_body),
                    false,
                )
            }
            1 => {
                let map_body = self.generate_map_closure_body(elem_prim);
                (
                    format!("{}.iter().map((x) => {}).sum()", arr_name, map_body),
                    false,
                )
            }
            _ => {
                // Use counter as threshold — tests that loop variable is correctly
                // captured in the filter closure across iterations.
                (
                    format!(
                        "{}.iter().filter((x) => x > {}).count()",
                        arr_name, counter_name
                    ),
                    true,
                )
            }
        };
        let _ = uses_counter;

        ctx.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );
        ctx.add_local(
            counter_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );
        ctx.add_local(
            guard_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );

        ctx.protected_vars.push(counter_name.clone());
        ctx.protected_vars.push(guard_name.clone());
        ctx.protected_vars.push(acc_name.clone());
        ctx.protected_vars.push(arr_name);

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
            indent,
            counter_name,
            indent,
            guard_name,
            indent,
            counter_name,
            limit,
            inner,
            guard_name,
            guard_name,
            inner,
            guard_name,
            guard_limit,
            inner,
            acc_name,
            acc_name,
            iter_expr,
            inner,
            counter_name,
            counter_name,
            indent,
        );

        Some(result)
    }

    /// Generate a for-in loop with match on the iteration variable.
    /// Combines iterator chain + for loop + match expression on loop variable.
    pub(super) fn try_generate_for_in_match_accum(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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

        ctx.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );
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
            indent,
            iter_name,
            arr_name,
            chain,
            inner,
            match_name,
            iter_name,
            inner2,
            arms_str,
            inner,
            inner,
            acc_name,
            acc_name,
            match_name,
            indent,
        );

        // Clean up protected vars
        ctx.protected_vars.pop();
        ctx.protected_vars.pop();

        Some(result)
    }

    /// Generate a string concatenation let-binding using the `+` operator.
    /// Combines in-scope string variables and/or literals.
    pub(super) fn try_generate_string_concat_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn try_generate_to_string_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find numeric variables in scope
        let numeric_vars: Vec<(String, PrimitiveType)> = ctx
            .locals
            .iter()
            .filter_map(|(name, ty, _)| {
                if let TypeInfo::Primitive(p) = ty
                    && matches!(
                        p,
                        PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64
                    )
                {
                    return Some((name.clone(), *p));
                }
                None
            })
            .chain(ctx.params.iter().filter_map(|p| {
                if let TypeInfo::Primitive(pt) = &p.param_type
                    && matches!(
                        pt,
                        PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64
                    )
                {
                    return Some((p.name.clone(), *pt));
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
    pub(super) fn try_generate_map_tostring_reduce(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn try_generate_struct_field_interpolation(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Find struct-typed locals with numeric or string fields
        let mut candidates: Vec<(String, String, PrimitiveType)> = Vec::new();

        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Struct(mod_id, sym_id) = ty
                && let Some(sym) = ctx.table.get_symbol(*mod_id, *sym_id)
                && let SymbolKind::Struct(ref info) = sym.kind
            {
                for f in &info.fields {
                    if let TypeInfo::Primitive(p) = &f.field_type
                        && matches!(
                            p,
                            PrimitiveType::I64
                                | PrimitiveType::I32
                                | PrimitiveType::F64
                                | PrimitiveType::String
                                | PrimitiveType::Bool
                        )
                    {
                        candidates.push((name.clone(), f.name.clone(), *p));
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
    pub(super) fn try_generate_when_iter_predicate(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        let expr_ctx = ctx.to_expr_context();
        let array_vars = expr_ctx.array_vars();
        let prim_arrays: Vec<(String, PrimitiveType)> = array_vars
            .into_iter()
            .filter_map(|(name, elem_ty)| {
                if let TypeInfo::Primitive(prim) = elem_ty
                    && matches!(
                        prim,
                        PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64
                    )
                {
                    return Some((name, prim));
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
    pub(super) fn try_generate_closure_result_concat(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn generate_split_for_loop(&mut self, ctx: &mut StmtContext) -> String {
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
            parts_name,
            input,
            indent,
            acc_name,
            indent,
            iter_name,
            parts_name,
            inner,
            acc_name,
            acc_name,
            iter_name,
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
    pub(super) fn try_generate_for_push_collect(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
            result_name, indent, iter_name, source_name, inner, result_name, transform, indent,
        );

        ctx.protected_vars.pop();
        ctx.protected_vars.pop();

        Some(result)
    }

    /// Generate an array literal whose elements are in-scope variables.
    /// E.g., `let arr = [x, y, x + y]` where x, y are i64 locals.
    pub(super) fn try_generate_array_from_vars(&mut self, ctx: &mut StmtContext) -> Option<String> {
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
    pub(super) fn try_generate_multi_push(&mut self, ctx: &mut StmtContext) -> Option<String> {
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
    pub(super) fn generate_literal_method_call(&mut self, ctx: &mut StmtContext) -> String {
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
    pub(super) fn try_generate_nested_when(&mut self, ctx: &mut StmtContext) -> Option<String> {
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
                cond1_var,
                cond1_op,
                cond1_thresh,
                cond2_var,
                cond2_op,
                cond2_thresh,
                vals[0],
                vals[1],
                vals[2],
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
                cond1_var,
                cond1_op,
                cond1_thresh,
                cond2_var,
                cond2_op,
                cond2_thresh,
                s0,
                s1,
                s2,
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
    pub(super) fn try_generate_match_on_method(&mut self, ctx: &mut StmtContext) -> Option<String> {
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
                    result_name,
                    var,
                    arm_len,
                    val0,
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
    pub(super) fn try_generate_struct_with_iter_fields(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        let module_id = ctx.module_id?;
        let module = ctx.table.get_module(module_id)?;

        // Find arrays of numeric type in scope
        let numeric_arrays: Vec<(String, PrimitiveType)> = ctx
            .locals
            .iter()
            .filter_map(|(name, ty, _)| {
                if let TypeInfo::Array(elem) = ty
                    && let TypeInfo::Primitive(prim) = elem.as_ref()
                    && matches!(prim, PrimitiveType::I64 | PrimitiveType::I32)
                {
                    return Some((name.clone(), *prim));
                }
                None
            })
            .chain(ctx.params.iter().filter_map(|p| {
                if let TypeInfo::Array(elem) = &p.param_type
                    && let TypeInfo::Primitive(prim) = elem.as_ref()
                    && matches!(prim, PrimitiveType::I64 | PrimitiveType::I32)
                {
                    return Some((p.name.clone(), *prim));
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
    pub(super) fn try_generate_iter_terminal_chain(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        let expr_ctx = ctx.to_expr_context();
        let array_vars = expr_ctx.array_vars();
        let prim_arrays: Vec<(String, PrimitiveType)> = array_vars
            .into_iter()
            .filter_map(|(name, elem_ty)| {
                if let TypeInfo::Primitive(prim) = elem_ty
                    && matches!(prim, PrimitiveType::I64 | PrimitiveType::I32)
                {
                    return Some((name, prim));
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
    pub(super) fn try_generate_when_string_method_conds(
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
            |var: &str, _rng: &mut dyn FnMut() -> i64| format!("{}.length() == 0", var),
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
    pub(super) fn generate_single_elem_array_ops(&mut self, ctx: &mut StmtContext) -> String {
        let arr_name = ctx.new_local_name();
        let result_name = ctx.new_local_name();
        let indent = self.indent_str();

        let (elem_type, elem_str, val) = match self.rng.gen_range(0..3u32) {
            0 => (
                PrimitiveType::I64,
                "i64",
                format!("{}", self.rng.gen_range(-100..=100)),
            ),
            1 => (
                PrimitiveType::I32,
                "i32",
                format!("{}_i32", self.rng.gen_range(-100..=100)),
            ),
            _ => (
                PrimitiveType::String,
                "string",
                format!(
                    "\"{}\"",
                    ["hello", "world", "test", "a"][self.rng.gen_range(0..4)]
                ),
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
                ctx.add_local(result_name.clone(), TypeInfo::Primitive(elem_type), false);
                format!("let {} = {}.iter().sum()", result_name, arr_name)
            }
            2 => {
                // arr[0]
                ctx.add_local(result_name.clone(), TypeInfo::Primitive(elem_type), false);
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
    pub(super) fn try_generate_tautological_when(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
            0 => format!("{} == {}", var, var), // always true
            1 => format!("{} >= {}", var, var), // always true
            2 => format!("{} <= {}", var, var), // always true
            _ => format!("{} * 0 == 0", var),   // always true (wrapping)
        };

        ctx.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        Some(format!(
            "let {} = when {{\n{indent}    {} => {},\n{indent}    _ => {}\n{indent}}}",
            result_name,
            cond,
            val_true,
            val_false,
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
    pub(super) fn try_generate_empty_string_concat(
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
    pub(super) fn try_generate_last_elem_access(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
                format!(
                    "{}[{}.length() - {}.length()]",
                    arr_name, arr_name, arr_name
                )
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
    pub(super) fn try_generate_for_length_indexed(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Find parameter arrays (guaranteed non-empty)
        let param_arrays: Vec<(String, PrimitiveType)> = ctx
            .params
            .iter()
            .filter_map(|p| {
                if let TypeInfo::Array(elem) = &p.param_type
                    && let TypeInfo::Primitive(prim) = elem.as_ref()
                    && matches!(prim, PrimitiveType::I64 | PrimitiveType::I32)
                {
                    return Some((p.name.clone(), *prim));
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
            acc_name,
            iter_name,
            arr_name,
            body_op,
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
    pub(super) fn generate_while_string_build(&mut self, ctx: &mut StmtContext) -> String {
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
            str_name,
            init,
            str_name,
            limit,
            str_name,
            str_name,
            append,
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
    pub(super) fn try_generate_compound_bool_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn try_generate_length_comparison_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Collect arrays and strings for .length() calls
        let length_sources: Vec<String> = ctx
            .locals
            .iter()
            .filter(|(_, ty, _)| {
                matches!(
                    ty,
                    TypeInfo::Array(_) | TypeInfo::Primitive(PrimitiveType::String)
                )
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
    pub(super) fn try_generate_interpolation_with_iter(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        let expr_ctx = ctx.to_expr_context();
        let array_vars = expr_ctx.array_vars();
        let prim_arrays: Vec<(String, PrimitiveType)> = array_vars
            .into_iter()
            .filter_map(|(name, elem_ty)| {
                if let TypeInfo::Primitive(prim) = elem_ty
                    && matches!(prim, PrimitiveType::I64 | PrimitiveType::I32)
                {
                    return Some((name, prim));
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
    pub(super) fn try_generate_reassign_from_when(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn try_generate_identity_arithmetic(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
            0 => format!("{} + 0", var), // x + 0 == x
            1 => format!("{} * 1", var), // x * 1 == x
            2 => format!("{} - 0", var), // x - 0 == x
            3 => format!("0 + {}", var), // 0 + x == x
            4 => format!("1 * {}", var), // 1 * x == x
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
    pub(super) fn try_generate_string_equality_let(
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
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
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

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );
        Some(format!("let {} = {}", name, expr))
    }

    /// Generate modulo edge cases: N % 1 (always 0), N % N (always 0 for non-zero),
    /// x % large_prime, etc. Tests division/modulo codegen paths.
    pub(super) fn generate_modulo_edge_case(&mut self, ctx: &mut StmtContext) -> String {
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
    pub(super) fn generate_array_uniform_ops(&mut self, ctx: &mut StmtContext) -> String {
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
    pub(super) fn try_generate_for_when_accumulate(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn try_generate_iter_in_when_arms(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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

        ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);

        Some(format!(
            "let {} = when {{ {} > {} => {}.iter().{}, _ => {}.iter().{} }}",
            name, cond_var, thresh, arr, t1, arr, t2
        ))
    }

    /// Generate when expression with 4+ boolean condition arms.
    /// Tests the compiler's handling of larger when expressions.
    pub(super) fn try_generate_multi_arm_when(&mut self, ctx: &mut StmtContext) -> Option<String> {
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

        ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);

        Some(format!(
            "let {} = when {{\n{}\n{}}}",
            name,
            arms.join("\n"),
            "    ".repeat(self.indent),
        ))
    }

    /// Generate match where arm values involve arithmetic computation.
    /// `match x { 0 => a + b, 1 => c * 2, _ => d - 1 }`
    pub(super) fn try_generate_match_with_computation(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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

        ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);

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
    pub(super) fn try_generate_string_replace_let(
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
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
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
    pub(super) fn try_generate_nested_match_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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

        ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);

        Some(format!(
            "let {} = match {} {{\n{}{} => match {} {{\n{}{} => {}\n{}_ => {}\n{}}}\n{}_ => {}\n{}}}",
            name,
            outer_var,
            indent,
            outer_val,
            inner_var,
            indent2,
            inner_val,
            result_a,
            indent2,
            result_b,
            indent,
            indent,
            result_c,
            "    ".repeat(self.indent),
        ))
    }

    /// Generate string .length() on literal strings of known lengths.
    /// Tests string-length codegen with edge cases: empty string, single char, etc.
    pub(super) fn generate_string_length_edge_cases(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();
        let expr = match self.rng.gen_range(0..5u32) {
            0 => "\"\".length()".to_string(),            // 0
            1 => "\"a\".length()".to_string(),           // 1
            2 => "\"hello\".length()".to_string(),       // 5
            3 => "\"hello world\".length()".to_string(), // 11
            _ => {
                // Variable .length()
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
                if !string_vars.is_empty() {
                    let var = &string_vars[self.rng.gen_range(0..string_vars.len())];
                    format!("{}.length()", var)
                } else {
                    "\"test\".length()".to_string() // 4
                }
            }
        };
        ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
        format!("let {} = {}", name, expr)
    }

    /// Generate range-checking booleans: `x > lo && x < hi`, `x >= 0 && x <= 100`.
    pub(super) fn try_generate_range_check_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
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
    pub(super) fn generate_for_string_build_with_match(&mut self, ctx: &mut StmtContext) -> String {
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
    pub(super) fn try_generate_when_with_string_concat_arms(
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
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
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
    pub(super) fn try_generate_bool_negation_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        let name = ctx.new_local_name();

        let expr = match self.rng.gen_range(0..5u32) {
            0 => "!true".to_string(),
            1 => "!false".to_string(),
            2 => {
                // !(x > 0)
                let i64_vars: Vec<String> = ctx
                    .locals
                    .iter()
                    .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
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
                    .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::Bool)))
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
                    .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
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
    pub(super) fn generate_chained_literal_method(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();

        match self.rng.gen_range(0..4u32) {
            0 => {
                // "hello world".split(" ").count() -> i64
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
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
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                format!("let {} = \"a,b,c\".split(\",\").count()", name)
            }
            _ => {
                // "HELLO".to_lower().length() -> i64
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                format!("let {} = \"HELLO\".to_lower().length()", name)
            }
        }
    }

    /// Generate method call on a when expression result.
    /// `let r = when { x > 0 => "hello", _ => "world" }.length()`
    pub(super) fn try_generate_when_result_method(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
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
    pub(super) fn try_generate_for_iter_when_string_body(
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
    pub(super) fn generate_while_false_deadcode(&mut self, ctx: &mut StmtContext) -> String {
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
    pub(super) fn try_generate_power_of_two_div(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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

        ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
        Some(format!("let {} = {} / {}", name, var, divisor))
    }

    /// Generate a string predicate call: `s.contains("sub")`, `s.starts_with("hel")`, `s.ends_with("rld")`
    /// Returns a bool-typed let binding.
    pub(super) fn try_generate_string_predicate_let(
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
            let literals = [
                "\"hello world\"",
                "\"testing\"",
                "\"abcdef\"",
                "\"vole lang\"",
            ];
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
    pub(super) fn try_generate_interpolation_expr_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn try_generate_match_string_length(
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
        let result_strs = [
            "\"empty\"",
            "\"one\"",
            "\"short\"",
            "\"medium\"",
            "\"long\"",
        ];
        let num_arms = self.rng.gen_range(2..=3);

        let mut arms = Vec::new();
        for i in 0..num_arms {
            let val = i as i64;
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
    pub(super) fn try_generate_array_length_guard(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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

        ctx.add_local(name.clone(), TypeInfo::Primitive(*elem_prim), false);
        Some(format!(
            "let {} = when {{\n    {}.length() > 0 => {}[0]\n    _ => {}\n}}",
            name, arr_name, arr_name, default_val
        ))
    }

    /// Generate a repeat literal: `let arr: [i64; 5] = [0; 5]`
    /// Note: Fixed-size arrays [T; N] don't support .iter()/.length() in Vole,
    /// so we don't register the local to avoid downstream generators using it.
    pub(super) fn generate_repeat_literal_let(&mut self, ctx: &mut StmtContext) -> String {
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
    pub(super) fn try_generate_iter_reduce_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
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
        if !numeric_array_params.is_empty()
            && (string_array_params.is_empty() || self.rng.gen_bool(0.6))
        {
            let (arr_name, prim) =
                &numeric_array_params[self.rng.gen_range(0..numeric_array_params.len())];
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

            ctx.add_local(name.clone(), TypeInfo::Primitive(*prim), false);
            Some(format!(
                "let {} = {}.iter().reduce({}, (acc: {}, x: {}) -> {} => acc {} x)",
                name, arr_name, init, type_annot, type_annot, type_annot, op
            ))
        } else {
            let arr_name = &string_array_params[self.rng.gen_range(0..string_array_params.len())];
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
    pub(super) fn generate_i32_boundary_safe(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();

        let expr = match self.rng.gen_range(0..6u32) {
            0 => "2147483647_i32 - 1_i32".to_string(),
            1 => "(-2147483647_i32 + 1_i32)".to_string(),
            2 => "(2147483646_i32 + 1_i32)".to_string(),
            3 => "(1073741823_i32 * 2_i32)".to_string(),
            4 => "(2147483647_i32 / 2_i32)".to_string(),
            _ => "(2147483647_i32 % 100_i32)".to_string(),
        };

        ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I32), false);
        format!("let {} = {}", name, expr)
    }

    /// Generate operations on empty strings to test edge cases.
    /// E.g.: `"".length()`, `"".to_upper()`, `"".trim()`, `"".split(",").count()`
    pub(super) fn generate_empty_string_ops(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();

        let (expr, ty) = match self.rng.gen_range(0..6u32) {
            0 => (
                "\"\"".to_string() + ".length()",
                TypeInfo::Primitive(PrimitiveType::I64),
            ),
            1 => (
                "\"\"".to_string() + ".to_upper()",
                TypeInfo::Primitive(PrimitiveType::String),
            ),
            2 => (
                "\"\"".to_string() + ".trim()",
                TypeInfo::Primitive(PrimitiveType::String),
            ),
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
    pub(super) fn try_generate_for_reduce_pattern(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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

        ctx.add_local(acc_name.clone(), TypeInfo::Primitive(*prim), true);

        Some(format!(
            "let mut {} = 0{}\nfor {} in {}.iter() {{\n    {} = {} {} {}\n}}",
            acc_name, suffix, iter_name, arr_name, acc_name, acc_name, op, iter_name
        ))
    }

    /// Generate a when expression with a match inside an arm:
    /// `when { cond => match x { 0 => a, _ => b }, _ => default }`
    pub(super) fn try_generate_when_match_combo(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
            name, var, match_val0, strs[0], match_val1, strs[1], strs[2], strs[3],
        ))
    }

    /// Generate a for loop over split string:
    /// `let parts = "a,b,c".split(",").collect(); let mut s = ""; for p in parts.iter() { s = s + p }`
    pub(super) fn generate_string_split_for(&mut self, ctx: &mut StmtContext) -> String {
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
    pub(super) fn try_generate_nested_when_string_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn try_generate_numeric_to_string_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn try_generate_substring_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
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
            (
                string_vars[self.rng.gen_range(0..string_vars.len())].clone(),
                3,
            )
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

        let start = self.rng.gen_range(0..max_len.min(4));
        let end = self.rng.gen_range(start..=max_len);

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
    pub(super) fn try_generate_match_to_string_arms(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn generate_for_interpolation_concat(&mut self, ctx: &mut StmtContext) -> String {
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
    pub(super) fn try_generate_bool_chain_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
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
        for part in parts.iter().skip(1) {
            let op = if self.rng.gen_bool(0.6) { "&&" } else { "||" };
            expr = format!("({} {} {})", expr, op, part);
        }

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );
        Some(format!("let {} = {}", name, expr))
    }

    /// Generate a comparison chain: `(a > b) == (c > d)`, `(a != 0) && (b != 0)`
    pub(super) fn try_generate_comparison_chain_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn try_generate_when_with_contains(
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
    pub(super) fn try_generate_match_array_length(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn try_generate_sorted_collect_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn try_generate_reverse_collect_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn try_generate_zero_division_guard(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn generate_single_char_string_ops(&mut self, ctx: &mut StmtContext) -> String {
        let chars = ["a", "Z", "0", " ", "x", "M"];
        let ch = chars[self.rng.gen_range(0..chars.len())];
        let name = ctx.new_local_name();

        match self.rng.gen_range(0..6) {
            0 => {
                // "x".to_upper()
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                format!("let {} = \"{}\".to_upper()", name, ch)
            }
            1 => {
                // "x".to_lower()
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                format!("let {} = \"{}\".to_lower()", name, ch)
            }
            2 => {
                // "x".length()
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                format!("let {} = \"{}\".length()", name, ch)
            }
            3 => {
                // "x".contains("x")
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                    false,
                );
                format!("let {} = \"{}\".contains(\"{}\")", name, ch, ch)
            }
            4 => {
                // "x".trim()
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                format!("let {} = \"{}\".trim()", name, ch)
            }
            _ => {
                // "x".substring(0, 1)
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                format!("let {} = \"{}\".substring(0, 1)", name, ch)
            }
        }
    }

    /// Generate f64 literal arithmetic operations.
    /// Tests floating-point codegen paths with known-safe values.
    pub(super) fn generate_f64_literal_ops_let(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();
        let literals = ["0.0", "1.0", "0.5", "2.5", "3.14", "100.0", "0.1", "99.9"];
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
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                    false,
                );
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
    pub(super) fn try_generate_iter_take_skip_collect_let(
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
    pub(super) fn generate_f64_comparison_edge_let(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();
        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );

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
    pub(super) fn generate_repeated_string_ops(&mut self, ctx: &mut StmtContext) -> String {
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
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                    false,
                );
                format!("let {} = \"{}\".contains(\"{}\")", name, s, ch)
            }
            2 => {
                // "aaa".replace("a", "b")
                let ch = &s[0..1];
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                format!("let {} = \"{}\".replace(\"{}\", \"b\")", name, s, ch)
            }
            3 => {
                // "   ".trim()
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                format!("let {} = \"{}\".trim()", name, s)
            }
            _ => {
                // "aaa".to_upper()
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                format!("let {} = \"{}\".to_upper()", name, s)
            }
        }
    }

    /// Generate a when expression with f64 variable conditions.
    /// E.g.: `when { x > 1.0 => "big", x > 0.0 => "small", _ => "zero" }`
    pub(super) fn try_generate_when_f64_cond_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
        Some(format!("let {} = when {{ {} }}", name, arms.join(", ")))
    }

    /// Generate a for-range loop that builds a string from index.to_string().
    /// E.g.: `let mut s = ""; for i in 0..5 { s = s + i.to_string() }`
    pub(super) fn generate_for_range_tostring_build(&mut self, ctx: &mut StmtContext) -> String {
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
    pub(super) fn try_generate_match_when_arm_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn try_generate_sorted_iter_accum(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
        ctx.add_local(acc_name.clone(), TypeInfo::Primitive(*elem_prim), true);

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
    pub(super) fn try_generate_filter_iter_tostring(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn try_generate_when_length_compare(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
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
    pub(super) fn generate_string_char_at_let(&mut self, ctx: &mut StmtContext) -> String {
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
        format!("let {} = \"{}\".substring({}, {})", name, s, idx, idx + 1)
    }

    /// Generate range-based iterator with map and collect.
    /// E.g.: `let arr = (0..5).iter().map((x) => x * 2).collect()`
    pub(super) fn generate_range_iter_map_collect(&mut self, ctx: &mut StmtContext) -> String {
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
    pub(super) fn try_generate_match_interpolation_length(
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
    pub(super) fn generate_for_range_when_accum(&mut self, ctx: &mut StmtContext) -> String {
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
    pub(super) fn try_generate_when_tostring_arms(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn try_generate_match_sorted_length(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
    pub(super) fn generate_single_elem_range_let(&mut self, ctx: &mut StmtContext) -> String {
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
    pub(super) fn generate_whitespace_string_ops(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();
        let ws_strings = ["  hello  ", "  ", " x ", "\thello\t", "  spaces  here  "];
        let s = ws_strings[self.rng.gen_range(0..ws_strings.len())];

        match self.rng.gen_range(0..4) {
            0 => {
                // trim
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                format!("let {} = \"{}\".trim()", name, s)
            }
            1 => {
                // length
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                format!("let {} = \"{}\".trim().length()", name, s)
            }
            2 => {
                // contains space
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                    false,
                );
                format!("let {} = \"{}\".contains(\" \")", name, s)
            }
            _ => {
                // replace spaces
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                format!("let {} = \"{}\".replace(\" \", \"\")", name, s)
            }
        }
    }

    /// Generate empty range (N..N) operations — produces empty collection.
    /// E.g.: `(5..5).iter().collect()`, `(0..0).iter().count()`
    pub(super) fn generate_empty_range_let(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();
        let n = self.rng.gen_range(0..=10);

        match self.rng.gen_range(0..3) {
            0 => {
                // Empty range collect -> empty array
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                    false,
                );
                format!("let {} = ({}..{}).iter().collect()", name, n, n)
            }
            1 => {
                // Empty range count -> 0
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                format!("let {} = ({}..{}).iter().count()", name, n, n)
            }
            _ => {
                // Empty range sum -> 0
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                format!("let {} = ({}..{}).iter().sum()", name, n, n)
            }
        }
    }

    /// Generate .to_string().length() chain on numeric variables.
    /// E.g.: `let n = x.to_string().length()`
    pub(super) fn try_generate_tostring_length_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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

        ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
        Some(format!("let {} = {}.to_string().length()", name, var))
    }

    /// Generate chained boolean literal operations.
    /// E.g.: `let b = true && false || true`
    pub(super) fn generate_bool_chain_edge_let(&mut self, ctx: &mut StmtContext) -> String {
        let name = ctx.new_local_name();

        let variant = self.rng.gen_range(0..5);
        let expr = match variant {
            0 => "true && true".to_string(),
            1 => "true && false || true".to_string(),
            2 => "false || false || true".to_string(),
            3 => "!(true && false)".to_string(),
            _ => "true && !false".to_string(),
        };

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );
        format!("let {} = {}", name, expr)
    }

    /// Generate safe first-element access with length guard.
    /// E.g.: `let x = when { arr.length() > 0 => arr[0], _ => default }`
    pub(super) fn try_generate_array_length_zero_check(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Find parameter arrays (guaranteed non-empty by generation)
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

        let (arr_name, elem_type) = &array_params[self.rng.gen_range(0..array_params.len())];
        let name = ctx.new_local_name();

        let default = match elem_type {
            PrimitiveType::I64 => "0",
            PrimitiveType::I32 => "0_i32",
            PrimitiveType::Bool => "false",
            PrimitiveType::String => "\"\"",
            PrimitiveType::F64 => "0.0",
            _ => return None,
        };

        ctx.add_local(name.clone(), TypeInfo::Primitive(*elem_type), false);
        Some(format!(
            "let {} = when {{ {}.length() > 0 => {}[0], _ => {} }}",
            name, arr_name, arr_name, default
        ))
    }

    /// Generate when expression with string replace in arms.
    /// E.g.: `let r = when { s.contains("a") => s.replace("a", "b"), _ => s }`
    pub(super) fn try_generate_when_replace_result(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        let str_vars: Vec<String> = ctx
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

        if str_vars.is_empty() {
            return None;
        }

        let var = &str_vars[self.rng.gen_range(0..str_vars.len())];
        let name = ctx.new_local_name();

        let search_chars = ["a", "e", "i", "o", " ", "0", "1"];
        let search = search_chars[self.rng.gen_range(0..search_chars.len())];
        let replace = if search == " " { "_" } else { "x" };

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = when {{ {}.contains(\"{}\") => {}.replace(\"{}\", \"{}\"), _ => {} }}",
            name, var, search, var, search, replace, var
        ))
    }

    /// Generate match with .to_string() in each arm.
    /// E.g.: `let s = match x { 0 => "zero", 1 => "one", _ => x.to_string() }`
    pub(super) fn try_generate_match_tostring_arms(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
        let num_arms = self.rng.gen_range(1..=3);

        let mut arms = String::new();
        let mut used_values = std::collections::HashSet::new();
        for _ in 0..num_arms {
            let val = self.rng.gen_range(0..10) as i64;
            if used_values.insert(val) {
                arms.push_str(&format!("{} => \"{}\", ", val, val));
            }
        }
        arms.push_str(&format!("_ => {}.to_string()", var));

        ctx.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!("let {} = match {} {{ {} }}", name, var, arms))
    }

    /// Generate manual min/max via when expression.
    /// E.g.: `let m = when { a > b => a, _ => b }` (max)
    /// or:   `let m = when { a < b => a, _ => b }` (min)
    pub(super) fn try_generate_manual_minmax_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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

        let a = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        let mut b = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        while b == a && i64_vars.len() > 1 {
            b = &i64_vars[self.rng.gen_range(0..i64_vars.len())];
        }

        let name = ctx.new_local_name();
        let op = if self.rng.gen_bool(0.5) { ">" } else { "<" };

        ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
        Some(format!(
            "let {} = when {{ {} {} {} => {}, _ => {} }}",
            name, a, op, b, a, b
        ))
    }

    /// Generate nested .to_string().length().to_string() chain.
    /// E.g.: `let s = x.to_string().length().to_string()`
    pub(super) fn try_generate_nested_tostring_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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

        let variant = self.rng.gen_range(0..3);
        match variant {
            0 => {
                // x.to_string().length().to_string() -> string
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!(
                    "let {} = {}.to_string().length().to_string()",
                    name, var
                ))
            }
            1 => {
                // x.to_string().contains("0") -> bool
                let digit = self.rng.gen_range(0..10);
                ctx.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                    false,
                );
                Some(format!(
                    "let {} = {}.to_string().contains(\"{}\")",
                    name, var, digit
                ))
            }
            _ => {
                // x.to_string().replace("-", "").length() -> i64
                ctx.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                Some(format!(
                    "let {} = {}.to_string().replace(\"-\", \"\").length()",
                    name, var
                ))
            }
        }
    }

    pub(super) fn try_generate_bool_match_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
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
    pub(super) fn try_computed_bool_scrutinee(
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

    pub(super) fn try_generate_variable_shadow(&mut self, ctx: &mut StmtContext) -> Option<String> {
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

    pub(super) fn try_generate_widening_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
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
    pub(super) fn widening_targets(narrow: PrimitiveType) -> Vec<PrimitiveType> {
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

    /// Generate an empty string and run an iterator chain on it.
    ///
    /// Produces a two-statement sequence:
    /// ```vole
    /// let s = ""
    /// let result = s.iter().count()
    /// ```
    pub(super) fn generate_empty_string_iter_let(&mut self, ctx: &mut StmtContext) -> String {
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
    pub(super) fn generate_wildcard_only_match(&mut self, ctx: &mut StmtContext) -> Option<String> {
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
    pub(super) fn try_generate_nested_when_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let result_type = self.random_primitive_type();
        let result_name = ctx.new_local_name();

        let expr_ctx = ctx.to_expr_context();

        // Generate outer condition
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let outer_cond =
            expr_gen.generate_simple(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx);

        // Generate inner condition
        let mut expr_gen = ExprGenerator::new(self.rng, &self.config.expr_config);
        let inner_cond =
            expr_gen.generate_simple(&TypeInfo::Primitive(PrimitiveType::Bool), &expr_ctx);

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
            indent,
            outer_cond,
            inner_indent,
            inner_cond,
            val1,
            inner_indent,
            val2,
            inner_close,
            indent,
            val3,
            close_indent,
        ))
    }

    /// Generate iterator chains that produce empty results from non-empty arrays.
    ///
    /// Uses `.take(0)` or `.skip(large)` to force zero-length iteration.
    pub(super) fn try_generate_empty_iter_edge(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find arrays with primitive element types
        let mut array_vars: Vec<(String, PrimitiveType)> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Array(inner) = ty
                && let TypeInfo::Primitive(p) = inner.as_ref()
            {
                match p {
                    PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::String => {
                        array_vars.push((name.clone(), *p));
                    }
                    _ => {}
                }
            }
        }
        for param in ctx.params.iter() {
            if let TypeInfo::Array(inner) = &param.param_type
                && let TypeInfo::Primitive(p) = inner.as_ref()
            {
                match p {
                    PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::String => {
                        array_vars.push((param.name.clone(), *p));
                    }
                    _ => {}
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
    pub(super) fn try_generate_match_iter_terminal(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Find i64 array params (guaranteed non-empty)
        let mut array_vars: Vec<String> = Vec::new();
        for param in ctx.params.iter() {
            if let TypeInfo::Array(inner) = &param.param_type
                && let TypeInfo::Primitive(p) = inner.as_ref()
                && matches!(p, PrimitiveType::I64 | PrimitiveType::I32)
            {
                array_vars.push(param.name.clone());
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
            indent,
            arm_val1,
            indent,
            arm_val2,
            indent,
            wildcard_val,
            close_indent,
        ))
    }

    ///
    /// Produces patterns like:
    /// - `let r = str.to_upper().to_lower().length()`
    /// - `let r = str.trim().to_upper().contains("x")`
    pub(super) fn try_generate_chained_string_methods(
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
            if matches!(
                &param.param_type,
                TypeInfo::Primitive(PrimitiveType::String)
            ) {
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
            _ => (String::new(), TypeInfo::Primitive(PrimitiveType::String)),
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
    pub(super) fn try_generate_match_array_elem(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Only use parameter arrays (guaranteed non-empty by generator).
        // Local arrays could be from .collect() which may produce empty arrays.
        let mut array_vars: Vec<(String, PrimitiveType)> = Vec::new();
        for param in ctx.params.iter() {
            if let TypeInfo::Array(inner) = &param.param_type
                && let TypeInfo::Primitive(p) = inner.as_ref()
                && matches!(p, PrimitiveType::I64 | PrimitiveType::I32)
            {
                array_vars.push((param.name.clone(), *p));
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

        let arms = [
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
    pub(super) fn generate_empty_array_iter_let(&mut self, ctx: &mut StmtContext) -> String {
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
                TypeInfo::Array(Box::new(elem_ty)),
            )
        } else if choice < 7 {
            // .filter().collect()
            let filter_body = self.generate_filter_closure_body(elem_prim);
            (
                format!(".filter((x) => {}).collect()", filter_body),
                TypeInfo::Array(Box::new(elem_ty)),
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
                TypeInfo::Array(Box::new(elem_ty)),
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
                TypeInfo::Array(Box::new(elem_ty)),
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
    pub(super) fn generate_range_iter_let(&mut self, ctx: &mut StmtContext) -> String {
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
}
