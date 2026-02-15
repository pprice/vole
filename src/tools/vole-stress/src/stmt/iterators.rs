//! Iterator-related statement generators.
//!
//! Contains generators for iterator map/filter chains, predicate lets,
//! chunks/windows, for_each, nth, string iteration, reiteration,
//! method map, and generic closure interface chains.

use rand::Rng;

use crate::expr::ExprGenerator;
use crate::symbols::{ModuleId, ParamInfo, PrimitiveType, SymbolId, SymbolKind, TypeInfo};

use super::{StmtContext, StmtGenerator};

impl<'a, R: Rng> StmtGenerator<'a, R> {
    /// Try to generate an iterator predicate let-binding.
    ///
    /// Finds a numeric array in scope and generates:
    /// - `let b = arr.iter().any((x) => x > 0)` → bool
    /// - `let b = arr.iter().all((x) => x > 0)` → bool
    pub(super) fn try_generate_iter_predicate_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Find numeric arrays in scope (i64, i32, f64)
        let mut array_vars: Vec<(String, PrimitiveType)> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Array(inner) = ty
                && let TypeInfo::Primitive(
                    p @ (PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64),
                ) = inner.as_ref()
            {
                array_vars.push((name.clone(), *p));
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
    pub(super) fn try_generate_iter_chunks_windows_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Find arrays with primitive element types
        let mut array_vars: Vec<(String, PrimitiveType)> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Array(inner) = ty
                && let TypeInfo::Primitive(p) = inner.as_ref()
            {
                match p {
                    PrimitiveType::I64
                    | PrimitiveType::I32
                    | PrimitiveType::F64
                    | PrimitiveType::Bool
                    | PrimitiveType::String => {
                        array_vars.push((name.clone(), *p));
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
    pub(super) fn try_generate_for_each_stmt(&mut self, ctx: &mut StmtContext) -> Option<String> {
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
            PrimitiveType::I64 | PrimitiveType::I32 => match self.rng.gen_range(0..3) {
                0 => "let y = x * 2".to_string(),
                1 => "let y = x + 1".to_string(),
                _ => "let y = x".to_string(),
            },
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
    pub(super) fn try_generate_nth_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        let mut array_vars: Vec<(String, PrimitiveType)> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Array(inner) = ty
                && let TypeInfo::Primitive(p) = inner.as_ref()
            {
                match p {
                    PrimitiveType::I64
                    | PrimitiveType::I32
                    | PrimitiveType::String
                    | PrimitiveType::Bool => {
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
                    PrimitiveType::I64
                    | PrimitiveType::I32
                    | PrimitiveType::String
                    | PrimitiveType::Bool => {
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
    pub(super) fn try_generate_string_iter_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
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

    /// Try to generate a re-iteration let-binding.
    ///
    /// Finds an existing array-typed local variable and chains a new iterator
    /// operation on it. This exercises the codegen path of iterating over
    /// dynamically-created arrays (results of prior .collect() calls).
    pub(super) fn try_generate_reiterate_let(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Find i64 array locals in scope
        let mut i64_array_vars: Vec<String> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Array(inner) = ty
                && matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::I64))
            {
                i64_array_vars.push(name.clone());
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
    pub(super) fn try_generate_iter_method_map(&mut self, ctx: &mut StmtContext) -> Option<String> {
        // Skip in method bodies to avoid mutual recursion
        if ctx.current_class_sym_id.is_some() {
            return None;
        }

        // Find i64 array variables in scope (locals + params)
        let mut array_candidates: Vec<String> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Array(elem) = ty
                && matches!(elem.as_ref(), TypeInfo::Primitive(PrimitiveType::I64))
            {
                array_candidates.push(name.clone());
            }
        }
        for param in ctx.params.iter() {
            if let TypeInfo::Array(elem) = &param.param_type
                && matches!(elem.as_ref(), TypeInfo::Primitive(PrimitiveType::I64))
            {
                array_candidates.push(param.name.clone());
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
            if let Some(sym) = ctx.table.get_symbol(mod_id, sym_id)
                && let SymbolKind::Class(ref info) = sym.kind
                && info.type_params.is_empty()
            {
                for method in &info.methods {
                    if !matches!(method.return_type, TypeInfo::Primitive(PrimitiveType::I64)) {
                        continue;
                    }
                    let has_i64 = method
                        .params
                        .iter()
                        .any(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)));
                    if has_i64 && !method.params.is_empty() {
                        method_candidates.push((
                            name.to_string(),
                            method.name.clone(),
                            method.params.clone(),
                        ));
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
                if !x_used && matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)) {
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
    pub(super) fn try_generate_iter_map_filter_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
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
                Some((String::new(), TypeInfo::Primitive(PrimitiveType::I64))),
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
    pub(super) fn generate_map_closure_body(&mut self, elem_prim: PrimitiveType) -> String {
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
    pub(super) fn generate_filter_closure_body(&mut self, elem_prim: PrimitiveType) -> String {
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
    pub(super) fn generate_reduce_closure(
        &mut self,
        elem_prim: PrimitiveType,
    ) -> (String, String, TypeInfo) {
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
                            format!("when {{ el > {} => acc + el, _ => acc }}", threshold),
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
                    "\"\"".to_string(),
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
    pub(super) fn generate_map_closure_body_param(
        &mut self,
        elem_prim: PrimitiveType,
        param: &str,
    ) -> String {
        let body = self.generate_map_closure_body(elem_prim);
        body.replace("x", param)
    }

    /// Generate a closure body for `.filter()` with a custom parameter name.
    ///
    /// Used for chained operations where the second closure needs a different
    /// parameter name to avoid shadowing.
    pub(super) fn generate_filter_closure_body_param(
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
    pub(super) fn try_generate_generic_closure_interface_chain(
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
                    && param_types.len() == 1
                    && let (TypeInfo::Primitive(pt), TypeInfo::Primitive(rt)) =
                        (&param_types[0], return_type.as_ref())
                    && pt == rt
                    && matches!(pt, PrimitiveType::I64 | PrimitiveType::I32)
                {
                    return Some((p.name.clone(), *pt));
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
}
