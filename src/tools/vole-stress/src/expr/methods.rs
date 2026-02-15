//! Method chain, string method, field access, and iterator expression generation.

use rand::Rng;

use super::{
    ExprContext, ExprGenerator, FieldPathSearch, get_type_param_constraint_methods,
    types_compatible,
};
use crate::symbols::{PrimitiveType, SymbolKind, TypeInfo};

impl<'a, R: Rng> ExprGenerator<'a, R> {
    /// Try to generate an array index expression on an array-typed local.
    ///
    /// Looks for array-typed variables in scope whose element type matches
    /// the target primitive type. Returns `Some("arrayVar[index]")` on success,
    /// using a small constant index (0..=1) to stay within bounds of typical
    /// small arrays (which have 2-4 elements).
    pub(super) fn try_generate_array_index(
        &mut self,
        prim: PrimitiveType,
        ctx: &ExprContext,
    ) -> Option<String> {
        let target = TypeInfo::Primitive(prim);
        let array_vars = ctx.array_vars();

        // Filter to arrays whose element type matches the target
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| types_compatible(elem_ty, &target))
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, _) = &candidates[idx];

        // Use index 0 to stay within bounds.  Arrays may have been reduced to
        // a single element by .skip()/.filter()/.unique() so index 1 is not safe.
        let index = 0;
        let suffix = match prim {
            PrimitiveType::I32 => "_i32",
            PrimitiveType::I64 => "_i64",
            _ => "_i64", // default index type
        };
        Some(format!("{}[{}{}]", var_name, index, suffix))
    }

    /// Try to generate a fixed array index expression on a fixed-array-typed local.
    ///
    /// Looks for fixed-array-typed variables in scope whose element type matches
    /// the target primitive type. Returns `Some("fixedArrayVar[index]")` on success,
    /// using a constant index within bounds of the array size.
    pub(super) fn try_generate_fixed_array_index(
        &mut self,
        prim: PrimitiveType,
        ctx: &ExprContext,
    ) -> Option<String> {
        let target = TypeInfo::Primitive(prim);
        let fixed_array_vars = ctx.fixed_array_vars();

        // Filter to fixed arrays whose element type matches the target
        let candidates: Vec<_> = fixed_array_vars
            .iter()
            .filter(|(_, elem_ty, _)| types_compatible(elem_ty, &target))
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, _, size) = &candidates[idx];

        // Use a constant index within bounds of the fixed array.
        // Clamp to 0..=(size-1) to stay within bounds.
        let max_index = size.saturating_sub(1).max(0);
        let index = self.rng.gen_range(0..=max_index);
        let suffix = match prim {
            PrimitiveType::I32 => "_i32",
            PrimitiveType::I64 => "_i64",
            _ => "_i64", // default index type
        };
        Some(format!("{}[{}{}]", var_name, index, suffix))
    }

    /// Try to generate a tuple index expression on a tuple-typed local.
    ///
    /// Looks for tuple-typed variables in scope that contain an element
    /// matching the target primitive type. Returns `Some("tupleVar[index]")`
    /// using a constant integer literal index. Tuple indexing requires a
    /// compile-time constant index in Vole (non-constant indices are rejected
    /// by codegen).
    pub(super) fn try_generate_tuple_index_for_type(
        &mut self,
        target: &TypeInfo,
        ctx: &ExprContext,
    ) -> Option<String> {
        let tuple_vars = ctx.tuple_vars();

        // Build candidates: (var_name, index) pairs where elem type matches target
        let mut candidates: Vec<(&str, usize)> = Vec::new();
        for (name, elem_types) in &tuple_vars {
            for (i, elem_ty) in elem_types.iter().enumerate() {
                if types_compatible(elem_ty, target) {
                    candidates.push((name.as_str(), i));
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, elem_index) = candidates[idx];
        Some(format!("{}[{}]", var_name, elem_index))
    }

    /// Try to generate a field access expression on a class-typed local.
    ///
    /// Looks for local variables with class type whose fields match the
    /// target primitive type. Returns `Some("local.field")` on success.
    /// Also supports nested field access through class-typed fields, e.g.,
    /// `local.inner.field` where `inner` is a class-typed field.
    /// Only considers non-generic classes (generic field types are too
    /// complex to resolve).
    pub(super) fn try_generate_field_access(
        &mut self,
        prim: PrimitiveType,
        ctx: &ExprContext,
    ) -> Option<String> {
        let target = TypeInfo::Primitive(prim);

        // Collect full access paths (e.g., "obj.field" or "obj.inner.field")
        let mut candidates: Vec<String> = Vec::new();

        for (name, ty) in ctx.locals {
            match ty {
                TypeInfo::Class(mod_id, sym_id) | TypeInfo::Struct(mod_id, sym_id) => {
                    self.collect_field_paths(&mut FieldPathSearch {
                        table: ctx.table,
                        mod_id: *mod_id,
                        sym_id: *sym_id,
                        prefix: name.clone(),
                        target: &target,
                        candidates: &mut candidates,
                        depth: 0,
                    });
                }
                _ => {}
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        Some(candidates[idx].clone())
    }

    /// Recursively collect field access paths that lead to the target type.
    ///
    /// This enables nested field access like `obj.inner.field` where `inner`
    /// is a class-typed field. Depth is limited to prevent infinite recursion
    /// in case of any cyclic references (though planning should prevent these).
    pub(super) fn collect_field_paths(&self, search: &mut FieldPathSearch) {
        // Limit depth to prevent excessive nesting (and handle any cycles)
        const MAX_DEPTH: usize = 3;
        if search.depth >= MAX_DEPTH {
            return;
        }

        let Some(sym) = search.table.get_symbol(search.mod_id, search.sym_id) else {
            return;
        };

        let fields = match &sym.kind {
            SymbolKind::Class(info) => {
                // Skip generic classes
                if !info.type_params.is_empty() {
                    return;
                }
                &info.fields
            }
            SymbolKind::Struct(info) => &info.fields,
            _ => return,
        };

        for field in fields {
            let field_path = format!("{}.{}", search.prefix, field.name);

            // Check if this field matches the target type
            if &field.field_type == search.target {
                search.candidates.push(field_path.clone());
            }

            // If this field is a class or struct type, recurse into it
            match &field.field_type {
                TypeInfo::Class(nested_mod_id, nested_sym_id)
                | TypeInfo::Struct(nested_mod_id, nested_sym_id) => {
                    self.collect_field_paths(&mut FieldPathSearch {
                        table: search.table,
                        mod_id: *nested_mod_id,
                        sym_id: *nested_sym_id,
                        prefix: field_path,
                        target: search.target,
                        candidates: search.candidates,
                        depth: search.depth + 1,
                    });
                }
                _ => {}
            }
        }
    }

    /// Try to generate a null coalescing expression (`optVar ?? defaultExpr`).
    ///
    /// Looks for optional-typed variables in scope whose inner type matches
    /// the target type. Returns `Some("optVar ?? defaultExpr")` on success.
    /// The result type is the inner type T (not T?).
    ///
    /// When multiple optional variables of matching type are in scope,
    /// generates a chained coalescing expression like
    /// `optA ?? optB ?? defaultExpr` (up to 3 optionals in the chain)
    /// with probability controlled by `config.chained_coalesce_probability`.
    pub(super) fn try_generate_null_coalesce(
        &mut self,
        target: &TypeInfo,
        ctx: &ExprContext,
        depth: usize,
    ) -> Option<String> {
        let candidates = ctx.optional_vars_matching(target);
        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (first_var, _inner_ty) = &candidates[idx];

        // When 2+ optional vars match, sometimes chain them: a ?? b ?? default
        if candidates.len() >= 2
            && self.config.chained_coalesce_probability > 0.0
            && self.rng.gen_bool(self.config.chained_coalesce_probability)
        {
            // Pick 1-2 additional optional vars for the chain (up to 3 total)
            let max_extra = (candidates.len() - 1).min(2);
            let extra_count = self.rng.gen_range(1..=max_extra);

            let mut chain_parts = vec![first_var.clone()];
            let mut used = std::collections::HashSet::new();
            used.insert(idx);

            for _ in 0..extra_count {
                // Pick a different candidate
                let remaining: Vec<usize> = (0..candidates.len())
                    .filter(|i| !used.contains(i))
                    .collect();
                if remaining.is_empty() {
                    break;
                }
                let pick = self.rng.gen_range(0..remaining.len());
                let chosen_idx = remaining[pick];
                used.insert(chosen_idx);
                chain_parts.push(candidates[chosen_idx].0.clone());
            }

            // Generate a default value of the inner type as the final fallback
            let default_expr = self.generate(target, ctx, depth + 1);
            chain_parts.push(default_expr);

            return Some(format!("({})", chain_parts.join(" ?? ")));
        }

        // Generate a default value of the inner type
        let default_expr = self.generate(target, ctx, depth + 1);

        Some(format!("({} ?? {})", first_var, default_expr))
    }

    /// Generate a simple string->string method call suffix for chaining.
    ///
    /// Returns a suffix like `.trim()`, `.to_upper()`, or `.to_lower()`.
    /// These are safe to chain onto any string expression without arguments,
    /// keeping the generated code simple and avoiding issues with nested
    /// `replace`/`substring` calls.
    pub(super) fn random_simple_string_chain_suffix(&mut self) -> &'static str {
        let methods = [".trim()", ".to_upper()", ".to_lower()"];
        methods[self.rng.gen_range(0..methods.len())]
    }

    /// Try to generate an `arr.length()` call for an i64 expression.
    ///
    /// Looks for any array-typed variable in scope and returns
    /// `Some("arrVar.length()")` on success.
    pub(super) fn try_generate_array_length(&mut self, ctx: &ExprContext) -> Option<String> {
        let candidates = ctx.array_vars();
        if candidates.is_empty() {
            return None;
        }
        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, _) = &candidates[idx];
        Some(format!("{}.length()", var_name))
    }

    /// Try to generate a `str.length()` call for an i64 expression.
    ///
    /// Looks for string-typed variables in scope and returns
    /// `Some("strVar.length()")` on success.
    pub(super) fn try_generate_string_length(&mut self, ctx: &ExprContext) -> Option<String> {
        let candidates = ctx.string_vars();
        if candidates.is_empty() {
            return None;
        }
        let idx = self.rng.gen_range(0..candidates.len());
        let var = &candidates[idx];

        // ~25% chance to prepend a string->string transform before .length()
        // e.g. str.trim().length()
        if self.rng.gen_bool(self.config.method_chain_probability) {
            let chain = self.random_simple_string_chain_suffix();
            Some(format!("{}{}.length()", var, chain))
        } else {
            Some(format!("{}.length()", var))
        }
    }

    /// Try to generate a bool-returning string method call.
    ///
    /// Randomly picks one of `contains`, `starts_with`, or `ends_with`.
    /// Looks for string-typed variables in scope and returns
    /// `Some("strVar.method(\"literal\")")` on success. The argument is
    /// always a short string literal to keep the expression simple.
    pub(super) fn try_generate_string_bool_method(&mut self, ctx: &ExprContext) -> Option<String> {
        let candidates = ctx.string_vars();
        if candidates.is_empty() {
            return None;
        }
        let idx = self.rng.gen_range(0..candidates.len());
        let var = &candidates[idx];

        // ~25% chance to prepend a string->string transform before the bool method
        // e.g. str.to_lower().contains("x")
        let chain = if self.rng.gen_bool(self.config.method_chain_probability) {
            self.random_simple_string_chain_suffix()
        } else {
            ""
        };

        // Pick a bool-returning string method
        let methods = ["contains", "starts_with", "ends_with"];
        let method = methods[self.rng.gen_range(0..methods.len())];

        // Use a short literal substring as the argument
        let substrings = ["str", "hello", "a", "test", "x", ""];
        let sub_idx = self.rng.gen_range(0..substrings.len());
        Some(format!(
            "{}{}.{}(\"{}\")",
            var, chain, method, substrings[sub_idx]
        ))
    }

    /// Try to generate a string-returning string method call.
    ///
    /// Randomly picks one of `to_upper`, `to_lower`, `trim`, `replace`,
    /// or `replace_all`. Looks for string-typed variables in scope and
    /// returns `Some("strVar.method(...)")` on success.
    ///
    /// For `replace`/`replace_all`, uses fixed string literal arguments
    /// to keep RNG consumption constant (exactly 2 RNG calls: one for
    /// the variable, one for the method) regardless of which method is
    /// selected.
    pub(super) fn try_generate_string_transform_method(
        &mut self,
        ctx: &ExprContext,
    ) -> Option<String> {
        let candidates = ctx.string_vars();
        if candidates.is_empty() {
            return None;
        }
        let idx = self.rng.gen_range(0..candidates.len());
        let var = &candidates[idx];

        // Pick a string-returning string method.
        // replace/replace_all take (old, new) string args; substring takes (start, end) i64 args;
        // others take no args.
        let methods = [
            "to_upper",
            "to_lower",
            "trim",
            "trim_start",
            "trim_end",
            "replace",
            "replace_all",
            "substring",
        ];
        let method = methods[self.rng.gen_range(0..methods.len())];

        let base = match method {
            "replace" | "replace_all" => {
                // Use varied literal arguments; pick from a fixed set so
                // RNG consumption stays constant (one gen_range call).
                let pairs = [("str", "val"), ("a", "b"), ("hello", "world"), (" ", "_")];
                let pair_idx = self.rng.gen_range(0..pairs.len());
                let (old, new) = pairs[pair_idx];
                format!("{}.{}(\"{}\", \"{}\")", var, method, old, new)
            }
            "substring" => {
                // substring(start, end) takes two i32 arguments.
                // Pick from a few fixed ranges to add variety.
                let ranges = [(0, 3), (0, 5), (1, 4), (0, 1)];
                let range_idx = self.rng.gen_range(0..ranges.len());
                let (start, end) = ranges[range_idx];
                format!("{}.substring({}, {})", var, start, end)
            }
            _ => format!("{}.{}()", var, method),
        };

        // ~25% chance to chain another simple string->string transform
        // e.g. str.trim().to_upper()
        if self.rng.gen_bool(self.config.method_chain_probability) {
            let chain = self.random_simple_string_chain_suffix();
            Some(format!("{}{}", base, chain))
        } else {
            Some(base)
        }
    }

    /// Try to generate a `.to_string()` call on a numeric or boolean variable.
    ///
    /// Looks for numeric (i8..u64, f32, f64) and bool variables in scope and
    /// returns `Some("var.to_string()")` on success. This produces a string-typed
    /// expression that exercises primitive method dispatch.
    pub(super) fn try_generate_to_string_call(&mut self, ctx: &ExprContext) -> Option<String> {
        let candidates = ctx.to_string_candidate_vars();
        if candidates.is_empty() {
            return None;
        }
        let idx = self.rng.gen_range(0..candidates.len());
        let var = &candidates[idx];
        Some(format!("{}.to_string()", var))
    }

    /// Try to generate a string interpolation containing a method call.
    ///
    /// Looks for string-typed or array-typed variables in scope and generates
    /// an interpolated string that includes a method call on the variable.
    /// For strings: `.to_upper()`, `.to_lower()`, `.trim()`, `.length()`.
    /// For arrays: `.length()`.
    /// Returns `None` if no suitable variables are in scope.
    pub(super) fn try_generate_method_call_interpolation(
        &mut self,
        ctx: &ExprContext,
    ) -> Option<String> {
        // Collect candidate variables: strings and arrays
        let string_vars = ctx.string_vars();
        let array_vars = ctx.array_vars();

        if string_vars.is_empty() && array_vars.is_empty() {
            return None;
        }

        // Build a flat list of (name, is_string) candidates
        let mut candidates: Vec<(&str, bool)> = Vec::new();
        for name in &string_vars {
            candidates.push((name.as_str(), true));
        }
        for (name, _elem_ty) in &array_vars {
            candidates.push((name.as_str(), false));
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, is_string) = candidates[idx];

        // Generate the method call expression
        let method_expr = if is_string {
            match self.rng.gen_range(0..4) {
                0 => format!("{}.to_upper()", var_name),
                1 => format!("{}.to_lower()", var_name),
                2 => format!("{}.trim()", var_name),
                _ => format!("{}.length()", var_name),
            }
        } else {
            format!("{}.length()", var_name)
        };

        // Wrap in an interpolated string with optional prefix text
        let prefixes = ["len: ", "upper: ", "result: ", "val: ", "got ", ""];
        let prefix = prefixes[self.rng.gen_range(0..prefixes.len())];
        Some(format!("\"{}{{{}}}\"", prefix, method_expr))
    }

    /// Try to generate a `str.split(",").collect()` call for a `[string]` expression.
    ///
    /// Looks for string-typed variables in scope and returns
    /// `Some("strVar.split(\"delim\").collect()")` on success.
    pub(super) fn try_generate_string_split(&mut self, ctx: &ExprContext) -> Option<String> {
        let candidates = ctx.string_vars();
        if candidates.is_empty() {
            return None;
        }
        let idx = self.rng.gen_range(0..candidates.len());
        let var = &candidates[idx];

        // Use a short literal delimiter
        let delimiters = [",", " ", ":", ";", "-", "::"];
        let delim = delimiters[self.rng.gen_range(0..delimiters.len())];

        Some(format!("{}.split(\"{}\").collect()", var, delim))
    }

    /// Try to generate a `str.chars().collect()` call for a `[i32]` expression.
    ///
    /// `.chars()` returns character codepoints as i32 values, so
    /// `.chars().collect()` produces `[i32]`. Looks for string-typed
    /// variables in scope and returns `Some("strVar.chars().collect()")`
    /// on success. Optionally chains a simple string transform before `.chars()`.
    pub(super) fn try_generate_string_chars_collect(
        &mut self,
        ctx: &ExprContext,
    ) -> Option<String> {
        let candidates = ctx.string_vars();
        if candidates.is_empty() {
            return None;
        }
        let idx = self.rng.gen_range(0..candidates.len());
        let var = &candidates[idx];

        // ~25% chance to prepend a string->string transform before .chars()
        // e.g. str.trim().chars().collect()
        if self.rng.gen_bool(self.config.method_chain_probability) {
            let chain = self.random_simple_string_chain_suffix();
            Some(format!("{}{}.chars().collect()", var, chain))
        } else {
            Some(format!("{}.chars().collect()", var))
        }
    }

    /// Generate a string concatenation expression using the `+` operator.
    ///
    /// Produces expressions like `"hello" + " world"`, `str_var + " suffix"`,
    /// `str_var + num.to_string()`, or `str_var + other_var`. Concatenates 2-3
    /// operands, each of which is a string variable, string literal, or a
    /// `.to_string()` call on a numeric/bool variable.
    pub(super) fn generate_string_concat(&mut self, ctx: &ExprContext, depth: usize) -> String {
        let str_ty = TypeInfo::Primitive(PrimitiveType::String);
        let operand_count = self.rng.gen_range(2..=3);
        let mut parts = Vec::new();

        for _ in 0..operand_count {
            // ~30% chance: use .to_string() on a numeric/bool variable
            if self.rng.gen_bool(0.3)
                && let Some(expr) = self.try_generate_to_string_call(ctx)
            {
                parts.push(expr);
                continue;
            }
            // Use a simple string expression (variable or literal) to avoid
            // deep nesting of complex sub-expressions in concatenation.
            parts.push(self.generate_simple(&str_ty, ctx));
        }

        let _ = depth; // depth reserved for future nested concat support
        format!("({})", parts.join(" + "))
    }

    /// Try to generate an interface method call on a type-param-typed variable.
    ///
    /// Looks for variables in scope whose type is a type parameter with interface
    /// constraints. If found, picks a method from one of the constraining interfaces
    /// whose return type matches the target type and generates a method call.
    ///
    /// Returns `Some("varName.methodName(args)")` on success.
    pub(super) fn try_generate_type_param_method_call(
        &mut self,
        target: &TypeInfo,
        ctx: &ExprContext,
    ) -> Option<String> {
        let constrained_vars = ctx.constrained_type_param_vars();
        if constrained_vars.is_empty() {
            return None;
        }

        // Collect all (var_name, method_name, params) candidates where method returns target type
        let mut candidates: Vec<(String, String, Vec<crate::symbols::ParamInfo>)> = Vec::new();

        for (var_name, _tp_name, constraints) in &constrained_vars {
            let methods = get_type_param_constraint_methods(ctx.table, constraints);
            for (_iface_info, method) in methods {
                // Check if return type matches target (only check non-generic interfaces)
                if types_compatible(&method.return_type, target) {
                    candidates.push((var_name.clone(), method.name.clone(), method.params.clone()));
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, method_name, params) = &candidates[idx];

        // Generate arguments for the method call
        let args = self.generate_method_args(params, ctx);
        Some(format!("{}.{}({})", var_name, method_name, args))
    }

    /// Try to generate an optional chaining expression (`optVar?.fieldName`).
    ///
    /// Looks for optional-typed variables in scope whose inner type is a class
    /// with accessible fields. Returns `Some(("optVar?.fieldName", field_type?))`
    /// where the result type is `Optional(field_type)`.
    /// Only considers non-generic classes.
    pub(super) fn try_generate_optional_chaining(
        &mut self,
        ctx: &ExprContext,
    ) -> Option<(String, TypeInfo)> {
        let opt_class_vars = ctx.optional_class_vars();
        if opt_class_vars.is_empty() {
            return None;
        }

        // Collect (var_name, field_name, field_type) candidates
        let mut candidates: Vec<(String, String, TypeInfo)> = Vec::new();

        for (var_name, mod_id, sym_id) in &opt_class_vars {
            if let Some(sym) = ctx.table.get_symbol(*mod_id, *sym_id)
                && let SymbolKind::Class(ref info) = sym.kind
            {
                // Skip generic classes
                if !info.type_params.is_empty() {
                    continue;
                }
                for field in &info.fields {
                    candidates.push((
                        var_name.clone(),
                        field.name.clone(),
                        field.field_type.clone(),
                    ));
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, field_name, field_type) = &candidates[idx];

        // The result of ?. is always optional
        let result_type = TypeInfo::Optional(Box::new(field_type.clone()));
        Some((format!("{}?.{}", var_name, field_name), result_type))
    }

    /// Try to generate an iterator `.any()` or `.all()` expression.
    ///
    /// Looks for array-typed variables in scope with primitive element types
    /// and generates `arrVar.iter().any((x) => PRED)` or
    /// `arrVar.iter().all((x) => PRED)`. Returns a bool-typed expression.
    ///
    /// Predicates are type-appropriate:
    /// - Numeric (i64, f64): comparisons like `x > 3`, `x < 10`, `x % 2 == 0`
    /// - Bool: `x` or `!x`
    /// - String: `x.length() > N`
    pub(super) fn try_generate_iter_any_all(&mut self, ctx: &ExprContext) -> Option<String> {
        let array_vars = ctx.array_vars();

        // Filter to arrays with primitive element types that support predicates
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| {
                matches!(
                    elem_ty,
                    TypeInfo::Primitive(
                        PrimitiveType::I64
                            | PrimitiveType::F64
                            | PrimitiveType::Bool
                            | PrimitiveType::String
                    )
                )
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, elem_ty) = candidates[idx];

        // Pick any() or all()
        let method = if self.rng.gen_bool(0.5) { "any" } else { "all" };

        // Generate a type-appropriate predicate body
        let pred = match elem_ty {
            TypeInfo::Primitive(PrimitiveType::I64) => match self.rng.gen_range(0..4) {
                0 => {
                    let n = self.rng.gen_range(0..=5);
                    format!("x > {}", n)
                }
                1 => {
                    let n = self.rng.gen_range(0..=10);
                    format!("x < {}", n)
                }
                2 => "x % 2 == 0".to_string(),
                _ => {
                    let n = self.rng.gen_range(0..=5);
                    format!("x != {}", n)
                }
            },
            TypeInfo::Primitive(PrimitiveType::F64) => {
                let n = self.rng.gen_range(0..=50);
                format!("x > {}.0", n)
            }
            TypeInfo::Primitive(PrimitiveType::Bool) => {
                if self.rng.gen_bool(0.5) {
                    "x".to_string()
                } else {
                    "!x".to_string()
                }
            }
            TypeInfo::Primitive(PrimitiveType::String) => {
                let n = self.rng.gen_range(0..=3);
                format!("x.length() > {}", n)
            }
            _ => return None,
        };

        Some(format!("{}.iter().{}((x) => {})", var_name, method, pred))
    }

    /// Try to generate an iterator `.map().collect()` expression for array generation.
    ///
    /// Looks for array-typed variables in scope with primitive element types and
    /// generates `arrVar.iter().map((x) => body).collect()` where the mapping
    /// closure transforms the source element type into the target element type.
    ///
    /// Supported same-type mappings:
    /// - `i64 -> i64`: `x * 2`, `x + 1`, `x % 10`, `-x`
    /// - `f64 -> f64`: `x * 2.0`, `x + 1.0`, `-x`
    /// - `i32 -> i32`: `x * 2`, `x + 1`
    /// - `string -> string`: `x.trim()`, `x.to_upper()`, `x.to_lower()`
    /// - `bool -> bool`: `!x`
    ///
    /// Supported cross-type mappings:
    /// - `i64 -> bool`: `x > 0`, `x % 2 == 0`
    /// - `string -> i64`: `x.length()`
    pub(super) fn try_generate_iter_map_collect(
        &mut self,
        target_elem: &TypeInfo,
        ctx: &ExprContext,
    ) -> Option<String> {
        let array_vars = ctx.array_vars();

        // Build candidates: (var_name, source_elem_ty) where we can map source -> target
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, src_elem)| self.can_map_types(src_elem, target_elem))
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, src_elem) = candidates[idx];

        let body = self.generate_map_body(src_elem, target_elem)?;

        Some(format!(
            "{}.iter().map((x) => {}).collect()",
            var_name, body
        ))
    }

    /// Check whether we can generate a map closure from `src` to `target`.
    fn can_map_types(&self, src: &TypeInfo, target: &TypeInfo) -> bool {
        use PrimitiveType::*;
        match (src, target) {
            // Same-type mappings
            (TypeInfo::Primitive(I64), TypeInfo::Primitive(I64)) => true,
            (TypeInfo::Primitive(F64), TypeInfo::Primitive(F64)) => true,
            (TypeInfo::Primitive(I32), TypeInfo::Primitive(I32)) => true,
            (TypeInfo::Primitive(String), TypeInfo::Primitive(String)) => true,
            (TypeInfo::Primitive(Bool), TypeInfo::Primitive(Bool)) => true,
            // Cross-type mappings
            (TypeInfo::Primitive(I64), TypeInfo::Primitive(Bool)) => true,
            (TypeInfo::Primitive(String), TypeInfo::Primitive(I64)) => true,
            _ => false,
        }
    }

    /// Generate the body of a map closure that transforms `src` type to `target` type.
    fn generate_map_body(&mut self, src: &TypeInfo, target: &TypeInfo) -> Option<String> {
        use PrimitiveType::*;
        match (src, target) {
            (TypeInfo::Primitive(I64), TypeInfo::Primitive(I64)) => {
                Some(match self.rng.gen_range(0..4) {
                    0 => "x * 2".to_string(),
                    1 => "x + 1".to_string(),
                    2 => "x % 10".to_string(),
                    _ => "-x".to_string(),
                })
            }
            (TypeInfo::Primitive(F64), TypeInfo::Primitive(F64)) => {
                Some(match self.rng.gen_range(0..3) {
                    0 => "x * 2.0".to_string(),
                    1 => "x + 1.0".to_string(),
                    _ => "-x".to_string(),
                })
            }
            (TypeInfo::Primitive(I32), TypeInfo::Primitive(I32)) => {
                Some(match self.rng.gen_range(0..2) {
                    0 => "x * 2_i32".to_string(),
                    _ => "x + 1_i32".to_string(),
                })
            }
            (TypeInfo::Primitive(String), TypeInfo::Primitive(String)) => {
                Some(match self.rng.gen_range(0..3) {
                    0 => "x.trim()".to_string(),
                    1 => "x.to_upper()".to_string(),
                    _ => "x.to_lower()".to_string(),
                })
            }
            (TypeInfo::Primitive(Bool), TypeInfo::Primitive(Bool)) => Some("!x".to_string()),
            (TypeInfo::Primitive(I64), TypeInfo::Primitive(Bool)) => {
                Some(match self.rng.gen_range(0..2) {
                    0 => "x > 0".to_string(),
                    _ => "x % 2 == 0".to_string(),
                })
            }
            (TypeInfo::Primitive(String), TypeInfo::Primitive(I64)) => {
                Some("x.length()".to_string())
            }
            _ => None,
        }
    }

    /// Try to generate an iterator `.filter().collect()` expression for array generation.
    ///
    /// Looks for array-typed variables in scope whose element type matches the
    /// target element type and generates `arrVar.iter().filter((x) => pred).collect()`.
    /// The predicate is type-appropriate, reusing the same patterns as `try_generate_iter_any_all`.
    pub(super) fn try_generate_iter_filter_collect(
        &mut self,
        target_elem: &TypeInfo,
        ctx: &ExprContext,
    ) -> Option<String> {
        let array_vars = ctx.array_vars();

        // Filter to arrays whose element type matches and is a supported primitive
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| {
                elem_ty == target_elem
                    && matches!(
                        elem_ty,
                        TypeInfo::Primitive(
                            PrimitiveType::I64
                                | PrimitiveType::F64
                                | PrimitiveType::I32
                                | PrimitiveType::Bool
                                | PrimitiveType::String
                        )
                    )
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, elem_ty) = candidates[idx];

        // Generate a type-appropriate predicate (same patterns as any/all)
        let pred = match elem_ty {
            TypeInfo::Primitive(PrimitiveType::I64) => match self.rng.gen_range(0..4) {
                0 => {
                    let n = self.rng.gen_range(0..=5);
                    format!("x > {}", n)
                }
                1 => {
                    let n = self.rng.gen_range(0..=10);
                    format!("x < {}", n)
                }
                2 => "x % 2 == 0".to_string(),
                _ => {
                    let n = self.rng.gen_range(0..=5);
                    format!("x != {}", n)
                }
            },
            TypeInfo::Primitive(PrimitiveType::F64) => {
                let n = self.rng.gen_range(0..=50);
                format!("x > {}.0", n)
            }
            TypeInfo::Primitive(PrimitiveType::I32) => match self.rng.gen_range(0..3) {
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
            TypeInfo::Primitive(PrimitiveType::Bool) => {
                if self.rng.gen_bool(0.5) {
                    "x".to_string()
                } else {
                    "!x".to_string()
                }
            }
            TypeInfo::Primitive(PrimitiveType::String) => {
                let n = self.rng.gen_range(0..=3);
                format!("x.length() > {}", n)
            }
            _ => return None,
        };

        Some(format!(
            "{}.iter().filter((x) => {}).collect()",
            var_name, pred
        ))
    }

    /// Try to generate an `.iter().count()` expression for i64 generation.
    ///
    /// Looks for array-typed variables in scope and generates `arrVar.iter().count()`.
    /// Optionally chains a `.filter()` before `.count()` for more interesting expressions.
    /// Returns an i64-typed expression.
    pub(super) fn try_generate_iter_count(&mut self, ctx: &ExprContext) -> Option<String> {
        let array_vars = ctx.array_vars();
        if array_vars.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..array_vars.len());
        let (var_name, elem_ty) = &array_vars[idx];

        // ~40% chance to chain a .filter() before .count()
        if self.rng.gen_bool(0.4) {
            let pred = match elem_ty {
                TypeInfo::Primitive(PrimitiveType::I64) => {
                    let n = self.rng.gen_range(0..=5);
                    Some(format!("x > {}", n))
                }
                TypeInfo::Primitive(PrimitiveType::F64) => {
                    let n = self.rng.gen_range(0..=50);
                    Some(format!("x > {}.0", n))
                }
                TypeInfo::Primitive(PrimitiveType::I32) => {
                    let n = self.rng.gen_range(0..=5);
                    Some(format!("x > {}", n))
                }
                TypeInfo::Primitive(PrimitiveType::Bool) => Some("x".to_string()),
                TypeInfo::Primitive(PrimitiveType::String) => {
                    let n = self.rng.gen_range(0..=3);
                    Some(format!("x.length() > {}", n))
                }
                _ => None,
            };
            if let Some(pred) = pred {
                return Some(format!(
                    "{}.iter().filter((x) => {}).count()",
                    var_name, pred
                ));
            }
        }

        Some(format!("{}.iter().count()", var_name))
    }

    /// Try to generate an `.iter().reduce()` expression.
    ///
    /// Looks for array-typed variables in scope and generates reduce expressions
    /// based on the target type:
    /// - `i64` target from `[i64]`: `arr.iter().reduce(0, (acc, x) => acc + x)` (sum)
    /// - `string` target from `[string]`: `arr.iter().reduce("", (acc, x) => acc + x + " ")` (join)
    /// - `string` target from `[i64]`: `arr.iter().map((x) => "" + x).reduce("", (acc, s) => acc + s + ",")` (stringify+join)
    pub(super) fn try_generate_iter_reduce(
        &mut self,
        target: &TypeInfo,
        ctx: &ExprContext,
    ) -> Option<String> {
        let array_vars = ctx.array_vars();
        if array_vars.is_empty() {
            return None;
        }

        // Collect candidates: (var_name, elem_type) pairs that can produce target
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| match target {
                TypeInfo::Primitive(PrimitiveType::I64) => {
                    matches!(elem_ty, TypeInfo::Primitive(PrimitiveType::I64))
                }
                TypeInfo::Primitive(PrimitiveType::String) => {
                    matches!(
                        elem_ty,
                        TypeInfo::Primitive(PrimitiveType::String | PrimitiveType::I64)
                    )
                }
                _ => false,
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, elem_ty) = candidates[idx];

        match (target, elem_ty) {
            // i64 from [i64]: sum via reduce
            (TypeInfo::Primitive(PrimitiveType::I64), TypeInfo::Primitive(PrimitiveType::I64)) => {
                Some(format!(
                    "{}.iter().reduce(0, (acc, x) => acc + x)",
                    var_name
                ))
            }
            // string from [string]: join with space
            (
                TypeInfo::Primitive(PrimitiveType::String),
                TypeInfo::Primitive(PrimitiveType::String),
            ) => Some(format!(
                "{}.iter().reduce(\"\", (acc, x) => acc + x + \" \")",
                var_name
            )),
            // string from [i64]: map to string then join with comma
            (
                TypeInfo::Primitive(PrimitiveType::String),
                TypeInfo::Primitive(PrimitiveType::I64),
            ) => Some(format!(
                "{}.iter().map((x) => \"\" + x).reduce(\"\", (acc, s) => acc + s + \",\")",
                var_name
            )),
            _ => None,
        }
    }

    /// Try to generate an `.iter().sum()` expression for numeric types.
    ///
    /// Looks for array-typed variables in scope with numeric element types (i64, f64)
    /// and generates `arrVar.iter().sum()`. Optionally chains a `.filter()` or `.map()`
    /// before `.sum()` for more interesting expressions.
    pub(super) fn try_generate_iter_sum(
        &mut self,
        target_prim: PrimitiveType,
        ctx: &ExprContext,
    ) -> Option<String> {
        let array_vars = ctx.array_vars();

        // Filter to arrays whose element type matches target numeric type
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| *elem_ty == TypeInfo::Primitive(target_prim))
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, _) = candidates[idx];

        // ~30% chance: chain a .filter() before .sum()
        if self.rng.gen_bool(0.3) {
            let pred = match target_prim {
                PrimitiveType::I64 => {
                    let n = self.rng.gen_range(0..=5);
                    format!("x > {}", n)
                }
                PrimitiveType::F64 => {
                    let n = self.rng.gen_range(0..=10);
                    format!("x > {}.0", n)
                }
                _ => return Some(format!("{}.iter().sum()", var_name)),
            };
            return Some(format!("{}.iter().filter((x) => {}).sum()", var_name, pred));
        }

        // ~20% chance: chain a .map() before .sum() (same type)
        if self.rng.gen_bool(0.2) {
            let body = match target_prim {
                PrimitiveType::I64 => match self.rng.gen_range(0..3) {
                    0 => "x * 2",
                    1 => "x + 1",
                    _ => "-x",
                },
                PrimitiveType::F64 => match self.rng.gen_range(0..2) {
                    0 => "x * 2.0",
                    _ => "x + 1.0",
                },
                _ => return Some(format!("{}.iter().sum()", var_name)),
            };
            return Some(format!("{}.iter().map((x) => {}).sum()", var_name, body));
        }

        Some(format!("{}.iter().sum()", var_name))
    }

    /// Try to generate an `.iter().first()`, `.iter().last()`, or `.iter().nth(N)` expression.
    ///
    /// Looks for array-typed variables in scope whose element type matches the
    /// target `inner` type (the inner type of an optional) and generates an
    /// iterator terminal that returns `T?`:
    /// - `arrVar.iter().first()`
    /// - `arrVar.iter().last()`
    /// - `arrVar.iter().nth(N)` (N in 0..=3)
    ///
    /// Optionally chains a `.filter()` (~20% chance) or `.map()` (~20% chance,
    /// same-type only) before the terminal method for more interesting expressions.
    pub(super) fn try_generate_iter_first_last_nth(
        &mut self,
        inner: &TypeInfo,
        ctx: &ExprContext,
    ) -> Option<String> {
        let array_vars = ctx.array_vars();

        // Filter to arrays whose element type matches inner and is a supported primitive
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| {
                elem_ty == inner
                    && matches!(
                        elem_ty,
                        TypeInfo::Primitive(
                            PrimitiveType::I64
                                | PrimitiveType::I32
                                | PrimitiveType::I128
                                | PrimitiveType::F64
                                | PrimitiveType::Bool
                                | PrimitiveType::String
                        )
                    )
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, elem_ty) = candidates[idx];

        // Pick the terminal method: first(), last(), or nth(N)
        let terminal = match self.rng.gen_range(0..3) {
            0 => ".first()".to_string(),
            1 => ".last()".to_string(),
            _ => {
                let n = self.rng.gen_range(0..=3);
                format!(".nth({})", n)
            }
        };

        // ~20% chance: chain a .filter() before the terminal
        if self.rng.gen_bool(0.2) {
            let pred = match elem_ty {
                TypeInfo::Primitive(PrimitiveType::I64) => match self.rng.gen_range(0..3) {
                    0 => {
                        let n = self.rng.gen_range(0..=5);
                        format!("x > {}", n)
                    }
                    1 => "x % 2 == 0".to_string(),
                    _ => {
                        let n = self.rng.gen_range(0..=10);
                        format!("x < {}", n)
                    }
                },
                TypeInfo::Primitive(PrimitiveType::I32) => match self.rng.gen_range(0..3) {
                    0 => {
                        let n = self.rng.gen_range(0..=5);
                        format!("x > {}", n)
                    }
                    1 => "x % 2 == 0".to_string(),
                    _ => {
                        let n = self.rng.gen_range(0..=10);
                        format!("x < {}", n)
                    }
                },
                TypeInfo::Primitive(PrimitiveType::I128) => match self.rng.gen_range(0..3) {
                    0 => {
                        let n = self.rng.gen_range(0..=5);
                        format!("x > {}", n)
                    }
                    1 => "x % 2 == 0".to_string(),
                    _ => {
                        let n = self.rng.gen_range(0..=10);
                        format!("x < {}", n)
                    }
                },
                TypeInfo::Primitive(PrimitiveType::F64) => {
                    let n = self.rng.gen_range(0..=50);
                    format!("x > {}.0", n)
                }
                TypeInfo::Primitive(PrimitiveType::Bool) => {
                    if self.rng.gen_bool(0.5) {
                        "x".to_string()
                    } else {
                        "!x".to_string()
                    }
                }
                TypeInfo::Primitive(PrimitiveType::String) => {
                    let n = self.rng.gen_range(0..=3);
                    format!("x.length() > {}", n)
                }
                _ => {
                    return Some(format!("{}.iter(){}", var_name, terminal));
                }
            };
            return Some(format!(
                "{}.iter().filter((x) => {}){}",
                var_name, pred, terminal
            ));
        }

        // ~20% chance: chain a .map() before the terminal (same-type only)
        if self.rng.gen_bool(0.2) {
            let body = match elem_ty {
                TypeInfo::Primitive(PrimitiveType::I64) => match self.rng.gen_range(0..4) {
                    0 => Some("x * 2"),
                    1 => Some("x + 1"),
                    2 => Some("x % 10"),
                    _ => Some("-x"),
                },
                TypeInfo::Primitive(PrimitiveType::I32) => match self.rng.gen_range(0..2) {
                    0 => Some("x * 2_i32"),
                    _ => Some("x + 1_i32"),
                },
                TypeInfo::Primitive(PrimitiveType::I128) => match self.rng.gen_range(0..2) {
                    0 => Some("x * 2_i128"),
                    _ => Some("x + 1_i128"),
                },
                TypeInfo::Primitive(PrimitiveType::F64) => match self.rng.gen_range(0..3) {
                    0 => Some("x * 2.0"),
                    1 => Some("x + 1.0"),
                    _ => Some("-x"),
                },
                TypeInfo::Primitive(PrimitiveType::Bool) => Some("!x"),
                TypeInfo::Primitive(PrimitiveType::String) => match self.rng.gen_range(0..3) {
                    0 => Some("x.trim()"),
                    1 => Some("x.to_upper()"),
                    _ => Some("x.to_lower()"),
                },
                _ => None,
            };
            if let Some(body) = body {
                return Some(format!(
                    "{}.iter().map((x) => {}){}",
                    var_name, body, terminal
                ));
            }
        }

        Some(format!("{}.iter(){}", var_name, terminal))
    }

    /// Try to generate an `.iter().skip(N).take(M).collect()` expression for array generation.
    ///
    /// Looks for array-typed variables in scope whose element type matches the
    /// target element type and generates `arrVar.iter().skip(N).take(M).collect()`.
    /// Uses small skip/take values to avoid producing empty arrays.
    pub(super) fn try_generate_iter_skip_take_collect(
        &mut self,
        target_elem: &TypeInfo,
        ctx: &ExprContext,
    ) -> Option<String> {
        let array_vars = ctx.array_vars();

        // Filter to arrays whose element type matches
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| elem_ty == target_elem)
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, _) = candidates[idx];

        // Use small values to keep results non-empty (arrays have min 2 elements)
        // ~40% skip+take, ~30% take only, ~30% skip only
        match self.rng.gen_range(0..10) {
            0..4 => {
                let skip = self.rng.gen_range(0..=1);
                let take = self.rng.gen_range(1..=2);
                Some(format!(
                    "{}.iter().skip({}).take({}).collect()",
                    var_name, skip, take
                ))
            }
            4..7 => {
                let take = self.rng.gen_range(1..=3);
                Some(format!("{}.iter().take({}).collect()", var_name, take))
            }
            _ => {
                let skip = self.rng.gen_range(0..=1);
                Some(format!("{}.iter().skip({}).collect()", var_name, skip))
            }
        }
    }

    /// Try to generate an `.iter().sorted().collect()` expression for array generation.
    ///
    /// Looks for array-typed variables in scope whose element type matches the
    /// target element type AND is i64 or i32 (sorted only works correctly on
    /// integer types). Randomly generates one of:
    /// - `arr.iter().sorted().collect()` (~40%)
    /// - `arr.iter().sorted().reverse().collect()` (~20%)
    /// - `arr.iter().filter((x) => pred).sorted().collect()` (~20%)
    /// - `arr.iter().map((x) => body).sorted().collect()` (~20%)
    pub(super) fn try_generate_iter_sorted_collect(
        &mut self,
        target_elem: &TypeInfo,
        ctx: &ExprContext,
    ) -> Option<String> {
        // Only works for i64 and i32 element types
        let is_i64 = matches!(target_elem, TypeInfo::Primitive(PrimitiveType::I64));
        let is_i32 = matches!(target_elem, TypeInfo::Primitive(PrimitiveType::I32));
        if !is_i64 && !is_i32 {
            return None;
        }

        let array_vars = ctx.array_vars();

        // Filter to arrays whose element type matches
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| elem_ty == target_elem)
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, _) = candidates[idx];

        // Pick a variant: sorted (40%), sorted+reverse (20%), filter+sorted (20%), map+sorted (20%)
        let variant = self.rng.gen_range(0..10);
        match variant {
            0..4 => {
                // arr.iter().sorted().collect()
                Some(format!("{}.iter().sorted().collect()", var_name))
            }
            4..6 => {
                // arr.iter().sorted().reverse().collect()
                Some(format!("{}.iter().sorted().reverse().collect()", var_name))
            }
            6..8 => {
                // arr.iter().filter((x) => pred).sorted().collect()
                let n = self.rng.gen_range(0..=5);
                let pred = if is_i32 {
                    format!("x > {}_i32", n)
                } else {
                    format!("x > {}", n)
                };
                Some(format!(
                    "{}.iter().filter((x) => {}).sorted().collect()",
                    var_name, pred
                ))
            }
            _ => {
                // arr.iter().map((x) => body).sorted().collect()
                let body = if is_i32 {
                    match self.rng.gen_range(0..3) {
                        0 => "x * 2_i32".to_string(),
                        1 => "x + 1_i32".to_string(),
                        _ => "-x".to_string(),
                    }
                } else {
                    match self.rng.gen_range(0..3) {
                        0 => "x * 2".to_string(),
                        1 => "x + 1".to_string(),
                        _ => "-x".to_string(),
                    }
                };
                Some(format!(
                    "{}.iter().map((x) => {}).sorted().collect()",
                    var_name, body
                ))
            }
        }
    }

    /// Try to generate an `.iter().chain(other.iter()).collect()` expression for array generation.
    ///
    /// Looks for TWO DIFFERENT array-typed variables in scope whose element type matches
    /// the target element type. Only supports i64 and i32 element types.
    /// Generates one of:
    /// - `arr1.iter().chain(arr2.iter()).collect()` (~60%)
    /// - `arr1.iter().chain(arr2.iter()).filter((x) => pred).collect()` (~20%)
    /// - `arr1.iter().chain(arr2.iter()).map((x) => body).collect()` (~20%)
    pub(super) fn try_generate_iter_chain_collect(
        &mut self,
        target_elem: &TypeInfo,
        ctx: &ExprContext,
    ) -> Option<String> {
        // Only works for i64 and i32 element types
        let is_i64 = matches!(target_elem, TypeInfo::Primitive(PrimitiveType::I64));
        let is_i32 = matches!(target_elem, TypeInfo::Primitive(PrimitiveType::I32));
        if !is_i64 && !is_i32 {
            return None;
        }

        let array_vars = ctx.array_vars();

        // Filter to arrays whose element type matches
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| elem_ty == target_elem)
            .collect();

        // Need at least 2 different array variables
        if candidates.len() < 2 {
            return None;
        }

        // Pick two different candidates
        let idx1 = self.rng.gen_range(0..candidates.len());
        let mut idx2 = self.rng.gen_range(0..candidates.len() - 1);
        if idx2 >= idx1 {
            idx2 += 1;
        }
        let (var1, _) = candidates[idx1];
        let (var2, _) = candidates[idx2];

        // Pick a variant: plain chain (60%), filter (20%), map (20%)
        let variant = self.rng.gen_range(0..10);
        match variant {
            0..6 => {
                // arr1.iter().chain(arr2.iter()).collect()
                Some(format!("{}.iter().chain({}.iter()).collect()", var1, var2))
            }
            6..8 => {
                // arr1.iter().chain(arr2.iter()).filter((x) => pred).collect()
                let pred = if is_i32 {
                    match self.rng.gen_range(0..3) {
                        0 => {
                            let n = self.rng.gen_range(0..=5);
                            format!("x > {}", n)
                        }
                        1 => {
                            let n = self.rng.gen_range(0..=10);
                            format!("x < {}", n)
                        }
                        _ => "x % 2 == 0".to_string(),
                    }
                } else {
                    match self.rng.gen_range(0..4) {
                        0 => {
                            let n = self.rng.gen_range(0..=5);
                            format!("x > {}", n)
                        }
                        1 => {
                            let n = self.rng.gen_range(0..=10);
                            format!("x < {}", n)
                        }
                        2 => "x % 2 == 0".to_string(),
                        _ => {
                            let n = self.rng.gen_range(0..=5);
                            format!("x != {}", n)
                        }
                    }
                };
                Some(format!(
                    "{}.iter().chain({}.iter()).filter((x) => {}).collect()",
                    var1, var2, pred
                ))
            }
            _ => {
                // arr1.iter().chain(arr2.iter()).map((x) => body).collect()
                let body = if is_i32 {
                    match self.rng.gen_range(0..3) {
                        0 => "x * 2_i32".to_string(),
                        1 => "x + 1_i32".to_string(),
                        _ => "-x".to_string(),
                    }
                } else {
                    match self.rng.gen_range(0..3) {
                        0 => "x * 2".to_string(),
                        1 => "x + 1".to_string(),
                        _ => "-x".to_string(),
                    }
                };
                Some(format!(
                    "{}.iter().chain({}.iter()).map((x) => {}).collect()",
                    var1, var2, body
                ))
            }
        }
    }

    /// Try to generate an `arr.iter().unique().collect()` expression for array generation.
    ///
    /// Only works for i64 and i32 element types (unique requires hashable elements,
    /// and bool unique has a runtime bug).
    pub(super) fn try_generate_iter_unique_collect(
        &mut self,
        target_elem: &TypeInfo,
        ctx: &ExprContext,
    ) -> Option<String> {
        // Only i64 and i32 -- unique() requires hashable elements
        let prim = match target_elem {
            TypeInfo::Primitive(PrimitiveType::I64) => PrimitiveType::I64,
            TypeInfo::Primitive(PrimitiveType::I32) => PrimitiveType::I32,
            _ => return None,
        };

        let array_vars = ctx.array_vars();
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| *elem_ty == *target_elem)
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, _) = candidates[idx];

        // ~30% chance: chain a .filter() before .unique()
        if self.rng.gen_bool(0.3) {
            let pred = match prim {
                PrimitiveType::I64 => {
                    let n = self.rng.gen_range(0..=5);
                    format!("x > {}", n)
                }
                PrimitiveType::I32 => {
                    let n = self.rng.gen_range(0..=5);
                    format!("x > {}_i32", n)
                }
                _ => unreachable!(),
            };
            return Some(format!(
                "{}.iter().filter((x) => {}).unique().collect()",
                var_name, pred
            ));
        }

        // ~20% chance: chain .sorted() after .unique() (sort the unique values)
        if self.rng.gen_bool(0.2) {
            return Some(format!("{}.iter().unique().sorted().collect()", var_name));
        }

        Some(format!("{}.iter().unique().collect()", var_name))
    }

    /// Try to generate an `.iter().flat_map((x) => [...]).collect()` expression for array generation.
    ///
    /// Only works for i64 and i32 element types. Looks for array-typed variables
    /// in scope whose element type matches the target, then generates one of:
    /// - `arr.iter().flat_map((x) => [x, x * 2]).collect()` (~40%)
    /// - `arr.iter().flat_map((x) => [x, -x]).collect()` (~20%)
    /// - `arr.iter().flat_map((x) => [x]).collect()` (~20%) -- identity-ish
    /// - `arr.iter().flat_map((x) => [x, x * 2]).filter((y) => pred).collect()` (~20%)
    pub(super) fn try_generate_iter_flat_map_collect(
        &mut self,
        target_elem: &TypeInfo,
        ctx: &ExprContext,
    ) -> Option<String> {
        let is_i64 = matches!(target_elem, TypeInfo::Primitive(PrimitiveType::I64));
        let is_i32 = matches!(target_elem, TypeInfo::Primitive(PrimitiveType::I32));
        if !is_i64 && !is_i32 {
            return None;
        }

        let array_vars = ctx.array_vars();
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| *elem_ty == *target_elem)
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, _) = candidates[idx];

        // Build the lambda body: [x, <expr>] where <expr> varies
        let (body_elems, suffix) = if is_i32 {
            let variant = self.rng.gen_range(0..10);
            match variant {
                0..4 => {
                    // [x, x * 2_i32]
                    ("x, x * 2_i32".to_string(), String::new())
                }
                4..6 => {
                    // [x, -x]
                    ("x, -x".to_string(), String::new())
                }
                6..8 => {
                    // [x] -- identity pass-through
                    ("x".to_string(), String::new())
                }
                _ => {
                    // [x, x * 2_i32] with a .filter() after
                    let n = self.rng.gen_range(0..=5);
                    (
                        "x, x * 2_i32".to_string(),
                        format!(".filter((y) => y > {}_i32)", n),
                    )
                }
            }
        } else {
            let variant = self.rng.gen_range(0..10);
            match variant {
                0..4 => {
                    // [x, x * 2]
                    ("x, x * 2".to_string(), String::new())
                }
                4..6 => {
                    // [x, -x]
                    ("x, -x".to_string(), String::new())
                }
                6..8 => {
                    // [x] -- identity pass-through
                    ("x".to_string(), String::new())
                }
                _ => {
                    // [x, x * 2] with a .filter() after
                    let n = self.rng.gen_range(0..=5);
                    ("x, x * 2".to_string(), format!(".filter((y) => y > {})", n))
                }
            }
        };

        Some(format!(
            "{}.iter().flat_map((x) => [{}]){}.collect()",
            var_name, body_elems, suffix
        ))
    }
}
