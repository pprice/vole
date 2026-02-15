//! Closure-related statement generators.
//!
//! Contains generators for match-closure arms, field-closure lets,
//! sentinel closure capture, struct closure capture, and nested closure capture.

use rand::Rng;

use crate::symbols::{PrimitiveType, SymbolKind, TypeInfo};

use super::{StmtContext, StmtGenerator};

impl<'a, R: Rng> StmtGenerator<'a, R> {
    /// Try to generate a match expression whose arms produce closures that
    /// capture surrounding variables.
    ///
    /// Finds an i64-typed variable to match on, plus a capturable numeric
    /// variable from the surrounding scope, and generates one of two patterns:
    ///
    /// **Pattern A — immediate invocation:**
    /// ```vole
    /// let f = match var {
    ///     1 => (n: i64) => n + captured
    ///     2 => (n: i64) => n * captured
    ///     _ => (n: i64) => n - captured
    /// }
    /// let result = f(some_arg)
    /// ```
    ///
    /// **Pattern B — iterator chain:**
    /// ```vole
    /// let f = match var {
    ///     1 => (n: i64) => n + captured
    ///     2 => (n: i64) => n * captured
    ///     _ => (n: i64) => n - captured
    /// }
    /// let result = arr.iter().map(f).collect()
    /// ```
    ///
    /// This exercises closure creation inside match arms, variable capture
    /// scope interaction, and function-typed match results in higher-order
    /// contexts.
    ///
    /// Returns `None` if preconditions are not met (need an i64 scrutinee
    /// and a capturable numeric variable).
    pub(super) fn try_generate_match_closure_arms(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Guard: closures that capture variables inside generic class methods hit a
        // compiler bug ("Captured variable not found"). Skip this pattern entirely
        // when we're generating a method body for a generic class.
        if let Some((cls_mod, cls_sym)) = ctx.current_class_sym_id
            && let Some(symbol) = ctx.table.get_symbol(cls_mod, cls_sym)
            && let SymbolKind::Class(info) = &symbol.kind
            && !info.type_params.is_empty()
        {
            return None;
        }

        // Step 1: Find an i64-typed variable to use as the match scrutinee
        let mut scrutinee_candidates: Vec<String> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)) {
                scrutinee_candidates.push(name.clone());
            }
        }
        for param in ctx.params.iter() {
            if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::I64)) {
                scrutinee_candidates.push(param.name.clone());
            }
        }
        if scrutinee_candidates.is_empty() {
            return None;
        }

        // Step 2: Find a capturable numeric variable (i64 or i32) that is
        // different from the scrutinee, to use inside the closure arms.
        let mut capture_candidates: Vec<(String, PrimitiveType)> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Primitive(p @ (PrimitiveType::I64 | PrimitiveType::I32)) = ty {
                capture_candidates.push((name.clone(), *p));
            }
        }
        for param in ctx.params.iter() {
            if let TypeInfo::Primitive(p @ (PrimitiveType::I64 | PrimitiveType::I32)) =
                &param.param_type
            {
                capture_candidates.push((param.name.clone(), *p));
            }
        }
        if capture_candidates.is_empty() {
            return None;
        }

        // Pick the scrutinee
        let scr_idx = self.rng.gen_range(0..scrutinee_candidates.len());
        let scrutinee = scrutinee_candidates[scr_idx].clone();

        // Pick a capture variable (prefer one different from the scrutinee)
        let non_scrutinee_captures: Vec<&(String, PrimitiveType)> = capture_candidates
            .iter()
            .filter(|(name, _)| *name != scrutinee)
            .collect();
        let (capture_var, capture_prim) = if !non_scrutinee_captures.is_empty() {
            let idx = self.rng.gen_range(0..non_scrutinee_captures.len());
            non_scrutinee_captures[idx].clone()
        } else {
            // Fall back to using the same variable (still valid, just less interesting)
            let idx = self.rng.gen_range(0..capture_candidates.len());
            capture_candidates[idx].clone()
        };

        // The closure parameter type and return type match the capture type.
        // We use i64 for the closure param type since all scrutinees are i64;
        // the closure body uses the capture variable which may be i64 or i32.
        // To keep type consistency, we make the closure always i64 -> i64 or
        // i32 -> i32 based on the capture variable type.
        let closure_prim = capture_prim;
        let closure_type_name = match closure_prim {
            PrimitiveType::I64 => "i64",
            PrimitiveType::I32 => "i32",
            _ => "i64",
        };

        // Generate 2-3 literal arms plus a wildcard, each producing a closure
        let arm_count = self.rng.gen_range(2..=3);
        let indent = "    ".repeat(self.indent + 1);
        let close_indent = "    ".repeat(self.indent);

        let mut arms = Vec::new();
        let mut used_values = std::collections::HashSet::new();

        // Closure operations pool: each arm captures the same variable but
        // applies a different operation.
        let operations = [
            ("n + {}", "add"),
            ("n * {}", "mul"),
            ("n - {}", "sub"),
            ("{} - n", "rsub"),
            ("{} + n", "radd"),
        ];

        for _ in 0..arm_count {
            let mut lit_val: i64 = self.rng.gen_range(0..10);
            while used_values.contains(&lit_val) {
                lit_val = self.rng.gen_range(0..10);
            }
            used_values.insert(lit_val);

            // Pick a random operation for this arm
            let op_idx = self.rng.gen_range(0..operations.len());
            let (op_template, _) = operations[op_idx];
            let body = op_template.replace("{}", &capture_var);

            arms.push(format!(
                "{}{} => (n: {}) => {}",
                indent, lit_val, closure_type_name, body
            ));
        }

        // Wildcard arm — always present, with a default operation
        let wildcard_op_idx = self.rng.gen_range(0..operations.len());
        let (wildcard_template, _) = operations[wildcard_op_idx];
        let wildcard_body = wildcard_template.replace("{}", &capture_var);
        arms.push(format!(
            "{}_ => (n: {}) => {}",
            indent, closure_type_name, wildcard_body
        ));

        let fn_name = ctx.new_local_name();
        let closure_type = TypeInfo::Function {
            param_types: vec![TypeInfo::Primitive(closure_prim)],
            return_type: Box::new(TypeInfo::Primitive(closure_prim)),
        };

        let match_stmt = format!(
            "let {} = match {} {{\n{}\n{}}}",
            fn_name,
            scrutinee,
            arms.join("\n"),
            close_indent,
        );

        // Now decide how to use the closure: Pattern A (invoke) or Pattern B (iterator chain)
        let expr_ctx = ctx.to_expr_context();
        let array_vars = expr_ctx.array_vars();

        // Filter to arrays whose element type matches the closure type
        let matching_arrays: Vec<&(String, TypeInfo)> = array_vars
            .iter()
            .filter(|(_, elem_ty)| matches!(elem_ty, TypeInfo::Primitive(p) if *p == closure_prim))
            .collect();

        // 40% chance to use iterator chain if matching arrays are available
        let use_iter = !matching_arrays.is_empty() && self.rng.gen_bool(0.4);

        if use_iter {
            // Pattern B: arr.iter().map(f).collect()
            let arr_idx = self.rng.gen_range(0..matching_arrays.len());
            let (arr_name, _) = matching_arrays[arr_idx];

            let result_name = ctx.new_local_name();
            let result_type = TypeInfo::Array(Box::new(TypeInfo::Primitive(closure_prim)));

            ctx.add_local(fn_name.clone(), closure_type, false);
            ctx.add_local(result_name.clone(), result_type, false);

            // Optionally add a .filter() after the .map() (~30%)
            let chain_suffix = if self.rng.gen_bool(0.3) {
                let pred = self.generate_filter_closure_body_param(closure_prim, "y");
                format!(".filter((y: {}) => {})", closure_type_name, pred)
            } else {
                String::new()
            };

            let iter_stmt = format!(
                "let {} = {}.iter().map({}){}.collect()",
                result_name, arr_name, fn_name, chain_suffix
            );
            Some(format!(
                "{}\n{}{}",
                match_stmt,
                "    ".repeat(self.indent),
                iter_stmt
            ))
        } else {
            // Pattern A: immediate invocation f(arg)
            let result_name = ctx.new_local_name();
            let result_type = TypeInfo::Primitive(closure_prim);

            // Generate a simple argument for the closure call
            let arg = match closure_prim {
                PrimitiveType::I64 => {
                    let n = self.rng.gen_range(1..=20);
                    format!("{}", n)
                }
                PrimitiveType::I32 => {
                    let n = self.rng.gen_range(1..=20);
                    format!("{}_i32", n)
                }
                _ => "0".to_string(),
            };

            ctx.add_local(fn_name.clone(), closure_type, false);
            ctx.add_local(result_name.clone(), result_type, false);

            let call_stmt = format!("let {} = {}({})", result_name, fn_name, arg);
            Some(format!(
                "{}\n{}{}",
                match_stmt,
                "    ".repeat(self.indent),
                call_stmt
            ))
        }
    }

    /// Try to generate a closure that captures a field value from a class/struct
    /// instance in scope.
    ///
    /// Finds a class-typed or struct-typed local variable, extracts a primitive
    /// field value from it, then creates a closure that captures the field value.
    /// The closure is either immediately invoked or passed to an iterator `.map()`
    /// chain on a small literal array.
    ///
    /// This exercises the interaction between:
    /// - Field access on class/struct instances (`instance.field`)
    /// - Closure capture of the extracted field value
    /// - Higher-order usage (direct invocation or `.map()` on array)
    ///
    /// Generated output shapes (Pattern A - direct invocation):
    /// ```vole
    /// let field_val = instance.field1
    /// let closure = (x: i64) -> i64 => x + field_val
    /// let result = closure(5)
    /// ```
    ///
    /// Generated output shapes (Pattern B - iterator chain):
    /// ```vole
    /// let field_val = instance.field1
    /// let result = [1, 2, 3].iter().map((x: i64) -> i64 => x + field_val).collect()
    /// ```
    ///
    /// Returns `None` if no class/struct-typed local with primitive fields is in scope.
    pub(super) fn try_generate_field_closure_let(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Guard: closures that capture variables inside generic class methods hit a
        // compiler bug ("Captured variable not found"). Skip this pattern entirely
        // when we're generating a method body for a generic class.
        if let Some((cls_mod, cls_sym)) = ctx.current_class_sym_id
            && let Some(symbol) = ctx.table.get_symbol(cls_mod, cls_sym)
            && let SymbolKind::Class(info) = &symbol.kind
            && !info.type_params.is_empty()
        {
            return None;
        }

        let _module_id = ctx.module_id?;

        // Collect class/struct-typed locals that have at least one primitive field.
        // For each candidate, store (local_name, field_name, field_prim_type).
        let mut candidates: Vec<(String, String, PrimitiveType)> = Vec::new();

        for (name, ty, _) in &ctx.locals {
            match ty {
                TypeInfo::Class(mod_id, sym_id) => {
                    if let Some(sym) = ctx.table.get_symbol(*mod_id, *sym_id)
                        && let SymbolKind::Class(ref info) = sym.kind
                    {
                        // Only non-generic classes (generic field types are unresolved)
                        if info.type_params.is_empty() {
                            for field in &info.fields {
                                if let TypeInfo::Primitive(p) = &field.field_type {
                                    // Only types the closure body can handle
                                    if matches!(
                                        p,
                                        PrimitiveType::I64
                                            | PrimitiveType::I32
                                            | PrimitiveType::F64
                                            | PrimitiveType::String
                                            | PrimitiveType::Bool
                                    ) {
                                        candidates.push((name.clone(), field.name.clone(), *p));
                                    }
                                }
                            }
                        }
                    }
                }
                TypeInfo::Struct(mod_id, sym_id) => {
                    if let Some(sym) = ctx.table.get_symbol(*mod_id, *sym_id)
                        && let SymbolKind::Struct(ref info) = sym.kind
                    {
                        for field in &info.fields {
                            if let TypeInfo::Primitive(p) = &field.field_type {
                                // Only types the closure body can handle
                                if matches!(
                                    p,
                                    PrimitiveType::I64
                                        | PrimitiveType::I32
                                        | PrimitiveType::F64
                                        | PrimitiveType::String
                                        | PrimitiveType::Bool
                                ) {
                                    candidates.push((name.clone(), field.name.clone(), *p));
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        if candidates.is_empty() {
            return None;
        }

        // Pick a random candidate field
        let idx = self.rng.gen_range(0..candidates.len());
        let (instance_name, field_name, field_prim) = candidates[idx].clone();

        // Step 1: Extract the field value into a local
        let field_local = ctx.new_local_name();
        ctx.add_local(field_local.clone(), TypeInfo::Primitive(field_prim), false);
        let field_stmt = format!("let {} = {}.{}", field_local, instance_name, field_name);

        // Step 2: Determine the closure's numeric type.
        // For numeric fields (i64, i32, f64), the closure operates on that type.
        // For non-numeric fields (string, bool), fall back to i64.
        let (closure_prim, closure_type_name) = match field_prim {
            PrimitiveType::I64 => (PrimitiveType::I64, "i64"),
            PrimitiveType::I32 => (PrimitiveType::I32, "i32"),
            PrimitiveType::F64 => (PrimitiveType::F64, "f64"),
            _ => (PrimitiveType::I64, "i64"),
        };

        // Operations that combine the closure parameter with the captured field value.
        // For numeric types, use arithmetic. For string fields captured as i64 proxy,
        // only use addition (safe default).
        let is_numeric_field = matches!(
            field_prim,
            PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64
        );

        let op = if is_numeric_field {
            // Direct arithmetic with the captured field value
            match self.rng.gen_range(0..4) {
                0 => format!("x + {}", field_local),
                1 => format!("x * {}", field_local),
                2 => format!("x - {}", field_local),
                _ => format!("{} + x", field_local),
            }
        } else if matches!(field_prim, PrimitiveType::String) {
            // String field: closure returns the string length plus x
            // We can't directly use the string in an i64 closure, so
            // use a simple captured literal derived from scope.
            // Actually, let's just produce an i64 closure that ignores
            // the string but still captures it to exercise the capture path.
            format!("x + {}.length()", field_local)
        } else if matches!(field_prim, PrimitiveType::Bool) {
            // Bool field: convert to i64 via when expression
            format!(
                "x + when {{\n{indent}    {} => 1\n{indent}    _ => 0\n{indent}    }}",
                field_local,
                indent = "    ".repeat(self.indent)
            )
        } else {
            // Candidate filtering above ensures only i64/i32/f64/string/bool reach here
            unreachable!(
                "unexpected field type in field-closure-let: {:?}",
                field_prim
            )
        };

        let indent = "    ".repeat(self.indent);

        // Decide usage pattern: Pattern A (direct invocation) or Pattern B (iterator chain)
        let use_iter = self.rng.gen_bool(0.5);

        if use_iter {
            // Pattern B: build a small literal array, map with inline closure
            let arr_size = self.rng.gen_range(2..=4);
            let arr_elems: Vec<String> = (0..arr_size)
                .map(|_| match closure_prim {
                    PrimitiveType::I32 => {
                        let n = self.rng.gen_range(1..=10);
                        format!("{}_i32", n)
                    }
                    PrimitiveType::F64 => {
                        let n: f64 = self.rng.gen_range(1.0..=10.0);
                        format!("{:.1}", n)
                    }
                    _ => {
                        let n = self.rng.gen_range(1..=10);
                        format!("{}", n)
                    }
                })
                .collect();

            let result_name = ctx.new_local_name();
            let result_type = TypeInfo::Array(Box::new(TypeInfo::Primitive(closure_prim)));
            ctx.add_local(result_name.clone(), result_type, false);

            let iter_stmt = format!(
                "let {} = [{}].iter().map((x: {}) -> {} => {}).collect()",
                result_name,
                arr_elems.join(", "),
                closure_type_name,
                closure_type_name,
                op,
            );

            Some(format!("{}\n{}{}", field_stmt, indent, iter_stmt))
        } else {
            // Pattern A: bind closure to a local, then invoke it
            let fn_name = ctx.new_local_name();
            let closure_type = TypeInfo::Function {
                param_types: vec![TypeInfo::Primitive(closure_prim)],
                return_type: Box::new(TypeInfo::Primitive(closure_prim)),
            };

            let closure_stmt = format!(
                "let {} = (x: {}) -> {} => {}",
                fn_name, closure_type_name, closure_type_name, op,
            );

            let result_name = ctx.new_local_name();
            let result_type = TypeInfo::Primitive(closure_prim);

            // Generate a simple argument
            let arg = match closure_prim {
                PrimitiveType::I64 => {
                    let n = self.rng.gen_range(1..=20);
                    format!("{}", n)
                }
                PrimitiveType::I32 => {
                    let n = self.rng.gen_range(1..=20);
                    format!("{}_i32", n)
                }
                PrimitiveType::F64 => {
                    let n: f64 = self.rng.gen_range(1.0..=20.0);
                    format!("{:.1}", n)
                }
                _ => "0".to_string(),
            };

            ctx.add_local(fn_name.clone(), closure_type, false);
            ctx.add_local(result_name.clone(), result_type, false);

            let call_stmt = format!("let {} = {}({})", result_name, fn_name, arg);
            Some(format!(
                "{}\n{}{}\n{}{}",
                field_stmt, indent, closure_stmt, indent, call_stmt
            ))
        }
    }

    /// Try to generate a closure that captures a sentinel union variable.
    ///
    /// Creates a `PrimType | Sentinel` union local, then a closure `(x: i64) -> i64`
    /// that captures the union variable and uses `when { captured is Sentinel => ..., _ => ... }`
    /// inside. The closure is immediately invoked with a literal argument.
    ///
    /// Example:
    /// ```vole
    /// let local0: i64 | Sent1 = Sent1
    /// let local1 = ((x: i64) -> i64 => when { local0 is Sent1 => x + 1, _ => x })(10)
    /// ```
    pub(super) fn try_generate_sentinel_closure_capture(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        let module_id = ctx.module_id?;
        let module = ctx.table.get_module(module_id)?;

        let sentinels: Vec<_> = module.sentinels().collect();
        if sentinels.is_empty() {
            return None;
        }

        let sentinel_idx = self.rng.gen_range(0..sentinels.len());
        let sentinel_name = sentinels[sentinel_idx].name.clone();
        let sentinel_sym_id = sentinels[sentinel_idx].id;

        // Create the union variable: i64 | Sentinel
        let union_var = ctx.new_local_name();
        let assign_sentinel = self.rng.gen_bool(0.5);
        let init_value = if assign_sentinel {
            sentinel_name.clone()
        } else {
            let n = self.rng.gen_range(-100..=100);
            format!("{}_i64", n)
        };
        let union_stmt = format!(
            "let {}: i64 | {} = {}",
            union_var, sentinel_name, init_value
        );
        ctx.add_local(
            union_var.clone(),
            TypeInfo::Union(vec![
                TypeInfo::Primitive(PrimitiveType::I64),
                TypeInfo::Sentinel(module_id, sentinel_sym_id),
            ]),
            false,
        );

        // Create a closure that captures the union variable
        let result_var = ctx.new_local_name();
        let sentinel_val = self.rng.gen_range(1..=100);
        let arg_val = self.rng.gen_range(1..=50);

        let closure_expr = format!(
            "((x: i64) -> i64 => when {{ {} is {} => x + {}_i64, _ => x }})({})",
            union_var, sentinel_name, sentinel_val, arg_val
        );

        let result_stmt = format!("let {} = {}", result_var, closure_expr);
        ctx.add_local(result_var, TypeInfo::Primitive(PrimitiveType::I64), false);

        Some(format!("{}\n{}", union_stmt, result_stmt))
    }

    /// Try to generate a closure that captures a whole struct variable and accesses
    /// multiple fields inside the closure body. This exercises the interaction between
    /// struct value capture in closure environments and field access through captured
    /// aggregate types.
    ///
    /// Pattern A (direct invocation):
    /// ```vole
    /// let result = ((x: i64) -> i64 => x + my_struct.fieldA + my_struct.fieldB)(5)
    /// ```
    ///
    /// Pattern B (iterator chain):
    /// ```vole
    /// let result = [1, 2, 3].iter().map((x: i64) -> i64 => x + my_struct.fieldA).collect()
    /// ```
    pub(super) fn try_generate_closure_struct_capture(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Guard: skip in generic class method contexts (same issue as field_closure_let)
        if let Some((cls_mod, cls_sym)) = ctx.current_class_sym_id
            && let Some(symbol) = ctx.table.get_symbol(cls_mod, cls_sym)
            && let SymbolKind::Class(info) = &symbol.kind
            && !info.type_params.is_empty()
        {
            return None;
        }

        let _module_id = ctx.module_id?;

        // Find struct-typed locals with at least 2 numeric fields (i64 or i32)
        // so we can access multiple fields inside the closure
        let mut candidates: Vec<(String, Vec<(String, PrimitiveType)>)> = Vec::new();

        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Struct(mod_id, sym_id) = ty
                && let Some(sym) = ctx.table.get_symbol(*mod_id, *sym_id)
                && let SymbolKind::Struct(ref info) = sym.kind
            {
                let numeric_fields: Vec<(String, PrimitiveType)> = info
                    .fields
                    .iter()
                    .filter_map(|f| {
                        if let TypeInfo::Primitive(p) = &f.field_type
                            && matches!(p, PrimitiveType::I64 | PrimitiveType::I32)
                        {
                            return Some((f.name.clone(), *p));
                        }
                        None
                    })
                    .collect();
                if numeric_fields.len() >= 2 {
                    candidates.push((name.clone(), numeric_fields));
                }
            }
        }

        // Also check params
        for p in ctx.params {
            if let TypeInfo::Struct(mod_id, sym_id) = &p.param_type
                && let Some(sym) = ctx.table.get_symbol(*mod_id, *sym_id)
                && let SymbolKind::Struct(ref info) = sym.kind
            {
                let numeric_fields: Vec<(String, PrimitiveType)> = info
                    .fields
                    .iter()
                    .filter_map(|f| {
                        if let TypeInfo::Primitive(pt) = &f.field_type
                            && matches!(pt, PrimitiveType::I64 | PrimitiveType::I32)
                        {
                            return Some((f.name.clone(), *pt));
                        }
                        None
                    })
                    .collect();
                if numeric_fields.len() >= 2 {
                    candidates.push((p.name.clone(), numeric_fields));
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (struct_name, numeric_fields) = candidates[idx].clone();

        // Pick 2-3 fields to use inside the closure
        let num_fields = std::cmp::min(numeric_fields.len(), self.rng.gen_range(2..=3));
        let mut chosen_fields = numeric_fields;
        // Shuffle and take first num_fields
        for i in (1..chosen_fields.len()).rev() {
            let j = self.rng.gen_range(0..=i);
            chosen_fields.swap(i, j);
        }
        chosen_fields.truncate(num_fields);

        // Check if any chosen field is i32 - if so we need to widen to i64
        let has_i32 = chosen_fields
            .iter()
            .any(|(_, p)| matches!(p, PrimitiveType::I32));

        // Build the closure body expression: x + struct.field1 + struct.field2 [+ 0_i64]
        let mut body_parts: Vec<String> = vec!["x".to_string()];
        for (field_name, _) in &chosen_fields {
            body_parts.push(format!("{}.{}", struct_name, field_name));
        }
        let mut body_expr = body_parts.join(" + ");
        if has_i32 {
            body_expr = format!("{} + 0_i64", body_expr);
        }

        let use_iter = self.rng.gen_bool(0.4);
        if use_iter {
            // Pattern B: iterator chain with closure capturing struct
            let arr_size = self.rng.gen_range(2..=4);
            let arr_elems: Vec<String> = (0..arr_size)
                .map(|_| {
                    let n = self.rng.gen_range(1..=20);
                    format!("{}", n)
                })
                .collect();

            let result_name = ctx.new_local_name();
            ctx.add_local(
                result_name.clone(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                false,
            );

            Some(format!(
                "let {} = [{}].iter().map((x: i64) -> i64 => {}).collect()",
                result_name,
                arr_elems.join(", "),
                body_expr,
            ))
        } else {
            // Pattern A: direct invocation of closure
            let arg_val = self.rng.gen_range(1..=50);
            let result_name = ctx.new_local_name();
            ctx.add_local(
                result_name.clone(),
                TypeInfo::Primitive(PrimitiveType::I64),
                false,
            );

            Some(format!(
                "let {} = ((x: i64) -> i64 => {})({})",
                result_name, body_expr, arg_val,
            ))
        }
    }

    /// Try to generate a nested closure capture pattern where one closure captures
    /// and invokes another closure that's already in scope.
    ///
    /// Pattern:
    /// ```vole
    /// let f = (x: i64) -> i64 => x + 1
    /// let g = (y: i64) -> i64 => f(y) + 2
    /// let result = g(5)
    /// ```
    ///
    /// Returns `None` if no suitable closure-typed local is in scope.
    pub(super) fn try_generate_nested_closure_capture(
        &mut self,
        ctx: &mut StmtContext,
    ) -> Option<String> {
        // Guard: skip in generic class method contexts (capture bug)
        if let Some((cls_mod, cls_sym)) = ctx.current_class_sym_id
            && let Some(symbol) = ctx.table.get_symbol(cls_mod, cls_sym)
            && let SymbolKind::Class(info) = &symbol.kind
            && !info.type_params.is_empty()
        {
            return None;
        }

        // Find closure-typed locals that take one i64 param and return i64
        let mut candidates: Vec<String> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if let TypeInfo::Function {
                param_types,
                return_type,
            } = ty
                && param_types.len() == 1
                && matches!(param_types[0], TypeInfo::Primitive(PrimitiveType::I64))
                && matches!(
                    return_type.as_ref(),
                    TypeInfo::Primitive(PrimitiveType::I64)
                )
            {
                candidates.push(name.clone());
            }
        }

        // Also check params
        for p in ctx.params {
            if let TypeInfo::Function {
                param_types,
                return_type,
            } = &p.param_type
                && param_types.len() == 1
                && matches!(param_types[0], TypeInfo::Primitive(PrimitiveType::I64))
                && matches!(
                    return_type.as_ref(),
                    TypeInfo::Primitive(PrimitiveType::I64)
                )
            {
                candidates.push(p.name.clone());
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let inner_fn = candidates[idx].clone();

        // Create the outer closure that captures the inner closure
        let outer_fn = ctx.new_local_name();
        let offset_val = self.rng.gen_range(1..=20);
        let op = match self.rng.gen_range(0..3) {
            0 => format!("{}(y) + {}", inner_fn, offset_val),
            1 => format!("{}(y) * {}", inner_fn, offset_val),
            _ => format!("{}(y + {})", inner_fn, offset_val),
        };

        let outer_closure = format!("let {} = (y: i64) -> i64 => {}", outer_fn, op);
        ctx.add_local(
            outer_fn.clone(),
            TypeInfo::Function {
                param_types: vec![TypeInfo::Primitive(PrimitiveType::I64)],
                return_type: Box::new(TypeInfo::Primitive(PrimitiveType::I64)),
            },
            false,
        );

        // Invoke the outer closure
        let result_name = ctx.new_local_name();
        let arg_val = self.rng.gen_range(1..=50);
        let call_stmt = format!("let {} = {}({})", result_name, outer_fn, arg_val);
        ctx.add_local(result_name, TypeInfo::Primitive(PrimitiveType::I64), false);

        let indent = "    ".repeat(self.indent);
        Some(format!("{}\n{}{}", outer_closure, indent, call_stmt))
    }
}
