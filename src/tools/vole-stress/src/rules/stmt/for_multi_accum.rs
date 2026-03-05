//! Rule: for-loop with multiple accumulator variables of different types.
//!
//! Generates a for loop iterating over a range with 3-5 accumulators
//! (i64 sum, string builder, bool flag) updated each iteration.
//! This stresses register allocation, RC tracking for string
//! accumulators in loops, and multiple mutable bindings.
//!
//! **Pattern (3 accumulators):**
//! ```vole
//! var local0 = 0
//! var local1 = ""
//! var local2 = false
//! for local3 in 0..5 {
//!     local0 = local0 + local3
//!     local1 = local1 + "{local3},"
//!     if local3 > 2 { local2 = true }
//! }
//! ```
//!
//! **Pattern (5 accumulators):**
//! ```vole
//! var local0 = 0
//! var local1 = ""
//! var local2 = false
//! var local3 = 0
//! var local4 = ""
//! for local5 in 0..6 {
//!     local0 = local0 + local5
//!     local1 = local1 + "{local5},"
//!     if local5 > 3 { local2 = true }
//!     local3 = local3 + 1
//!     local4 = when { local5 > 2 => local4 + "big", _ => local4 + "sm" }
//! }
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ForMultiAccum;

impl StmtRule for ForMultiAccum {
    fn name(&self) -> &'static str {
        "for_multi_accum"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Pick 3-5 accumulators
        let num_accums = emit.random_in(3, 5) as usize;
        let range_end = emit.random_in(3, 8);
        let threshold = emit.gen_range(1..range_end);

        let indent = emit.indent_str();
        let body_indent = format!("{}    ", indent);

        // Generate accumulator names and types
        // Pattern: [i64_sum, string_builder, bool_flag, i64_count, string_builder2]
        let accum_types: Vec<AccumKind> = (0..num_accums)
            .map(|i| match i % 3 {
                0 => AccumKind::I64Sum,
                1 => AccumKind::StringBuilder,
                _ => AccumKind::BoolFlag,
            })
            .collect();

        let mut accum_names = Vec::with_capacity(num_accums);
        let mut lines = Vec::new();

        // Declare accumulators
        for kind in &accum_types {
            let name = scope.fresh_name();
            scope.protected_vars.push(name.clone());
            match kind {
                AccumKind::I64Sum => {
                    scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), true);
                    lines.push(format!("var {} = 0", name));
                }
                AccumKind::StringBuilder => {
                    scope.add_local(
                        name.clone(),
                        TypeInfo::Primitive(PrimitiveType::String),
                        true,
                    );
                    lines.push(format!("var {} = \"\"", name));
                }
                AccumKind::BoolFlag => {
                    scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::Bool), true);
                    lines.push(format!("var {} = false", name));
                }
            }
            accum_names.push(name);
        }

        let iter_var = scope.fresh_name();

        // Build loop body
        let mut body_lines = Vec::new();
        for (i, kind) in accum_types.iter().enumerate() {
            let name = &accum_names[i];
            match kind {
                AccumKind::I64Sum => {
                    if i == 0 {
                        // First i64: add loop variable
                        body_lines
                            .push(format!("{}{} = {} + {}", body_indent, name, name, iter_var));
                    } else {
                        // Subsequent i64: add constant
                        body_lines.push(format!("{}{} = {} + 1", body_indent, name, name));
                    }
                }
                AccumKind::StringBuilder => {
                    if i == 1 {
                        // First string: interpolate loop var
                        body_lines.push(format!(
                            "{}{} = {} + \"{{{}}},\"",
                            body_indent, name, name, iter_var
                        ));
                    } else {
                        // Subsequent string: when expression
                        body_lines.push(format!(
                            "{}{} = when {{ {} > {} => {} + \"big\", _ => {} + \"sm\" }}",
                            body_indent, name, iter_var, threshold, name, name
                        ));
                    }
                }
                AccumKind::BoolFlag => {
                    body_lines.push(format!(
                        "{}if {} > {} {{ {} = true }}",
                        body_indent, iter_var, threshold, name
                    ));
                }
            }
        }

        // Assemble the for loop
        lines.push(format!("for {} in 0..{} {{", iter_var, range_end));
        for body_line in &body_lines {
            // Strip the indent from body lines since we add indent below
            lines.push(body_line.clone());
        }
        lines.push(format!("{}}}", indent));

        // Join with indent prefix
        let mut result = String::new();
        for (i, line) in lines.iter().enumerate() {
            if i > 0 {
                result.push('\n');
                // Don't add indent to body lines (they already have body_indent)
                // or to the closing brace
                if !line.starts_with(&body_indent)
                    && !line.starts_with(&format!("{}if", body_indent))
                {
                    result.push_str(&indent);
                }
            }
            result.push_str(line);
        }

        Some(result)
    }
}

#[derive(Clone, Copy)]
enum AccumKind {
    I64Sum,
    StringBuilder,
    BoolFlag,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::SymbolTable;
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(
            rng,
            EMPTY_STMT,
            EMPTY_EXPR,
            resolved,
            crate::symbols::SymbolTable::empty_ref(),
        )
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(ForMultiAccum.name(), "for_multi_accum");
    }

    #[test]
    fn generates_loop_with_accumulators() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ForMultiAccum.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains("var"),
            "expected var declarations, got: {text}"
        );
        assert!(text.contains("for"), "expected for loop, got: {text}");
    }

    #[test]
    fn adds_accumulators_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        ForMultiAccum.generate(&mut scope, &mut emit, &params);
        // Should add 3-5 accumulators
        assert!(
            scope.locals.len() >= initial_len + 3,
            "expected at least 3 accumulators added"
        );
    }

    #[test]
    fn has_mixed_types() {
        let table = SymbolTable::new();

        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ForMultiAccum.generate(&mut scope, &mut emit, &params) {
                // All outputs should have at least i64 + string + bool accumulators
                assert!(
                    text.contains("var") && text.contains("for"),
                    "missing structure, got: {text}"
                );
                // Check for i64 sum (= ... + ...)
                assert!(
                    text.contains("+ 1") || text.contains(&format!("+")),
                    "expected i64 accumulation, got: {text}"
                );
            }
        }
    }

    #[test]
    fn protects_accumulator_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        ForMultiAccum.generate(&mut scope, &mut emit, &params);
        assert!(
            scope.protected_vars.len() >= 3,
            "expected at least 3 protected vars"
        );
    }
}
