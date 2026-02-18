//! Rule: nested for-loop statement.
//!
//! Generates two nested for-loops where the inner loop uses `break`
//! or `continue`. Exercises complex control flow with multiple loop
//! scopes, ensuring that break/continue target the correct (inner) loop.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct NestedForLoop;

impl StmtRule for NestedForLoop {
    fn name(&self) -> &'static str {
        "nested_for_loop"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Need depth budget for two levels of nesting
        scope.depth + 2 <= scope.max_depth
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let outer_iter = scope.fresh_name();
        let inner_iter = scope.fresh_name();

        // Generate small ranges
        let outer_end = emit.random_in(2, 4);
        let inner_end = emit.random_in(3, 6);

        let outer_inclusive = emit.gen_bool(0.3);
        let inner_inclusive = emit.gen_bool(0.3);

        let outer_range = if outer_inclusive {
            format!("0..={}", outer_end)
        } else {
            format!("0..{}", outer_end)
        };
        let inner_range = if inner_inclusive {
            format!("0..={}", inner_end)
        } else {
            format!("0..{}", inner_end)
        };

        // Build the inner loop with break/continue
        let keyword = if emit.gen_bool(0.5) {
            "break"
        } else {
            "continue"
        };

        let bool_ty = TypeInfo::Primitive(PrimitiveType::Bool);

        // Generate inner loop body in nested scopes
        let outer_body = scope.enter_scope(|outer_inner| {
            outer_inner.in_loop = true;
            outer_inner.in_while_loop = false;
            outer_inner.add_local(
                outer_iter.clone(),
                TypeInfo::Primitive(PrimitiveType::I64),
                false,
            );

            // Build inner loop
            let inner_loop = outer_inner.enter_scope(|inner_inner| {
                inner_inner.add_local(
                    inner_iter.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );

                // Generate condition for break/continue
                let cond = emit.sub_expr(&bool_ty, inner_inner);

                // Build inner body: conditional break/continue + 1-2 statements
                let inner_body = emit.indented(|emit| {
                    emit.indented(|emit| {
                        let indent = emit.indent_str();
                        let if_indent = format!("{}    ", indent);
                        let mut parts = Vec::new();

                        // Conditional break/continue
                        parts.push(format!(
                            "{}if {} {{\n{}{}\n{}}}",
                            indent, cond, if_indent, keyword, indent
                        ));

                        // 1-2 extra statements
                        let extra = emit.random_in(1, 2);
                        for _ in 0..extra {
                            let stmt = emit.sub_stmt(inner_inner);
                            if !stmt.is_empty() {
                                parts.push(format!("{}{}", indent, stmt));
                            }
                        }

                        parts.join("\n")
                    })
                });

                let indent = emit.indent_str();
                format!(
                    "for {} in {} {{\n{}\n{}}}",
                    inner_iter, inner_range, inner_body, indent
                )
            });

            // Optionally add statements before/after inner loop
            let indent = emit.indent_str();
            let inner_indent = format!("{}    ", indent);

            let mut outer_parts = Vec::new();
            if emit.gen_bool(0.3) {
                let stmt = emit.sub_stmt(outer_inner);
                if !stmt.is_empty() {
                    outer_parts.push(format!("{}{}", inner_indent, stmt));
                }
            }
            outer_parts.push(format!("{}{}", inner_indent, inner_loop));
            if emit.gen_bool(0.3) {
                let stmt = emit.sub_stmt(outer_inner);
                if !stmt.is_empty() {
                    outer_parts.push(format!("{}{}", inner_indent, stmt));
                }
            }

            outer_parts.join("\n")
        });

        let indent = emit.indent_str();
        Some(format!(
            "for {} in {} {{\n{}\n{}}}",
            outer_iter, outer_range, outer_body, indent
        ))
    }
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
        assert_eq!(NestedForLoop.name(), "nested_for_loop");
    }

    #[test]
    fn generates_nested_loops() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = NestedForLoop.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        // Should have two "for" keywords (outer and inner)
        let for_count = text.matches("for ").count();
        assert!(
            for_count >= 2,
            "expected at least 2 for loops, got {for_count} in: {text}"
        );
        // Should have break or continue
        assert!(
            text.contains("break") || text.contains("continue"),
            "expected break/continue, got: {text}"
        );
    }

    #[test]
    fn respects_depth_limit() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.depth = scope.max_depth - 1; // only 1 level left, need 2
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!NestedForLoop.precondition(&scope, &params));
    }
}
