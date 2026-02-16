//! Rule: if statement.
//!
//! Generates if/else-if/else statements with recursive block bodies.
//! Optionally generates else-if chains (1-3 arms) with a trailing else.
//! Requires sufficient depth budget for recursive generation.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct IfStmt;

impl StmtRule for IfStmt {
    fn name(&self) -> &'static str {
        "if_stmt"
    }

    fn params(&self) -> Vec<Param> {
        vec![
            Param::prob("probability", 0.08),
            Param::prob("else_if_probability", 0.25),
        ]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.can_recurse()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, params: &Params) -> Option<String> {
        let else_if_prob = params.prob("else_if_probability");
        let bool_ty = TypeInfo::Primitive(PrimitiveType::Bool);

        // Generate condition
        let cond = emit.sub_expr(&bool_ty, scope);

        // Generate then branch
        let then_body = scope.enter_scope(|inner| {
            let num_stmts = emit.random_in(1, 3);
            emit.block(inner, num_stmts)
        });

        let indent = emit.indent_str();

        // Decide whether to generate else-if chains
        let use_else_if = else_if_prob > 0.0 && emit.gen_bool(else_if_prob);

        let else_part = if use_else_if {
            let arm_count = emit.random_in(1, 3);
            let mut else_if_parts = Vec::new();

            for _ in 0..arm_count {
                let else_if_cond = emit.sub_expr(&bool_ty, scope);
                let else_if_body = scope.enter_scope(|inner| {
                    let n = emit.random_in(1, 2);
                    emit.block(inner, n)
                });
                else_if_parts.push(format!(
                    " else if {} {{\n{}\n{}}}",
                    else_if_cond, else_if_body, indent
                ));
            }

            // Always end with a plain else block
            let else_body = scope.enter_scope(|inner| {
                let n = emit.random_in(1, 2);
                emit.block(inner, n)
            });
            format!(
                "{} else {{\n{}\n{}}}",
                else_if_parts.join(""),
                else_body,
                indent
            )
        } else if emit.gen_bool(0.5) {
            // 50% chance of simple else
            let else_body = scope.enter_scope(|inner| {
                let n = emit.random_in(1, 2);
                emit.block(inner, n)
            });
            format!(" else {{\n{}\n{}}}", else_body, indent)
        } else {
            String::new()
        };

        Some(format!(
            "if {} {{\n{}\n{}}}{}",
            cond, then_body, indent, else_part
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(IfStmt.name(), "if_stmt");
    }

    #[test]
    fn generates_if_statement() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([
            ("probability", ParamValue::Probability(1.0)),
            ("else_if_probability", ParamValue::Probability(0.0)),
        ]);

        let result = IfStmt.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("if "), "expected if, got: {text}");
        assert!(text.contains('{'), "expected block, got: {text}");
    }

    #[test]
    fn respects_depth_limit() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.depth = scope.max_depth; // at max depth
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!IfStmt.precondition(&scope, &params));
    }
}
