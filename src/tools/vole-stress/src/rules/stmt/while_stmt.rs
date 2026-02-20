//! Rule: while statement.
//!
//! Generates bounded while loops with a counter and a guard variable.
//! The guard increments unconditionally at the top of each iteration
//! and breaks if it exceeds a limit, guaranteeing termination even
//! when `continue` skips the manual counter increment.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct WhileStmt;

impl StmtRule for WhileStmt {
    fn name(&self) -> &'static str {
        "while_stmt"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.05)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.can_recurse()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let counter_name = scope.fresh_name();
        let guard_name = scope.fresh_name();
        let limit = emit.random_in(1, 5) as i64;
        let guard_limit = limit * 10;

        // Add counter and guard to outer scope (they persist after the loop)
        scope.add_local(
            counter_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );
        scope.add_local(
            guard_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );

        // Protect both from compound assignments inside the loop
        scope.protected_vars.push(counter_name.clone());
        scope.protected_vars.push(guard_name.clone());

        // Generate body in a nested scope
        let body = scope.enter_scope(|inner| {
            inner.in_loop = true;
            inner.in_while_loop = true;

            let num_stmts = emit.random_in(1, 3);
            let user_body = emit.block(inner, num_stmts);

            // Build full body: guard increment + break check, user stmts, counter increment
            let inner_indent = emit.indent_str();
            let guard_inc = format!("{}{} = {} + 1", inner_indent, guard_name, guard_name);
            let guard_check = format!(
                "{}if {} > {} {{ break }}",
                inner_indent, guard_name, guard_limit
            );
            let counter_inc = format!("{}{} = {} + 1", inner_indent, counter_name, counter_name);

            format!(
                "{}\n{}\n{}\n{}",
                guard_inc, guard_check, user_body, counter_inc
            )
        });

        let indent = emit.indent_str();

        Some(format!(
            "var {} = 0\n{}var {} = 0\n{}while {} < {} {{\n{}\n{}}}",
            counter_name, indent, guard_name, indent, counter_name, limit, body, indent
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
        assert_eq!(WhileStmt.name(), "while_stmt");
    }

    #[test]
    fn generates_while_statement() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WhileStmt.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("while "), "expected while, got: {text}");
        assert!(text.contains("var"), "expected counter init, got: {text}");
        assert!(text.contains("break"), "expected guard break, got: {text}");
    }

    #[test]
    fn respects_depth_limit() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.depth = scope.max_depth;
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!WhileStmt.precondition(&scope, &params));
    }
}
