//! Rule: break or continue statement inside a loop.
//!
//! Generates `if <cond> { break }` or `if <cond> { continue }` when inside
//! a loop body. Occasionally generates an early return instead (~20% when
//! the function has a non-void return type).

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct BreakContinue;

impl StmtRule for BreakContinue {
    fn name(&self) -> &'static str {
        "break_continue"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.15)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.in_loop
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        if !scope.in_loop {
            return None;
        }

        let indent = emit.indent_str();
        let inner_indent = format!("{}    ", indent);

        // ~20% chance: early return from inside a loop
        if let Some(ref ret_ty) = scope.return_type {
            if !matches!(ret_ty, TypeInfo::Void) && emit.gen_bool(0.20) {
                let cond = emit.literal(&TypeInfo::Primitive(PrimitiveType::Bool));
                let return_expr = emit.literal(ret_ty);

                return Some(format!(
                    "if {} {{\n{}return {}\n{}}}",
                    cond, inner_indent, return_expr, indent,
                ));
            }
        }

        let keyword = if emit.gen_bool(0.5) {
            "break"
        } else {
            "continue"
        };

        let cond = emit.literal(&TypeInfo::Primitive(PrimitiveType::Bool));

        Some(format!(
            "if {} {{\n{}{}\n{}}}",
            cond, inner_indent, keyword, indent,
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
        assert_eq!(BreakContinue.name(), "break_continue");
    }

    #[test]
    fn generates_break_or_continue() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.in_loop = true;

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = BreakContinue.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("if "), "got: {text}");
        assert!(
            text.contains("break") || text.contains("continue") || text.contains("return"),
            "got: {text}"
        );
    }

    #[test]
    fn returns_none_outside_loop() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.in_loop = false;

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            BreakContinue
                .generate(&mut scope, &mut emit, &rule_params)
                .is_none()
        );
    }
}
