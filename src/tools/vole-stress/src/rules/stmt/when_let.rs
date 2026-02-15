//! Rule: when-expression let-binding.
//!
//! Generates a multiline `when` expression used as a let initializer:
//! ```vole
//! let result = when {
//!     <bool_cond> => <expr>
//!     <bool_cond> => <expr>
//!     _ => <expr>
//! }
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct WhenLet;

impl StmtRule for WhenLet {
    fn name(&self) -> &'static str {
        "when_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.08)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let result_type = emit.random_primitive_type();
        let result_name = scope.fresh_name();

        let use_unreachable = emit.gen_bool(0.10);

        // 2 = simple (1 condition + wildcard), 3-4 = multi-arm
        let arm_count = if emit.gen_bool(0.35) {
            emit.random_in(3, 4)
        } else {
            2
        };

        let indent = emit.indented(|e| e.indent_str());
        let mut arms = Vec::new();

        if use_unreachable {
            // First arm uses `true` so the wildcard is provably dead code
            let arm_expr = arm_value(emit, &result_type);
            arms.push(format!("{}true => {}", indent, arm_expr));

            // Additional arms (dead code but syntactically valid)
            for _ in 1..arm_count {
                let cond = emit.literal(&TypeInfo::Primitive(PrimitiveType::Bool));
                let arm_expr = arm_value(emit, &result_type);
                arms.push(format!("{}{} => {}", indent, cond, arm_expr));
            }

            arms.push(format!("{}_ => unreachable", indent));
        } else {
            for _ in 0..arm_count {
                let cond = emit.literal(&TypeInfo::Primitive(PrimitiveType::Bool));
                let arm_expr = arm_value(emit, &result_type);
                arms.push(format!("{}{} => {}", indent, cond, arm_expr));
            }

            let wildcard_expr = arm_value(emit, &result_type);
            arms.push(format!("{}_ => {}", indent, wildcard_expr));
        }

        let close_indent = emit.indent_str();
        scope.add_local(result_name.clone(), result_type, false);

        Some(format!(
            "let {} = when {{\n{}\n{}}}",
            result_name,
            arms.join("\n"),
            close_indent,
        ))
    }
}

/// Generate a when arm value -- 25% chance of nested when, otherwise literal.
fn arm_value(emit: &mut Emit, result_type: &TypeInfo) -> String {
    if emit.gen_bool(0.25) {
        let inner_indent = emit.indented(|e| e.indented(|e2| e2.indent_str()));
        let inner_close = emit.indented(|e| e.indent_str());
        let cond = emit.literal(&TypeInfo::Primitive(PrimitiveType::Bool));
        let true_val = emit.literal(result_type);
        let false_val = emit.literal(result_type);
        format!(
            "when {{\n{}{} => {}\n{}_ => {}\n{}}}",
            inner_indent, cond, true_val, inner_indent, false_val, inner_close
        )
    } else {
        emit.literal(result_type)
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
        assert_eq!(WhenLet.name(), "when_let");
    }

    #[test]
    fn generates_when_expression() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WhenLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("when"), "got: {text}");
        assert!(text.contains("=>"), "got: {text}");
    }
}
