//! Rule: early return inside a guarded `if` block.
//!
//! Generates `if <cond> { return <expr> }` in functions with non-void return
//! types. The condition and return value are type-appropriate literals.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct EarlyReturn;

impl StmtRule for EarlyReturn {
    fn name(&self) -> &'static str {
        "early_return"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.05)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        matches!(&scope.return_type, Some(ty) if !matches!(ty, TypeInfo::Void))
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let return_type = scope.return_type.as_ref()?;
        if matches!(return_type, TypeInfo::Void) {
            return None;
        }

        let cond = emit.literal(&TypeInfo::Primitive(PrimitiveType::Bool));
        let return_expr = emit.literal(return_type);

        let indent = emit.indent_str();
        let inner_indent = format!("{}    ", indent);

        Some(format!(
            "if {} {{\n{}return {}\n{}}}",
            cond, inner_indent, return_expr, indent,
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
        assert_eq!(EarlyReturn.name(), "early_return");
    }

    #[test]
    fn generates_early_return() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.return_type = Some(TypeInfo::Primitive(PrimitiveType::I64));

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = EarlyReturn.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("return"), "got: {text}");
        assert!(text.starts_with("if "), "got: {text}");
    }

    #[test]
    fn returns_none_for_void() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.return_type = Some(TypeInfo::Void);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            EarlyReturn
                .generate(&mut scope, &mut emit, &rule_params)
                .is_none()
        );
    }

    #[test]
    fn returns_none_without_return_type() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            EarlyReturn
                .generate(&mut scope, &mut emit, &rule_params)
                .is_none()
        );
    }
}
