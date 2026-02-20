//! Rule: simple primitive let-binding (fallback rule).
//!
//! Generates `let localN = <literal>` or `let mut localN = <literal>` with
//! an optional explicit type annotation (~15% chance).
//! This is the simplest statement rule and serves as the catch-all fallback.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct PrimitiveLet;

impl StmtRule for PrimitiveLet {
    fn name(&self) -> &'static str {
        "primitive_let"
    }

    fn params(&self) -> Vec<Param> {
        // Higher probability than most rules -- this is the fallback
        vec![Param::prob("probability", 0.50)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let ty = emit.random_primitive_type();
        let is_mutable = emit.gen_bool(0.3);

        let value = emit.literal(&ty);
        let name = scope.fresh_name();

        scope.add_local(name.clone(), ty.clone(), is_mutable);

        let mutability = if is_mutable { "var" } else { "let" };

        // ~15% chance: add explicit type annotation
        if emit.gen_bool(0.15) {
            let type_str = ty.to_vole_syntax(scope.table);
            Some(format!("{} {}: {} = {}", mutability, name, type_str, value))
        } else {
            Some(format!("{} {} = {}", mutability, name, value))
        }
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
        assert_eq!(PrimitiveLet.name(), "primitive_let");
    }

    #[test]
    fn generates_primitive_let() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = PrimitiveLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let"), "got: {text}");
    }

    #[test]
    fn adds_local_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        assert!(scope.locals.is_empty());

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        PrimitiveLet.generate(&mut scope, &mut emit, &rule_params);
        assert_eq!(scope.locals.len(), 1);
    }
}
