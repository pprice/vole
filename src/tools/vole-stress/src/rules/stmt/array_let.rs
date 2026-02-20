//! Rule: let-bind a small array literal.
//!
//! Produces `let localN = [elem1, elem2, elem3]` with 2-4 elements of a
//! random primitive type. Optionally `let mut` for enabling push/index
//! assignment operations. ~12% chance of large arrays (6-10 elements).

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ArrayLet;

impl StmtRule for ArrayLet {
    fn name(&self) -> &'static str {
        "array_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.12)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let elem_prim = emit.random_array_element_type();
        let elem_ty = TypeInfo::Primitive(elem_prim);
        let is_mutable = emit.gen_bool(0.3);

        // Array size distribution: ~12% large 6-10, ~88% standard 2-4
        let elem_count = if emit.gen_bool(0.12) {
            emit.random_in(6, 10)
        } else {
            emit.random_in(2, 4)
        };

        let elements: Vec<String> = (0..elem_count)
            .map(|_| emit.literal(&TypeInfo::Primitive(elem_prim)))
            .collect();

        let name = scope.fresh_name();
        let array_ty = TypeInfo::Array(Box::new(elem_ty));
        scope.add_local(name.clone(), array_ty, is_mutable);

        let mutability = if is_mutable { "var" } else { "let" };
        Some(format!(
            "{} {} = [{}]",
            mutability,
            name,
            elements.join(", ")
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
        assert_eq!(ArrayLet.name(), "array_let");
    }

    #[test]
    fn generates_array_let() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ArrayLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let"), "got: {text}");
        assert!(text.contains('['), "got: {text}");
    }
}
