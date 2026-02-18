//! Rule: tuple let-binding with destructuring.
//!
//! Produces a two-statement sequence:
//! ```vole
//! let tN: [i64, string] = [42_i64, "hello"]
//! let [a, b] = tN
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::TypeInfo;

pub struct TupleLet;

impl StmtRule for TupleLet {
    fn name(&self) -> &'static str {
        "tuple_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.05)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let tuple_ty = emit.random_tuple_type();
        let elem_types = match &tuple_ty {
            TypeInfo::Tuple(elems) => elems.clone(),
            _ => unreachable!(),
        };

        // Generate the tuple literal expression
        let value = emit.literal(&tuple_ty);

        let tuple_name = scope.fresh_name();
        let type_annotation = tuple_ty.to_vole_syntax(scope.table);

        // Add the tuple variable itself to scope
        scope.add_local(tuple_name.clone(), tuple_ty, false);

        // Generate destructuring names for each element
        let destruct_names: Vec<String> = elem_types.iter().map(|_| scope.fresh_name()).collect();

        // Add destructured locals to scope
        for (name, ty) in destruct_names.iter().zip(elem_types.iter()) {
            scope.add_local(name.clone(), ty.clone(), false);
        }

        let pattern = format!("[{}]", destruct_names.join(", "));
        let indent = emit.indent_str();
        Some(format!(
            "let {}: {} = {}\n{}let {} = {}",
            tuple_name, type_annotation, value, indent, pattern, tuple_name,
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
        assert_eq!(TupleLet.name(), "tuple_let");
    }

    #[test]
    fn generates_tuple_let() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = TupleLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("let"), "got: {text}");
    }
}
