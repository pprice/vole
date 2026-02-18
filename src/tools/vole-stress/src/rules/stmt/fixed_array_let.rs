//! Rule: fixed-size array let-binding with destructuring.
//!
//! Produces a two-statement sequence:
//! ```vole
//! let arrN: [i64; 3] = [42_i64; 3]
//! let [a, b, c] = arrN
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::TypeInfo;

pub struct FixedArrayLet;

impl StmtRule for FixedArrayLet {
    fn name(&self) -> &'static str {
        "fixed_array_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.05)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let fixed_array_ty = emit.random_fixed_array_type();
        let (elem_ty, size) = match &fixed_array_ty {
            TypeInfo::FixedArray(elem, size) => (*elem.clone(), *size),
            _ => unreachable!(),
        };

        // Generate the repeat literal expression
        let value = emit.literal(&fixed_array_ty);

        let arr_name = scope.fresh_name();
        let type_annotation = fixed_array_ty.to_vole_syntax(scope.table);

        // Generate destructuring names for each element
        let destruct_names: Vec<String> = (0..size).map(|_| scope.fresh_name()).collect();

        // Add destructured locals to scope with the element type
        for name in &destruct_names {
            scope.add_local(name.clone(), elem_ty.clone(), false);
        }

        let pattern = format!("[{}]", destruct_names.join(", "));
        let indent = emit.indent_str();
        Some(format!(
            "let {}: {} = {}\n{}let {} = {}",
            arr_name, type_annotation, value, indent, pattern, arr_name,
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
        assert_eq!(FixedArrayLet.name(), "fixed_array_let");
    }

    #[test]
    fn generates_fixed_array_let() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = FixedArrayLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("let"), "got: {text}");
        assert!(
            text.contains(';'),
            "expected fixed array syntax, got: {text}"
        );
    }
}
