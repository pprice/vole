//! Rule: large tuple let-binding with destructuring.
//!
//! Generates a two-statement sequence with 5-8 element tuples of mixed types:
//! ```vole
//! let tN: [i64, string, bool, i64, string, i64, bool, string] = [42, "hi", true, 7, "bye", 3, false, "end"]
//! let [a, b, c, d, e, f, g, h] = tN
//! ```
//!
//! Stresses tuple memory layout, destructuring codegen, and RC handling for
//! string elements in large tuples.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct LargeTupleLet;

/// Short string literals used for string elements.
const STRING_POOL: &[&str] = &["hi", "bye", "ok", "yes", "no", "abc", "xyz"];

impl StmtRule for LargeTupleLet {
    fn name(&self) -> &'static str {
        "large_tuple_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        if !scope.can_recurse() {
            return None;
        }

        // Choose tuple size: 5 to 8 elements
        let elem_count = emit.gen_range(0..4) + 5; // 5, 6, 7, or 8

        // For each element, pick a random type and generate a literal
        let mut elem_types: Vec<TypeInfo> = Vec::with_capacity(elem_count);
        let mut elem_values: Vec<String> = Vec::with_capacity(elem_count);

        for _ in 0..elem_count {
            let type_choice = emit.gen_range(0..3);
            match type_choice {
                0 => {
                    // i64
                    elem_types.push(TypeInfo::Primitive(PrimitiveType::I64));
                    let val = emit.gen_range(0..21);
                    elem_values.push(format!("{}", val));
                }
                1 => {
                    // string
                    elem_types.push(TypeInfo::Primitive(PrimitiveType::String));
                    let idx = emit.gen_range(0..STRING_POOL.len());
                    elem_values.push(format!("\"{}\"", STRING_POOL[idx]));
                }
                _ => {
                    // bool
                    elem_types.push(TypeInfo::Primitive(PrimitiveType::Bool));
                    let val = emit.gen_bool(0.5);
                    elem_values.push(if val { "true" } else { "false" }.to_string());
                }
            }
        }

        let tuple_ty = TypeInfo::Tuple(elem_types.clone());
        let type_annotation = tuple_ty.to_vole_syntax(scope.table);

        let tuple_name = scope.fresh_name();
        scope.add_local(tuple_name.clone(), tuple_ty, false);

        // Generate destructuring names for each element
        let destruct_names: Vec<String> = (0..elem_count).map(|_| scope.fresh_name()).collect();

        // Add destructured locals to scope
        for (name, ty) in destruct_names.iter().zip(elem_types.iter()) {
            scope.add_local(name.clone(), ty.clone(), false);
        }

        let values_str = elem_values.join(", ");
        let pattern = format!("[{}]", destruct_names.join(", "));
        let indent = emit.indent_str();

        Some(format!(
            "let {}: {} = [{}]\n{}let {} = {}",
            tuple_name, type_annotation, values_str, indent, pattern, tuple_name,
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
        assert_eq!(LargeTupleLet.name(), "large_tuple_let");
    }

    #[test]
    fn generates_large_tuple() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = LargeTupleLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();

        // Must contain a type annotation with at least one type
        assert!(
            text.contains("i64") || text.contains("string") || text.contains("bool"),
            "expected type annotation, got: {text}"
        );
        // Must contain destructuring
        assert!(
            text.contains("let ["),
            "expected destructuring, got: {text}"
        );
    }

    #[test]
    fn tuple_has_5_to_8_elements() {
        for seed in 0..50u64 {
            let table = SymbolTable::new();
            let mut scope = Scope::new(&[], &table);

            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            let result = LargeTupleLet.generate(&mut scope, &mut emit, &rule_params);
            let text = result.unwrap();

            // Extract the type annotation portion: between the first `: [` and `] =`
            let type_start = text.find(": [").expect("no type annotation start");
            let type_end = text.find("] =").expect("no type annotation end");
            let type_str = &text[type_start + 2..type_end + 1]; // includes brackets

            // Count commas in the type annotation to determine element count
            let commas = type_str.chars().filter(|&c| c == ',').count();
            let elem_count = commas + 1;

            assert!(
                (5..=8).contains(&elem_count),
                "seed {seed}: expected 5-8 elements, got {elem_count} in type: {type_str}"
            );
        }
    }

    #[test]
    fn generates_multiple_seeds_without_panic() {
        for seed in 0..50u64 {
            let table = SymbolTable::new();
            let mut scope = Scope::new(&[], &table);

            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            let result = LargeTupleLet.generate(&mut scope, &mut emit, &rule_params);
            assert!(result.is_some(), "seed {seed} returned None");
        }
    }
}
