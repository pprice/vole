//! Rule: for-loop indexed by array length.
//!
//! Generates `let mut acc = 0; for i in 0..arr.length() { acc = acc + arr[i] }`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ForLengthIndexed;

impl StmtRule for ForLengthIndexed {
    fn name(&self) -> &'static str {
        "for_length_indexed"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let param_arrays: Vec<(String, PrimitiveType)> = scope
            .params
            .iter()
            .filter_map(|p| {
                if let TypeInfo::Array(elem) = &p.param_type {
                    if let TypeInfo::Primitive(prim) = elem.as_ref() {
                        if matches!(prim, PrimitiveType::I64 | PrimitiveType::I32) {
                            return Some((p.name.clone(), *prim));
                        }
                    }
                }
                None
            })
            .collect();

        if param_arrays.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..param_arrays.len());
        let (arr_name, _prim) = &param_arrays[idx];
        let acc_name = scope.fresh_name();
        let iter_name = scope.fresh_name();
        let indent = emit.indent_str();

        scope.protected_vars.push(acc_name.clone());
        scope.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );

        let body_op = match emit.gen_range(0..3) {
            0 => format!("{} = {} + {}[{}]", acc_name, acc_name, arr_name, iter_name),
            1 => format!(
                "{} = {} + when {{ {}[{}] > 0 => 1, _ => 0 }}",
                acc_name, acc_name, arr_name, iter_name
            ),
            _ => format!(
                "if {}[{}] > 0 {{ {} = {} + 1 }}",
                arr_name, iter_name, acc_name, acc_name
            ),
        };

        Some(format!(
            "let mut {} = 0\n{indent}for {} in 0..{}.length() {{\n{indent}    {}\n{indent}}}",
            acc_name,
            iter_name,
            arr_name,
            body_op,
            indent = indent,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{ParamInfo, SymbolTable};
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
        assert_eq!(ForLengthIndexed.name(), "for_length_indexed");
    }

    #[test]
    fn generates_indexed_loop() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "arr".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ForLengthIndexed.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("for"), "got: {text}");
        assert!(text.contains(".length()"), "got: {text}");
    }
}
