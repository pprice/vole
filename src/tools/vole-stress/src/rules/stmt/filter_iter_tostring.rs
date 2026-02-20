//! Rule: filter-collect then iterate with to_string.
//!
//! Generates `let filtered = arr.iter().filter((x) => x > N).collect(); let mut s = ""; for x in filtered.iter() { s = s + x.to_string() }`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct FilterIterTostring;

impl StmtRule for FilterIterTostring {
    fn name(&self) -> &'static str {
        "filter_iter_tostring"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_arrays: Vec<String> = scope
            .params
            .iter()
            .filter_map(|p| match &p.param_type {
                TypeInfo::Array(inner)
                    if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::I64)) =>
                {
                    Some(p.name.clone())
                }
                _ => None,
            })
            .collect();

        if i64_arrays.is_empty() {
            return None;
        }

        let arr_name = &i64_arrays[emit.gen_range(0..i64_arrays.len())];
        let filtered_name = scope.fresh_name();
        let acc_name = scope.fresh_name();
        let iter_var = scope.fresh_name();
        let indent = emit.indent_str();

        let threshold = emit.gen_i64_range(0, 5);

        scope.add_local(
            filtered_name.clone(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );
        scope.protected_vars.push(acc_name.clone());
        scope.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            true,
        );

        Some(format!(
            "let {} = {}.iter().filter((x) => x > {}).collect()\n\
             {}let mut {} = \"\"\n\
             {}for {} in {}.iter() {{\n\
             {}    {} = {} + {}.to_string()\n\
             {}}}",
            filtered_name,
            arr_name,
            threshold,
            indent,
            acc_name,
            indent,
            iter_var,
            filtered_name,
            indent,
            acc_name,
            acc_name,
            iter_var,
            indent,
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
        assert_eq!(FilterIterTostring.name(), "filter_iter_tostring");
    }

    #[test]
    fn generates_filter_tostring() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "arr".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            has_default: false,
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = FilterIterTostring.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".filter("), "got: {text}");
        assert!(text.contains(".to_string()"), "got: {text}");
    }
}
