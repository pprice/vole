//! Rule: for loop building string with when body.
//!
//! Generates a for loop over array params that accumulates a string using when.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ForIterWhenStringBody;

impl StmtRule for ForIterWhenStringBody {
    fn name(&self) -> &'static str {
        "for_iter_when_string_body"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let array_params: Vec<String> = scope
            .params
            .iter()
            .filter(|p| {
                matches!(
                    &p.param_type,
                    TypeInfo::Array(inner) if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::I64))
                )
            })
            .map(|p| p.name.clone())
            .collect();

        if array_params.is_empty() {
            return None;
        }

        let arr = &array_params[emit.gen_range(0..array_params.len())];
        let s_name = scope.fresh_name();
        let item_name = scope.fresh_name();
        let indent = emit.indent_str();
        let thresh = emit.gen_i64_range(-5, 10);

        let (s_true, s_false) = match emit.gen_range(0..3) {
            0 => ("+", "-"),
            1 => ("y", "n"),
            _ => ("1", "0"),
        };

        scope.add_local(
            s_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            true,
        );
        scope.protected_vars.push(s_name.clone());

        Some(format!(
            "let mut {} = \"\"\n{}for {} in {} {{\n{}    {} = {} + when {{ {} > {} => \"{}\", _ => \"{}\" }}\n{}}}",
            s_name,
            indent,
            item_name,
            arr,
            indent,
            s_name,
            s_name,
            item_name,
            thresh,
            s_true,
            s_false,
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
        assert_eq!(ForIterWhenStringBody.name(), "for_iter_when_string_body");
    }

    #[test]
    fn generates_for_when() {
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

        let result = ForIterWhenStringBody.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("for"), "got: {text}");
        assert!(text.contains("when"), "got: {text}");
    }
}
