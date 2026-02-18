//! Rule: for-loop with when-based accumulation on array params.
//!
//! Generates `let mut acc = 0; for item in arr { acc = acc + when { item > N => item, _ => M } }`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ForWhenAccumulate;

impl StmtRule for ForWhenAccumulate {
    fn name(&self) -> &'static str {
        "for_when_accumulate"
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
        let acc_name = scope.fresh_name();
        let item_name = scope.fresh_name();
        let indent = emit.indent_str();

        let thresh = emit.gen_i64_range(-5, 10);
        let op = [">", ">=", "<"][emit.gen_range(0..3)];
        let fallback = emit.gen_i64_range(0, 5);

        scope.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );
        scope.protected_vars.push(acc_name.clone());

        Some(format!(
            "let mut {} = 0\n{}for {} in {} {{\n{}    {} = {} + when {{ {} {} {} => {}, _ => {} }}\n{}}}",
            acc_name,
            indent,
            item_name,
            arr,
            indent,
            acc_name,
            acc_name,
            item_name,
            op,
            thresh,
            item_name,
            fallback,
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
        assert_eq!(ForWhenAccumulate.name(), "for_when_accumulate");
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

        let result = ForWhenAccumulate.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("for"), "got: {text}");
        assert!(text.contains("when"), "got: {text}");
    }
}
