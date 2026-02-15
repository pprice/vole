//! Rule: call a function-typed parameter.
//!
//! Finds function-typed parameters in scope and generates a call with
//! literal arguments. If the return type is non-void, binds the result
//! to a new local.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::TypeInfo;

pub struct FnParamCall;

impl StmtRule for FnParamCall {
    fn name(&self) -> &'static str {
        "fn_param_call"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.20)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let fn_params: Vec<(String, Vec<TypeInfo>, TypeInfo)> = scope
            .params
            .iter()
            .filter_map(|p| {
                if let TypeInfo::Function {
                    param_types,
                    return_type,
                } = &p.param_type
                {
                    Some((
                        p.name.clone(),
                        param_types.clone(),
                        return_type.as_ref().clone(),
                    ))
                } else {
                    None
                }
            })
            .collect();

        if fn_params.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..fn_params.len());
        let (fn_name, param_types, return_type) = fn_params[idx].clone();

        let args: Vec<String> = param_types.iter().map(|ty| emit.literal(ty)).collect();
        let call = format!("{}({})", fn_name, args.join(", "));

        if matches!(return_type, TypeInfo::Void) {
            Some(call)
        } else {
            let name = scope.fresh_name();
            scope.add_local(name.clone(), return_type, false);
            Some(format!("let {} = {}", name, call))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{ParamInfo, PrimitiveType, SymbolTable};
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(FnParamCall.name(), "fn_param_call");
    }

    #[test]
    fn generates_fn_param_call() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "transform".to_string(),
            param_type: TypeInfo::Function {
                param_types: vec![TypeInfo::Primitive(PrimitiveType::I64)],
                return_type: Box::new(TypeInfo::Primitive(PrimitiveType::I64)),
            },
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = FnParamCall.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("transform("), "got: {text}");
    }

    #[test]
    fn returns_none_without_fn_params() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "x".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::I64),
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            FnParamCall
                .generate(&mut scope, &mut emit, &rule_params)
                .is_none()
        );
    }
}
