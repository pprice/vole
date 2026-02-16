//! Rule: boolean from length comparisons.
//!
//! Generates `.length()` comparisons on arrays/strings:
//! ```vole
//! let b = arr.length() > 3
//! let b = str.length() > 0 && arr.length() < 10
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct LengthComparison;

impl StmtRule for LengthComparison {
    fn name(&self) -> &'static str {
        "length_comparison"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let sources = collect_length_sources(scope);
        if sources.is_empty() {
            return None;
        }

        let result_name = scope.fresh_name();
        let var1 = &sources[emit.gen_range(0..sources.len())];
        let thresh1 = emit.random_in(0, 10);
        let op = match emit.gen_range(0..4) {
            0 => ">",
            1 => ">=",
            2 => "<",
            _ => "==",
        };

        let expr = if sources.len() >= 2 && emit.gen_bool(0.4) {
            let var2 = &sources[emit.gen_range(0..sources.len())];
            let thresh2 = emit.random_in(0, 10);
            let op2 = match emit.gen_range(0..3) {
                0 => ">",
                1 => ">=",
                _ => "<",
            };
            let logic = if emit.gen_bool(0.5) { "&&" } else { "||" };
            format!(
                "{}.length() {} {} {} {}.length() {} {}",
                var1, op, thresh1, logic, var2, op2, thresh2
            )
        } else {
            format!("{}.length() {} {}", var1, op, thresh1)
        };

        scope.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );
        Some(format!("let {} = {}", result_name, expr))
    }
}

fn collect_length_sources(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if matches!(
            ty,
            TypeInfo::Array(_) | TypeInfo::Primitive(PrimitiveType::String)
        ) {
            out.push(name.clone());
        }
    }
    for param in scope.params {
        if matches!(
            param.param_type,
            TypeInfo::Array(_) | TypeInfo::Primitive(PrimitiveType::String)
        ) {
            out.push(param.name.clone());
        }
    }
    out
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(LengthComparison.name(), "length_comparison");
    }

    #[test]
    fn returns_none_without_length_sources() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            LengthComparison
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_with_string_var() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "s".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = LengthComparison.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".length()"), "got: {text}");
    }

    #[test]
    fn generates_with_array_param() {
        let table = SymbolTable::new();
        let fn_params = [ParamInfo {
            name: "arr".into(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        }];
        let mut scope = Scope::new(&fn_params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = LengthComparison.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("arr.length()"), "got: {text}");
    }
}
