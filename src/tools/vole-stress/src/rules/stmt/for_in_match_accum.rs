//! Rule: for-in loop with match on iteration variable.
//!
//! Generates a for-in loop over an i64 array (with optional filter) where each
//! element is matched and accumulated.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ForInMatchAccum;

impl StmtRule for ForInMatchAccum {
    fn name(&self) -> &'static str {
        "for_in_match_accum"
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
        let iter_name = scope.fresh_name();
        let acc_name = scope.fresh_name();

        // Optional filter prefix: ~40% chance
        let chain = if emit.gen_bool(0.40) {
            let n = emit.gen_i64_range(-5, 2);
            format!(".filter((x) => x > {})", n)
        } else {
            String::new()
        };

        // Generate match arms: 2-3 literal arms + wildcard
        let num_arms = emit.random_in(2, 3);
        let mut arm_values: Vec<i64> = Vec::new();
        for _ in 0..num_arms {
            let v = emit.gen_i64_range(0, 10);
            if !arm_values.contains(&v) {
                arm_values.push(v);
            }
        }

        let mut arms = Vec::new();
        for v in &arm_values {
            let result = emit.gen_i64_range(0, 20);
            arms.push(format!("{} => {}", v, result));
        }
        arms.push(format!("_ => {}", iter_name));
        let arms_str = arms.join(", ");

        scope.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );
        scope.protected_vars.push(acc_name.clone());

        let match_name = scope.fresh_name();
        let indent = emit.indent_str();
        let inner = format!("{}    ", indent);
        let inner2 = format!("{}        ", indent);

        let result = format!(
            "let mut {} = 0\n\
             {}for {} in {}.iter(){} {{\n\
             {}let {} = match {} {{\n\
             {}{}\n\
             {}}}\n\
             {}{} = {} + {}\n\
             {}}}",
            acc_name,
            indent,
            iter_name,
            arr_name,
            chain,
            inner,
            match_name,
            iter_name,
            inner2,
            arms_str,
            inner,
            inner,
            acc_name,
            acc_name,
            match_name,
            indent,
        );

        Some(result)
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
        assert_eq!(ForInMatchAccum.name(), "for_in_match_accum");
    }

    #[test]
    fn generates_for_match() {
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

        let result = ForInMatchAccum.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("for"), "got: {text}");
        assert!(text.contains("match"), "got: {text}");
    }
}
