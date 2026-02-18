//! Rule: method call interpolation expression.
//!
//! Generates a string containing a method call interpolation like
//! `"val: {str.to_upper()}"` or `"len: {arr.length()}"`.
//! Result type is `string`.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct MethodInterpolation;

impl ExprRule for MethodInterpolation {
    fn name(&self) -> &'static str {
        "method_interpolation"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.08)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        let has_strings = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::String)))
            .first()
            .is_some();
        let has_arrays = !scope.array_vars().is_empty();
        has_strings || has_arrays
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        if !matches!(expected_type, TypeInfo::Primitive(PrimitiveType::String)) {
            return None;
        }

        let string_vars = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::String)));
        let array_vars = scope.array_vars();

        if string_vars.is_empty() && array_vars.is_empty() {
            return None;
        }

        // Build candidates: (name, is_string)
        let mut candidates: Vec<(String, bool)> = Vec::new();
        for v in &string_vars {
            candidates.push((v.name.clone(), true));
        }
        for (name, _) in &array_vars {
            candidates.push((name.clone(), false));
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, is_string) = &candidates[idx];

        let method_expr = if *is_string {
            match emit.gen_range(0..4_usize) {
                0 => format!("{}.to_upper()", var_name),
                1 => format!("{}.to_lower()", var_name),
                2 => format!("{}.trim()", var_name),
                _ => format!("{}.length()", var_name),
            }
        } else {
            format!("{}.length()", var_name)
        };

        let prefixes = ["len: ", "upper: ", "result: ", "val: ", "got ", ""];
        let prefix = prefixes[emit.gen_range(0..prefixes.len())];
        Some(format!("\"{}{{{}}}\"", prefix, method_expr))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ParamValue, StmtRule};
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
        assert_eq!(MethodInterpolation.name(), "method_interpolation");
    }

    #[test]
    fn generates_interpolation() {
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

        let result = MethodInterpolation.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::String),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains('{'), "expected interpolation, got: {text}");
    }
}
