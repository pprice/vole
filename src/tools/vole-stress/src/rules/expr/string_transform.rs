//! Rule: string transform method expression.
//!
//! Generates string-returning method calls: `.to_upper()`, `.to_lower()`,
//! `.trim()`, `.trim_start()`, `.trim_end()`, `.replace(...)`,
//! `.replace_all(...)`, `.substring(...)`.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct StringTransform;

impl ExprRule for StringTransform {
    fn name(&self) -> &'static str {
        "string_transform"
    }

    fn params(&self) -> Vec<Param> {
        vec![
            Param::prob("probability", 0.12),
            Param::prob("chain_probability", 0.20),
        ]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::String)))
            .first()
            .is_some()
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        if !matches!(expected_type, TypeInfo::Primitive(PrimitiveType::String)) {
            return None;
        }

        let candidates = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::String)));
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let var = &candidates[idx].name;

        let methods = [
            "to_upper",
            "to_lower",
            "trim",
            "trim_start",
            "trim_end",
            "replace",
            "replace_all",
            "substring",
        ];
        let method = methods[emit.gen_range(0..methods.len())];

        let base = match method {
            "replace" | "replace_all" => {
                let pairs = [("str", "val"), ("a", "b"), ("hello", "world"), (" ", "_")];
                let pair_idx = emit.gen_range(0..pairs.len());
                let (old, new) = pairs[pair_idx];
                format!("{}.{}(\"{}\", \"{}\")", var, method, old, new)
            }
            "substring" => {
                let ranges = [(0, 3), (0, 5), (1, 4), (0, 1)];
                let range_idx = emit.gen_range(0..ranges.len());
                let (start, end) = ranges[range_idx];
                format!("{}.substring({}, {})", var, start, end)
            }
            _ => format!("{}.{}()", var, method),
        };

        let chain_prob = params.prob("chain_probability");
        if emit.gen_bool(chain_prob) {
            let chain = random_string_chain(emit);
            Some(format!("{}{}", base, chain))
        } else {
            Some(base)
        }
    }
}

fn random_string_chain(emit: &mut Emit) -> &'static str {
    let methods = [".trim()", ".to_upper()", ".to_lower()"];
    methods[emit.gen_range(0..methods.len())]
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(StringTransform.name(), "string_transform");
    }

    #[test]
    fn returns_none_for_non_string() {
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
        let params = Params::from_iter([
            ("probability", ParamValue::Probability(1.0)),
            ("chain_probability", ParamValue::Probability(0.0)),
        ]);

        let result = StringTransform.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }

    #[test]
    fn generates_string_transform() {
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
        let params = Params::from_iter([
            ("probability", ParamValue::Probability(1.0)),
            ("chain_probability", ParamValue::Probability(0.0)),
        ]);

        let result = StringTransform.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::String),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.starts_with("s."),
            "expected method call on s, got: {text}"
        );
    }
}
