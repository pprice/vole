//! Rule: match on iterator terminal.
//!
//! Finds an i64/i32 array parameter and generates a match on an iterator
//! terminal (`.count()`, `.sum()`, or `.filter(...).count()`):
//! ```vole
//! let result = match arr.iter().count() {
//!     0 => <expr>
//!     1 => <expr>
//!     _ => <expr>
//! }
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MatchIter;

impl StmtRule for MatchIter {
    fn name(&self) -> &'static str {
        "match_iter"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let array_vars = collect_integer_array_params(scope);
        if array_vars.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..array_vars.len());
        let arr_name = array_vars[idx].clone();
        let result_name = scope.fresh_name();

        let terminal = pick_terminal(emit);

        let result_type = emit.random_primitive_type();
        let indent = emit.indent_str();

        let arm_val1 = emit.literal(&result_type);
        let arm_val2 = emit.literal(&result_type);
        let wildcard_val = emit.literal(&result_type);

        scope.add_local(result_name.clone(), result_type, false);

        Some(format!(
            "let {} = match {}{} {{\n\
             {}    0 => {}\n\
             {}    1 => {}\n\
             {}    _ => {}\n\
             {}}}",
            result_name,
            arr_name,
            terminal,
            indent,
            arm_val1,
            indent,
            arm_val2,
            indent,
            wildcard_val,
            indent,
        ))
    }
}

fn collect_integer_array_params(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for param in scope.params {
        if let TypeInfo::Array(inner) = &param.param_type {
            if matches!(
                inner.as_ref(),
                TypeInfo::Primitive(PrimitiveType::I64 | PrimitiveType::I32)
            ) {
                out.push(param.name.clone());
            }
        }
    }
    out
}

fn pick_terminal(emit: &mut Emit) -> String {
    match emit.gen_range(0..3) {
        0 => ".iter().count()".to_string(),
        1 => ".iter().sum()".to_string(),
        _ => ".iter().filter((x) => x > 0).count()".to_string(),
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
        assert_eq!(MatchIter.name(), "match_iter");
    }

    #[test]
    fn returns_none_without_integer_array_params() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(MatchIter.generate(&mut scope, &mut emit, &params).is_none());
    }

    #[test]
    fn generates_with_i64_array_param() {
        let table = SymbolTable::new();
        let fn_params = [ParamInfo {
            name: "arr".into(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            has_default: false,
        }];
        let mut scope = Scope::new(&fn_params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = MatchIter.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match arr"), "got: {text}");
        assert!(text.contains(".iter()"), "got: {text}");
        assert!(text.contains("_ =>"), "got: {text}");
    }
}
