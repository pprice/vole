//! Rule: match on first array element.
//!
//! Picks a parameter array of i64/i32 elements and generates a match on `arr[0]`:
//! ```vole
//! let result = match arr[0] {
//!     5 => <expr>
//!     -2 => <expr>
//!     _ => <expr>
//! }
//! ```
//! Only uses parameter arrays (guaranteed non-empty by the test harness).

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MatchArray;

impl StmtRule for MatchArray {
    fn name(&self) -> &'static str {
        "match_array"
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
        let (arr_name, elem_prim) = array_vars[idx].clone();

        let result_type = emit.random_primitive_type();
        let result_name = scope.fresh_name();
        let indent = emit.indent_str();

        // Generate 2 specific literal arms + wildcard
        let lit1 = literal_for_prim(elem_prim, emit);
        let lit2 = literal_for_prim(elem_prim, emit);
        let arm_val1 = emit.literal(&result_type);
        let arm_val2 = emit.literal(&result_type);
        let wildcard_val = emit.literal(&result_type);

        let arms = [
            format!("{}    {} => {}", indent, lit1, arm_val1),
            format!("{}    {} => {}", indent, lit2, arm_val2),
            format!("{}    _ => {}", indent, wildcard_val),
        ];

        scope.add_local(result_name.clone(), result_type, false);

        Some(format!(
            "let {} = match {}[0] {{\n{}\n{}}}",
            result_name,
            arr_name,
            arms.join("\n"),
            indent,
        ))
    }
}

/// Collect parameter arrays with i64/i32 element type.
fn collect_integer_array_params(scope: &Scope) -> Vec<(String, PrimitiveType)> {
    let mut out = Vec::new();
    for param in scope.params {
        if let TypeInfo::Array(inner) = &param.param_type {
            if let TypeInfo::Primitive(p @ (PrimitiveType::I64 | PrimitiveType::I32)) =
                inner.as_ref()
            {
                out.push((param.name.clone(), *p));
            }
        }
    }
    out
}

/// Generate a literal value for a primitive type.
fn literal_for_prim(prim: PrimitiveType, emit: &mut Emit) -> String {
    match prim {
        PrimitiveType::I32 => {
            let v = emit.gen_i64_range(-10, 20);
            format!("{}_i32", v)
        }
        _ => {
            let v = emit.gen_i64_range(-10, 20);
            format!("{}", v)
        }
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
        assert_eq!(MatchArray.name(), "match_array");
    }

    #[test]
    fn returns_none_without_array_params() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            MatchArray
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
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

        let result = MatchArray.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match arr[0]"), "got: {text}");
        assert!(text.contains("_ =>"), "got: {text}");
    }

    #[test]
    fn adds_one_local() {
        let table = SymbolTable::new();
        let fn_params = [ParamInfo {
            name: "arr".into(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            has_default: false,
        }];
        let mut scope = Scope::new(&fn_params, &table);
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        MatchArray.generate(&mut scope, &mut emit, &params);
        assert_eq!(scope.locals.len(), initial_len + 1);
    }
}
