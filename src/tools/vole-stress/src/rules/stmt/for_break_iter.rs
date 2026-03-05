//! Rule: for-loop over array iterator with early break or continue.
//!
//! Generates a for-loop over `arr.iter()` that uses `break` or `continue`
//! inside a conditional, accumulating elements into a mutable variable.
//! Stresses iterator cleanup on early exit, control flow codegen in loop
//! bodies, and the interaction between break/continue and iterator state.
//!
//! Two variants (~50/50):
//!
//! 1. **break** – accumulate elements, break when one exceeds a threshold.
//! 2. **continue** – skip elements matching a condition, accumulate the rest.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ForBreakIter;

impl StmtRule for ForBreakIter {
    fn name(&self) -> &'static str {
        "for_break_iter"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.can_recurse() && has_i64_array(scope)
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let arr_name = pick_i64_array(scope, emit)?;

        if emit.gen_bool(0.5) {
            Some(gen_break_variant(scope, emit, &arr_name))
        } else {
            Some(gen_continue_variant(scope, emit, &arr_name))
        }
    }
}

/// Check whether there is at least one `[i64]` array variable in scope.
fn has_i64_array(scope: &Scope) -> bool {
    scope
        .array_vars()
        .iter()
        .any(|(_, elem)| matches!(elem, TypeInfo::Primitive(PrimitiveType::I64)))
}

/// Pick a random `[i64]` array variable from scope.
fn pick_i64_array(scope: &Scope, emit: &mut Emit) -> Option<String> {
    let i64_arrays: Vec<String> = scope
        .array_vars()
        .into_iter()
        .filter(|(_, elem)| matches!(elem, TypeInfo::Primitive(PrimitiveType::I64)))
        .map(|(name, _)| name)
        .collect();

    if i64_arrays.is_empty() {
        return None;
    }

    let idx = emit.gen_range(0..i64_arrays.len());
    Some(i64_arrays[idx].clone())
}

// ---------------------------------------------------------------------------
// Break variant
// ---------------------------------------------------------------------------

fn gen_break_variant(scope: &mut Scope, emit: &mut Emit, arr_name: &str) -> String {
    let accum = scope.fresh_name();
    let elem = scope.fresh_name();
    let threshold = emit.gen_i64_range(0, 10);
    let indent = emit.indent_str();

    scope.add_local(accum.clone(), TypeInfo::Primitive(PrimitiveType::I64), true);
    scope.protected_vars.push(accum.clone());

    format!(
        "var {accum} = 0\n\
         {indent}for {elem} in {arr_name}.iter() {{\n\
         {indent}    if {elem} > {threshold} {{\n\
         {indent}        break\n\
         {indent}    }}\n\
         {indent}    {accum} = {accum} + {elem}\n\
         {indent}}}",
        accum = accum,
        elem = elem,
        arr_name = arr_name,
        threshold = threshold,
        indent = indent,
    )
}

// ---------------------------------------------------------------------------
// Continue variant
// ---------------------------------------------------------------------------

fn gen_continue_variant(scope: &mut Scope, emit: &mut Emit, arr_name: &str) -> String {
    let accum = scope.fresh_name();
    let elem = scope.fresh_name();
    let indent = emit.indent_str();

    // Pick a condition style: `elem == N` (~60%) or `elem > N` (~40%)
    let condition = if emit.gen_bool(0.6) {
        let skip_val = emit.gen_i64_range(0, 5);
        format!("{elem} == {skip_val}")
    } else {
        let skip_threshold = emit.gen_i64_range(0, 5);
        format!("{elem} > {skip_threshold}")
    };

    scope.add_local(accum.clone(), TypeInfo::Primitive(PrimitiveType::I64), true);
    scope.protected_vars.push(accum.clone());

    format!(
        "var {accum} = 0\n\
         {indent}for {elem} in {arr_name}.iter() {{\n\
         {indent}    if {condition} {{\n\
         {indent}        continue\n\
         {indent}    }}\n\
         {indent}    {accum} = {accum} + {elem}\n\
         {indent}}}",
        accum = accum,
        elem = elem,
        arr_name = arr_name,
        condition = condition,
        indent = indent,
    )
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

    fn i64_array_params() -> Vec<ParamInfo> {
        vec![ParamInfo {
            name: "nums".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            has_default: false,
        }]
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(ForBreakIter.name(), "for_break_iter");
    }

    #[test]
    fn returns_none_without_arrays() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(
            !ForBreakIter.precondition(&scope, &params),
            "should fail precondition without arrays"
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let result = ForBreakIter.generate(&mut scope, &mut emit, &params);
        assert!(result.is_none());
    }

    #[test]
    fn generates_with_array() {
        let table = SymbolTable::new();
        let param_info = i64_array_params();
        let mut scope = Scope::new(&param_info, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ForBreakIter.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("for "), "expected for, got: {text}");
        assert!(text.contains(".iter()"), "expected .iter(), got: {text}");
        assert!(
            text.contains("break") || text.contains("continue"),
            "expected break or continue, got: {text}"
        );
    }

    #[test]
    fn generates_multiple_seeds_without_panic() {
        let table = SymbolTable::new();
        let param_info = i64_array_params();
        let resolved = ResolvedParams::new();
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        for seed in 0..50 {
            let mut scope = Scope::new(&param_info, &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut emit = test_emit(&mut rng, &resolved);
            let result = ForBreakIter.generate(&mut scope, &mut emit, &params);
            assert!(result.is_some(), "seed {seed} returned None");
        }
    }
}
