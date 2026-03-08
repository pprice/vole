//! Rule: nested for-loops with break/continue and accumulator variables.
//!
//! Generates nested for-loops that use `break` and/or `continue` alongside
//! a mutable accumulator, then asserts the expected value.  This exercises
//! edge cases in codegen's control flow graph -- nested blocks, early exits,
//! and mutable state across loop iterations.
//!
//! Three variants:
//!
//! 1. **break** -- Inner loop breaks at a threshold.
//!    ```vole
//!    var acc = 0_i64
//!    for i in 0..N {
//!        for j in 0..M {
//!            if j >= K { break }
//!            acc = acc + 1
//!        }
//!    }
//!    assert(acc == N * K)
//!    ```
//!
//! 2. **continue** -- Inner loop skips one value per iteration.
//!    ```vole
//!    var acc = 0_i64
//!    for i in 0..N {
//!        for j in 0..M {
//!            if j == K { continue }
//!            acc = acc + 1
//!        }
//!    }
//!    assert(acc == N * (M - 1))
//!    ```
//!
//! 3. **combined** -- Single loop with both continue and break.
//!    ```vole
//!    var acc = 0_i64
//!    for i in 0..N {
//!        if i == S { continue }
//!        if i >= L { break }
//!        acc = acc + 1
//!    }
//!    assert(acc == L - 1)   // or L - 2 when S < L
//!    ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct NestedLoopBreakContinue;

impl StmtRule for NestedLoopBreakContinue {
    fn name(&self) -> &'static str {
        "nested_loop_break_continue"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..3);
        match variant {
            0 => Some(gen_break_variant(scope, emit)),
            1 => Some(gen_continue_variant(scope, emit)),
            _ => Some(gen_combined_variant(scope, emit)),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0: nested loop with break
// ---------------------------------------------------------------------------

fn gen_break_variant(scope: &mut Scope, emit: &mut Emit) -> String {
    let acc = scope.fresh_name();
    let outer_iter = scope.fresh_name();
    let inner_iter = scope.fresh_name();

    let outer_end = emit.random_in(3, 6); // N
    let inner_end = emit.random_in(3, 6); // M
    // K must be < M so break actually fires
    let threshold = emit.random_in(1, inner_end - 1); // K

    let expected = (outer_end * threshold) as i64;

    let indent = emit.indent_str();
    let body1 = format!("{}    ", indent);
    let body2 = format!("{}        ", indent);

    scope.add_local(acc.clone(), TypeInfo::Primitive(PrimitiveType::I64), true);
    scope.protected_vars.push(acc.clone());

    format!(
        "var {acc} = 0_i64\n\
         {indent}for {outer_iter} in 0..{outer_end} {{\n\
         {body1}for {inner_iter} in 0..{inner_end} {{\n\
         {body2}if {inner_iter} >= {threshold} {{\n\
         {body2}    break\n\
         {body2}}}\n\
         {body2}{acc} = {acc} + 1\n\
         {body1}}}\n\
         {indent}}}\n\
         {indent}assert({acc} == {expected})",
    )
}

// ---------------------------------------------------------------------------
// Variant 1: nested loop with continue
// ---------------------------------------------------------------------------

fn gen_continue_variant(scope: &mut Scope, emit: &mut Emit) -> String {
    let acc = scope.fresh_name();
    let outer_iter = scope.fresh_name();
    let inner_iter = scope.fresh_name();

    let outer_end = emit.random_in(3, 6); // N
    let inner_end = emit.random_in(3, 6); // M
    // K must be < M so continue actually fires
    let skip_val = emit.random_in(0, inner_end - 1); // K

    // Each outer iteration: inner runs M times, skips 1 => M-1 increments
    let expected = (outer_end * (inner_end - 1)) as i64;

    let indent = emit.indent_str();
    let body1 = format!("{}    ", indent);
    let body2 = format!("{}        ", indent);

    scope.add_local(acc.clone(), TypeInfo::Primitive(PrimitiveType::I64), true);
    scope.protected_vars.push(acc.clone());

    format!(
        "var {acc} = 0_i64\n\
         {indent}for {outer_iter} in 0..{outer_end} {{\n\
         {body1}for {inner_iter} in 0..{inner_end} {{\n\
         {body2}if {inner_iter} == {skip_val} {{\n\
         {body2}    continue\n\
         {body2}}}\n\
         {body2}{acc} = {acc} + 1\n\
         {body1}}}\n\
         {indent}}}\n\
         {indent}assert({acc} == {expected})",
    )
}

// ---------------------------------------------------------------------------
// Variant 2: single loop with both continue and break
// ---------------------------------------------------------------------------

fn gen_combined_variant(scope: &mut Scope, emit: &mut Emit) -> String {
    let acc = scope.fresh_name();
    let iter_var = scope.fresh_name();

    let range_end = emit.random_in(4, 6); // N (need room for both skip and limit)
    let limit = emit.random_in(2, range_end - 1); // L: break when i >= L
    let skip_val = emit.random_in(0, limit - 1); // S: continue when i == S

    // Iterations that actually increment: 0..L, minus the one skipped by continue
    let expected = (limit - 1) as i64; // L values minus the skipped one

    let indent = emit.indent_str();
    let body = format!("{}    ", indent);

    scope.add_local(acc.clone(), TypeInfo::Primitive(PrimitiveType::I64), true);
    scope.protected_vars.push(acc.clone());

    format!(
        "var {acc} = 0_i64\n\
         {indent}for {iter_var} in 0..{range_end} {{\n\
         {body}if {iter_var} == {skip_val} {{\n\
         {body}    continue\n\
         {body}}}\n\
         {body}if {iter_var} >= {limit} {{\n\
         {body}    break\n\
         {body}}}\n\
         {body}{acc} = {acc} + 1\n\
         {indent}}}\n\
         {indent}assert({acc} == {expected})",
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
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
        assert_eq!(NestedLoopBreakContinue.name(), "nested_loop_break_continue");
    }

    #[test]
    fn generates_with_break_or_continue() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = NestedLoopBreakContinue.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("var "), "expected var, got: {text}");
        assert!(text.contains("for "), "expected for, got: {text}");
        assert!(text.contains("assert("), "expected assert, got: {text}");
        assert!(
            text.contains("break") || text.contains("continue"),
            "expected break or continue, got: {text}"
        );
    }

    #[test]
    fn all_three_variants_reachable() {
        let table = SymbolTable::new();
        let resolved = ResolvedParams::new();
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let mut found_break = false;
        let mut found_continue = false;
        let mut found_combined = false;

        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut emit = test_emit(&mut rng, &resolved);
            if let Some(text) =
                NestedLoopBreakContinue.generate(&mut scope, &mut emit, &rule_params)
            {
                let has_break = text.contains("break");
                let has_continue = text.contains("continue");
                let for_count = text.matches("for ").count();

                if has_break && !has_continue && for_count == 2 {
                    found_break = true;
                } else if has_continue && !has_break && for_count == 2 {
                    found_continue = true;
                } else if has_break && has_continue && for_count == 1 {
                    found_combined = true;
                }
            }
            if found_break && found_continue && found_combined {
                break;
            }
        }

        assert!(found_break, "break variant not reached");
        assert!(found_continue, "continue variant not reached");
        assert!(found_combined, "combined variant not reached");
    }

    #[test]
    fn adds_accumulator_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        NestedLoopBreakContinue.generate(&mut scope, &mut emit, &params);
        assert!(
            scope.locals.len() > initial_len,
            "expected accumulator added to scope"
        );
    }

    #[test]
    fn protects_accumulator_var() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        NestedLoopBreakContinue.generate(&mut scope, &mut emit, &params);
        assert!(
            !scope.protected_vars.is_empty(),
            "expected accumulator to be protected"
        );
    }
}
