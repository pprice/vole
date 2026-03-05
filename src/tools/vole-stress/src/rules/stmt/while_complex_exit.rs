//! Rule: while loop with complex boolean exit conditions.
//!
//! Generates while loops that combine a counter check with an additional
//! boolean condition using `&&`.  Three variants:
//!
//! **Boolean flag** -- `while count < N && !found { ... }`
//! ```vole
//! var count = 0
//! var found = false
//! while count < 10 && !found {
//!     if count == 7 { found = true }
//!     count = count + 1
//! }
//! ```
//!
//! **Sum accumulator** -- `while i < N && sum < T { ... }`
//! ```vole
//! var i = 0
//! var sum = 0
//! while i < 5 && sum < 8 {
//!     sum = sum + i
//!     i = i + 1
//! }
//! ```
//!
//! **String build** -- `while n < N && s.length() < L { ... }`
//! ```vole
//! var s = ""
//! var n = 0
//! while s.length() < 10 && n < 20 {
//!     s = s + "ab"
//!     n = n + 1
//! }
//! ```
//!
//! Variables are local to the generated block and are NOT registered in scope
//! (they are dead after the loop and registering them could confuse later rules).

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;

pub struct WhileComplexExit;

impl StmtRule for WhileComplexExit {
    fn name(&self) -> &'static str {
        "while_complex_exit"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.can_recurse()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..3);
        match variant {
            0 => generate_bool_flag(scope, emit),
            1 => generate_sum_accum(scope, emit),
            _ => generate_string_build(scope, emit),
        }
    }
}

/// Boolean flag variant:
/// ```vole
/// var count = 0
/// var found = false
/// while count < LIMIT && !found {
///     if count == TRIGGER { found = true }
///     count = count + 1
/// }
/// ```
fn generate_bool_flag(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let counter = scope.fresh_name();
    let flag = scope.fresh_name();
    let limit: usize = emit.random_in(5, 15);
    let trigger: usize = emit.random_in(2, limit.saturating_sub(1).max(2));

    let indent = emit.indent_str();

    Some(format!(
        "var {counter} = 0\n\
         {indent}var {flag} = false\n\
         {indent}while {counter} < {limit} && !{flag} {{\n\
         {indent}    if {counter} == {trigger} {{ {flag} = true }}\n\
         {indent}    {counter} = {counter} + 1\n\
         {indent}}}"
    ))
}

/// Sum accumulator variant:
/// ```vole
/// var i = 0
/// var sum = 0
/// while i < LIMIT && sum < THRESHOLD {
///     sum = sum + i
///     i = i + 1
/// }
/// ```
fn generate_sum_accum(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let counter = scope.fresh_name();
    let sum = scope.fresh_name();
    let limit: usize = emit.random_in(5, 15);
    let threshold: usize = emit.random_in(3, 12);

    let indent = emit.indent_str();

    Some(format!(
        "var {counter} = 0\n\
         {indent}var {sum} = 0\n\
         {indent}while {counter} < {limit} && {sum} < {threshold} {{\n\
         {indent}    {sum} = {sum} + {counter}\n\
         {indent}    {counter} = {counter} + 1\n\
         {indent}}}"
    ))
}

/// String build variant:
/// ```vole
/// var s = ""
/// var n = 0
/// while s.length() < STR_LIMIT && n < COUNTER_LIMIT {
///     s = s + CHUNK
///     n = n + 1
/// }
/// ```
fn generate_string_build(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let str_name = scope.fresh_name();
    let counter = scope.fresh_name();
    let str_limit: usize = emit.random_in(5, 15);
    let counter_limit: usize = emit.random_in(10, 15);

    let chunk_choice = emit.gen_range(0..3);
    let chunk = match chunk_choice {
        0 => "\"ab\"",
        1 => "\"xy\"",
        _ => "\"ok\"",
    };

    let indent = emit.indent_str();

    Some(format!(
        "var {str_name} = \"\"\n\
         {indent}var {counter} = 0\n\
         {indent}while {str_name}.length() < {str_limit} && {counter} < {counter_limit} {{\n\
         {indent}    {str_name} = {str_name} + {chunk}\n\
         {indent}    {counter} = {counter} + 1\n\
         {indent}}}"
    ))
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
        assert_eq!(WhileComplexExit.name(), "while_complex_exit");
    }

    #[test]
    fn respects_depth_limit() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.depth = scope.max_depth;
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!WhileComplexExit.precondition(&scope, &params));
    }

    #[test]
    fn generates_while_with_double_condition() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WhileComplexExit.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("while "), "expected while, got: {text}");
        assert!(text.contains("&&"), "expected &&, got: {text}");
        assert!(text.contains("var "), "expected var decl, got: {text}");
    }

    #[test]
    fn bool_flag_variant_has_expected_structure() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(99);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = generate_bool_flag(&mut scope, &mut emit);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("= false"), "expected bool init, got: {text}");
        assert!(
            text.contains("!local"),
            "expected negated flag, got: {text}"
        );
        assert!(
            text.contains("= true"),
            "expected flag set to true, got: {text}"
        );
        assert!(
            text.contains("= local0 + 1") || text.contains("+ 1"),
            "expected counter increment, got: {text}"
        );
    }

    #[test]
    fn sum_accum_variant_has_expected_structure() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(77);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = generate_sum_accum(&mut scope, &mut emit);
        assert!(result.is_some());
        let text = result.unwrap();
        // Two var declarations initialised to 0
        assert_eq!(
            text.matches("= 0").count(),
            2,
            "expected two zero inits, got: {text}"
        );
        // Sum accumulation: sum = sum + counter
        assert!(
            text.contains("= local0 + local1") || text.contains("= local1 + local0"),
            "expected sum accumulation, got: {text}"
        );
    }

    #[test]
    fn string_build_variant_has_expected_structure() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(55);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = generate_string_build(&mut scope, &mut emit);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".length()"),
            "expected .length() call, got: {text}"
        );
        assert!(
            text.contains("= \"\""),
            "expected empty string init, got: {text}"
        );
        assert!(
            text.contains("+ \"ab\"") || text.contains("+ \"xy\"") || text.contains("+ \"ok\""),
            "expected string concat, got: {text}"
        );
    }

    #[test]
    fn does_not_register_locals_in_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        WhileComplexExit.generate(&mut scope, &mut emit, &params);
        assert!(
            scope.locals.is_empty(),
            "internal vars should not leak into scope"
        );
        assert!(
            scope.protected_vars.is_empty(),
            "no protected vars should be registered"
        );
    }
}
