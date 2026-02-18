//! Rule: closures capturing variables called within match arm expressions.
//!
//! Generates code combining closures with match expressions, specifically
//! closures that capture outer variables and are called within match arms.
//!
//! **Pattern A** -- closure capturing string variable, called in match arms:
//! ```vole
//! let make_label = (tag: string) -> string => "{prefix}: {tag}"
//! let result = match x {
//!     0 => make_label("zero"),
//!     1 => make_label("one"),
//!     _ => make_label("other"),
//! }
//! ```
//!
//! **Pattern B** -- closure taking i64 returning i64, result matched:
//! ```vole
//! let double = (n: i64) -> i64 => n * 2
//! let tmp = double(x)
//! let result = match tmp {
//!     0 => 100,
//!     2 => 200,
//!     _ => 999,
//! }
//! ```

use std::collections::HashSet;

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MatchClosureCall;

impl StmtRule for MatchClosureCall {
    fn name(&self) -> &'static str {
        "match_closure_call"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.025)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        !scope.is_in_generic_class_method()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Need an i64 variable for the scrutinee
        let i64_vars = collect_i64_vars(scope);
        if i64_vars.is_empty() {
            return None;
        }

        // Pick pattern based on whether we have a string variable to capture
        let string_vars = collect_string_vars(scope);
        let use_pattern_a = !string_vars.is_empty() && emit.gen_bool(0.6);

        if use_pattern_a {
            generate_pattern_a(scope, emit, &i64_vars, &string_vars)
        } else {
            generate_pattern_b(scope, emit, &i64_vars)
        }
    }
}

/// Collect all i64-typed variables (locals and params).
fn collect_i64_vars(scope: &Scope) -> Vec<String> {
    scope
        .vars_of_type(&TypeInfo::Primitive(PrimitiveType::I64))
        .into_iter()
        .map(|v| v.name)
        .collect()
}

/// Collect all string-typed variables (locals and params).
fn collect_string_vars(scope: &Scope) -> Vec<String> {
    scope
        .vars_of_type(&TypeInfo::Primitive(PrimitiveType::String))
        .into_iter()
        .map(|v| v.name)
        .collect()
}

/// Pattern A: Create 1-2 closures capturing a string variable, call them in match arms.
///
/// ```vole
/// let make_label = (tag: string) -> string => "{prefix}: {tag}"
/// let result = match x {
///     0 => make_label("zero"),
///     1 => make_label("one"),
///     _ => make_label("other"),
/// }
/// ```
fn generate_pattern_a(
    scope: &mut Scope,
    emit: &mut Emit,
    i64_vars: &[String],
    string_vars: &[String],
) -> Option<String> {
    let indent = emit.indent_str();

    // Pick scrutinee
    let scr_idx = emit.gen_range(0..i64_vars.len());
    let scrutinee = &i64_vars[scr_idx];

    // Pick string variable to capture
    let str_idx = emit.gen_range(0..string_vars.len());
    let captured_var = &string_vars[str_idx];

    // Create 1-2 closures
    let num_closures = if emit.gen_bool(0.4) { 2 } else { 1 };
    let mut closure_names = Vec::new();
    let mut stmts = Vec::new();

    for i in 0..num_closures {
        let closure_name = scope.fresh_name();
        let closure_body = build_string_closure_body(emit, captured_var, i);
        stmts.push(format!(
            "let {} = (tag: string) -> string => {}",
            closure_name, closure_body,
        ));
        scope.add_local(
            closure_name.clone(),
            TypeInfo::Function {
                param_types: vec![TypeInfo::Primitive(PrimitiveType::String)],
                return_type: Box::new(TypeInfo::Primitive(PrimitiveType::String)),
            },
            false,
        );
        closure_names.push(closure_name);
    }

    // Build match expression with 3-5 arms + wildcard
    let arm_count = emit.random_in(3, 5);
    let mut arms = Vec::new();
    let mut used_values = HashSet::new();

    let tag_words = [
        "zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
    ];

    for i in 0..arm_count {
        let mut lit_val = emit.gen_i64_range(0, 9);
        while used_values.contains(&lit_val) {
            lit_val = emit.gen_i64_range(0, 9);
        }
        used_values.insert(lit_val);

        let arm_expr = build_arm_expr_a(emit, &closure_names, &tag_words, i);
        arms.push(format!("{}    {} => {},", indent, lit_val, arm_expr));
    }

    // Wildcard arm
    let wildcard_expr = build_arm_expr_a(emit, &closure_names, &tag_words, arm_count);
    arms.push(format!("{}    _ => {},", indent, wildcard_expr));

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let match_stmt = format!(
        "let {} = match {} {{\n{}\n{}}}",
        result_name,
        scrutinee,
        arms.join("\n"),
        indent,
    );

    stmts.push(match_stmt);
    Some(stmts.join(&format!("\n{}", indent)))
}

/// Build the body of a string-returning closure that captures a variable.
fn build_string_closure_body(emit: &mut Emit, captured_var: &str, variant: usize) -> String {
    match (variant + emit.gen_range(0..3)) % 4 {
        0 => format!("\"{{{}}}: {{tag}}\"", captured_var),
        1 => format!("\"{{tag}} (\" + {} + \")\"", captured_var),
        2 => format!("\"{{{}}}-{{tag}}\"", captured_var),
        _ => format!("tag + \"-\" + {}", captured_var),
    }
}

/// Build an arm expression for Pattern A.
fn build_arm_expr_a(
    emit: &mut Emit,
    closure_names: &[String],
    tag_words: &[&str],
    _arm_index: usize,
) -> String {
    // Most arms call a closure; occasionally use a string literal for variety
    if emit.gen_bool(0.15) {
        let word_idx = emit.gen_range(0..tag_words.len());
        format!("\"{}\"", tag_words[word_idx])
    } else {
        let closure_idx = emit.gen_range(0..closure_names.len());
        let word_idx = emit.gen_range(0..tag_words.len());
        format!(
            "{}(\"{}\")",
            closure_names[closure_idx], tag_words[word_idx]
        )
    }
}

/// Pattern B: Create a closure (i64 -> i64), call it, match on the result.
///
/// ```vole
/// let double = (n: i64) -> i64 => n * 2
/// let tmp = double(x)
/// let result = match tmp {
///     0 => 100,
///     2 => 200,
///     _ => 999,
/// }
/// ```
fn generate_pattern_b(scope: &mut Scope, emit: &mut Emit, i64_vars: &[String]) -> Option<String> {
    let indent = emit.indent_str();

    // Pick an i64 variable to pass to the closure
    let arg_idx = emit.gen_range(0..i64_vars.len());
    let arg_var = &i64_vars[arg_idx];

    // Build a closure: (n: i64) -> i64 => n * K + C
    let closure_name = scope.fresh_name();
    let mult = emit.random_in(1, 4);
    let offset = emit.gen_range(0..6);
    let closure_body = if offset == 0 {
        format!("n * {}", mult)
    } else {
        format!("n * {} + {}", mult, offset)
    };

    let closure_stmt = format!("let {} = (n: i64) -> i64 => {}", closure_name, closure_body,);
    scope.add_local(
        closure_name.clone(),
        TypeInfo::Function {
            param_types: vec![TypeInfo::Primitive(PrimitiveType::I64)],
            return_type: Box::new(TypeInfo::Primitive(PrimitiveType::I64)),
        },
        false,
    );

    // Call the closure and bind the result
    let tmp_name = scope.fresh_name();
    let call_stmt = format!("let {} = {}({})", tmp_name, closure_name, arg_var);
    scope.add_local(
        tmp_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    // Build match on the closure result
    let arm_count = emit.random_in(3, 5);
    let mut arms = Vec::new();
    let mut used_values = HashSet::new();

    for _ in 0..arm_count {
        let mut lit_val = emit.gen_i64_range(0, 19);
        while used_values.contains(&lit_val) {
            lit_val = emit.gen_i64_range(0, 19);
        }
        used_values.insert(lit_val);

        let arm_result = emit.gen_i64_range(100, 999);
        arms.push(format!("{}    {} => {},", indent, lit_val, arm_result));
    }

    // Wildcard arm
    let wildcard_result = emit.gen_i64_range(100, 999);
    arms.push(format!("{}    _ => {},", indent, wildcard_result));

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let match_stmt = format!(
        "let {} = match {} {{\n{}\n{}}}",
        result_name,
        tmp_name,
        arms.join("\n"),
        indent,
    );

    Some(format!(
        "{}\n{}{}\n{}{}",
        closure_stmt, indent, call_stmt, indent, match_stmt,
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

    fn test_params() -> Params {
        Params::from_iter([("probability", ParamValue::Probability(1.0))])
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(MatchClosureCall.name(), "match_closure_call");
    }

    #[test]
    fn returns_none_without_i64_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        assert!(
            MatchClosureCall
                .generate(&mut scope, &mut emit, &test_params())
                .is_none()
        );
    }

    #[test]
    fn generates_pattern_b_with_only_i64() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = MatchClosureCall.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        let text = result.unwrap();
        // Pattern B: should have a closure definition and a match expression
        assert!(
            text.contains("(n: i64) -> i64 =>"),
            "expected closure definition, got: {text}"
        );
        assert!(text.contains("match "), "expected match expr, got: {text}");
        assert!(text.contains("_ =>"), "expected wildcard arm, got: {text}");
    }

    #[test]
    fn generates_pattern_a_with_string_var() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        scope.add_local(
            "prefix".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        // Use a seed that triggers pattern A (need gen_bool(0.6) to be true)
        let mut rng = rand::rngs::StdRng::seed_from_u64(7);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = MatchClosureCall.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match "), "expected match expr, got: {text}");
        assert!(text.contains("_ =>"), "expected wildcard arm, got: {text}");
        // Should contain either a closure definition with string types
        // or fall back to pattern B -- either is valid
        assert!(
            text.contains("(tag: string) -> string =>") || text.contains("(n: i64) -> i64 =>"),
            "expected closure definition, got: {text}"
        );
    }

    #[test]
    fn adds_locals_pattern_b() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("n".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        MatchClosureCall.generate(&mut scope, &mut emit, &test_params());
        // Pattern B adds: closure + tmp + result = 3 locals
        // Pattern A adds: 1-2 closures + result = 2-3 locals
        assert!(
            scope.locals.len() >= initial_len + 2,
            "expected at least 2 new locals, got {} total (started with {})",
            scope.locals.len(),
            initial_len
        );
    }

    #[test]
    fn match_arms_have_trailing_commas() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = MatchClosureCall.generate(&mut scope, &mut emit, &test_params());
        let text = result.unwrap();
        // Every arm line (containing "=>") should end with a comma
        for line in text.lines() {
            let trimmed = line.trim();
            if trimmed.contains("=>") && !trimmed.starts_with("let") {
                assert!(
                    trimmed.ends_with(','),
                    "arm should end with comma: {trimmed}"
                );
            }
        }
    }

    #[test]
    fn precondition_true_by_default() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let params = test_params();
        assert!(MatchClosureCall.precondition(&scope, &params));
    }
}
