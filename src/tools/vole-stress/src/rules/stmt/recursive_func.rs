//! Rule: module-level recursive function with base case, then call + assert.
//!
//! This tests call stack handling, return values through recursion, and
//! function call codegen.
//!
//! Three variants:
//!
//! **Variant 0 -- factorial:**
//! ```vole
//! func factorial_local0(n: i64) -> i64 {
//!     if n <= 1 {
//!         return 1
//!     }
//!     return n * factorial_local0(n - 1)
//! }
//! let local1 = factorial_local0(5)
//! assert(local1 == 120)
//! ```
//!
//! **Variant 1 -- sum to n:**
//! ```vole
//! func sum_to_local0(n: i64) -> i64 {
//!     if n <= 0 {
//!         return 0
//!     }
//!     return n + sum_to_local0(n - 1)
//! }
//! let local1 = sum_to_local0(10)
//! assert(local1 == 55)
//! ```
//!
//! **Variant 2 -- string repeat (recursive):**
//! ```vole
//! func repeat_str_local0(s: string, n: i64) -> string {
//!     if n <= 0 {
//!         return ""
//!     }
//!     return s + repeat_str_local0(s, n - 1)
//! }
//! let local1 = repeat_str_local0("ab", 3)
//! assert(local1 == "ababab")
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct RecursiveFunc;

/// Short strings for the repeat variant.
const REPEAT_STRS: &[&str] = &["ab", "xy", "hi", "ok"];

impl StmtRule for RecursiveFunc {
    fn name(&self) -> &'static str {
        "recursive_func"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..3);
        match variant {
            0 => emit_factorial(scope, emit),
            1 => emit_sum_to(scope, emit),
            _ => emit_repeat_str(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0 -- factorial
// ---------------------------------------------------------------------------

fn emit_factorial(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_name = scope.fresh_name();
    let fn_label = format!("factorial_{}", fn_name);

    // Pick n from 3..=8 to avoid stack overflow
    let n = emit.gen_i64_range(3, 8);
    let expected = factorial(n);

    let decl = format!(
        "func {}(n: i64) -> i64 {{\n    if n <= 1 {{\n        return 1\n    }}\n    return n * {}(n - 1)\n}}",
        fn_label, fn_label,
    );
    scope.add_module_decl(decl);

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}({})\n{}assert({} == {})",
        result_name, fn_label, n, indent, result_name, expected,
    ))
}

fn factorial(n: i64) -> i64 {
    if n <= 1 { 1 } else { n * factorial(n - 1) }
}

// ---------------------------------------------------------------------------
// Variant 1 -- sum to n
// ---------------------------------------------------------------------------

fn emit_sum_to(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_name = scope.fresh_name();
    let fn_label = format!("sum_to_{}", fn_name);

    // Pick n from 5..=20
    let n = emit.gen_i64_range(5, 20);
    let expected = n * (n + 1) / 2;

    let decl = format!(
        "func {}(n: i64) -> i64 {{\n    if n <= 0 {{\n        return 0\n    }}\n    return n + {}(n - 1)\n}}",
        fn_label, fn_label,
    );
    scope.add_module_decl(decl);

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}({})\n{}assert({} == {})",
        result_name, fn_label, n, indent, result_name, expected,
    ))
}

// ---------------------------------------------------------------------------
// Variant 2 -- string repeat (recursive)
// ---------------------------------------------------------------------------

fn emit_repeat_str(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_name = scope.fresh_name();
    let fn_label = format!("repeat_str_{}", fn_name);

    let str_idx = emit.gen_range(0..REPEAT_STRS.len());
    let s = REPEAT_STRS[str_idx];
    // Pick n from 2..=5
    let n = emit.gen_i64_range(2, 5);
    let expected = s.repeat(n as usize);

    let decl = format!(
        "func {}(s: string, n: i64) -> string {{\n    if n <= 0 {{\n        return \"\"\n    }}\n    return s + {}(s, n - 1)\n}}",
        fn_label, fn_label,
    );
    scope.add_module_decl(decl);

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}(\"{}\", {})\n{}assert({} == \"{}\")",
        result_name, fn_label, s, n, indent, result_name, expected,
    ))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

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
        assert_eq!(RecursiveFunc.name(), "recursive_func");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!RecursiveFunc.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(RecursiveFunc.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!RecursiveFunc.precondition(&scope, &params));
    }

    #[test]
    fn generates_factorial_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = RecursiveFunc.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("factorial_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for factorial variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> i64"),
                        "expected i64 return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return n * factorial_"),
                        "expected recursive call in decl: {decl}"
                    );
                    assert!(
                        decl.contains("if n <= 1"),
                        "expected base case in decl: {decl}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated factorial variant in 100 seeds");
    }

    #[test]
    fn generates_sum_to_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = RecursiveFunc.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("sum_to_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for sum_to variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> i64"),
                        "expected i64 return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return n + sum_to_"),
                        "expected recursive call in decl: {decl}"
                    );
                    assert!(
                        decl.contains("if n <= 0"),
                        "expected base case in decl: {decl}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated sum_to variant in 100 seeds");
    }

    #[test]
    fn generates_repeat_str_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = RecursiveFunc.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("repeat_str_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for repeat_str variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> string"),
                        "expected string return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return s + repeat_str_"),
                        "expected recursive call in decl: {decl}"
                    );
                    assert!(
                        decl.contains("if n <= 0"),
                        "expected base case in decl: {decl}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated repeat_str variant in 100 seeds");
    }

    #[test]
    fn adds_module_decl() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        RecursiveFunc.generate(&mut scope, &mut emit, &test_params());
        assert_eq!(
            scope.module_decls.len(),
            1,
            "expected exactly one module decl"
        );
    }

    #[test]
    fn adds_result_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = RecursiveFunc.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        assert!(
            !scope.locals.is_empty(),
            "expected result local added to scope"
        );
        let result_local = scope.locals.last().expect("should add result local");
        // Result type depends on variant but should be either I64 or String.
        assert!(
            result_local.1 == TypeInfo::Primitive(PrimitiveType::I64)
                || result_local.1 == TypeInfo::Primitive(PrimitiveType::String),
            "result must be i64 or string, got: {:?}",
            result_local.1,
        );
    }

    #[test]
    fn factorial_computation_is_correct() {
        assert_eq!(factorial(1), 1);
        assert_eq!(factorial(3), 6);
        assert_eq!(factorial(5), 120);
        assert_eq!(factorial(8), 40320);
    }
}
