//! Rule: call a generic function with a closure argument.
//!
//! Stresses the intersection of generics + closures + monomorphization by
//! generating module-level generic helper functions and calling them with
//! inline closures that force monomorphization at a concrete type.
//!
//! The helper functions are emitted at module level via
//! [`Scope::add_module_decl`] because nested `func<T>` is rewritten to
//! `let = lambda` by vole-fmt, and lambdas don't support type parameters.
//!
//! Three variants:
//!
//! **Variant 0 -- apply -> string: `(T, (T) -> string) -> string`**
//! ```vole
//! func apply_to_str_local0<T>(x: T, f: (T) -> string) -> string {
//!     return f(x)
//! }
//! let local1 = apply_to_str_local0(42, (x: i64) => x.to_string())
//! assert(local1 == "42")
//! ```
//!
//! **Variant 1 -- apply -> i64: `(T, (T) -> i64) -> i64`**
//! ```vole
//! func apply_to_i64_local0<T>(x: T, f: (T) -> i64) -> i64 {
//!     return f(x)
//! }
//! let local1 = apply_to_i64_local0("hello", (s: string) => s.length())
//! assert(local1 == 5)
//! ```
//!
//! **Variant 2 -- double apply: `(T, (T) -> T) -> T`**
//! ```vole
//! func double_apply_local0<T>(x: T, f: (T) -> T) -> T {
//!     return f(f(x))
//! }
//! let local1 = double_apply_local0(5, (x: i64) => x + 1)
//! assert(local1 == 7)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct GenericClosureCall;

impl StmtRule for GenericClosureCall {
    fn name(&self) -> &'static str {
        "generic_closure_call"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..3);
        match variant {
            0 => emit_apply_to_str(scope, emit),
            1 => emit_apply_to_i64(scope, emit),
            _ => emit_double_apply(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0: apply -> string -- `(T, (T) -> string) -> string`
// ---------------------------------------------------------------------------

/// Generate `apply_to_str_<N>` at module level and a call with a closure that
/// converts the argument to a string.
///
/// Picks a random concrete type (i64, bool, or i32), generates a matching
/// literal and `.to_string()` closure, then asserts the result equals the
/// expected string representation.
fn emit_apply_to_str(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_name = scope.fresh_name();
    let fn_label = format!("apply_to_str_{}", fn_name);

    let decl = format!(
        "func {}<T>(x: T, f: (T) -> string) -> string {{\n    return f(x)\n}}",
        fn_label
    );
    scope.add_module_decl(decl);

    // Pick a concrete type and build the argument + closure + expected value.
    let concrete_type = emit.gen_range(0..3);
    let (arg_literal, closure, expected) = match concrete_type {
        0 => {
            // i64
            let val = emit.gen_i64_range(0, 100);
            (
                format!("{}", val),
                "(x: i64) => x.to_string()".to_string(),
                format!("{}", val),
            )
        }
        1 => {
            // bool
            let val = emit.gen_bool(0.5);
            let lit = if val { "true" } else { "false" };
            (
                lit.to_string(),
                "(b: bool) => b.to_string()".to_string(),
                lit.to_string(),
            )
        }
        _ => {
            // i32
            let val = emit.gen_i64_range(0, 100) as i32;
            (
                format!("{}_i32", val),
                "(x: i32) => x.to_string()".to_string(),
                format!("{}", val),
            )
        }
    };

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}({}, {})\n{}assert({} == \"{}\")",
        result_name, fn_label, arg_literal, closure, indent, result_name, expected,
    ))
}

// ---------------------------------------------------------------------------
// Variant 1: apply -> i64 -- `(T, (T) -> i64) -> i64`
// ---------------------------------------------------------------------------

/// Generate `apply_to_i64_<N>` at module level and a call with a closure that
/// computes the length of a string argument.
fn emit_apply_to_i64(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_name = scope.fresh_name();
    let fn_label = format!("apply_to_i64_{}", fn_name);

    let decl = format!(
        "func {}<T>(x: T, f: (T) -> i64) -> i64 {{\n    return f(x)\n}}",
        fn_label
    );
    scope.add_module_decl(decl);

    let words = ["hello", "world", "vole", "test", "abc"];
    let idx = emit.gen_range(0..words.len());
    let word = words[idx];
    let expected = word.len() as i64;

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}(\"{}\", (s: string) => s.length())\n{}assert({} == {})",
        result_name, fn_label, word, indent, result_name, expected,
    ))
}

// ---------------------------------------------------------------------------
// Variant 2: double apply -- `(T, (T) -> T) -> T`
// ---------------------------------------------------------------------------

/// Generate `double_apply_<N>` at module level and a call with a `+1` closure.
/// The function applies the closure twice, so the expected result is `initial + 2`.
fn emit_double_apply(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_name = scope.fresh_name();
    let fn_label = format!("double_apply_{}", fn_name);

    let decl = format!(
        "func {}<T>(x: T, f: (T) -> T) -> T {{\n    return f(f(x))\n}}",
        fn_label
    );
    scope.add_module_decl(decl);

    let initial = emit.gen_i64_range(1, 10);
    let expected = initial + 2;

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}({}, (x: i64) => x + 1)\n{}assert({} == {})",
        result_name, fn_label, initial, indent, result_name, expected,
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
        assert_eq!(GenericClosureCall.name(), "generic_closure_call");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!GenericClosureCall.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(GenericClosureCall.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!GenericClosureCall.precondition(&scope, &params));
    }

    #[test]
    fn generates_apply_to_str_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = GenericClosureCall.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("apply_to_str_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for apply_to_str variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("<T>"),
                        "expected generic type param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("-> string"),
                        "expected string return type in decl: {decl}"
                    );
                    assert!(decl.contains("f(x)"), "expected f(x) body: {decl}");
                    assert!(
                        text.contains(".to_string()"),
                        "expected to_string closure in code: {text}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated apply_to_str variant in 100 seeds");
    }

    #[test]
    fn generates_apply_to_i64_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = GenericClosureCall.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("apply_to_i64_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for apply_to_i64 variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("<T>"),
                        "expected generic type param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("-> i64"),
                        "expected i64 return type in decl: {decl}"
                    );
                    assert!(
                        text.contains("s.length()"),
                        "expected length closure in code: {text}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated apply_to_i64 variant in 100 seeds");
    }

    #[test]
    fn generates_double_apply_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = GenericClosureCall.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("double_apply_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for double_apply variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("<T>"),
                        "expected generic type param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("f(f(x))"),
                        "expected double apply body: {decl}"
                    );
                    assert!(
                        text.contains("x + 1"),
                        "expected +1 closure in code: {text}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated double_apply variant in 100 seeds");
    }

    #[test]
    fn adds_module_decl() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        GenericClosureCall.generate(&mut scope, &mut emit, &test_params());
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

        let result = GenericClosureCall.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        assert!(
            !scope.locals.is_empty(),
            "expected result local added to scope"
        );
    }
}
