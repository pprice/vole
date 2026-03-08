//! Rule: generic struct declarations with helper functions that create and
//! operate on them.
//!
//! Stresses monomorphization and generic struct construction codegen by
//! emitting a generic struct, one or more generic/concrete helper functions,
//! and inline code that instantiates the struct via the helpers and asserts
//! on the result.
//!
//! The struct and helper functions are emitted at module level via
//! [`Scope::add_module_decl`] because nested `func<T>` is rewritten to
//! `let = lambda` by vole-fmt, and lambdas don't support type parameters.
//!
//! **Variant 0 -- Wrapper with unwrap (i64):**
//! ```vole
//! struct WrapperLocal0<T> {
//!     value: T
//! }
//! func wrap_local0<T>(x: T) -> WrapperLocal0<T> {
//!     return WrapperLocal0<T> { value: x }
//! }
//! let local1 = wrap_local0(N)
//! assert(local1.value == N)
//! ```
//!
//! **Variant 1 -- Pair with accessor (i64):**
//! ```vole
//! struct PairLocal0<T> {
//!     first: T
//!     second: T
//! }
//! func make_pair_local0<T>(a: T, b: T) -> PairLocal0<T> {
//!     return PairLocal0<T> { first: a, second: b }
//! }
//! func sum_pair_local0(p: PairLocal0<i64>) -> i64 {
//!     return p.first + p.second
//! }
//! let local1 = make_pair_local0(A, B)
//! assert(sum_pair_local0(local1) == A+B)
//! ```
//!
//! **Variant 2 -- Wrapper with string:**
//! ```vole
//! struct BoxLocal0<T> {
//!     item: T
//! }
//! func box_local0<T>(x: T) -> BoxLocal0<T> {
//!     return BoxLocal0<T> { item: x }
//! }
//! let local1 = box_local0("STR")
//! assert(local1.item == "STR")
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct GenericStructLet;

/// Short strings for the box/string variant.
const BOX_STRS: &[&str] = &["hi", "ok", "ab", "go"];

impl StmtRule for GenericStructLet {
    fn name(&self) -> &'static str {
        "generic_struct_let"
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
            0 => emit_wrapper(scope, emit),
            1 => emit_pair(scope, emit),
            _ => emit_box_string(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0 -- Wrapper with unwrap (i64)
// ---------------------------------------------------------------------------

fn emit_wrapper(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let base = scope.fresh_name();
    let struct_name = format!("Wrapper{}", capitalize(&base));
    let wrap_fn = format!("wrap_{}", base);

    let n = emit.gen_i64_range(1, 100);

    // struct WrapperLocal0<T> { value: T }
    let struct_decl = format!("struct {}<T> {{\n    value: T\n}}", struct_name,);
    scope.add_module_decl(struct_decl);

    // func wrap_local0<T>(x: T) -> WrapperLocal0<T> { return WrapperLocal0<T> { value: x } }
    let fn_decl = format!(
        "func {}<T>(x: T) -> {}<T> {{\n    return {}<T> {{ value: x }}\n}}",
        wrap_fn, struct_name, struct_name,
    );
    scope.add_module_decl(fn_decl);

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}({})\n{}assert({}.value == {})",
        result_name, wrap_fn, n, indent, result_name, n,
    ))
}

// ---------------------------------------------------------------------------
// Variant 1 -- Pair with sum accessor (i64)
// ---------------------------------------------------------------------------

fn emit_pair(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let base = scope.fresh_name();
    let struct_name = format!("Pair{}", capitalize(&base));
    let make_fn = format!("make_pair_{}", base);
    let sum_fn = format!("sum_pair_{}", base);

    let a = emit.gen_i64_range(1, 50);
    let b = emit.gen_i64_range(1, 50);
    let expected = a + b;

    // struct PairLocal0<T> { first: T\n    second: T }
    let struct_decl = format!(
        "struct {}<T> {{\n    first: T\n    second: T\n}}",
        struct_name,
    );
    scope.add_module_decl(struct_decl);

    // func make_pair_local0<T>(a: T, b: T) -> PairLocal0<T> { ... }
    let make_decl = format!(
        "func {}<T>(a: T, b: T) -> {}<T> {{\n    return {}<T> {{ first: a, second: b }}\n}}",
        make_fn, struct_name, struct_name,
    );
    scope.add_module_decl(make_decl);

    // func sum_pair_local0(p: PairLocal0<i64>) -> i64 { ... }
    let sum_decl = format!(
        "func {}(p: {}<i64>) -> i64 {{\n    return p.first + p.second\n}}",
        sum_fn, struct_name,
    );
    scope.add_module_decl(sum_decl);

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}({}, {})\n{}assert({}({}) == {})",
        result_name, make_fn, a, b, indent, sum_fn, result_name, expected,
    ))
}

// ---------------------------------------------------------------------------
// Variant 2 -- Box with string
// ---------------------------------------------------------------------------

fn emit_box_string(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let base = scope.fresh_name();
    let struct_name = format!("Box{}", capitalize(&base));
    let box_fn = format!("box_{}", base);

    let str_idx = emit.gen_range(0..BOX_STRS.len());
    let s = BOX_STRS[str_idx];

    // struct BoxLocal0<T> { item: T }
    let struct_decl = format!("struct {}<T> {{\n    item: T\n}}", struct_name,);
    scope.add_module_decl(struct_decl);

    // func box_local0<T>(x: T) -> BoxLocal0<T> { return BoxLocal0<T> { item: x } }
    let fn_decl = format!(
        "func {}<T>(x: T) -> {}<T> {{\n    return {}<T> {{ item: x }}\n}}",
        box_fn, struct_name, struct_name,
    );
    scope.add_module_decl(fn_decl);

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}(\"{}\")\n{}assert({}.item == \"{}\")",
        result_name, box_fn, s, indent, result_name, s,
    ))
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Capitalize the first character of a string (e.g. "local0" -> "Local0").
fn capitalize(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
    }
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
        assert_eq!(GenericStructLet.name(), "generic_struct_let");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!GenericStructLet.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(GenericStructLet.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!GenericStructLet.precondition(&scope, &params));
    }

    #[test]
    fn generates_wrapper_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = GenericStructLet.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains(".value ==") && !text.contains(".item ==") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        2,
                        "expected 2 module_decls for wrapper variant (struct + wrap fn)"
                    );
                    let struct_decl = &scope.module_decls[0];
                    assert!(
                        struct_decl.contains("<T>"),
                        "expected generic param in struct decl: {struct_decl}"
                    );
                    assert!(
                        struct_decl.contains("value: T"),
                        "expected value field in struct decl: {struct_decl}"
                    );
                    let fn_decl = &scope.module_decls[1];
                    assert!(
                        fn_decl.contains("<T>"),
                        "expected generic param in fn decl: {fn_decl}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated wrapper variant in 100 seeds");
    }

    #[test]
    fn generates_pair_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = GenericStructLet.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("sum_pair_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        3,
                        "expected 3 module_decls for pair variant (struct + make + sum)"
                    );
                    let struct_decl = &scope.module_decls[0];
                    assert!(
                        struct_decl.contains("<T>"),
                        "expected generic param in struct decl: {struct_decl}"
                    );
                    assert!(
                        struct_decl.contains("first: T"),
                        "expected first field in struct decl: {struct_decl}"
                    );
                    assert!(
                        struct_decl.contains("second: T"),
                        "expected second field in struct decl: {struct_decl}"
                    );
                    let sum_decl = &scope.module_decls[2];
                    assert!(
                        sum_decl.contains("-> i64"),
                        "expected i64 return type in sum decl: {sum_decl}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated pair variant in 100 seeds");
    }

    #[test]
    fn generates_box_string_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = GenericStructLet.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains(".item ==") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        2,
                        "expected 2 module_decls for box variant (struct + box fn)"
                    );
                    let struct_decl = &scope.module_decls[0];
                    assert!(
                        struct_decl.contains("<T>"),
                        "expected generic param in struct decl: {struct_decl}"
                    );
                    assert!(
                        struct_decl.contains("item: T"),
                        "expected item field in struct decl: {struct_decl}"
                    );
                    assert!(
                        text.contains("\""),
                        "expected string literal in code: {text}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated box_string variant in 100 seeds");
    }

    #[test]
    fn adds_module_decls() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        GenericStructLet.generate(&mut scope, &mut emit, &test_params());
        assert!(
            scope.module_decls.len() >= 2,
            "expected at least 2 module_decls (struct + helper function(s)), got {}",
            scope.module_decls.len(),
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

        let result = GenericStructLet.generate(&mut scope, &mut emit, &test_params());
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
}
