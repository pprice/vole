//! Rule: generate generic functions that use string interpolation with type
//! parameters.
//!
//! Stresses the intersection of generics monomorphization and
//! `StringConversion` annotation.  A real compiler bug was found and fixed in
//! this exact area (commit d8456670 -- generic string interpolation reused
//! the first monomorph's `StringConversion`).
//!
//! The generic function is emitted at module level via
//! [`Scope::add_module_decl`] because nested `func<T>` is not supported.
//! Each variant calls the generic function with at least two different
//! concrete types (i64 and string) to force different monomorphizations.
//!
//! **Variant 0 -- generic function with interpolation:**
//! ```vole
//! func describe_42918<T>(x: T) -> string {
//!     return "{x}"
//! }
//! let local0 = describe_42918(42)
//! let local1 = describe_42918("hello")
//! ```
//!
//! **Variant 1 -- generic function with interpolation + extra string param:**
//! ```vole
//! func wrap_42918<T>(x: T, label: string) -> string {
//!     return "{label}: {x}"
//! }
//! let local0 = wrap_42918(99, "count")
//! let local1 = wrap_42918("world", "tag")
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct GenericInterpolation;

impl StmtRule for GenericInterpolation {
    fn name(&self) -> &'static str {
        "generic_interpolation"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Generic functions must be at module level, not inside class methods
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..2);
        match variant {
            0 => emit_describe_variant(scope, emit),
            _ => emit_wrap_variant(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0: generic function with interpolation -- `(T) -> string`
// ---------------------------------------------------------------------------

/// Generate a generic `describe_<N>` function at module level and call it
/// with both an i64 and a string argument to force different monomorphizations
/// of the `StringConversion` path.
fn emit_describe_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("describe_{}", uid);

    // Module-level generic function declaration
    let decl = format!(
        concat!(
            "func {}<T>(x: T) -> string {{\n",
            "    return \"{{x}}\"\n",
            "}}"
        ),
        fn_name
    );
    scope.add_module_decl(decl);

    let indent = emit.indent_str();

    // Call 1: i64 argument
    let i64_val = emit.gen_i64_range(1, 200);
    let local_i64 = scope.fresh_name();
    scope.add_local(
        local_i64.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    // Call 2: string argument
    let words = ["hello", "world", "foo", "bar", "test", "vole"];
    let word = words[emit.gen_range(0..words.len())];
    let local_str = scope.fresh_name();
    scope.add_local(
        local_str.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let code = format!(
        "let {li} = {fn_name}({ival})\n\
         {indent}assert({li} == \"{ival}\")\n\
         {indent}let {ls} = {fn_name}(\"{word}\")\n\
         {indent}assert({ls} == \"{word}\")",
        li = local_i64,
        fn_name = fn_name,
        ival = i64_val,
        ls = local_str,
        word = word,
        indent = indent,
    );

    Some(code)
}

// ---------------------------------------------------------------------------
// Variant 1: generic function with interpolation + extra string param
// ---------------------------------------------------------------------------

/// Generate a generic `wrap_<N>` function at module level and call it
/// with both an i64 and a string argument to force different monomorphizations.
fn emit_wrap_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("wrap_{}", uid);

    // Module-level generic function declaration
    let decl = format!(
        concat!(
            "func {}<T>(x: T, label: string) -> string {{\n",
            "    return \"{{label}}: {{x}}\"\n",
            "}}"
        ),
        fn_name
    );
    scope.add_module_decl(decl);

    let indent = emit.indent_str();

    // Call 1: i64 argument
    let i64_val = emit.gen_i64_range(1, 200);
    let labels = ["count", "num", "score", "total", "amount"];
    let label1 = labels[emit.gen_range(0..labels.len())];
    let local_i64 = scope.fresh_name();
    scope.add_local(
        local_i64.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    // Call 2: string argument
    let words = ["world", "hello", "vole", "test", "data"];
    let word = words[emit.gen_range(0..words.len())];
    let tags = ["tag", "key", "label", "name", "item"];
    let label2 = tags[emit.gen_range(0..tags.len())];
    let local_str = scope.fresh_name();
    scope.add_local(
        local_str.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let code = format!(
        "let {li} = {fn_name}({ival}, \"{lab1}\")\n\
         {indent}assert({li} == \"{lab1}: {ival}\")\n\
         {indent}let {ls} = {fn_name}(\"{word}\", \"{lab2}\")\n\
         {indent}assert({ls} == \"{lab2}: {word}\")",
        li = local_i64,
        fn_name = fn_name,
        ival = i64_val,
        lab1 = label1,
        ls = local_str,
        word = word,
        lab2 = label2,
        indent = indent,
    );

    Some(code)
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

    #[test]
    fn name_is_correct() {
        assert_eq!(GenericInterpolation.name(), "generic_interpolation");
    }

    #[test]
    fn precondition_requires_module_level() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        // No module => precondition fails
        assert!(!GenericInterpolation.precondition(&scope, &params));
        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(GenericInterpolation.precondition(&scope, &params));
        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!GenericInterpolation.precondition(&scope, &params));
    }

    #[test]
    fn generates_describe_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericInterpolation.generate(&mut scope, &mut emit, &params) {
                if text.contains("describe_") {
                    found = true;
                    // Verify module decl was registered
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for describe variant, got {}",
                        scope.module_decls.len()
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
                    assert!(
                        decl.contains("{x}"),
                        "expected interpolation in decl: {decl}"
                    );
                    // Inline code should call with both i64 and string
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    // Should have two locals (both string-typed)
                    assert_eq!(
                        scope.locals.len(),
                        2,
                        "expected 2 locals, got {}",
                        scope.locals.len()
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated describe variant in 100 seeds");
    }

    #[test]
    fn generates_wrap_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericInterpolation.generate(&mut scope, &mut emit, &params) {
                if text.contains("wrap_") {
                    found = true;
                    // Verify module decl was registered
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for wrap variant, got {}",
                        scope.module_decls.len()
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("<T>"),
                        "expected generic type param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("label: string"),
                        "expected label param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("{label}"),
                        "expected label interpolation in decl: {decl}"
                    );
                    assert!(
                        decl.contains("{x}"),
                        "expected x interpolation in decl: {decl}"
                    );
                    // Inline code should call with both i64 and string
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    // Should have two locals (both string-typed)
                    assert_eq!(
                        scope.locals.len(),
                        2,
                        "expected 2 locals, got {}",
                        scope.locals.len()
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated wrap variant in 100 seeds");
    }

    #[test]
    fn adds_string_locals_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = GenericInterpolation.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        // Both variants add 2 locals
        assert_eq!(
            scope.locals.len(),
            2,
            "expected 2 locals added to scope, got {}",
            scope.locals.len()
        );
        // Both should be string types
        for (name, ty, _) in &scope.locals {
            assert_eq!(
                *ty,
                TypeInfo::Primitive(PrimitiveType::String),
                "expected string type for local '{}', got {:?}",
                name,
                ty
            );
        }
    }

    #[test]
    fn calls_with_both_i64_and_string() {
        let table = SymbolTable::new();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericInterpolation.generate(&mut scope, &mut emit, &params) {
                // The first call should pass an integer literal (bare number)
                // The second call should pass a string literal (quoted)
                // Both variants follow this pattern
                let lines: Vec<&str> = text.lines().collect();
                // First line: `let localN = fn_name(NUMBER)` or `let localN = fn_name(NUMBER, "label")`
                let first_let = lines[0];
                assert!(
                    first_let.starts_with("let "),
                    "expected let binding: {first_let}"
                );
                // There should be a call with a quoted string argument somewhere
                let has_string_call = text.contains("(\"");
                assert!(
                    has_string_call,
                    "expected call with string argument in code: {text}"
                );
                return;
            }
        }
        panic!("never generated output in 50 seeds");
    }
}
