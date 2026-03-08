//! Rule: generate `is` type checks on optional values.
//!
//! Stresses the `IsCheck` codegen path, type narrowing inside `if x is T`
//! blocks, and optional handling by generating module-level functions that
//! accept an optional parameter and use `is` to narrow it before operating
//! on the unwrapped value.
//!
//! The functions are emitted at module level via [`Scope::add_module_decl`]
//! to keep them in the correct scope for stress-generated programs.
//!
//! **Variant 0 -- `is` check on i64 optional:**
//! ```vole
//! func check_42918(x: i64?) -> i64 {
//!     if x is i64 {
//!         return x + 1
//!     }
//!     return -1
//! }
//! let local0 = check_42918(42)
//! assert(local0 == 43)
//! let local1 = check_42918(nil)
//! assert(local1 == -1)
//! ```
//!
//! **Variant 1 -- `is` check on string optional:**
//! ```vole
//! func describe_42918(x: string?) -> string {
//!     if x is string {
//!         return "got: {x}"
//!     }
//!     return "nothing"
//! }
//! let local0 = describe_42918("hello")
//! assert(local0 == "got: hello")
//! let local1 = describe_42918(nil)
//! assert(local1 == "nothing")
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct IsCheckOptional;

impl StmtRule for IsCheckOptional {
    fn name(&self) -> &'static str {
        "is_check_optional"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Functions must be at module level, not inside class methods
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..2);
        match variant {
            0 => emit_i64_is_check(scope, emit),
            _ => emit_string_is_check(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0: `is` check on i64 optional -- `(i64?) -> i64`
// ---------------------------------------------------------------------------

/// Generate a `check_<N>` function that takes `i64?`, uses `if x is i64`
/// to narrow, and returns `x + offset` when present or `-1` when nil.
fn emit_i64_is_check(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("check_{}", uid);
    let offset = emit.gen_i64_range(1, 10);

    // Module-level function declaration
    let decl = format!(
        concat!(
            "func {}(x: i64?) -> i64 {{\n",
            "    if x is i64 {{\n",
            "        return x + {}\n",
            "    }}\n",
            "    return -1\n",
            "}}"
        ),
        fn_name, offset
    );
    scope.add_module_decl(decl);

    let indent = emit.indent_str();

    let input_val = emit.gen_i64_range(1, 100);
    let expected = input_val + offset;

    let local_hit = scope.fresh_name();
    scope.add_local(
        local_hit.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let local_miss = scope.fresh_name();
    scope.add_local(
        local_miss.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let code = format!(
        "let {hit} = {fn_name}({input})\n\
         {indent}assert({hit} == {expected})\n\
         {indent}let {miss} = {fn_name}(nil)\n\
         {indent}assert({miss} == -1)",
        hit = local_hit,
        fn_name = fn_name,
        input = input_val,
        expected = expected,
        miss = local_miss,
        indent = indent,
    );

    Some(code)
}

// ---------------------------------------------------------------------------
// Variant 1: `is` check on string optional -- `(string?) -> string`
// ---------------------------------------------------------------------------

/// Generate a `describe_<N>` function that takes `string?`, uses
/// `if x is string` to narrow, and returns an interpolation when present
/// or `"nothing"` when nil.
fn emit_string_is_check(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("describe_{}", uid);

    let prefixes = ["got", "found", "saw", "have", "received"];
    let prefix = prefixes[emit.gen_range(0..prefixes.len())];

    // Module-level function declaration
    let decl = format!(
        concat!(
            "func {}(x: string?) -> string {{\n",
            "    if x is string {{\n",
            "        return \"{}: {{x}}\"\n",
            "    }}\n",
            "    return \"nothing\"\n",
            "}}"
        ),
        fn_name, prefix
    );
    scope.add_module_decl(decl);

    let indent = emit.indent_str();

    let words = ["hello", "world", "foo", "bar", "test", "vole"];
    let word = words[emit.gen_range(0..words.len())];

    let local_hit = scope.fresh_name();
    scope.add_local(
        local_hit.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let local_miss = scope.fresh_name();
    scope.add_local(
        local_miss.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let code = format!(
        "let {hit} = {fn_name}(\"{word}\")\n\
         {indent}assert({hit} == \"{prefix}: {word}\")\n\
         {indent}let {miss} = {fn_name}(nil)\n\
         {indent}assert({miss} == \"nothing\")",
        hit = local_hit,
        fn_name = fn_name,
        word = word,
        prefix = prefix,
        miss = local_miss,
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
        assert_eq!(IsCheckOptional.name(), "is_check_optional");
    }

    #[test]
    fn precondition_requires_module_level() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        // No module => precondition fails
        assert!(!IsCheckOptional.precondition(&scope, &params));
        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(IsCheckOptional.precondition(&scope, &params));
        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!IsCheckOptional.precondition(&scope, &params));
    }

    #[test]
    fn generates_i64_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = IsCheckOptional.generate(&mut scope, &mut emit, &params) {
                if text.contains("check_") {
                    found = true;
                    // Verify module decl was registered
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for i64 variant, got {}",
                        scope.module_decls.len()
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("x: i64?"),
                        "expected optional i64 param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("-> i64"),
                        "expected i64 return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("x is i64"),
                        "expected is-check in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return -1"),
                        "expected fallback return in decl: {decl}"
                    );
                    // Inline code should have both value and nil asserts
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    assert!(text.contains("== -1"), "expected -1 check in code: {text}");
                    assert!(text.contains("(nil)"), "expected nil call in code: {text}");
                    // Should have two locals (both i64-typed)
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
        assert!(found, "never generated i64 variant in 100 seeds");
    }

    #[test]
    fn generates_string_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = IsCheckOptional.generate(&mut scope, &mut emit, &params) {
                if text.contains("describe_") {
                    found = true;
                    // Verify module decl was registered
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for string variant, got {}",
                        scope.module_decls.len()
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("x: string?"),
                        "expected optional string param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("-> string"),
                        "expected string return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("x is string"),
                        "expected is-check in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return \"nothing\""),
                        "expected fallback return in decl: {decl}"
                    );
                    // Inline code should have both value and nil asserts
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    assert!(
                        text.contains("\"nothing\""),
                        "expected nothing check in code: {text}"
                    );
                    assert!(text.contains("(nil)"), "expected nil call in code: {text}");
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
        assert!(found, "never generated string variant in 100 seeds");
    }

    #[test]
    fn adds_correct_typed_locals() {
        let table = SymbolTable::new();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = IsCheckOptional.generate(&mut scope, &mut emit, &params) {
                assert_eq!(
                    scope.locals.len(),
                    2,
                    "expected 2 locals added to scope, got {}",
                    scope.locals.len()
                );
                if text.contains("check_") {
                    // i64 variant: both locals should be i64
                    for (name, ty, _) in &scope.locals {
                        assert_eq!(
                            *ty,
                            TypeInfo::Primitive(PrimitiveType::I64),
                            "expected i64 type for local '{}', got {:?}",
                            name,
                            ty
                        );
                    }
                } else {
                    // string variant: both locals should be string
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
                return;
            }
        }
        panic!("never generated output in 50 seeds");
    }

    #[test]
    fn exercises_both_variants() {
        let table = SymbolTable::new();
        let mut saw_i64 = false;
        let mut saw_string = false;

        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = IsCheckOptional.generate(&mut scope, &mut emit, &params) {
                if text.contains("check_") {
                    saw_i64 = true;
                }
                if text.contains("describe_") {
                    saw_string = true;
                }
            }

            if saw_i64 && saw_string {
                break;
            }
        }

        assert!(saw_i64, "never generated i64 variant in 200 seeds");
        assert!(saw_string, "never generated string variant in 200 seeds");
    }
}
