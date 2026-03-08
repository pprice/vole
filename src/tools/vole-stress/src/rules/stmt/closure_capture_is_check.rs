//! Rule: generate closures that capture optional values and use `is` type
//! checks inside the closure body.
//!
//! This pattern stresses the intersection of closure capture and union
//! narrowing -- a real compiler bug (vol-gedw, fixed in 3f8cbee8) was found
//! where closure capture of optionals read stale stack data and missed union
//! narrowing.
//!
//! The outer function is emitted at module level via [`Scope::add_module_decl`]
//! because nested `func` declarations get reformatted to lambdas by vole-fmt,
//! and we want the function body to contain a closure that captures the
//! optional local.
//!
//! **Variant 0 -- closure capturing `i64?` with is-check:**
//! ```vole
//! func check_42918() -> i64 {
//!     let x: i64? = 42
//!     let checker = () -> i64 => {
//!         if x is i64 {
//!             return x + 3
//!         }
//!         return -1
//!     }
//!     return checker()
//! }
//! let local0 = check_42918()
//! assert(local0 == 45)
//! ```
//!
//! **Variant 1 -- closure capturing `string?` with is-check:**
//! ```vole
//! func describe_42918() -> string {
//!     let name: string? = "hello"
//!     let describe = () -> string => {
//!         if name is string {
//!             return "got: {name}"
//!         }
//!         return "nothing"
//!     }
//!     return describe()
//! }
//! let local0 = describe_42918()
//! assert(local0 == "got: hello")
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ClosureCaptureIsCheck;

impl StmtRule for ClosureCaptureIsCheck {
    fn name(&self) -> &'static str {
        "closure_capture_is_check"
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
            0 => emit_i64_closure_is_check(scope, emit),
            _ => emit_string_closure_is_check(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0: closure capturing `i64?` with is-check
// ---------------------------------------------------------------------------

/// Generate a `check_<N>` function at module level that declares a local
/// `i64?`, captures it in a closure, and uses `if x is i64` inside the
/// closure body.  The call site asserts the expected result.
fn emit_i64_closure_is_check(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("check_{}", uid);
    let input_val = emit.gen_i64_range(1, 100);
    let offset = emit.gen_i64_range(1, 10);
    let expected = input_val + offset;

    // Module-level function declaration with closure capturing optional
    let decl = format!(
        concat!(
            "func {}() -> i64 {{\n",
            "    let x: i64? = {}\n",
            "    let checker = () -> i64 => {{\n",
            "        if x is i64 {{\n",
            "            return x + {}\n",
            "        }}\n",
            "        return -1\n",
            "    }}\n",
            "    return checker()\n",
            "}}"
        ),
        fn_name, input_val, offset
    );
    scope.add_module_decl(decl);

    let indent = emit.indent_str();

    let local = scope.fresh_name();
    scope.add_local(
        local.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let code = format!(
        "let {local} = {fn_name}()\n\
         {indent}assert({local} == {expected})",
        local = local,
        fn_name = fn_name,
        expected = expected,
        indent = indent,
    );

    Some(code)
}

// ---------------------------------------------------------------------------
// Variant 1: closure capturing `string?` with is-check
// ---------------------------------------------------------------------------

/// Generate a `describe_<N>` function at module level that declares a local
/// `string?`, captures it in a closure, and uses `if name is string` inside
/// the closure body.  The call site asserts the expected interpolated result.
fn emit_string_closure_is_check(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("describe_{}", uid);

    let words = ["hello", "world", "foo", "bar", "test", "vole"];
    let word = words[emit.gen_range(0..words.len())];

    // Module-level function declaration with closure capturing optional
    let decl = format!(
        concat!(
            "func {}() -> string {{\n",
            "    let name: string? = \"{}\"\n",
            "    let describe = () -> string => {{\n",
            "        if name is string {{\n",
            "            return \"got: {{name}}\"\n",
            "        }}\n",
            "        return \"nothing\"\n",
            "    }}\n",
            "    return describe()\n",
            "}}"
        ),
        fn_name, word
    );
    scope.add_module_decl(decl);

    let indent = emit.indent_str();

    let local = scope.fresh_name();
    scope.add_local(
        local.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let code = format!(
        "let {local} = {fn_name}()\n\
         {indent}assert({local} == \"got: {word}\")",
        local = local,
        fn_name = fn_name,
        word = word,
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
        assert_eq!(ClosureCaptureIsCheck.name(), "closure_capture_is_check");
    }

    #[test]
    fn precondition_requires_module_level() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        // No module => precondition fails
        assert!(!ClosureCaptureIsCheck.precondition(&scope, &params));
        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(ClosureCaptureIsCheck.precondition(&scope, &params));
        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!ClosureCaptureIsCheck.precondition(&scope, &params));
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

            if let Some(text) = ClosureCaptureIsCheck.generate(&mut scope, &mut emit, &params) {
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
                        decl.contains("let x: i64?"),
                        "expected optional i64 local in decl: {decl}"
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
                        decl.contains("() -> i64 =>"),
                        "expected closure signature in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return checker()"),
                        "expected closure call in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return -1"),
                        "expected fallback return in decl: {decl}"
                    );
                    // Inline code should have assert
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    // Should have one local (i64-typed)
                    assert_eq!(
                        scope.locals.len(),
                        1,
                        "expected 1 local, got {}",
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

            if let Some(text) = ClosureCaptureIsCheck.generate(&mut scope, &mut emit, &params) {
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
                        decl.contains("let name: string?"),
                        "expected optional string local in decl: {decl}"
                    );
                    assert!(
                        decl.contains("-> string"),
                        "expected string return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("name is string"),
                        "expected is-check in decl: {decl}"
                    );
                    assert!(
                        decl.contains("() -> string =>"),
                        "expected closure signature in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return describe()"),
                        "expected closure call in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return \"nothing\""),
                        "expected fallback return in decl: {decl}"
                    );
                    // Inline code should have assert
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    assert!(
                        text.contains("\"got: "),
                        "expected interpolated result in code: {text}"
                    );
                    // Should have one local (string-typed)
                    assert_eq!(
                        scope.locals.len(),
                        1,
                        "expected 1 local, got {}",
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

            if let Some(text) = ClosureCaptureIsCheck.generate(&mut scope, &mut emit, &params) {
                assert_eq!(
                    scope.locals.len(),
                    1,
                    "expected 1 local added to scope, got {}",
                    scope.locals.len()
                );
                if text.contains("check_") {
                    let (name, ty, _) = &scope.locals[0];
                    assert_eq!(
                        *ty,
                        TypeInfo::Primitive(PrimitiveType::I64),
                        "expected i64 type for local '{}', got {:?}",
                        name,
                        ty
                    );
                } else {
                    let (name, ty, _) = &scope.locals[0];
                    assert_eq!(
                        *ty,
                        TypeInfo::Primitive(PrimitiveType::String),
                        "expected string type for local '{}', got {:?}",
                        name,
                        ty
                    );
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

            if let Some(text) = ClosureCaptureIsCheck.generate(&mut scope, &mut emit, &params) {
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
