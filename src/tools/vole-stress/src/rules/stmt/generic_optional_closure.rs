//! Rule: generate generic functions combining optionals, closures, and generics.
//!
//! Stresses the intersection of generics with closures and optional return
//! types by generating module-level generic functions that use all three
//! features simultaneously, forcing the compiler to handle monomorphization,
//! optional wrapping, and closure typing in concert.
//!
//! The generic functions are emitted at module level via
//! [`Scope::add_module_decl`] because nested `func<T>` is rewritten to
//! `let = lambda` by vole-fmt, and lambdas don't support type parameters.
//!
//! **Variant 0 -- generic find with predicate:**
//! ```vole
//! func find_first_42918<T>(items: [T], predicate: (T) -> bool) -> T? {
//!     for item in items {
//!         if predicate(item) {
//!             return item
//!         }
//!     }
//!     return nil
//! }
//! let result_42918 = find_first_42918([1, 2, 3, 4, 5], (x: i64) => x > 3)
//! assert(result_42918 != nil)
//! ```
//!
//! **Variant 1 -- generic apply_if with condition:**
//! ```vole
//! func apply_if_42918<T>(x: T, condition: bool, f: (T) -> T) -> T {
//!     if condition {
//!         return f(x)
//!     }
//!     return x
//! }
//! let result_42918 = apply_if_42918(42, true, (x: i64) => x * 2)
//! assert(result_42918 == 84)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct GenericOptionalClosure;

impl StmtRule for GenericOptionalClosure {
    fn name(&self) -> &'static str {
        "generic_optional_closure"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Generic functions must be at module level, not inside class methods
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..2);
        match variant {
            0 => emit_find_first_variant(scope, emit),
            _ => emit_apply_if_variant(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0: generic find_first -- `([T], (T) -> bool) -> T?`
// ---------------------------------------------------------------------------

/// Generate a generic `find_first_<N>` function at module level and call it
/// with an i64 array and a predicate closure.
///
/// ```vole
/// func find_first_42918<T>(items: [T], predicate: (T) -> bool) -> T? {
///     for item in items {
///         if predicate(item) {
///             return item
///         }
///     }
///     return nil
/// }
/// let result_42918 = find_first_42918([1, 2, 3, 4, 5], (x: i64) => x > 3)
/// assert(result_42918 != nil)
/// ```
fn emit_find_first_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("find_first_{}", uid);

    // Module-level generic function declaration
    let decl = format!(
        "func {}<T>(items: [T], predicate: (T) -> bool) -> T? {{\n\
         \x20   for item in items {{\n\
         \x20       if predicate(item) {{\n\
         \x20           return item\n\
         \x20       }}\n\
         \x20   }}\n\
         \x20   return nil\n\
         }}",
        fn_name
    );
    scope.add_module_decl(decl);

    // Generate an array of small positive integers where at least one matches
    let threshold = emit.gen_i64_range(2, 8);
    let len = emit.gen_range(3..6);
    let elems: Vec<i64> = (1..=len as i64).collect();
    let array_str = format!(
        "[{}]",
        elems
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join(", ")
    );

    let result_name = format!("result_{}", uid);

    // Do NOT add result to scope -- it's T? (optional), complex type
    let indent = emit.indent_str();
    let code = format!(
        "let {rn} = {fn_name}({array}, (x: i64) => x > {threshold})\n\
         {indent}assert({rn} != nil)",
        rn = result_name,
        fn_name = fn_name,
        array = array_str,
        threshold = threshold,
        indent = indent,
    );

    Some(code)
}

// ---------------------------------------------------------------------------
// Variant 1: generic apply_if -- `(T, bool, (T) -> T) -> T`
// ---------------------------------------------------------------------------

/// Generate a generic `apply_if_<N>` function at module level and call it
/// with a concrete i64 value, a `true` condition, and a closure.
///
/// ```vole
/// func apply_if_42918<T>(x: T, condition: bool, f: (T) -> T) -> T {
///     if condition {
///         return f(x)
///     }
///     return x
/// }
/// let result_42918 = apply_if_42918(42, true, (x: i64) => x * 2)
/// assert(result_42918 == 84)
/// ```
fn emit_apply_if_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("apply_if_{}", uid);

    // Module-level generic function declaration
    let decl = format!(
        "func {}<T>(x: T, condition: bool, f: (T) -> T) -> T {{\n\
         \x20   if condition {{\n\
         \x20       return f(x)\n\
         \x20   }}\n\
         \x20   return x\n\
         }}",
        fn_name
    );
    scope.add_module_decl(decl);

    // Pick an input value and a closure operation
    let input_val = emit.gen_i64_range(1, 50);
    let (closure, expected) = pick_apply_if_closure(emit, input_val);

    let result_name = format!("result_{}", uid);
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();
    let code = format!(
        "let {rn} = {fn_name}({input}, true, {closure})\n\
         {indent}assert({rn} == {expected})",
        rn = result_name,
        fn_name = fn_name,
        input = input_val,
        closure = closure,
        expected = expected,
        indent = indent,
    );

    Some(code)
}

/// Pick a closure and compute the expected result for the apply_if variant.
fn pick_apply_if_closure(emit: &mut Emit, input: i64) -> (String, i64) {
    let op = emit.gen_range(0..3);
    match op {
        0 => {
            // multiplication
            let factor = emit.gen_i64_range(2, 5);
            (format!("(x: i64) => x * {}", factor), input * factor)
        }
        1 => {
            // addition
            let addend = emit.gen_i64_range(1, 20);
            (format!("(x: i64) => x + {}", addend), input + addend)
        }
        _ => {
            // subtraction
            let subtrahend = emit.gen_i64_range(1, 10);
            (
                format!("(x: i64) => x - {}", subtrahend),
                input - subtrahend,
            )
        }
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

    #[test]
    fn name_is_correct() {
        assert_eq!(GenericOptionalClosure.name(), "generic_optional_closure");
    }

    #[test]
    fn precondition_requires_module_level() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        // No module => precondition fails
        assert!(!GenericOptionalClosure.precondition(&scope, &params));
        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(GenericOptionalClosure.precondition(&scope, &params));
        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!GenericOptionalClosure.precondition(&scope, &params));
    }

    #[test]
    fn generates_find_first_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericOptionalClosure.generate(&mut scope, &mut emit, &params) {
                if text.contains("find_first_") {
                    found = true;
                    // Verify module decl was registered
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for find_first variant, got {}",
                        scope.module_decls.len()
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("<T>"),
                        "expected generic type param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("predicate: (T) -> bool"),
                        "expected predicate param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("-> T?"),
                        "expected optional return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return nil"),
                        "expected nil fallback in decl: {decl}"
                    );
                    // Inline code should have assert with != nil
                    assert!(
                        text.contains("assert(") && text.contains("!= nil"),
                        "expected assert with != nil in code: {text}"
                    );
                    // Inline code should have typed closure
                    assert!(
                        text.contains("(x: i64) =>"),
                        "expected typed closure in code: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated find_first variant in 100 seeds");
    }

    #[test]
    fn generates_apply_if_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericOptionalClosure.generate(&mut scope, &mut emit, &params) {
                if text.contains("apply_if_") {
                    found = true;
                    // Verify module decl was registered
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for apply_if variant, got {}",
                        scope.module_decls.len()
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("<T>"),
                        "expected generic type param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("condition: bool"),
                        "expected condition param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("f: (T) -> T"),
                        "expected closure param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return f(x)"),
                        "expected apply body in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return x"),
                        "expected identity fallback in decl: {decl}"
                    );
                    // Inline code should have assert with ==
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    assert!(
                        text.contains("== "),
                        "expected equality check in code: {text}"
                    );
                    // Inline code should have typed closure
                    assert!(
                        text.contains("(x: i64) =>"),
                        "expected typed closure in code: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated apply_if variant in 100 seeds");
    }

    #[test]
    fn find_first_does_not_add_result_to_scope() {
        let table = SymbolTable::new();
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericOptionalClosure.generate(&mut scope, &mut emit, &params) {
                if text.contains("find_first_") {
                    assert!(
                        scope.locals.is_empty(),
                        "find_first variant should not add result to scope (it's T?)"
                    );
                    return;
                }
            }
        }
        panic!("never generated find_first variant in 100 seeds");
    }

    #[test]
    fn apply_if_adds_result_to_scope() {
        let table = SymbolTable::new();
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericOptionalClosure.generate(&mut scope, &mut emit, &params) {
                if text.contains("apply_if_") {
                    assert!(
                        !scope.locals.is_empty(),
                        "apply_if variant should add result to scope"
                    );
                    let result_local = scope.locals.last().expect("should add result local");
                    assert_eq!(
                        result_local.1,
                        TypeInfo::Primitive(PrimitiveType::I64),
                        "result type must be i64"
                    );
                    return;
                }
            }
        }
        panic!("never generated apply_if variant in 100 seeds");
    }

    #[test]
    fn result_names_use_uid() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(7);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        if let Some(text) = GenericOptionalClosure.generate(&mut scope, &mut emit, &params) {
            // Result name should match `result_NNNNN` pattern
            assert!(
                text.contains("result_"),
                "expected result_ prefix in code: {text}"
            );
        }
    }
}
