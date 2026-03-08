//! Rule: generate generic functions with optional return types.
//!
//! Stresses the intersection of generics with optional/nil handling by
//! generating module-level generic functions that return `T?` and calling
//! them with concrete arguments that exercise both the value and nil paths.
//!
//! The generic functions are emitted at module level via
//! [`Scope::add_module_decl`] because nested `func<T>` is rewritten to
//! `let = lambda` by vole-fmt, and lambdas don't support type parameters.
//!
//! **Variant 0 -- generic find:**
//! ```vole
//! func find_first_42918<T>(items: [T], pred: (T) -> bool) -> T? {
//!     for item in items {
//!         if pred(item) {
//!             return item
//!         }
//!     }
//!     return nil
//! }
//! let found_42918 = find_first_42918([1, 2, 3, 4], (x: i64) => x > 2)
//! assert(found_42918 == 3)
//! let missed_42918 = find_first_42918([1, 2, 3], (x: i64) => x > 10)
//! assert(missed_42918 == nil)
//! ```
//!
//! **Variant 1 -- generic conditional transform:**
//! ```vole
//! func maybe_transform_42918<T>(v: T, flag: bool) -> T? {
//!     if flag {
//!         return v
//!     }
//!     return nil
//! }
//! let got_42918 = maybe_transform_42918(42, true)
//! assert(got_42918 == 42)
//! let missed_42918 = maybe_transform_42918(42, false)
//! assert(missed_42918 == nil)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct GenericOptionalReturn;

impl StmtRule for GenericOptionalReturn {
    fn name(&self) -> &'static str {
        "generic_optional_return"
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
            0 => emit_find_variant(scope, emit),
            _ => emit_transform_variant(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Concrete type selection
// ---------------------------------------------------------------------------

/// Pick a concrete type to instantiate the generic with, returning the
/// type annotation string, a sample value, a "not found" predicate, and
/// the expected found value.
enum ConcreteType {
    I64,
    String,
    Bool,
}

fn pick_concrete_type(emit: &mut Emit) -> ConcreteType {
    match emit.gen_range(0..3) {
        0 => ConcreteType::I64,
        1 => ConcreteType::String,
        _ => ConcreteType::Bool,
    }
}

// ---------------------------------------------------------------------------
// Variant 0: generic find -- `([T], (T) -> bool) -> T?`
// ---------------------------------------------------------------------------

/// Generate a generic `find_first_<N>` function at module level and call it
/// with concrete arguments that exercise both the value and nil return paths.
fn emit_find_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("find_first_{}", uid);

    // Module-level generic function declaration
    let decl = format!(
        concat!(
            "func {}<T>(items: [T], pred: (T) -> bool) -> T? {{\n",
            "    for item in items {{\n",
            "        if pred(item) {{\n",
            "            return item\n",
            "        }}\n",
            "    }}\n",
            "    return nil\n",
            "}}"
        ),
        fn_name
    );
    scope.add_module_decl(decl);

    let indent = emit.indent_str();

    let concrete = pick_concrete_type(emit);
    let code = match concrete {
        ConcreteType::I64 => {
            let (array_lit, pred_match, expected, pred_miss) = pick_i64_find(emit);
            let found_name = format!("found_{}", uid);
            let missed_name = format!("missed_{}", uid);

            scope.add_local(
                found_name.clone(),
                TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                false,
            );
            scope.add_local(
                missed_name.clone(),
                TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                false,
            );

            format!(
                "let {found} = {fn_name}({array}, {pred_match})\n\
                 {indent}assert({found} == {expected})\n\
                 {indent}let {missed} = {fn_name}({array}, {pred_miss})\n\
                 {indent}assert({missed} == nil)",
                found = found_name,
                fn_name = fn_name,
                array = array_lit,
                pred_match = pred_match,
                expected = expected,
                pred_miss = pred_miss,
                missed = missed_name,
                indent = indent,
            )
        }
        ConcreteType::String => {
            let found_name = format!("found_{}", uid);
            let missed_name = format!("missed_{}", uid);

            scope.add_local(
                found_name.clone(),
                TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                false,
            );
            scope.add_local(
                missed_name.clone(),
                TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                false,
            );

            format!(
                "let {found} = {fn_name}([\"apple\", \"banana\", \"cherry\"], (x: string) => x.length() > 5)\n\
                 {indent}assert({found} == \"banana\")\n\
                 {indent}let {missed} = {fn_name}([\"a\", \"bb\"], (x: string) => x.length() > 5)\n\
                 {indent}assert({missed} == nil)",
                found = found_name,
                fn_name = fn_name,
                missed = missed_name,
                indent = indent,
            )
        }
        ConcreteType::Bool => {
            let found_name = format!("found_{}", uid);
            let missed_name = format!("missed_{}", uid);

            scope.add_local(
                found_name.clone(),
                TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::Bool))),
                false,
            );
            scope.add_local(
                missed_name.clone(),
                TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::Bool))),
                false,
            );

            format!(
                "let {found} = {fn_name}([false, true, false], (x: bool) => x)\n\
                 {indent}assert({found} == true)\n\
                 {indent}let {missed} = {fn_name}([false, false], (x: bool) => x)\n\
                 {indent}assert({missed} == nil)",
                found = found_name,
                fn_name = fn_name,
                missed = missed_name,
                indent = indent,
            )
        }
    };

    Some(code)
}

/// Pick an i64 find scenario: (array_literal, match_predicate, expected_value, miss_predicate).
fn pick_i64_find(emit: &mut Emit) -> (String, String, i64, String) {
    let op = emit.gen_range(0..3);
    match op {
        0 => {
            // Find first value > threshold
            let threshold = emit.gen_i64_range(2, 8);
            let elems: Vec<i64> = (1..=5).collect();
            let expected = elems.iter().copied().find(|&x| x > threshold).unwrap_or(5);
            let array_str = format!(
                "[{}]",
                elems
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            (
                array_str,
                format!("(x: i64) => x > {}", threshold),
                expected,
                "(x: i64) => x > 100".to_string(),
            )
        }
        1 => {
            // Find first even/odd value
            let elems: Vec<i64> = vec![1, 3, 5, 6, 8];
            let expected = 6; // first even
            let array_str = format!(
                "[{}]",
                elems
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            (
                array_str,
                "(x: i64) => x % 2 == 0".to_string(),
                expected,
                "(x: i64) => x > 100".to_string(),
            )
        }
        _ => {
            // Find specific value
            let target = emit.gen_i64_range(1, 10);
            let mut elems: Vec<i64> = (1..=5).collect();
            if !elems.contains(&target) {
                elems.push(target);
            }
            let array_str = format!(
                "[{}]",
                elems
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            (
                array_str,
                format!("(x: i64) => x == {}", target),
                target,
                "(x: i64) => x == 999".to_string(),
            )
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 1: generic conditional transform -- `(T, bool) -> T?`
// ---------------------------------------------------------------------------

/// Generate a generic `maybe_transform_<N>` function at module level and
/// call it with both `true` (returns value) and `false` (returns nil).
fn emit_transform_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("maybe_transform_{}", uid);

    // Module-level generic function declaration
    let decl = format!(
        concat!(
            "func {}<T>(v: T, flag: bool) -> T? {{\n",
            "    if flag {{\n",
            "        return v\n",
            "    }}\n",
            "    return nil\n",
            "}}"
        ),
        fn_name
    );
    scope.add_module_decl(decl);

    let indent = emit.indent_str();

    let concrete = pick_concrete_type(emit);
    let code = match concrete {
        ConcreteType::I64 => {
            let input_val = emit.gen_i64_range(1, 50);
            let got_name = format!("got_{}", uid);
            let missed_name = format!("missed_{}", uid);

            scope.add_local(
                got_name.clone(),
                TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                false,
            );
            scope.add_local(
                missed_name.clone(),
                TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                false,
            );

            format!(
                "let {got} = {fn_name}({input}, true)\n\
                 {indent}assert({got} == {input})\n\
                 {indent}let {missed} = {fn_name}({input}, false)\n\
                 {indent}assert({missed} == nil)",
                got = got_name,
                fn_name = fn_name,
                input = input_val,
                missed = missed_name,
                indent = indent,
            )
        }
        ConcreteType::String => {
            let got_name = format!("got_{}", uid);
            let missed_name = format!("missed_{}", uid);

            scope.add_local(
                got_name.clone(),
                TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                false,
            );
            scope.add_local(
                missed_name.clone(),
                TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                false,
            );

            let words = ["hello", "world", "foo", "bar", "test"];
            let word = words[emit.gen_range(0..words.len())];

            format!(
                "let {got} = {fn_name}(\"{word}\", true)\n\
                 {indent}assert({got} == \"{word}\")\n\
                 {indent}let {missed} = {fn_name}(\"{word}\", false)\n\
                 {indent}assert({missed} == nil)",
                got = got_name,
                fn_name = fn_name,
                word = word,
                missed = missed_name,
                indent = indent,
            )
        }
        ConcreteType::Bool => {
            let got_name = format!("got_{}", uid);
            let missed_name = format!("missed_{}", uid);

            scope.add_local(
                got_name.clone(),
                TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::Bool))),
                false,
            );
            scope.add_local(
                missed_name.clone(),
                TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::Bool))),
                false,
            );

            format!(
                "let {got} = {fn_name}(true, true)\n\
                 {indent}assert({got} == true)\n\
                 {indent}let {missed} = {fn_name}(true, false)\n\
                 {indent}assert({missed} == nil)",
                got = got_name,
                fn_name = fn_name,
                missed = missed_name,
                indent = indent,
            )
        }
    };

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
        assert_eq!(GenericOptionalReturn.name(), "generic_optional_return");
    }

    #[test]
    fn precondition_requires_module_level() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        // No module => precondition fails
        assert!(!GenericOptionalReturn.precondition(&scope, &params));
        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(GenericOptionalReturn.precondition(&scope, &params));
        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!GenericOptionalReturn.precondition(&scope, &params));
    }

    #[test]
    fn generates_find_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericOptionalReturn.generate(&mut scope, &mut emit, &params) {
                if text.contains("find_first_") {
                    found = true;
                    // Verify module decl was registered
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for find variant, got {}",
                        scope.module_decls.len()
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("<T>"),
                        "expected generic type param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("-> T?"),
                        "expected optional return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return nil"),
                        "expected nil return path in decl: {decl}"
                    );
                    // Inline code should have both value and nil asserts
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    assert!(
                        text.contains("== nil"),
                        "expected nil check in code: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated find variant in 100 seeds");
    }

    #[test]
    fn generates_transform_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericOptionalReturn.generate(&mut scope, &mut emit, &params) {
                if text.contains("maybe_transform_") {
                    found = true;
                    // Verify module decl was registered
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for transform variant, got {}",
                        scope.module_decls.len()
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("<T>"),
                        "expected generic type param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("-> T?"),
                        "expected optional return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return nil"),
                        "expected nil return path in decl: {decl}"
                    );
                    // Inline code: value path and nil path
                    assert!(text.contains("true)"), "expected true call in code: {text}");
                    assert!(
                        text.contains("false)"),
                        "expected false call in code: {text}"
                    );
                    assert!(
                        text.contains("== nil"),
                        "expected nil check in code: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated transform variant in 100 seeds");
    }

    #[test]
    fn adds_result_locals_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = GenericOptionalReturn.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        // Both variants add 2 locals (found + missed, or got + missed)
        assert_eq!(
            scope.locals.len(),
            2,
            "expected 2 locals added to scope, got {}",
            scope.locals.len()
        );
        // Both should be optional types
        for (name, ty, _) in &scope.locals {
            assert!(
                matches!(ty, TypeInfo::Optional(_)),
                "expected optional type for local '{}', got {:?}",
                name,
                ty
            );
        }
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

        if let Some(text) = GenericOptionalReturn.generate(&mut scope, &mut emit, &params) {
            // Result names should contain uid-based suffix
            assert!(
                text.contains("found_") || text.contains("got_"),
                "expected uid-based result name in code: {text}"
            );
            assert!(
                text.contains("missed_"),
                "expected uid-based missed name in code: {text}"
            );
        }
    }

    #[test]
    fn exercises_all_concrete_types() {
        let table = SymbolTable::new();
        let mut saw_i64 = false;
        let mut saw_string = false;
        let mut saw_bool = false;

        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericOptionalReturn.generate(&mut scope, &mut emit, &params) {
                if text.contains("(x: i64)") || text.contains("i64)") {
                    // Check for i64 in find variant or numeric literal in transform
                    for (_, ty, _) in &scope.locals {
                        if let TypeInfo::Optional(inner) = ty {
                            if **inner == TypeInfo::Primitive(PrimitiveType::I64) {
                                saw_i64 = true;
                            }
                        }
                    }
                }
                if text.contains("(x: string)")
                    || text.contains("\"hello\"")
                    || text.contains("\"world\"")
                    || text.contains("\"foo\"")
                    || text.contains("\"bar\"")
                    || text.contains("\"test\"")
                {
                    saw_string = true;
                }
                if text.contains("(x: bool)")
                    || text.contains("(true, true)")
                    || text.contains("(true, false)")
                {
                    saw_bool = true;
                }
            }

            if saw_i64 && saw_string && saw_bool {
                break;
            }
        }

        assert!(saw_i64, "never generated i64 variant in 200 seeds");
        assert!(saw_string, "never generated string variant in 200 seeds");
        assert!(saw_bool, "never generated bool variant in 200 seeds");
    }
}
