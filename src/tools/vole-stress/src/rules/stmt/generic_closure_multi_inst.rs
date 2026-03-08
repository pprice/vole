//! Rule: generate generic functions with closure parameters, instantiated
//! with **multiple concrete types** in the same block.
//!
//! Stresses the intersection of generics with closures by generating
//! module-level generic functions that accept a value and a closure, then
//! calling them with *both* i64 and string arguments, exercising
//! monomorphization of closure-parameter generic functions across distinct
//! instantiations.
//!
//! Unlike `generic_closure_param` (which picks a single concrete type per
//! generation), this rule always generates test calls for both i64 and
//! string in the same output block.
//!
//! The generic functions are emitted at module level via
//! [`Scope::add_module_decl`] because nested `func<T>` is rewritten to
//! `let = lambda` by vole-fmt, and lambdas don't support type parameters.
//!
//! **Variant 0 -- apply closure, return string:**
//! ```vole
//! func apply_str_42918<T>(item: T, f: (T) -> string) -> string {
//!     return f(item)
//! }
//! let r1_42918 = apply_str_42918(42, (x: i64) => x.to_string())
//! assert(r1_42918 == "42")
//! let r2_42918 = apply_str_42918("hello", (x: string) => x.to_upper())
//! assert(r2_42918 == "HELLO")
//! ```
//!
//! **Variant 1 -- apply closure, return i64:**
//! ```vole
//! func apply_num_42918<T>(item: T, f: (T) -> i64) -> i64 {
//!     return f(item)
//! }
//! let r1_42918 = apply_num_42918(42, (x: i64) => x * 2)
//! assert(r1_42918 == 84)
//! let r2_42918 = apply_num_42918("hello", (x: string) => x.length())
//! assert(r2_42918 == 5)
//! ```
//!
//! **Variant 2 -- apply closure, return string, with bool:**
//! ```vole
//! func show_42918<T>(item: T, f: (T) -> string) -> string {
//!     return f(item)
//! }
//! let r1_42918 = show_42918(42, (x: i64) => x.to_string())
//! assert(r1_42918 == "42")
//! let r2_42918 = show_42918("hello", (x: string) => x.to_upper())
//! assert(r2_42918 == "HELLO")
//! let r3_42918 = show_42918(true, (x: bool) => x.to_string())
//! assert(r3_42918 == "true")
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct GenericClosureMultiInst;

impl StmtRule for GenericClosureMultiInst {
    fn name(&self) -> &'static str {
        "generic_closure_multi_inst"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Generic functions must be at module level, not inside class methods
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..3);
        match variant {
            0 => emit_apply_str_variant(scope, emit),
            1 => emit_apply_num_variant(scope, emit),
            _ => emit_show_variant(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0: apply closure returning string -- `(T, (T) -> string) -> string`
// ---------------------------------------------------------------------------

/// Generate a generic `apply_str_<N>` function that applies a closure to a
/// value and returns a string.  Calls it with both i64 and string.
fn emit_apply_str_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("apply_str_{}", uid);

    let decl = format!(
        "func {}<T>(item: T, f: (T) -> string) -> string {{\n    return f(item)\n}}",
        fn_name
    );
    scope.add_module_decl(decl);

    let indent = emit.indent_str();

    // i64 instantiation: pick a value, closure converts to string
    let i64_val = emit.gen_i64_range(1, 99);

    let r1 = format!("r1_{}", uid);
    scope.add_local(
        r1.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    // string instantiation: pick a word, closure converts to upper
    let words = ["hello", "world", "vole", "test"];
    let word_idx = emit.gen_range(0..words.len());
    let word = words[word_idx];
    let word_upper = word.to_uppercase();

    let r2 = format!("r2_{}", uid);
    scope.add_local(
        r2.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let code = format!(
        "let {r1} = {fn_name}({i64_val}, (x: i64) => x.to_string())\n\
         {indent}assert({r1} == \"{i64_val}\")\n\
         {indent}let {r2} = {fn_name}(\"{word}\", (x: string) => x.to_upper())\n\
         {indent}assert({r2} == \"{word_upper}\")",
    );

    Some(code)
}

// ---------------------------------------------------------------------------
// Variant 1: apply closure returning i64 -- `(T, (T) -> i64) -> i64`
// ---------------------------------------------------------------------------

/// Generate a generic `apply_num_<N>` function that applies a closure to a
/// value and returns an i64.  Calls it with both i64 and string.
fn emit_apply_num_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("apply_num_{}", uid);

    let decl = format!(
        "func {}<T>(item: T, f: (T) -> i64) -> i64 {{\n    return f(item)\n}}",
        fn_name
    );
    scope.add_module_decl(decl);

    let indent = emit.indent_str();

    // i64 instantiation: pick a value and a simple operation
    let i64_val = emit.gen_i64_range(1, 50);
    let factor = emit.gen_i64_range(2, 5);
    let expected_i64 = i64_val * factor;

    let r1 = format!("r1_{}", uid);
    scope.add_local(r1.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);

    // string instantiation: use .length()
    let words = ["hello", "world", "vole", "test", "stress"];
    let word_idx = emit.gen_range(0..words.len());
    let word = words[word_idx];
    let expected_len = word.len() as i64;

    let r2 = format!("r2_{}", uid);
    scope.add_local(r2.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);

    let code = format!(
        "let {r1} = {fn_name}({i64_val}, (x: i64) => x * {factor})\n\
         {indent}assert({r1} == {expected_i64})\n\
         {indent}let {r2} = {fn_name}(\"{word}\", (x: string) => x.length())\n\
         {indent}assert({r2} == {expected_len})",
    );

    Some(code)
}

// ---------------------------------------------------------------------------
// Variant 2: show -- three instantiations (i64, string, bool)
// ---------------------------------------------------------------------------

/// Generate a generic `show_<N>` function that applies a closure to a
/// value and returns a string.  Calls it with i64, string, and bool for
/// three distinct monomorphizations.
fn emit_show_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("show_{}", uid);

    let decl = format!(
        "func {}<T>(item: T, f: (T) -> string) -> string {{\n    return f(item)\n}}",
        fn_name
    );
    scope.add_module_decl(decl);

    let indent = emit.indent_str();

    // i64 instantiation
    let i64_val = emit.gen_i64_range(1, 99);

    let r1 = format!("r1_{}", uid);
    scope.add_local(
        r1.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    // string instantiation
    let words = ["hello", "world", "vole", "test"];
    let word_idx = emit.gen_range(0..words.len());
    let word = words[word_idx];
    let word_upper = word.to_uppercase();

    let r2 = format!("r2_{}", uid);
    scope.add_local(
        r2.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    // bool instantiation
    let bool_val = emit.gen_range(0..2) == 0;
    let bool_str = if bool_val { "true" } else { "false" };

    let r3 = format!("r3_{}", uid);
    scope.add_local(
        r3.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let code = format!(
        "let {r1} = {fn_name}({i64_val}, (x: i64) => x.to_string())\n\
         {indent}assert({r1} == \"{i64_val}\")\n\
         {indent}let {r2} = {fn_name}(\"{word}\", (x: string) => x.to_upper())\n\
         {indent}assert({r2} == \"{word_upper}\")\n\
         {indent}let {r3} = {fn_name}({bool_val}, (x: bool) => x.to_string())\n\
         {indent}assert({r3} == \"{bool_str}\")",
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

    fn test_params() -> Params {
        Params::from_iter([("probability", ParamValue::Probability(1.0))])
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(GenericClosureMultiInst.name(), "generic_closure_multi_inst");
    }

    #[test]
    fn precondition_requires_module_level() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();
        // No module => precondition fails
        assert!(!GenericClosureMultiInst.precondition(&scope, &params));
        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(GenericClosureMultiInst.precondition(&scope, &params));
        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!GenericClosureMultiInst.precondition(&scope, &params));
    }

    #[test]
    fn generates_apply_str_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) =
                GenericClosureMultiInst.generate(&mut scope, &mut emit, &test_params())
            {
                if text.contains("apply_str_") {
                    found = true;
                    // Module decl registered
                    assert_eq!(scope.module_decls.len(), 1);
                    let decl = &scope.module_decls[0];
                    assert!(decl.contains("<T>"), "expected <T> in decl: {decl}");
                    assert!(
                        decl.contains("(T) -> string"),
                        "expected closure param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return f(item)"),
                        "expected apply body in decl: {decl}"
                    );
                    // i64 closure with to_string
                    assert!(
                        text.contains("(x: i64) => x.to_string()"),
                        "expected i64 to_string closure: {text}"
                    );
                    // string closure with to_upper
                    assert!(
                        text.contains("(x: string) => x.to_upper()"),
                        "expected string to_upper closure: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated apply_str variant in 100 seeds");
    }

    #[test]
    fn generates_apply_num_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) =
                GenericClosureMultiInst.generate(&mut scope, &mut emit, &test_params())
            {
                if text.contains("apply_num_") {
                    found = true;
                    let decl = &scope.module_decls[0];
                    assert!(decl.contains("<T>"), "expected <T> in decl: {decl}");
                    assert!(
                        decl.contains("(T) -> i64"),
                        "expected closure param in decl: {decl}"
                    );
                    // i64 closure with multiplication
                    assert!(
                        text.contains("(x: i64) => x *"),
                        "expected i64 multiply closure: {text}"
                    );
                    // string closure with length
                    assert!(
                        text.contains("(x: string) => x.length()"),
                        "expected string length closure: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated apply_num variant in 100 seeds");
    }

    #[test]
    fn generates_show_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) =
                GenericClosureMultiInst.generate(&mut scope, &mut emit, &test_params())
            {
                if text.contains("show_") {
                    found = true;
                    let decl = &scope.module_decls[0];
                    assert!(decl.contains("<T>"), "expected <T> in decl: {decl}");
                    assert!(
                        decl.contains("(T) -> string"),
                        "expected closure param in decl: {decl}"
                    );
                    // Three instantiations: i64, string, bool
                    assert!(
                        text.contains("(x: i64) => x.to_string()"),
                        "expected i64 to_string closure: {text}"
                    );
                    assert!(
                        text.contains("(x: string) => x.to_upper()"),
                        "expected string to_upper closure: {text}"
                    );
                    assert!(
                        text.contains("(x: bool) => x.to_string()"),
                        "expected bool to_string closure: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated show variant in 100 seeds");
    }

    #[test]
    fn all_variants_add_locals_to_scope() {
        let table = SymbolTable::new();
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if GenericClosureMultiInst
                .generate(&mut scope, &mut emit, &test_params())
                .is_some()
            {
                // All variants add at least 2 locals
                assert!(
                    scope.locals.len() >= 2,
                    "expected at least 2 locals, got {}",
                    scope.locals.len()
                );
                return;
            }
        }
        panic!("never generated any variant in 100 seeds");
    }

    #[test]
    fn multi_type_instantiation_present() {
        // Verify that every generated variant includes calls with multiple
        // concrete types (both i64-typed and string-typed closures).
        let table = SymbolTable::new();
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) =
                GenericClosureMultiInst.generate(&mut scope, &mut emit, &test_params())
            {
                // Must have both i64-typed and string-typed closures
                assert!(
                    text.contains("(x: i64)"),
                    "expected i64-typed closure in code: {text}"
                );
                assert!(
                    text.contains("(x: string)"),
                    "expected string-typed closure in code: {text}"
                );
                return;
            }
        }
        panic!("never generated any variant in 100 seeds");
    }

    #[test]
    fn result_names_use_uid() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(7);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        if let Some(text) = GenericClosureMultiInst.generate(&mut scope, &mut emit, &test_params())
        {
            // All result names should contain r{N}_ prefix with uid
            assert!(
                text.contains("r1_") || text.contains("r2_") || text.contains("r3_"),
                "expected uid-based result names in code: {text}"
            );
        }
    }
}
