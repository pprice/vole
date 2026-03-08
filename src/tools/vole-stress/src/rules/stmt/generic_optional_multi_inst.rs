//! Rule: generate generic functions returning optional types, instantiated
//! with **multiple concrete types** in the same block.
//!
//! Stresses the intersection of generics with optional/nil handling by
//! generating module-level generic functions that return `T?` and calling
//! them with *both* i64 and string arguments, exercising monomorphization
//! of optional type construction across distinct instantiations.
//!
//! Unlike `generic_optional_return` (which picks a single concrete type per
//! generation), this rule always generates test calls for both i64 and
//! string in the same output block.
//!
//! The generic functions are emitted at module level via
//! [`Scope::add_module_decl`] because nested `func<T>` is rewritten to
//! `let = lambda` by vole-fmt, and lambdas don't support type parameters.
//!
//! **Variant 0 -- generic search (equality match):**
//! ```vole
//! func find_match_42918<T>(items: [T], target: T) -> T? {
//!     for item in items {
//!         if item == target {
//!             return item
//!         }
//!     }
//!     return nil
//! }
//! let r1_42918 = find_match_42918([1, 2, 3], 2)
//! assert(r1_42918 != nil)
//! let r2_42918 = find_match_42918([1, 2, 3], 99)
//! assert(r2_42918 == nil)
//! let r3_42918 = find_match_42918(["a", "b"], "b")
//! assert(r3_42918 != nil)
//! ```
//!
//! **Variant 1 -- generic conditional return:**
//! ```vole
//! func check_42918<T>(x: T, flag: bool) -> T? {
//!     if flag {
//!         return x
//!     }
//!     return nil
//! }
//! let r1_42918 = check_42918(42, true)
//! assert(r1_42918 == 42)
//! let r2_42918 = check_42918(42, false)
//! assert(r2_42918 == nil)
//! let r3_42918 = check_42918("hello", true)
//! assert(r3_42918 == "hello")
//! ```
//!
//! **Variant 2 -- generic first-of-array:**
//! ```vole
//! func first_42918<T>(items: [T]) -> T? {
//!     if items.length() > 0 {
//!         return items[0]
//!     }
//!     return nil
//! }
//! let r1_42918 = first_42918([10, 20])
//! assert(r1_42918 == 10)
//! let r2_42918 = first_42918(["x", "y"])
//! assert(r2_42918 == "x")
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct GenericOptionalMultiInst;

impl StmtRule for GenericOptionalMultiInst {
    fn name(&self) -> &'static str {
        "generic_optional_multi_inst"
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
            0 => emit_find_match_variant(scope, emit),
            1 => emit_check_variant(scope, emit),
            _ => emit_first_variant(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0: generic search -- `([T], T) -> T?`
// ---------------------------------------------------------------------------

/// Generate a generic `find_match_<N>` function that searches an array for
/// a target using `==`, returning the item or nil.  Calls it with both i64
/// and string arrays.
fn emit_find_match_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("find_match_{}", uid);

    let decl = format!(
        concat!(
            "func {}<T>(items: [T], target: T) -> T? {{\n",
            "    for item in items {{\n",
            "        if item == target {{\n",
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

    // i64 instantiation: pick a small array and a target that IS present
    let hit_val = emit.gen_i64_range(1, 5);
    let i64_elems: Vec<i64> = (1..=5).collect();
    let i64_array = format!(
        "[{}]",
        i64_elems
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join(", ")
    );
    // miss target: always outside the array
    let miss_val = emit.gen_i64_range(90, 99);

    let r1 = format!("r1_{}", uid);
    let r2 = format!("r2_{}", uid);

    scope.add_local(
        r1.clone(),
        TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        false,
    );
    scope.add_local(
        r2.clone(),
        TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        false,
    );

    // string instantiation
    let words = ["apple", "banana", "cherry"];
    let hit_idx = emit.gen_range(0..words.len());
    let hit_word = words[hit_idx];
    let str_array = format!(
        "[{}]",
        words
            .iter()
            .map(|w| format!("\"{}\"", w))
            .collect::<Vec<_>>()
            .join(", ")
    );

    let r3 = format!("r3_{}", uid);
    scope.add_local(
        r3.clone(),
        TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
        false,
    );

    let code = format!(
        "let {r1} = {fn_name}({i64_array}, {hit_val})\n\
         {indent}assert({r1} != nil)\n\
         {indent}let {r2} = {fn_name}({i64_array}, {miss_val})\n\
         {indent}assert({r2} == nil)\n\
         {indent}let {r3} = {fn_name}({str_array}, \"{hit_word}\")\n\
         {indent}assert({r3} != nil)",
    );

    Some(code)
}

// ---------------------------------------------------------------------------
// Variant 1: generic conditional return -- `(T, bool) -> T?`
// ---------------------------------------------------------------------------

/// Generate a generic `check_<N>` function that returns its argument when
/// the flag is true, nil otherwise.  Calls it with i64 and string.
fn emit_check_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("check_{}", uid);

    let decl = format!(
        concat!(
            "func {}<T>(x: T, flag: bool) -> T? {{\n",
            "    if flag {{\n",
            "        return x\n",
            "    }}\n",
            "    return nil\n",
            "}}"
        ),
        fn_name
    );
    scope.add_module_decl(decl);

    let indent = emit.indent_str();

    // i64 instantiation
    let i64_val = emit.gen_i64_range(1, 50);

    let r1 = format!("r1_{}", uid);
    let r2 = format!("r2_{}", uid);

    scope.add_local(
        r1.clone(),
        TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        false,
    );
    scope.add_local(
        r2.clone(),
        TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        false,
    );

    // string instantiation
    let str_words = ["hello", "world", "vole", "test"];
    let str_val = str_words[emit.gen_range(0..str_words.len())];

    let r3 = format!("r3_{}", uid);
    scope.add_local(
        r3.clone(),
        TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
        false,
    );

    let code = format!(
        "let {r1} = {fn_name}({i64_val}, true)\n\
         {indent}assert({r1} == {i64_val})\n\
         {indent}let {r2} = {fn_name}({i64_val}, false)\n\
         {indent}assert({r2} == nil)\n\
         {indent}let {r3} = {fn_name}(\"{str_val}\", true)\n\
         {indent}assert({r3} == \"{str_val}\")",
    );

    Some(code)
}

// ---------------------------------------------------------------------------
// Variant 2: generic first-of-array -- `([T]) -> T?`
// ---------------------------------------------------------------------------

/// Generate a generic `first_<N>` function that returns the first element
/// of an array, or nil if empty.  Calls it with i64 and string arrays.
fn emit_first_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let fn_name = format!("first_{}", uid);

    let decl = format!(
        concat!(
            "func {}<T>(items: [T]) -> T? {{\n",
            "    if items.length() > 0 {{\n",
            "        return items[0]\n",
            "    }}\n",
            "    return nil\n",
            "}}"
        ),
        fn_name
    );
    scope.add_module_decl(decl);

    let indent = emit.indent_str();

    // i64 instantiation
    let first_i64 = emit.gen_i64_range(1, 50);
    let second_i64 = emit.gen_i64_range(51, 99);

    let r1 = format!("r1_{}", uid);
    scope.add_local(
        r1.clone(),
        TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        false,
    );

    // string instantiation
    let str_words = ["alpha", "beta", "gamma", "delta"];
    let first_str = str_words[emit.gen_range(0..str_words.len())];
    let second_str = str_words[emit.gen_range(0..str_words.len())];

    let r2 = format!("r2_{}", uid);
    scope.add_local(
        r2.clone(),
        TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
        false,
    );

    let code = format!(
        "let {r1} = {fn_name}([{first_i64}, {second_i64}])\n\
         {indent}assert({r1} == {first_i64})\n\
         {indent}let {r2} = {fn_name}([\"{first_str}\", \"{second_str}\"])\n\
         {indent}assert({r2} == \"{first_str}\")",
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
        assert_eq!(
            GenericOptionalMultiInst.name(),
            "generic_optional_multi_inst"
        );
    }

    #[test]
    fn precondition_requires_module_level() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();
        // No module => precondition fails
        assert!(!GenericOptionalMultiInst.precondition(&scope, &params));
        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(GenericOptionalMultiInst.precondition(&scope, &params));
        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!GenericOptionalMultiInst.precondition(&scope, &params));
    }

    #[test]
    fn generates_find_match_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) =
                GenericOptionalMultiInst.generate(&mut scope, &mut emit, &test_params())
            {
                if text.contains("find_match_") {
                    found = true;
                    // Module decl registered
                    assert_eq!(scope.module_decls.len(), 1);
                    let decl = &scope.module_decls[0];
                    assert!(decl.contains("<T>"), "expected <T> in decl: {decl}");
                    assert!(
                        decl.contains("-> T?"),
                        "expected optional return in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return nil"),
                        "expected nil return in decl: {decl}"
                    );
                    // Both i64 and string calls present
                    assert!(
                        text.contains("== nil"),
                        "expected nil check in code: {text}"
                    );
                    assert!(
                        text.contains("!= nil"),
                        "expected non-nil check in code: {text}"
                    );
                    // String instantiation present (quoted strings in call)
                    assert!(
                        text.contains('"'),
                        "expected string instantiation in code: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated find_match variant in 100 seeds");
    }

    #[test]
    fn generates_check_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) =
                GenericOptionalMultiInst.generate(&mut scope, &mut emit, &test_params())
            {
                if text.contains("check_") {
                    found = true;
                    let decl = &scope.module_decls[0];
                    assert!(decl.contains("<T>"), "expected <T> in decl: {decl}");
                    assert!(
                        decl.contains("-> T?"),
                        "expected optional return in decl: {decl}"
                    );
                    // Both true and false calls
                    assert!(text.contains("true)"), "expected true call: {text}");
                    assert!(text.contains("false)"), "expected false call: {text}");
                    // nil check and value check
                    assert!(text.contains("== nil"), "expected nil check: {text}");
                    // String instantiation
                    assert!(text.contains('"'), "expected string instantiation: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated check variant in 100 seeds");
    }

    #[test]
    fn generates_first_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) =
                GenericOptionalMultiInst.generate(&mut scope, &mut emit, &test_params())
            {
                if text.contains("first_") {
                    found = true;
                    let decl = &scope.module_decls[0];
                    assert!(decl.contains("<T>"), "expected <T> in decl: {decl}");
                    assert!(
                        decl.contains("-> T?"),
                        "expected optional return in decl: {decl}"
                    );
                    assert!(
                        decl.contains("items.length()"),
                        "expected length check in decl: {decl}"
                    );
                    // Both i64 and string calls
                    assert!(text.contains('"'), "expected string instantiation: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated first variant in 100 seeds");
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

            if GenericOptionalMultiInst
                .generate(&mut scope, &mut emit, &test_params())
                .is_some()
            {
                // All variants add at least 2 locals
                assert!(
                    scope.locals.len() >= 2,
                    "expected at least 2 locals, got {}",
                    scope.locals.len()
                );
                // All locals should be optional types
                for (name, ty, _) in &scope.locals {
                    assert!(
                        matches!(ty, TypeInfo::Optional(_)),
                        "expected optional type for local '{}', got {:?}",
                        name,
                        ty
                    );
                }
                return;
            }
        }
        panic!("never generated any variant in 100 seeds");
    }

    #[test]
    fn multi_type_instantiation_present() {
        // Verify that every generated variant includes both i64 and string
        // instantiations by checking for numeric literals AND quoted strings.
        let table = SymbolTable::new();
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) =
                GenericOptionalMultiInst.generate(&mut scope, &mut emit, &test_params())
            {
                // Must have both i64 locals and string locals
                let has_i64_local = scope
                    .locals
                    .iter()
                    .any(|(_, ty, _)| {
                        matches!(
                            ty,
                            TypeInfo::Optional(inner) if **inner == TypeInfo::Primitive(PrimitiveType::I64)
                        )
                    });
                let has_string_local = scope
                    .locals
                    .iter()
                    .any(|(_, ty, _)| {
                        matches!(
                            ty,
                            TypeInfo::Optional(inner) if **inner == TypeInfo::Primitive(PrimitiveType::String)
                        )
                    });
                assert!(has_i64_local, "expected i64 optional local in code: {text}");
                assert!(
                    has_string_local,
                    "expected string optional local in code: {text}"
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

        if let Some(text) = GenericOptionalMultiInst.generate(&mut scope, &mut emit, &test_params())
        {
            // All result names should contain r{N}_ prefix with uid
            assert!(
                text.contains("r1_") || text.contains("r2_") || text.contains("r3_"),
                "expected uid-based result names in code: {text}"
            );
        }
    }
}
