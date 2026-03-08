//! Rule: closures that return closures, then call both layers and assert the
//! result.
//!
//! This stresses capture handling and RC lifecycle when captures flow through
//! nested closure boundaries.
//!
//! **Variant 0 -- i64 adder factory:**
//! ```vole
//! let local0 = (n: i64) => {
//!     return (x: i64) => x + n
//! }
//! let local1 = local0(5)
//! let local2 = local1(10)
//! assert(local2 == 15)
//! ```
//!
//! **Variant 1 -- string prefixer:**
//! ```vole
//! let local0 = (prefix: string) => {
//!     return (s: string) => prefix + " " + s
//! }
//! let local1 = local0("Hello")
//! let local2 = local1("World")
//! assert(local2 == "Hello World")
//! ```
//!
//! **Variant 2 -- i64 multiplier:**
//! ```vole
//! let local0 = (factor: i64) => {
//!     return (x: i64) => x * factor
//! }
//! let local1 = local0(3)
//! let local2 = local1(7)
//! assert(local2 == 21)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct NestedClosure;

/// Fixed prefixes for the string prefixer variant.
const PREFIXES: &[&str] = &["Hello", "Hi", "Hey", "Dear"];

/// Fixed names for the string prefixer variant.
const NAMES: &[&str] = &["World", "Vole", "Alice", "Bob"];

impl StmtRule for NestedClosure {
    fn name(&self) -> &'static str {
        "nested_closure"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..3);
        match variant {
            0 => emit_adder_factory(scope, emit),
            1 => emit_string_prefixer(scope, emit),
            _ => emit_multiplier_factory(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0 -- i64 adder factory
// ---------------------------------------------------------------------------

fn emit_adder_factory(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let factory_name = scope.fresh_name();
    let closure_name = scope.fresh_name();
    let result_name = scope.fresh_name();

    let n = emit.gen_i64_range(1, 20);
    let arg = emit.gen_i64_range(1, 50);
    let expected = n + arg;

    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = (n: i64) => {{\n{indent}    return (x: i64) => x + n\n{indent}}}\n\
         {indent}let {} = {}({})\n\
         {indent}let {} = {}({})\n\
         {indent}assert({} == {})",
        factory_name,
        closure_name,
        factory_name,
        n,
        result_name,
        closure_name,
        arg,
        result_name,
        expected,
    ))
}

// ---------------------------------------------------------------------------
// Variant 1 -- string prefixer
// ---------------------------------------------------------------------------

fn emit_string_prefixer(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let factory_name = scope.fresh_name();
    let closure_name = scope.fresh_name();
    let result_name = scope.fresh_name();

    let prefix_idx = emit.gen_range(0..PREFIXES.len());
    let name_idx = emit.gen_range(0..NAMES.len());
    let prefix = PREFIXES[prefix_idx];
    let name = NAMES[name_idx];
    let expected = format!("{} {}", prefix, name);

    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = (prefix: string) => {{\n{indent}    return (s: string) => prefix + \" \" + s\n{indent}}}\n\
         {indent}let {} = {}(\"{}\")\n\
         {indent}let {} = {}(\"{}\")\n\
         {indent}assert({} == \"{}\")",
        factory_name,
        closure_name,
        factory_name,
        prefix,
        result_name,
        closure_name,
        name,
        result_name,
        expected,
    ))
}

// ---------------------------------------------------------------------------
// Variant 2 -- i64 multiplier factory
// ---------------------------------------------------------------------------

fn emit_multiplier_factory(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let factory_name = scope.fresh_name();
    let closure_name = scope.fresh_name();
    let result_name = scope.fresh_name();

    let factor = emit.gen_i64_range(2, 10);
    let arg = emit.gen_i64_range(1, 20);
    let expected = factor * arg;

    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = (factor: i64) => {{\n{indent}    return (x: i64) => x * factor\n{indent}}}\n\
         {indent}let {} = {}({})\n\
         {indent}let {} = {}({})\n\
         {indent}assert({} == {})",
        factory_name,
        closure_name,
        factory_name,
        factor,
        result_name,
        closure_name,
        arg,
        result_name,
        expected,
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
        assert_eq!(NestedClosure.name(), "nested_closure");
    }

    #[test]
    fn precondition_requires_module() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!NestedClosure.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(NestedClosure.precondition(&scope, &params));
    }

    #[test]
    fn generates_adder_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = NestedClosure.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("x + n") {
                    found = true;
                    assert!(
                        text.contains("return (x: i64) => x + n"),
                        "expected inner closure body in text: {text}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    // No module decls for this rule
                    assert_eq!(
                        scope.module_decls.len(),
                        0,
                        "expected no module_decls for nested_closure"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated adder variant in 100 seeds");
    }

    #[test]
    fn generates_string_prefixer_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = NestedClosure.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("prefix + \" \" + s") {
                    found = true;
                    assert!(
                        text.contains("return (s: string) => prefix + \" \" + s"),
                        "expected inner closure body in text: {text}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    assert_eq!(
                        scope.module_decls.len(),
                        0,
                        "expected no module_decls for nested_closure"
                    );
                    break;
                }
            }
        }
        assert!(
            found,
            "never generated string prefixer variant in 100 seeds"
        );
    }

    #[test]
    fn generates_multiplier_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = NestedClosure.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("x * factor") {
                    found = true;
                    assert!(
                        text.contains("return (x: i64) => x * factor"),
                        "expected inner closure body in text: {text}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    assert_eq!(
                        scope.module_decls.len(),
                        0,
                        "expected no module_decls for nested_closure"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated multiplier variant in 100 seeds");
    }

    #[test]
    fn adds_result_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = NestedClosure.generate(&mut scope, &mut emit, &test_params());
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
    fn no_module_decls_added() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        NestedClosure.generate(&mut scope, &mut emit, &test_params());
        assert_eq!(
            scope.module_decls.len(),
            0,
            "nested_closure should not add module decls"
        );
    }
}
