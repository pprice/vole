//! Rule: module-level function that returns a closure, then calls it and
//! asserts the result.
//!
//! This tests closure creation, captured variable RC lifecycle, and function
//! pointer handling when the factory function is a module-level declaration.
//!
//! Two variants:
//!
//! **Variant 0 -- make_adder (captures i64):**
//! ```vole
//! func make_adder_local0(n: i64) -> (i64) -> i64 {
//!     return (x: i64) => x + n
//! }
//! let local1 = make_adder_local0(5)
//! let local2 = local1(10)
//! assert(local2 == 15)
//! ```
//!
//! **Variant 1 -- make_greeter (captures string):**
//! ```vole
//! func make_greeter_local0(prefix: string) -> (string) -> string {
//!     return (name: string) => prefix + " " + name
//! }
//! let local1 = make_greeter_local0("Hello")
//! let local2 = local1("World")
//! assert(local2 == "Hello World")
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ClosureReturn;

/// Fixed prefixes for the greeter variant.
const PREFIXES: &[&str] = &["Hello", "Hi", "Hey", "Dear"];

/// Fixed names for the greeter variant.
const NAMES: &[&str] = &["World", "Vole", "Alice", "Bob"];

impl StmtRule for ClosureReturn {
    fn name(&self) -> &'static str {
        "closure_return"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..2);
        match variant {
            0 => emit_make_adder(scope, emit),
            _ => emit_make_greeter(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0 -- make_adder (captures i64)
// ---------------------------------------------------------------------------

fn emit_make_adder(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_name = scope.fresh_name();
    let fn_label = format!("make_adder_{}", fn_name);

    let n = emit.gen_i64_range(1, 20);
    let arg = emit.gen_i64_range(1, 50);
    let expected = n + arg;

    let decl = format!(
        "func {}(n: i64) -> (i64) -> i64 {{\n    return (x: i64) => x + n\n}}",
        fn_label,
    );
    scope.add_module_decl(decl);

    let closure_name = scope.fresh_name();
    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}({})\n{}let {} = {}({})\n{}assert({} == {})",
        closure_name,
        fn_label,
        n,
        indent,
        result_name,
        closure_name,
        arg,
        indent,
        result_name,
        expected,
    ))
}

// ---------------------------------------------------------------------------
// Variant 1 -- make_greeter (captures string)
// ---------------------------------------------------------------------------

fn emit_make_greeter(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_name = scope.fresh_name();
    let fn_label = format!("make_greeter_{}", fn_name);

    let prefix_idx = emit.gen_range(0..PREFIXES.len());
    let name_idx = emit.gen_range(0..NAMES.len());
    let prefix = PREFIXES[prefix_idx];
    let name = NAMES[name_idx];
    let expected = format!("{} {}", prefix, name);

    let decl = format!(
        "func {}(prefix: string) -> (string) -> string {{\n    return (name: string) => prefix + \" \" + name\n}}",
        fn_label,
    );
    scope.add_module_decl(decl);

    let closure_name = scope.fresh_name();
    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}(\"{}\")\n{}let {} = {}(\"{}\")\n{}assert({} == \"{}\")",
        closure_name,
        fn_label,
        prefix,
        indent,
        result_name,
        closure_name,
        name,
        indent,
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
        assert_eq!(ClosureReturn.name(), "closure_return");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!ClosureReturn.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(ClosureReturn.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!ClosureReturn.precondition(&scope, &params));
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

            if let Some(text) = ClosureReturn.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("make_adder_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for adder variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> (i64) -> i64"),
                        "expected closure return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return (x: i64) => x + n"),
                        "expected closure body in decl: {decl}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated adder variant in 100 seeds");
    }

    #[test]
    fn generates_greeter_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = ClosureReturn.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("make_greeter_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for greeter variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> (string) -> string"),
                        "expected closure return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("return (name: string) => prefix + \" \" + name"),
                        "expected closure body in decl: {decl}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated greeter variant in 100 seeds");
    }

    #[test]
    fn adds_module_decl() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        ClosureReturn.generate(&mut scope, &mut emit, &test_params());
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

        let result = ClosureReturn.generate(&mut scope, &mut emit, &test_params());
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
