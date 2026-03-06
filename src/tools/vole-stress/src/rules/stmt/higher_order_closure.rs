//! Rule: generate higher-order closure patterns.
//!
//! Stresses nested function types, calling conventions, and closure capture by
//! generating functions that take closures as arguments or return closures.
//!
//! Helper functions are emitted at module level via [`Scope::add_module_decl`]
//! because nested `func<T>` is rewritten to `let = lambda` by vole-fmt, and
//! lambdas don't support type parameters.
//!
//! **Variant 1 -- compose: generic composition of two closures:**
//! ```vole
//! func compose_42918<A, B, C>(f: (A) -> B, g: (B) -> C) -> (A) -> C {
//!     return (x: A) => g(f(x))
//! }
//! let local0 = compose_42918((x: i64) => x * 2, (x: i64) => x + 1)
//! let local1 = local0(5)
//! ```
//!
//! **Variant 2 -- apply_chain: generic function applying two transforms:**
//! ```vole
//! func apply_chain_42918<T>(x: T, f: (T) -> T, g: (T) -> T) -> T {
//!     return g(f(x))
//! }
//! let local0 = apply_chain_42918(10, (n: i64) => n + 5, (n: i64) => n * 3)
//! ```
//!
//! **Variant 3 -- make_adder/make_formatter: function returning a closure:**
//! ```vole
//! func make_adder_42918(n: i64) -> (i64) -> i64 {
//!     return (x: i64) => x + n
//! }
//! let local0 = make_adder_42918(5)
//! let local1 = local0(10)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct HigherOrderClosure;

impl StmtRule for HigherOrderClosure {
    fn name(&self) -> &'static str {
        "higher_order_closure"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Only fire at top level of a free function (not inside class methods,
        // where module-level decls cannot be spliced).
        scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..3);
        match variant {
            0 => emit_compose(scope, emit),
            1 => emit_apply_chain(scope, emit),
            _ => emit_make_closure(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 1: compose -- `<A, B, C>(f: (A) -> B, g: (B) -> C) -> (A) -> C`
// ---------------------------------------------------------------------------

/// Generate a generic `compose_<N>` function and call it with two closures.
///
/// Sub-variant A (i64 -> i64 -> i64):
/// ```vole
/// func compose_42918<A, B, C>(f: (A) -> B, g: (B) -> C) -> (A) -> C {
///     return (x: A) => g(f(x))
/// }
/// let local0 = compose_42918((x: i64) => x * 2, (x: i64) => x + 1)
/// let local1 = local0(5)
/// ```
///
/// Sub-variant B (i64 -> i64 -> string):
/// ```vole
/// let local0 = compose_42918((x: i64) => x * 3, (x: i64) => x.to_string())
/// let local1 = local0(7)
/// ```
fn emit_compose(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_id = emit.gen_range(10000..99999);
    let fn_name = format!("compose_{}", fn_id);

    // Module-level generic function declaration
    let decl = format!(
        "func {}<A, B, C>(f: (A) -> B, g: (B) -> C) -> (A) -> C {{\n    return (x: A) => g(f(x))\n}}",
        fn_name
    );
    scope.add_module_decl(decl);

    // Pick sub-variant: all-i64 or i64->string
    let to_string = emit.gen_bool(0.4);

    let indent = emit.indent_str();

    if to_string {
        // i64 -> i64 -> string
        let multiplier = emit.gen_i64_range(2, 5);
        let arg_val = emit.gen_i64_range(1, 20);

        let composed_name = scope.fresh_name();
        let result_name = scope.fresh_name();

        scope.add_local(
            composed_name.clone(),
            TypeInfo::Function {
                param_types: vec![TypeInfo::Primitive(PrimitiveType::I64)],
                return_type: Box::new(TypeInfo::Primitive(PrimitiveType::String)),
            },
            false,
        );
        scope.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        Some(format!(
            "let {composed} = {fn_name}((x: i64) => x * {mul}, (x: i64) => x.to_string())\n\
             {indent}let {result} = {composed}({arg})",
            composed = composed_name,
            fn_name = fn_name,
            mul = multiplier,
            result = result_name,
            arg = arg_val,
            indent = indent,
        ))
    } else {
        // i64 -> i64 -> i64
        let mul = emit.gen_i64_range(2, 5);
        let add = emit.gen_i64_range(1, 10);
        let arg_val = emit.gen_i64_range(1, 20);

        let composed_name = scope.fresh_name();
        let result_name = scope.fresh_name();

        scope.add_local(
            composed_name.clone(),
            TypeInfo::Function {
                param_types: vec![TypeInfo::Primitive(PrimitiveType::I64)],
                return_type: Box::new(TypeInfo::Primitive(PrimitiveType::I64)),
            },
            false,
        );
        scope.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        Some(format!(
            "let {composed} = {fn_name}((x: i64) => x * {mul}, (x: i64) => x + {add})\n\
             {indent}let {result} = {composed}({arg})",
            composed = composed_name,
            fn_name = fn_name,
            mul = mul,
            add = add,
            result = result_name,
            arg = arg_val,
            indent = indent,
        ))
    }
}

// ---------------------------------------------------------------------------
// Variant 2: apply_chain -- `<T>(x: T, f: (T) -> T, g: (T) -> T) -> T`
// ---------------------------------------------------------------------------

/// Generate `apply_chain_<N>` at module level and a call with two closures.
///
/// ```vole
/// func apply_chain_42918<T>(x: T, f: (T) -> T, g: (T) -> T) -> T {
///     return g(f(x))
/// }
/// let local0 = apply_chain_42918(10, (n: i64) => n + 5, (n: i64) => n * 3)
/// ```
fn emit_apply_chain(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_id = emit.gen_range(10000..99999);
    let fn_name = format!("apply_chain_{}", fn_id);

    // Module-level generic function declaration
    let decl = format!(
        "func {}<T>(x: T, f: (T) -> T, g: (T) -> T) -> T {{\n    return g(f(x))\n}}",
        fn_name
    );
    scope.add_module_decl(decl);

    // Pick type: i64 or string
    let use_string = emit.gen_bool(0.3);

    if use_string {
        emit_apply_chain_string(scope, emit, &fn_name)
    } else {
        emit_apply_chain_i64(scope, emit, &fn_name)
    }
}

fn emit_apply_chain_i64(scope: &mut Scope, emit: &mut Emit, fn_name: &str) -> Option<String> {
    let start_val = emit.gen_i64_range(1, 20);
    let add_val = emit.gen_i64_range(1, 10);
    let mul_val = emit.gen_i64_range(2, 5);

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    Some(format!(
        "let {result} = {fn_name}({start}, (n: i64) => n + {add}, (n: i64) => n * {mul})",
        result = result_name,
        fn_name = fn_name,
        start = start_val,
        add = add_val,
        mul = mul_val,
    ))
}

fn emit_apply_chain_string(scope: &mut Scope, emit: &mut Emit, fn_name: &str) -> Option<String> {
    let suffixes = ["!", "?", ".", ".."];
    let suffix_idx = emit.gen_range(0..suffixes.len());
    let suffix = suffixes[suffix_idx];

    let prefixes = ["hi", "ok", "yo", "go"];
    let prefix_idx = emit.gen_range(0..prefixes.len());
    let prefix = prefixes[prefix_idx];

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    Some(format!(
        "let {result} = {fn_name}(\"{base}\", (s: string) => s + \"{suf}\", (s: string) => s + s)",
        result = result_name,
        fn_name = fn_name,
        base = prefix,
        suf = suffix,
    ))
}

// ---------------------------------------------------------------------------
// Variant 3: make_adder / make_formatter -- returns a closure
// ---------------------------------------------------------------------------

/// Generate a factory function that returns a closure capturing a parameter.
///
/// Sub-variant A -- make_adder:
/// ```vole
/// func make_adder_42918(n: i64) -> (i64) -> i64 {
///     return (x: i64) => x + n
/// }
/// let local0 = make_adder_42918(5)
/// let local1 = local0(10)
/// ```
///
/// Sub-variant B -- make_formatter:
/// ```vole
/// func make_formatter_42918(prefix: string) -> (i64) -> string {
///     return (x: i64) => prefix + x.to_string()
/// }
/// let local0 = make_formatter_42918("val=")
/// let local1 = local0(42)
/// ```
fn emit_make_closure(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let use_formatter = emit.gen_bool(0.4);

    if use_formatter {
        emit_make_formatter(scope, emit)
    } else {
        emit_make_adder(scope, emit)
    }
}

fn emit_make_adder(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_id = emit.gen_range(10000..99999);
    let fn_name = format!("make_adder_{}", fn_id);

    // Module-level function declaration (non-generic but still needs module level
    // to keep the pattern consistent and avoid vole-fmt lambda rewriting)
    let decl = format!(
        "func {}(n: i64) -> (i64) -> i64 {{\n    return (x: i64) => x + n\n}}",
        fn_name
    );
    scope.add_module_decl(decl);

    let n_val = emit.gen_i64_range(1, 20);
    let x_val = emit.gen_i64_range(1, 50);

    let indent = emit.indent_str();

    let closure_name = scope.fresh_name();
    let result_name = scope.fresh_name();

    scope.add_local(
        closure_name.clone(),
        TypeInfo::Function {
            param_types: vec![TypeInfo::Primitive(PrimitiveType::I64)],
            return_type: Box::new(TypeInfo::Primitive(PrimitiveType::I64)),
        },
        false,
    );
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    Some(format!(
        "let {closure} = {fn_name}({n})\n\
         {indent}let {result} = {closure}({x})",
        closure = closure_name,
        fn_name = fn_name,
        n = n_val,
        result = result_name,
        x = x_val,
        indent = indent,
    ))
}

fn emit_make_formatter(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_id = emit.gen_range(10000..99999);
    let fn_name = format!("make_formatter_{}", fn_id);

    let decl = format!(
        "func {}(prefix: string) -> (i64) -> string {{\n    return (x: i64) => prefix + x.to_string()\n}}",
        fn_name
    );
    scope.add_module_decl(decl);

    let prefixes = ["val=", "n=", "x=", "num=", "id="];
    let prefix_idx = emit.gen_range(0..prefixes.len());
    let prefix = prefixes[prefix_idx];

    let x_val = emit.gen_i64_range(1, 100);

    let indent = emit.indent_str();

    let closure_name = scope.fresh_name();
    let result_name = scope.fresh_name();

    scope.add_local(
        closure_name.clone(),
        TypeInfo::Function {
            param_types: vec![TypeInfo::Primitive(PrimitiveType::I64)],
            return_type: Box::new(TypeInfo::Primitive(PrimitiveType::String)),
        },
        false,
    );
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    Some(format!(
        "let {closure} = {fn_name}(\"{prefix}\")\n\
         {indent}let {result} = {closure}({x})",
        closure = closure_name,
        fn_name = fn_name,
        prefix = prefix,
        result = result_name,
        x = x_val,
        indent = indent,
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

    #[test]
    fn name_is_correct() {
        assert_eq!(HigherOrderClosure.name(), "higher_order_closure");
    }

    #[test]
    fn precondition_rejects_class_methods() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        // No class => precondition passes
        assert!(HigherOrderClosure.precondition(&scope, &params));
        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!HigherOrderClosure.precondition(&scope, &params));
    }

    #[test]
    fn generates_compose_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = HigherOrderClosure.generate(&mut scope, &mut emit, &params) {
                if text.contains("compose_") {
                    found = true;
                    // Verify module decl was registered
                    assert!(
                        !scope.module_decls.is_empty(),
                        "expected module_decl for compose"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("<A, B, C>"),
                        "expected generic type params in decl: {decl}"
                    );
                    assert!(decl.contains("g(f(x))"), "expected compose body: {decl}");
                    // Lambda params must have type annotations
                    assert!(
                        text.contains("(x: i64)"),
                        "expected typed lambda param: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated compose variant in 200 seeds");
    }

    #[test]
    fn generates_apply_chain_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = HigherOrderClosure.generate(&mut scope, &mut emit, &params) {
                if text.contains("apply_chain_") {
                    found = true;
                    assert!(
                        !scope.module_decls.is_empty(),
                        "expected module_decl for apply_chain"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("<T>"),
                        "expected generic type param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("g(f(x))"),
                        "expected apply_chain body: {decl}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated apply_chain variant in 200 seeds");
    }

    #[test]
    fn generates_make_adder_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = HigherOrderClosure.generate(&mut scope, &mut emit, &params) {
                if text.contains("make_adder_") {
                    found = true;
                    assert!(
                        !scope.module_decls.is_empty(),
                        "expected module_decl for make_adder"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("(n: i64) -> (i64) -> i64"),
                        "expected return type in decl: {decl}"
                    );
                    assert!(decl.contains("x + n"), "expected adder body: {decl}");
                    // Should have two let bindings (closure + result)
                    let let_count = text.matches("let ").count();
                    assert!(
                        let_count >= 2,
                        "expected at least 2 let bindings, got {let_count}: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated make_adder variant in 200 seeds");
    }

    #[test]
    fn generates_make_formatter_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = HigherOrderClosure.generate(&mut scope, &mut emit, &params) {
                if text.contains("make_formatter_") {
                    found = true;
                    assert!(
                        !scope.module_decls.is_empty(),
                        "expected module_decl for make_formatter"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("(prefix: string) -> (i64) -> string"),
                        "expected return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("prefix + x.to_string()"),
                        "expected formatter body: {decl}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated make_formatter variant in 200 seeds");
    }

    #[test]
    fn adds_locals_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = HigherOrderClosure.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        // All variants add at least one local
        assert!(
            !scope.locals.is_empty(),
            "expected result local added to scope"
        );
    }

    #[test]
    fn compose_adds_function_typed_local() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = HigherOrderClosure.generate(&mut scope, &mut emit, &params) {
                if text.contains("compose_") {
                    found = true;
                    // First local should be a Function type (the composed closure)
                    let (_, ref ty, _) = scope.locals[0];
                    assert!(
                        matches!(ty, TypeInfo::Function { .. }),
                        "expected Function type for composed closure, got: {ty:?}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated compose variant in 200 seeds");
    }

    #[test]
    fn make_adder_closure_local_has_function_type() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = HigherOrderClosure.generate(&mut scope, &mut emit, &params) {
                if text.contains("make_adder_") || text.contains("make_formatter_") {
                    found = true;
                    // First local should be a Function type (the returned closure)
                    let (_, ref ty, _) = scope.locals[0];
                    assert!(
                        matches!(ty, TypeInfo::Function { .. }),
                        "expected Function type for returned closure, got: {ty:?}"
                    );
                    // Second local should be the result of calling the closure
                    assert!(
                        scope.locals.len() >= 2,
                        "expected at least 2 locals for make_adder/make_formatter"
                    );
                    break;
                }
            }
        }
        assert!(
            found,
            "never generated make_adder/make_formatter in 200 seeds"
        );
    }

    #[test]
    fn all_lambda_params_have_type_annotations() {
        let table = SymbolTable::new();
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = HigherOrderClosure.generate(&mut scope, &mut emit, &params) {
                // Every `=>` should be preceded by a typed parameter like `(x: i64)` or `(s: string)`
                // We check that no bare `(x)` or `(n)` patterns appear before `=>`
                let combined = format!("{}\n{}", scope.module_decls.join("\n"), text);
                for line in combined.lines() {
                    // Skip lines that are part of function signatures (not lambda bodies)
                    if !line.contains("=>") {
                        continue;
                    }
                    // Lambda params should always have `: type` annotation
                    // Look for patterns like `(x: i64)` or `(s: string)` or `(n: i64)`
                    assert!(
                        line.contains(": i64)") || line.contains(": string)"),
                        "seed {seed}: lambda param missing type annotation in: {line}"
                    );
                }
            }
        }
    }
}
