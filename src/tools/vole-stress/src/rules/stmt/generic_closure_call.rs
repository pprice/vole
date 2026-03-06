//! Rule: call a generic function with a closure argument.
//!
//! Stresses the intersection of generics + closures + monomorphization by
//! generating module-level generic helper functions and calling them with
//! inline closures that force monomorphization at a concrete type.
//!
//! The helper functions are emitted at module level via
//! [`Scope::add_module_decl`] because nested `func<T>` is rewritten to
//! `let = lambda` by vole-fmt, and lambdas don't support type parameters.
//!
//! **Variant 1 -- apply_twice: `(T, (T) -> T) -> T`**
//! ```vole
//! func apply_twice_local0<T>(x: T, f: (T) -> T) -> T {
//!     return f(f(x))
//! }
//! let local1 = apply_twice_local0(5, (n: i64) => n + 1)
//! ```
//!
//! **Variant 2 -- transform: `(T, (T) -> string) -> string`**
//! ```vole
//! func transform_local2<T>(x: T, f: (T) -> string) -> string {
//!     return f(x)
//! }
//! let local3 = transform_local2(42, (n: i64) => "v:{n}")
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct GenericClosureCall;

impl StmtRule for GenericClosureCall {
    fn name(&self) -> &'static str {
        "generic_closure_call"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Only fire at the top level of a free function (not inside class
        // methods, where module-level decls cannot be spliced).
        scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..2);
        match variant {
            0 => emit_apply_twice(scope, emit),
            _ => emit_transform(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 1: apply_twice -- `(T, (T) -> T) -> T`
// ---------------------------------------------------------------------------

/// Generate `apply_twice_<N>` at module level and a call with a closure.
///
/// For i64:
/// ```vole
/// func apply_twice_local0<T>(x: T, f: (T) -> T) -> T {
///     return f(f(x))
/// }
/// let local1 = apply_twice_local0(5, (n: i64) => n + 1)
/// ```
///
/// For string:
/// ```vole
/// func apply_twice_local0<T>(x: T, f: (T) -> T) -> T {
///     return f(f(x))
/// }
/// let local1 = apply_twice_local0("hi", (s: string) => s + "!")
/// ```
fn emit_apply_twice(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let prim = pick_apply_type(emit);
    let type_name = prim_type_name(prim);

    let fn_id = emit.gen_range(10000..99999);
    let fn_name = format!("apply_twice_{}", fn_id);

    // Module-level generic function declaration
    let decl = format!(
        "func {}<T>(x: T, f: (T) -> T) -> T {{\n    return f(f(x))\n}}",
        fn_name
    );
    scope.add_module_decl(decl);

    // Build the closure and argument
    let (arg_literal, closure) = match prim {
        PrimitiveType::String => {
            let lit = pick_string_literal(emit);
            (lit, format!("(s: string) => s + \"!\""))
        }
        _ => {
            // i64
            let val = emit.gen_i64_range(0, 20);
            (format!("{}", val), format!("(n: {}) => n + 1", type_name))
        }
    };

    let result_name = scope.fresh_name();
    scope.add_local(result_name.clone(), TypeInfo::Primitive(prim), false);

    Some(format!(
        "let {} = {}({}, {})",
        result_name, fn_name, arg_literal, closure,
    ))
}

// ---------------------------------------------------------------------------
// Variant 2: transform -- `(T, (T) -> string) -> string`
// ---------------------------------------------------------------------------

/// Generate `transform_<N>` at module level and a call with a closure.
///
/// ```vole
/// func transform_local2<T>(x: T, f: (T) -> string) -> string {
///     return f(x)
/// }
/// let local3 = transform_local2(42, (n: i64) => "v:{n}")
/// ```
fn emit_transform(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let prim = pick_transform_type(emit);
    let type_name = prim_type_name(prim);

    let fn_id = emit.gen_range(10000..99999);
    let fn_name = format!("transform_{}", fn_id);

    // Module-level generic function declaration
    let decl = format!(
        "func {}<T>(x: T, f: (T) -> string) -> string {{\n    return f(x)\n}}",
        fn_name
    );
    scope.add_module_decl(decl);

    // Build the closure and argument
    let (arg_literal, closure) = match prim {
        PrimitiveType::Bool => {
            let val = if emit.gen_bool(0.5) { "true" } else { "false" };
            (val.to_string(), format!("(b: bool) => \"val:{{b}}\""))
        }
        PrimitiveType::String => {
            let lit = pick_string_literal(emit);
            (lit, format!("(s: string) => \"val:{{s}}\""))
        }
        _ => {
            // i64
            let val = emit.gen_i64_range(0, 100);
            (
                format!("{}", val),
                format!("(n: {}) => \"v:{{n}}\"", type_name),
            )
        }
    };

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    Some(format!(
        "let {} = {}({}, {})",
        result_name, fn_name, arg_literal, closure,
    ))
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Pick a type for the apply_twice variant (i64 or string).
fn pick_apply_type(emit: &mut Emit) -> PrimitiveType {
    if emit.gen_bool(0.6) {
        PrimitiveType::I64
    } else {
        PrimitiveType::String
    }
}

/// Pick a type for the transform variant (i64, string, or bool).
fn pick_transform_type(emit: &mut Emit) -> PrimitiveType {
    match emit.gen_range(0..3) {
        0 => PrimitiveType::I64,
        1 => PrimitiveType::String,
        _ => PrimitiveType::Bool,
    }
}

fn prim_type_name(prim: PrimitiveType) -> &'static str {
    match prim {
        PrimitiveType::I64 => "i64",
        PrimitiveType::String => "string",
        PrimitiveType::Bool => "bool",
        _ => "i64",
    }
}

/// Pick a short string literal.
fn pick_string_literal(emit: &mut Emit) -> String {
    let choices = ["\"hi\"", "\"ok\"", "\"ab\"", "\"yo\""];
    let idx = emit.gen_range(0..choices.len());
    choices[idx].to_string()
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
        assert_eq!(GenericClosureCall.name(), "generic_closure_call");
    }

    #[test]
    fn precondition_rejects_class_methods() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        // No class => precondition passes
        assert!(GenericClosureCall.precondition(&scope, &params));
        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!GenericClosureCall.precondition(&scope, &params));
    }

    #[test]
    fn generates_apply_twice_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericClosureCall.generate(&mut scope, &mut emit, &params) {
                if text.contains("apply_twice_") {
                    found = true;
                    // Verify module decl was registered
                    assert!(
                        !scope.module_decls.is_empty(),
                        "expected module_decl for apply_twice"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("<T>"),
                        "expected generic type param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("f(f(x))"),
                        "expected apply twice body: {decl}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated apply_twice variant in 100 seeds");
    }

    #[test]
    fn generates_transform_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericClosureCall.generate(&mut scope, &mut emit, &params) {
                if text.contains("transform_") {
                    found = true;
                    // Verify module decl was registered
                    assert!(
                        !scope.module_decls.is_empty(),
                        "expected module_decl for transform"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("<T>"),
                        "expected generic type param in decl: {decl}"
                    );
                    assert!(decl.contains("f(x)"), "expected transform body: {decl}");
                    // Result type should be string
                    let result_local = scope.locals.last().expect("should add result local");
                    assert_eq!(
                        result_local.1,
                        TypeInfo::Primitive(PrimitiveType::String),
                        "transform result must be string"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated transform variant in 100 seeds");
    }

    #[test]
    fn adds_result_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = GenericClosureCall.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        // The func name consumes one fresh_name, the result consumes another.
        // Verify at least one local was added.
        assert!(
            !scope.locals.is_empty(),
            "expected result local added to scope"
        );
    }
}
