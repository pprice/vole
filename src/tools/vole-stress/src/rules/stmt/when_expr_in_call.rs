//! Rule: `when` expression used as an inline argument to a function call.
//!
//! Generates a module-level helper function via [`Scope::add_module_decl`],
//! then calls it with a `when` expression as one of its arguments.  This
//! exercises expression evaluation inside call argument lists -- a position
//! the generator doesn't otherwise place `when` expressions in.
//!
//! Two variants are chosen at random:
//!
//! **Variant 0 -- i64 helper**
//! ```vole
//! func helper_12345(a: i64, b: i64) -> i64 {
//!     return a + b
//! }
//! let result = helper_12345(when { x > 5 => 10_i64, _ => 0_i64 }, 5_i64)
//! ```
//!
//! **Variant 1 -- string helper**
//! ```vole
//! func fmt_12345(s: string) -> string {
//!     return "({s})"
//! }
//! let result = fmt_12345(when { x > 5 => "yes", _ => "no" })
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct WhenExprInCall;

impl StmtRule for WhenExprInCall {
    fn name(&self) -> &'static str {
        "when_expr_in_call"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Module-level decls cannot be spliced inside a class body.
        scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..2);
        match variant {
            0 => emit_i64_variant(scope, emit),
            _ => emit_string_variant(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Condition generation
// ---------------------------------------------------------------------------

/// Build a boolean condition for a `when` arm.
///
/// If an i64 variable is in scope, generate a comparison like `x > 5`.
/// Otherwise fall back to a literal `true` or `false`.
fn gen_condition(scope: &Scope, emit: &mut Emit) -> String {
    let i64_ty = TypeInfo::Primitive(PrimitiveType::I64);
    let i64_vars = scope.vars_of_type(&i64_ty);

    if !i64_vars.is_empty() {
        let var = &i64_vars[emit.gen_range(0..i64_vars.len())];
        let ops = ["==", "!=", ">", "<", ">=", "<="];
        let op = ops[emit.gen_range(0..ops.len())];
        let rhs = emit.gen_i64_range(0, 10);
        format!("{} {} {}_i64", var.name, op, rhs)
    } else {
        emit.literal(&TypeInfo::Primitive(PrimitiveType::Bool))
    }
}

// ---------------------------------------------------------------------------
// Variant 0: i64 helper -- when expr as i64 argument
// ---------------------------------------------------------------------------

fn emit_i64_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_id = emit.gen_range(10000..99999);
    let fn_name = format!("helper_{}", fn_id);

    // Emit module-level function: func helper_NNNNN(a: i64, b: i64) -> i64
    let decl = format!(
        "func {}(a: i64, b: i64) -> i64 {{\n    return a + b\n}}",
        fn_name,
    );
    scope.add_module_decl(decl);

    // Build a when expression that produces an i64.
    let cond = gen_condition(scope, emit);
    let true_val = emit.literal(&TypeInfo::Primitive(PrimitiveType::I64));
    let false_val = emit.literal(&TypeInfo::Primitive(PrimitiveType::I64));

    let when_expr = format!("when {{ {} => {}, _ => {} }}", cond, true_val, false_val,);

    // Second argument is a plain i64 literal.
    let other_arg = emit.literal(&TypeInfo::Primitive(PrimitiveType::I64));

    // Randomly decide whether the when expr is the first or second argument.
    let call_expr = if emit.gen_bool(0.5) {
        format!("{}({}, {})", fn_name, when_expr, other_arg)
    } else {
        format!("{}({}, {})", fn_name, other_arg, when_expr)
    };

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    Some(format!("let {} = {}", result_name, call_expr))
}

// ---------------------------------------------------------------------------
// Variant 1: string helper -- when expr as string argument
// ---------------------------------------------------------------------------

fn emit_string_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_id = emit.gen_range(10000..99999);
    let fn_name = format!("fmt_{}", fn_id);

    // Emit module-level function: func fmt_NNNNN(s: string) -> string
    let decl = format!(
        "func {}(s: string) -> string {{\n    return \"(\" + s + \")\"\n}}",
        fn_name,
    );
    scope.add_module_decl(decl);

    // Build a when expression that produces a string.
    let cond = gen_condition(scope, emit);

    let string_literals = [
        "\"yes\"", "\"no\"", "\"ok\"", "\"err\"", "\"on\"", "\"off\"",
    ];
    let true_val = string_literals[emit.gen_range(0..string_literals.len())];
    let false_val = string_literals[emit.gen_range(0..string_literals.len())];

    let when_expr = format!("when {{ {} => {}, _ => {} }}", cond, true_val, false_val,);

    let call_expr = format!("{}({})", fn_name, when_expr);

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    Some(format!("let {} = {}", result_name, call_expr))
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
        assert_eq!(WhenExprInCall.name(), "when_expr_in_call");
    }

    #[test]
    fn precondition_rejects_class_methods() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(WhenExprInCall.precondition(&scope, &params));

        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!WhenExprInCall.precondition(&scope, &params));
    }

    #[test]
    fn generates_i64_variant() {
        let table = SymbolTable::new();
        let mut found = false;

        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = WhenExprInCall.generate(&mut scope, &mut emit, &params) {
                if text.contains("helper_") {
                    found = true;
                    assert!(text.contains("when {"), "expected when expr, got: {text}");
                    assert!(text.contains("=>"), "expected =>, got: {text}");
                    assert!(
                        !scope.module_decls.is_empty(),
                        "expected module decl for i64 variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> i64"),
                        "expected i64 return in decl: {decl}"
                    );
                    let result_local = scope.locals.last().expect("should have result local");
                    assert_eq!(result_local.1, TypeInfo::Primitive(PrimitiveType::I64));
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
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = WhenExprInCall.generate(&mut scope, &mut emit, &params) {
                if text.contains("fmt_") {
                    found = true;
                    assert!(text.contains("when {"), "expected when expr, got: {text}");
                    assert!(text.contains("=>"), "expected =>, got: {text}");
                    assert!(
                        !scope.module_decls.is_empty(),
                        "expected module decl for string variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> string"),
                        "expected string return in decl: {decl}"
                    );
                    let result_local = scope.locals.last().expect("should have result local");
                    assert_eq!(result_local.1, TypeInfo::Primitive(PrimitiveType::String));
                    break;
                }
            }
        }
        assert!(found, "never generated string variant in 100 seeds");
    }

    #[test]
    fn uses_scope_variable_in_condition() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "myvar".into(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WhenExprInCall.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains("myvar"),
            "expected scope variable in condition, got: {text}"
        );
    }

    #[test]
    fn adds_module_decl() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        WhenExprInCall.generate(&mut scope, &mut emit, &params);
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
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        WhenExprInCall.generate(&mut scope, &mut emit, &params);
        assert_eq!(scope.locals.len(), initial_len + 1);
    }
}
