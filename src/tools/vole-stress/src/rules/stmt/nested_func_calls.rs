//! Rule: deeply nested function calls like `f(g(h(x)))`.
//!
//! Generates 4-6 small expression-body helper functions, then composes them
//! into a single deeply-nested call expression and binds the result.
//!
//! Three variants are chosen at random:
//! 1. **Pure i64 chain**: all functions `i64 -> i64`.
//! 2. **String chain**: all functions `string -> string`.
//! 3. **Mixed ending in string**: 3-4 `i64 -> i64` functions, then one that
//!    converts to string via interpolation.
//!
//! This stresses deeply nested call expressions, return-value threading, and
//! register allocation under many live temporaries.
//!
//! ```vole
//! func local0(x: i64) -> i64 => x * 2
//! func local1(x: i64) -> i64 => x + 1
//! func local2(x: i64) -> i64 => x * x
//! func local3(x: i64) -> i64 => x - 3
//! let local4 = local3(local2(local1(local0(5_i64))))
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct NestedFuncCalls;

/// Variant of the nested call chain.
#[derive(Debug, Clone, Copy)]
enum Variant {
    /// All functions are `i64 -> i64`.
    PureI64,
    /// All functions are `string -> string`.
    StringChain,
    /// 3-4 `i64 -> i64` functions, then one final `i64 -> string`.
    MixedToString,
}

/// A helper function definition.
struct FuncDef {
    /// The generated function name.
    name: String,
    /// The parameter type.
    param_type: PrimitiveType,
    /// The return type.
    return_type: PrimitiveType,
    /// The expression body (after `=>`).
    body: String,
}

impl StmtRule for NestedFuncCalls {
    fn name(&self) -> &'static str {
        "nested_func_calls"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.can_recurse()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Pick 4-6 functions in the chain.
        let depth = emit.random_in(4, 6);

        // Pick a variant.
        let variant = match emit.gen_range(0..3) {
            0 => Variant::PureI64,
            1 => Variant::StringChain,
            _ => Variant::MixedToString,
        };

        // Generate helper function definitions.
        let funcs = build_func_defs(scope, emit, variant, depth);

        // Build output lines.
        let indent = emit.indent_str();
        let mut lines = Vec::with_capacity(funcs.len() + 1);

        // Emit each function definition.
        for f in &funcs {
            lines.push(format!(
                "func {}(x: {}) -> {} => {}",
                f.name,
                f.param_type.as_str(),
                f.return_type.as_str(),
                f.body,
            ));
        }

        // Build the nested call: fn_N(fn_N-1(...(fn_0(initial_value))...))
        let initial_value = match funcs[0].param_type {
            PrimitiveType::I64 => emit.literal(&TypeInfo::Primitive(PrimitiveType::I64)),
            PrimitiveType::String => emit.literal(&TypeInfo::Primitive(PrimitiveType::String)),
            _ => emit.literal(&TypeInfo::Primitive(PrimitiveType::I64)),
        };

        let mut nested = initial_value;
        for f in &funcs {
            nested = format!("{}({})", f.name, nested);
        }

        let result_name = scope.fresh_name();
        let result_type = match funcs.last().unwrap().return_type {
            PrimitiveType::I64 => TypeInfo::Primitive(PrimitiveType::I64),
            PrimitiveType::String => TypeInfo::Primitive(PrimitiveType::String),
            other => TypeInfo::Primitive(other),
        };

        lines.push(format!("let {} = {}", result_name, nested));

        scope.add_local(result_name, result_type, false);

        Some(lines.join(&format!("\n{}", indent)))
    }
}

/// Build the list of function definitions for the given variant and depth.
fn build_func_defs(
    scope: &mut Scope,
    emit: &mut Emit,
    variant: Variant,
    depth: usize,
) -> Vec<FuncDef> {
    match variant {
        Variant::PureI64 => build_i64_chain(scope, emit, depth),
        Variant::StringChain => build_string_chain(scope, emit, depth),
        Variant::MixedToString => build_mixed_chain(scope, emit, depth),
    }
}

/// Build a chain of `i64 -> i64` functions.
fn build_i64_chain(scope: &mut Scope, emit: &mut Emit, depth: usize) -> Vec<FuncDef> {
    let bodies = [
        |emit: &mut Emit| {
            let n = emit.random_in(2, 5);
            format!("x * {}_i64", n)
        },
        |emit: &mut Emit| {
            let n = emit.random_in(1, 10);
            format!("x + {}_i64", n)
        },
        |_emit: &mut Emit| "x * x".to_string(),
        |emit: &mut Emit| {
            let n = emit.random_in(1, 5);
            format!("x - {}_i64", n)
        },
        |emit: &mut Emit| {
            let n = emit.random_in(1, 100);
            format!("x + {}_i64", n)
        },
        |_emit: &mut Emit| "0_i64 - x".to_string(),
    ];

    let mut funcs = Vec::with_capacity(depth);
    for _ in 0..depth {
        let idx = emit.gen_range(0..bodies.len());
        let body = bodies[idx](emit);
        let name = scope.fresh_name();
        funcs.push(FuncDef {
            name,
            param_type: PrimitiveType::I64,
            return_type: PrimitiveType::I64,
            body,
        });
    }
    funcs
}

/// Build a chain of `string -> string` functions.
fn build_string_chain(scope: &mut Scope, emit: &mut Emit, depth: usize) -> Vec<FuncDef> {
    let bodies: Vec<fn(&mut Emit) -> String> = vec![
        |_emit: &mut Emit| "x.trim()".to_string(),
        |_emit: &mut Emit| "x.to_lower()".to_string(),
        |_emit: &mut Emit| "x.to_upper()".to_string(),
        |_emit: &mut Emit| "\"[\" + x + \"]\"".to_string(),
        |_emit: &mut Emit| "x + \"_end\"".to_string(),
        |_emit: &mut Emit| "\"pre_\" + x".to_string(),
        |_emit: &mut Emit| "x.replace(\"a\", \"b\")".to_string(),
    ];

    let mut funcs = Vec::with_capacity(depth);
    for _ in 0..depth {
        let idx = emit.gen_range(0..bodies.len());
        let body = bodies[idx](emit);
        let name = scope.fresh_name();
        funcs.push(FuncDef {
            name,
            param_type: PrimitiveType::String,
            return_type: PrimitiveType::String,
            body,
        });
    }
    funcs
}

/// Build a chain of 3-4 `i64 -> i64` functions followed by one `i64 -> string`.
fn build_mixed_chain(scope: &mut Scope, emit: &mut Emit, depth: usize) -> Vec<FuncDef> {
    // Use depth-1 i64 functions, then 1 final i64->string converter.
    let i64_count = depth - 1;
    let mut funcs = build_i64_chain(scope, emit, i64_count);

    // Add the final converter function.
    let converter_name = scope.fresh_name();
    let converter_idx = emit.gen_range(0..3);
    let body = match converter_idx {
        0 => "\"result: ${x}\"".to_string(),
        1 => "\"val=\" + x.to_string()".to_string(),
        _ => "\"[${x}]\"".to_string(),
    };

    funcs.push(FuncDef {
        name: converter_name,
        param_type: PrimitiveType::I64,
        return_type: PrimitiveType::String,
        body,
    });
    funcs
}

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
        assert_eq!(NestedFuncCalls.name(), "nested_func_calls");
    }

    #[test]
    fn generates_functions_and_nested_call() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = NestedFuncCalls.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        // Should contain at least 4 `func` definitions.
        let func_count = text.matches("func ").count();
        assert!(
            func_count >= 4,
            "expected >= 4 func defs, got {func_count} in: {text}"
        );
        // Should contain the nested call result binding.
        assert!(text.contains("let "), "expected let binding, got: {text}");
    }

    #[test]
    fn adds_result_local_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        NestedFuncCalls.generate(&mut scope, &mut emit, &rule_params);
        // Should add 1 local (the call result).
        assert_eq!(scope.locals.len(), initial_len + 1);
    }

    #[test]
    fn respects_depth_limit() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.depth = scope.max_depth;
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!NestedFuncCalls.precondition(&scope, &params));
    }

    #[test]
    fn generates_all_three_variants() {
        let table = SymbolTable::new();
        let mut found_pure_i64 = false;
        let mut found_string = false;
        let mut found_mixed = false;

        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = NestedFuncCalls.generate(&mut scope, &mut emit, &rule_params) {
                let has_string_param = text.contains("(x: string)");
                let has_i64_to_string = text.contains("-> string => \"");

                if !has_string_param && !has_i64_to_string {
                    // Pure i64 chain: all params i64, all returns i64.
                    found_pure_i64 = true;
                } else if has_string_param {
                    // String chain: at least one string param.
                    found_string = true;
                } else if has_i64_to_string {
                    // Mixed chain: has an i64 -> string converter.
                    found_mixed = true;
                }
            }
        }
        assert!(found_pure_i64, "never generated pure i64 variant");
        assert!(found_string, "never generated string chain variant");
        assert!(found_mixed, "never generated mixed-to-string variant");
    }

    #[test]
    fn nested_call_has_correct_depth() {
        let table = SymbolTable::new();

        for seed in 0..20 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = NestedFuncCalls.generate(&mut scope, &mut emit, &rule_params) {
                let func_count = text.matches("func ").count();
                assert!(
                    (4..=6).contains(&func_count),
                    "expected 4-6 func defs, got {func_count} for seed {seed}: {text}"
                );

                // The last line should be the let binding with nested calls.
                let last_line = text.lines().last().unwrap();
                assert!(
                    last_line.contains("let "),
                    "last line should be let binding for seed {seed}: {last_line}"
                );
                // Count nesting: number of opening parens in the nested call
                // should match the number of functions.
                let let_eq_idx = last_line.find(" = ").unwrap();
                let call_expr = &last_line[let_eq_idx + 3..];
                let open_parens = call_expr.chars().filter(|c| *c == '(').count();
                assert!(
                    open_parens >= func_count,
                    "expected >= {func_count} nested calls, got {open_parens} parens for seed {seed}: {call_expr}"
                );
            }
        }
    }
}
