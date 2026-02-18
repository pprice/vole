//! Rule: for statement.
//!
//! Generates for-in loops over:
//! - Numeric ranges: `for x in start..end { ... }`
//! - Array variables: `for elem in arr { ... }`
//! - Iterator chains: `for x in arr.iter().filter/map/sorted/take(...) { ... }`
//! - Enumerate: `for pair in arr.iter().enumerate() { ... }`
//! - Zip: `for pair in a.iter().zip(b.iter()) { ... }`

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ForStmt;

impl StmtRule for ForStmt {
    fn name(&self) -> &'static str {
        "for_stmt"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.08)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.can_recurse()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let array_vars = scope.array_vars();

        // Filter to arrays with primitive element types
        let prim_array_vars: Vec<(String, PrimitiveType)> = array_vars
            .iter()
            .filter_map(|(name, elem_ty)| match elem_ty {
                TypeInfo::Primitive(
                    p @ (PrimitiveType::I64
                    | PrimitiveType::F64
                    | PrimitiveType::Bool
                    | PrimitiveType::String),
                ) => Some((name.clone(), *p)),
                _ => None,
            })
            .collect();

        // ~8% chance for enumerate (needs i64 arrays)
        if !prim_array_vars.is_empty() && emit.gen_bool(0.08) {
            let i64_arrays: Vec<_> = prim_array_vars
                .iter()
                .filter(|(_, p)| matches!(p, PrimitiveType::I64))
                .cloned()
                .collect();
            if !i64_arrays.is_empty() {
                return Some(gen_enumerate(scope, emit, &i64_arrays));
            }
        }

        // ~6% chance for zip (needs 2+ i64 arrays)
        if prim_array_vars.len() >= 2 && emit.gen_bool(0.06) {
            let i64_arrays: Vec<_> = prim_array_vars
                .iter()
                .filter(|(_, p)| matches!(p, PrimitiveType::I64))
                .cloned()
                .collect();
            if i64_arrays.len() >= 2 {
                return Some(gen_zip(scope, emit, &i64_arrays));
            }
        }

        // ~20% iterator chain when primitive arrays available
        if !prim_array_vars.is_empty() && emit.gen_bool(0.2) {
            return Some(gen_iterator(scope, emit, &prim_array_vars));
        }

        // ~40% array iteration when arrays available
        if !array_vars.is_empty() && emit.gen_bool(0.4) {
            return Some(gen_array(scope, emit, &array_vars));
        }

        Some(gen_range(scope, emit))
    }
}

// ---------------------------------------------------------------------------
// For-in-range
// ---------------------------------------------------------------------------

fn gen_range(scope: &mut Scope, emit: &mut Emit) -> String {
    let iter_name = scope.fresh_name();
    let inclusive = emit.gen_bool(0.5);
    let range = gen_range_expr(emit, inclusive);

    let body = scope.enter_scope(|inner| {
        inner.in_loop = true;
        inner.in_while_loop = false;
        inner.add_local(
            iter_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );
        let n = emit.random_in(1, 3);
        emit.block(inner, n)
    });

    let indent = emit.indent_str();
    format!("for {} in {} {{\n{}\n{}}}", iter_name, range, body, indent)
}

fn gen_range_expr(emit: &mut Emit, inclusive: bool) -> String {
    // ~10% chance for edge-case range
    if emit.gen_bool(0.10) {
        let start = emit.random_in(0, 2);
        return match emit.gen_range(0..3) {
            0 => format!("{}..{}", start, start),
            1 => format!("{}..={}", start, start),
            _ => format!("{}..{}", start, start + 1),
        };
    }

    let start = emit.random_in(0, 2);
    if inclusive {
        let end = emit.random_in(0, 4);
        format!("{}..={}", start, end)
    } else {
        let end = emit.random_in(1, 5);
        format!("{}..{}", start, end)
    }
}

// ---------------------------------------------------------------------------
// For-in-array
// ---------------------------------------------------------------------------

fn gen_array(scope: &mut Scope, emit: &mut Emit, array_vars: &[(String, TypeInfo)]) -> String {
    let iter_name = scope.fresh_name();
    let idx = emit.gen_range(0..array_vars.len());
    let (arr_name, elem_type) = &array_vars[idx];
    let arr_name = arr_name.clone();
    let elem_type = elem_type.clone();

    let body = scope.enter_scope(|inner| {
        inner.in_loop = true;
        inner.in_while_loop = false;
        inner.add_local(iter_name.clone(), elem_type, false);
        inner.protected_vars.push(arr_name.clone());
        let n = emit.random_in(1, 3);
        emit.block(inner, n)
    });

    let indent = emit.indent_str();
    format!(
        "for {} in {} {{\n{}\n{}}}",
        iter_name, arr_name, body, indent
    )
}

// ---------------------------------------------------------------------------
// For-in-iterator
// ---------------------------------------------------------------------------

fn gen_iterator(
    scope: &mut Scope,
    emit: &mut Emit,
    prim_array_vars: &[(String, PrimitiveType)],
) -> String {
    let iter_name = scope.fresh_name();
    let idx = emit.gen_range(0..prim_array_vars.len());
    let (arr_name, elem_prim) = &prim_array_vars[idx];
    let arr_name = arr_name.clone();
    let elem_prim = *elem_prim;
    let is_numeric = matches!(elem_prim, PrimitiveType::I64 | PrimitiveType::F64);

    // Pick first chain operation
    let chain = gen_chain_op(emit, elem_prim, is_numeric);

    // ~25% chance for a second chain operation
    let chain = if emit.gen_bool(0.25) {
        let second = gen_second_chain_op(emit, elem_prim, is_numeric);
        format!("{}{}", chain, second)
    } else {
        chain
    };

    let body = scope.enter_scope(|inner| {
        inner.in_loop = true;
        inner.in_while_loop = false;
        inner.add_local(iter_name.clone(), TypeInfo::Primitive(elem_prim), false);
        inner.protected_vars.push(arr_name.clone());
        let n = emit.random_in(1, 3);
        emit.block(inner, n)
    });

    let indent = emit.indent_str();
    format!(
        "for {} in {}.iter(){} {{\n{}\n{}}}",
        iter_name, arr_name, chain, body, indent
    )
}

fn gen_chain_op(emit: &mut Emit, elem_prim: PrimitiveType, is_numeric: bool) -> String {
    if is_numeric {
        match emit.gen_range(0..10) {
            0..3 => {
                let pred = gen_filter_pred(emit, elem_prim);
                format!(".filter((x) => {})", pred)
            }
            3..6 => {
                let body = gen_map_body(emit, elem_prim);
                format!(".map((x) => {})", body)
            }
            6..8 => ".sorted()".to_string(),
            _ => {
                let n = emit.random_in(1, 3);
                format!(".take({})", n)
            }
        }
    } else {
        match emit.gen_range(0..10) {
            0..4 => {
                let pred = gen_filter_pred(emit, elem_prim);
                format!(".filter((x) => {})", pred)
            }
            4..7 => {
                let body = gen_map_body(emit, elem_prim);
                format!(".map((x) => {})", body)
            }
            _ => {
                let n = emit.random_in(1, 3);
                format!(".take({})", n)
            }
        }
    }
}

fn gen_second_chain_op(emit: &mut Emit, elem_prim: PrimitiveType, is_numeric: bool) -> String {
    if is_numeric {
        match emit.gen_range(0..4) {
            0 => {
                let pred = gen_filter_pred(emit, elem_prim);
                format!(".filter((x) => {})", pred)
            }
            1 => ".sorted()".to_string(),
            2 => ".reverse()".to_string(),
            _ => {
                let n = emit.random_in(1, 3);
                format!(".take({})", n)
            }
        }
    } else {
        match emit.gen_range(0..3) {
            0 => {
                let pred = gen_filter_pred(emit, elem_prim);
                format!(".filter((x) => {})", pred)
            }
            1 => ".reverse()".to_string(),
            _ => {
                let n = emit.random_in(1, 3);
                format!(".take({})", n)
            }
        }
    }
}

fn gen_filter_pred(emit: &mut Emit, prim: PrimitiveType) -> String {
    match prim {
        PrimitiveType::I64 => {
            let n = emit.gen_i64_range(0, 5);
            format!("x > {}", n)
        }
        PrimitiveType::F64 => {
            let n = emit.gen_i64_range(0, 10);
            format!("x > {}.0", n)
        }
        PrimitiveType::Bool => "x".to_string(),
        PrimitiveType::String => {
            let n = emit.gen_i64_range(0, 3);
            format!("x.length() > {}", n)
        }
        _ => "true".to_string(),
    }
}

fn gen_map_body(emit: &mut Emit, prim: PrimitiveType) -> String {
    match prim {
        PrimitiveType::I64 => match emit.gen_range(0..3) {
            0 => "x * 2".to_string(),
            1 => "x + 1".to_string(),
            _ => "-x".to_string(),
        },
        PrimitiveType::F64 => match emit.gen_range(0..3) {
            0 => "x * 2.0".to_string(),
            1 => "x + 1.0".to_string(),
            _ => "-x".to_string(),
        },
        PrimitiveType::Bool => "!x".to_string(),
        PrimitiveType::String => match emit.gen_range(0..3) {
            0 => "x.trim()".to_string(),
            1 => "x.to_upper()".to_string(),
            _ => "x.to_lower()".to_string(),
        },
        _ => "x".to_string(),
    }
}

// ---------------------------------------------------------------------------
// For-in-enumerate
// ---------------------------------------------------------------------------

fn gen_enumerate(
    scope: &mut Scope,
    emit: &mut Emit,
    i64_arrays: &[(String, PrimitiveType)],
) -> String {
    let pair_name = scope.fresh_name();
    let acc_name = scope.fresh_name();

    let idx = emit.gen_range(0..i64_arrays.len());
    let (arr_name, _) = &i64_arrays[idx];
    let arr_name = arr_name.clone();

    // Optional prefix chain: ~20% chance
    let prefix = if emit.gen_bool(0.20) {
        match emit.gen_range(0..2) {
            0 => {
                let n = emit.random_in(1, 3);
                format!(".take({})", n)
            }
            _ => {
                let pred = gen_filter_pred(emit, PrimitiveType::I64);
                format!(".filter((x) => {})", pred)
            }
        }
    } else {
        String::new()
    };

    // Pick accumulation body
    let body_expr = match emit.gen_range(0..3) {
        0 => format!(
            "{} = {} + {}[0] + {}[1]",
            acc_name, acc_name, pair_name, pair_name
        ),
        1 => format!("{} = {} + {}[0]", acc_name, acc_name, pair_name),
        _ => format!("{} = {} + {}[1]", acc_name, acc_name, pair_name),
    };

    scope.protected_vars.push(arr_name.clone());
    scope.add_local(
        acc_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        true,
    );

    let indent = emit.indent_str();
    emit.indented(|_emit| {
        let inner_indent = format!("{}    ", indent);
        format!(
            "let mut {} = 0\n{}for {} in {}.iter(){}.enumerate() {{\n{}{}\n{}}}",
            acc_name, indent, pair_name, arr_name, prefix, inner_indent, body_expr, indent
        )
    })
}

// ---------------------------------------------------------------------------
// For-in-zip
// ---------------------------------------------------------------------------

fn gen_zip(scope: &mut Scope, emit: &mut Emit, i64_arrays: &[(String, PrimitiveType)]) -> String {
    let pair_name = scope.fresh_name();
    let acc_name = scope.fresh_name();

    // Pick two distinct arrays
    let idx_a = emit.gen_range(0..i64_arrays.len());
    let mut idx_b = emit.gen_range(0..i64_arrays.len());
    if idx_b == idx_a {
        idx_b = (idx_a + 1) % i64_arrays.len();
    }
    let (arr_a, _) = &i64_arrays[idx_a];
    let (arr_b, _) = &i64_arrays[idx_b];
    let arr_a = arr_a.clone();
    let arr_b = arr_b.clone();

    // Pick accumulation body
    let body_expr = match emit.gen_range(0..3) {
        0 => format!(
            "{} = {} + {}[0] + {}[1]",
            acc_name, acc_name, pair_name, pair_name
        ),
        1 => format!(
            "{} = {} + ({}[0] * {}[1])",
            acc_name, acc_name, pair_name, pair_name
        ),
        _ => format!(
            "{} = {} + {}[0] - {}[1]",
            acc_name, acc_name, pair_name, pair_name
        ),
    };

    scope.protected_vars.push(arr_a.clone());
    scope.protected_vars.push(arr_b.clone());
    scope.add_local(
        acc_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        true,
    );

    let indent = emit.indent_str();
    emit.indented(|_emit| {
        let inner_indent = format!("{}    ", indent);
        format!(
            "let mut {} = 0\n{}for {} in {}.iter().zip({}.iter()) {{\n{}{}\n{}}}",
            acc_name, indent, pair_name, arr_a, arr_b, inner_indent, body_expr, indent,
        )
    })
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
        assert_eq!(ForStmt.name(), "for_stmt");
    }

    #[test]
    fn generates_range_for_loop() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ForStmt.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("for "), "expected for, got: {text}");
        assert!(text.contains(".."), "expected range, got: {text}");
    }

    #[test]
    fn generates_array_for_loop() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "arr".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );

        let resolved = ResolvedParams::new();
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        // Run several times - at least some should iterate over the array
        let mut found_arr = false;
        for seed in 0..20 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut emit = test_emit(&mut rng, &resolved);
            if let Some(text) = ForStmt.generate(&mut scope, &mut emit, &params) {
                if text.contains("in arr") {
                    found_arr = true;
                    break;
                }
            }
        }
        assert!(found_arr, "expected at least one array iteration");
    }

    #[test]
    fn respects_depth_limit() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.depth = scope.max_depth;
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!ForStmt.precondition(&scope, &params));
    }
}
