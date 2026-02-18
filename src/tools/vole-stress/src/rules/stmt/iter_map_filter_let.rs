//! Rule: iterator map/filter chain let-binding.
//!
//! Generates complex iterator chains on arrays with primitive element types:
//! `.iter().map(...)`, `.iter().filter(...)`, `.iter().map(...).filter(...)`,
//! `.iter().sorted().map(...)`, `.iter().enumerate().count()`, etc.
//!
//! Terminals include `.collect()`, `.count()`, `.sum()`, `.reduce()`,
//! `.take(N).collect()`, `.first()`, `.last()`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct IterMapFilterLet;

impl StmtRule for IterMapFilterLet {
    fn name(&self) -> &'static str {
        "iter_map_filter_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.10)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let prim_array_vars: Vec<(String, PrimitiveType)> = scope
            .array_vars()
            .into_iter()
            .filter_map(|(name, elem_ty)| {
                if let TypeInfo::Primitive(prim) = elem_ty {
                    match prim {
                        PrimitiveType::I64
                        | PrimitiveType::F64
                        | PrimitiveType::Bool
                        | PrimitiveType::String => Some((name, prim)),
                        _ => None,
                    }
                } else {
                    None
                }
            })
            .collect();

        if prim_array_vars.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..prim_array_vars.len());
        let (arr_name, elem_prim) = &prim_array_vars[idx];
        let elem_prim = *elem_prim;
        let arr_name = arr_name.clone();

        let name = scope.fresh_name();

        let prefix = generate_prefix(emit, elem_prim);
        let (chain, enumerate_terminal) = generate_chain(emit, elem_prim);

        // If the enumerate chain already includes its terminal, use that directly.
        if let Some((terminal, result_type)) = enumerate_terminal {
            scope.add_local(name.clone(), result_type, false);
            return Some(format!(
                "let {} = {}.iter(){}{}{}",
                name, arr_name, prefix, chain, terminal
            ));
        }

        let (terminal, result_type) = generate_terminal(emit, elem_prim);

        scope.add_local(name.clone(), result_type, false);
        Some(format!(
            "let {} = {}.iter(){}{}{}",
            name, arr_name, prefix, chain, terminal
        ))
    }
}

/// Optionally prepend `.sorted()`, `.reverse()`, `.unique()`, or `.skip(N)` (~25%).
fn generate_prefix(emit: &mut Emit, elem_prim: PrimitiveType) -> String {
    let is_numeric = matches!(elem_prim, PrimitiveType::I64 | PrimitiveType::F64);
    if emit.gen_bool(0.25) {
        match emit.gen_range(0..4) {
            0 if is_numeric => ".sorted()".to_string(),
            1 => ".reverse()".to_string(),
            2 if elem_prim != PrimitiveType::Bool => ".unique()".to_string(),
            3 => format!(".skip({})", emit.gen_range(0..2)),
            _ => ".reverse()".to_string(),
        }
    } else {
        String::new()
    }
}

/// Build the iterator chain: 1-2 operations before the terminal.
///
/// Returns `(chain_string, Option<(terminal, result_type)>)`.
/// When the second element is `Some`, the chain includes its own terminal
/// (e.g. `.enumerate().count()`) and bypasses normal terminal selection.
fn generate_chain(
    emit: &mut Emit,
    elem_prim: PrimitiveType,
) -> (String, Option<(String, TypeInfo)>) {
    let is_numeric = matches!(elem_prim, PrimitiveType::I64 | PrimitiveType::F64);
    let chain_choice = emit.gen_range(0..23);

    if chain_choice < 6 {
        // Single .map()
        let map_body = map_closure_body(emit, elem_prim, "x");
        (format!(".map((x) => {})", map_body), None)
    } else if chain_choice < 11 {
        // Single .filter()
        let filter_body = filter_closure_body(emit, elem_prim, "x");
        (format!(".filter((x) => {})", filter_body), None)
    } else if chain_choice < 14 {
        // Chained .map().filter()
        let map_body = map_closure_body(emit, elem_prim, "x");
        let filter_body = filter_closure_body(emit, elem_prim, "y");
        (
            format!(".map((x) => {}).filter((y) => {})", map_body, filter_body),
            None,
        )
    } else if chain_choice < 17 && is_numeric {
        // .sorted() before .map()
        let map_body = map_closure_body(emit, elem_prim, "x");
        (format!(".sorted().map((x) => {})", map_body), None)
    } else if chain_choice < 20 && is_numeric {
        // .filter() then .sorted()
        let filter_body = filter_closure_body(emit, elem_prim, "x");
        (format!(".filter((x) => {}).sorted()", filter_body), None)
    } else if chain_choice < 21 {
        // .enumerate().count()
        (
            ".enumerate().count()".to_string(),
            Some((String::new(), TypeInfo::Primitive(PrimitiveType::I64))),
        )
    } else if chain_choice < 23 && is_numeric {
        // .enumerate().filter(...).map(...)
        let pred = match elem_prim {
            PrimitiveType::I64 => "(e) => e[1] > 0_i64",
            PrimitiveType::F64 => "(e) => e[1] > 0.0_f64",
            _ => "(e) => true",
        };
        (
            format!(".enumerate().filter({}).map((e) => e[1])", pred),
            None,
        )
    } else {
        // Chained .filter().map()
        let filter_body = filter_closure_body(emit, elem_prim, "x");
        let map_body = map_closure_body(emit, elem_prim, "y");
        (
            format!(".filter((x) => {}).map((y) => {})", filter_body, map_body),
            None,
        )
    }
}

/// Pick a terminal operation for the chain.
fn generate_terminal(emit: &mut Emit, elem_prim: PrimitiveType) -> (String, TypeInfo) {
    let terminal_choice = emit.gen_range(0..24);

    if terminal_choice < 8 {
        // .collect() -> [T]
        (
            ".collect()".to_string(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_prim))),
        )
    } else if terminal_choice < 11 {
        // .count() -> i64
        (
            ".count()".to_string(),
            TypeInfo::Primitive(PrimitiveType::I64),
        )
    } else if terminal_choice < 14 {
        // .sum() only valid for numeric types
        match elem_prim {
            PrimitiveType::I64 | PrimitiveType::F64 => {
                (".sum()".to_string(), TypeInfo::Primitive(elem_prim))
            }
            _ => (
                ".count()".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            ),
        }
    } else if terminal_choice < 17 {
        // .reduce()
        if elem_prim == PrimitiveType::Bool {
            (
                ".collect()".to_string(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_prim))),
            )
        } else {
            let (init, body, result_ty) = reduce_closure(emit, elem_prim);
            (
                format!(".reduce({}, (acc, el) => {})", init, body),
                result_ty,
            )
        }
    } else if terminal_choice < 20 {
        // .take(N).collect()
        let n = emit.random_in(1, 3);
        (
            format!(".take({}).collect()", n),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_prim))),
        )
    } else {
        // .first() or .last() -> T? or T (with ??)
        let method = if emit.gen_bool(0.5) {
            ".first()"
        } else {
            ".last()"
        };
        if emit.gen_bool(0.5) {
            // Produce T? -- optional local
            (
                method.to_string(),
                TypeInfo::Optional(Box::new(TypeInfo::Primitive(elem_prim))),
            )
        } else {
            // Immediately unwrap with ?? default -- produces T
            let default_val = emit.literal(&TypeInfo::Primitive(elem_prim));
            (
                format!("{} ?? {}", method, default_val),
                TypeInfo::Primitive(elem_prim),
            )
        }
    }
}

/// Generate a map closure body for the given element type and parameter name.
fn map_closure_body(emit: &mut Emit, elem_prim: PrimitiveType, param: &str) -> String {
    match elem_prim {
        PrimitiveType::I64 => match emit.gen_range(0..3) {
            0 => {
                let n = emit.random_in(2, 5);
                format!("{} * {}", param, n)
            }
            1 => {
                let n = emit.random_in(1, 10);
                format!("{} + {}", param, n)
            }
            _ => {
                let n = emit.random_in(1, 3);
                format!("{} - {}", param, n)
            }
        },
        PrimitiveType::F64 => match emit.gen_range(0..2) {
            0 => {
                let n = emit.random_in(2, 5);
                format!("{} * {}.0", param, n)
            }
            _ => {
                let n = emit.random_in(1, 10);
                format!("{} + {}.0", param, n)
            }
        },
        PrimitiveType::Bool => format!("!{}", param),
        PrimitiveType::String => match emit.gen_range(0..3) {
            0 => format!("{}.to_upper()", param),
            1 => format!("{}.to_lower()", param),
            _ => format!("{}.trim()", param),
        },
        _ => param.to_string(),
    }
}

/// Generate a filter closure body (boolean predicate) for the given element type.
fn filter_closure_body(emit: &mut Emit, elem_prim: PrimitiveType, param: &str) -> String {
    match elem_prim {
        PrimitiveType::I64 => match emit.gen_range(0..3) {
            0 => {
                let n = emit.gen_i64_range(-5, 2);
                format!("{} > {}", param, n)
            }
            1 => {
                let n = emit.gen_i64_range(5, 20);
                format!("{} < {}", param, n)
            }
            _ => format!("{} % 2 == 0", param),
        },
        PrimitiveType::F64 => {
            let n = emit.gen_i64_range(0, 20);
            format!("{} > {}.0", param, n)
        }
        PrimitiveType::Bool => {
            if emit.gen_bool(0.5) {
                param.to_string()
            } else {
                format!("!{}", param)
            }
        }
        PrimitiveType::String => {
            let n = emit.gen_range(0..2);
            format!("{}.length() > {}", param, n)
        }
        _ => "true".to_string(),
    }
}

/// Generate a `.reduce()` closure: `(init, body, result_type)`.
fn reduce_closure(emit: &mut Emit, elem_prim: PrimitiveType) -> (String, String, TypeInfo) {
    match elem_prim {
        PrimitiveType::I64 => match emit.gen_range(0..4) {
            0 => (
                "0".to_string(),
                "acc + el".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            ),
            1 => {
                let n = emit.random_in(1, 3);
                (
                    format!("{}", n),
                    "acc * el".to_string(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                )
            }
            2 => {
                let threshold = emit.gen_range(0..6);
                (
                    "0".to_string(),
                    format!("when {{ el > {} => acc + el, _ => acc }}", threshold),
                    TypeInfo::Primitive(PrimitiveType::I64),
                )
            }
            _ => (
                "0".to_string(),
                "when { el > acc => el, _ => acc }".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            ),
        },
        PrimitiveType::F64 => (
            "0.0".to_string(),
            "acc + el".to_string(),
            TypeInfo::Primitive(PrimitiveType::F64),
        ),
        PrimitiveType::String => {
            let sep = if emit.gen_bool(0.5) { "," } else { " " };
            (
                "\"\"".to_string(),
                format!("acc + el + \"{}\"", sep),
                TypeInfo::Primitive(PrimitiveType::String),
            )
        }
        _ => (
            "0".to_string(),
            "acc + 1".to_string(),
            TypeInfo::Primitive(PrimitiveType::I64),
        ),
    }
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
        assert_eq!(IterMapFilterLet.name(), "iter_map_filter_let");
    }

    #[test]
    fn generates_map_or_filter() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "arr".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterMapFilterLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".iter()"), "got: {text}");
    }

    #[test]
    fn returns_none_without_arrays() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            IterMapFilterLet
                .generate(&mut scope, &mut emit, &rule_params)
                .is_none()
        );
    }

    #[test]
    fn exercises_multiple_seeds() {
        // Run with many seeds to exercise different chain/terminal paths
        let table = SymbolTable::new();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.add_local(
                "nums".into(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                false,
            );
            scope.add_local(
                "strs".into(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                false,
            );

            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            let result = IterMapFilterLet.generate(&mut scope, &mut emit, &rule_params);
            assert!(result.is_some(), "seed {} returned None", seed);
            let text = result.unwrap();
            assert!(
                text.starts_with("let "),
                "seed {} unexpected: {}",
                seed,
                text
            );
        }
    }
}
