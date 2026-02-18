//! Rule: range-based iterator chain let-binding.
//!
//! Generates a range with an iterator chain and terminal:
//! ```vole
//! let r = (0..5).iter().map((x) => x * 2).collect()
//! let r = (1..=3).iter().filter((x) => x > 1).sum()
//! ```
//!
//! Supports various chain patterns: single map, single filter,
//! map+filter, filter+map, sorted+map, filter+sorted.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct RangeIterLet;

impl StmtRule for RangeIterLet {
    fn name(&self) -> &'static str {
        "range_iter_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.04)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();

        // Generate a small, bounded range
        let use_inclusive = emit.gen_bool(0.3);
        let start = emit.gen_i64_range(0, 2);
        let end = if use_inclusive {
            emit.gen_i64_range(start, start + 7)
        } else {
            emit.gen_i64_range(start + 1, start + 9)
        };

        let range_expr = if use_inclusive {
            format!("({}..={})", start, end)
        } else {
            format!("({}..{})", start, end)
        };

        // Optional prefix: .sorted(), .reverse(), .skip(N)
        let prefix = if emit.gen_bool(0.20) {
            match emit.gen_range(0..3) {
                0 => ".sorted()".to_string(),
                1 => ".reverse()".to_string(),
                _ => format!(".skip({})", emit.gen_range(0..2)),
            }
        } else {
            String::new()
        };

        // Build the chain
        let chain = gen_chain(emit);

        // Pick a terminal
        let (terminal, result_type) = gen_terminal(emit);

        scope.add_local(name.clone(), result_type, false);

        Some(format!(
            "let {} = {}.iter(){}{}{}",
            name, range_expr, prefix, chain, terminal
        ))
    }
}

fn gen_chain(emit: &mut Emit) -> String {
    let choice = emit.gen_range(0..18);
    if choice < 5 {
        let body = gen_map_body(emit);
        format!(".map((x) => {})", body)
    } else if choice < 9 {
        let body = gen_filter_body(emit);
        format!(".filter((x) => {})", body)
    } else if choice < 12 {
        let map_body = gen_map_body(emit);
        let filter_body = gen_filter_body_param(emit, "y");
        format!(".map((x) => {}).filter((y) => {})", map_body, filter_body)
    } else if choice < 14 {
        let filter_body = gen_filter_body(emit);
        let map_body = gen_map_body_param(emit, "y");
        format!(".filter((x) => {}).map((y) => {})", filter_body, map_body)
    } else if choice < 16 {
        let map_body = gen_map_body(emit);
        format!(".sorted().map((x) => {})", map_body)
    } else {
        let filter_body = gen_filter_body(emit);
        format!(".filter((x) => {}).sorted()", filter_body)
    }
}

fn gen_terminal(emit: &mut Emit) -> (String, TypeInfo) {
    let choice = emit.gen_range(0..20);
    let i64_ty = TypeInfo::Primitive(PrimitiveType::I64);
    let arr_ty = TypeInfo::Array(Box::new(i64_ty.clone()));

    if choice < 6 {
        (".collect()".to_string(), arr_ty)
    } else if choice < 9 {
        (".count()".to_string(), i64_ty)
    } else if choice < 12 {
        (".sum()".to_string(), i64_ty)
    } else if choice < 14 {
        let init = emit.gen_i64_range(0, 10);
        let ops = ["acc + el", "acc * el + 1", "acc + el * 2"];
        let body = ops[emit.gen_range(0..ops.len())];
        (format!(".reduce({}, (acc, el) => {})", init, body), i64_ty)
    } else if choice < 17 {
        let n = emit.random_in(1, 3);
        (format!(".take({}).collect()", n), arr_ty)
    } else if choice < 19 {
        (".first() ?? 0".to_string(), i64_ty)
    } else {
        (".last() ?? 0".to_string(), i64_ty)
    }
}

fn gen_map_body(emit: &mut Emit) -> String {
    gen_map_body_param(emit, "x")
}

fn gen_map_body_param(emit: &mut Emit, param: &str) -> String {
    let ops = [
        format!("{} * 2", param),
        format!("{} + 1", param),
        format!("{} * {} + 1", param, param),
        format!("{} - 1", param),
    ];
    ops[emit.gen_range(0..ops.len())].clone()
}

fn gen_filter_body(emit: &mut Emit) -> String {
    gen_filter_body_param(emit, "x")
}

fn gen_filter_body_param(emit: &mut Emit, param: &str) -> String {
    let threshold = emit.gen_i64_range(-5, 10);
    let ops = [
        format!("{} > {}", param, threshold),
        format!("{} >= {}", param, threshold),
        format!("{} != {}", param, threshold),
    ];
    ops[emit.gen_range(0..ops.len())].clone()
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
        assert_eq!(RangeIterLet.name(), "range_iter_let");
    }

    #[test]
    fn generates_range_iter() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = RangeIterLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("iter()"), "got: {text}");
        assert!(text.contains(".."), "expected range, got: {text}");
    }
}
