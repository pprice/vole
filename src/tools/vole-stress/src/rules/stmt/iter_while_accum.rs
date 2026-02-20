//! Rule: while-loop with iterator terminal accumulation.
//!
//! Generates a while-loop that accumulates results from iterator chains on
//! numeric arrays.  Three variants: filter+count, map+sum, filter-by-counter+count.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct IterWhileAccum;

impl StmtRule for IterWhileAccum {
    fn name(&self) -> &'static str {
        "iter_while_accum"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let prim_arrays: Vec<(String, PrimitiveType)> = scope
            .params
            .iter()
            .filter_map(|p| {
                if let TypeInfo::Array(inner) = &p.param_type {
                    if let TypeInfo::Primitive(prim) = inner.as_ref() {
                        if matches!(prim, PrimitiveType::I64 | PrimitiveType::I32) {
                            return Some((p.name.clone(), *prim));
                        }
                    }
                }
                None
            })
            .collect();

        if prim_arrays.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..prim_arrays.len());
        let (arr_name, elem_prim) = &prim_arrays[idx];
        let arr_name = arr_name.clone();
        let elem_prim = *elem_prim;

        let acc_name = scope.fresh_name();
        let counter_name = scope.fresh_name();
        let guard_name = scope.fresh_name();
        let limit = emit.random_in(2, 4);
        let guard_limit = limit * 10;

        let iter_expr = build_iter_expr(emit, &arr_name, &counter_name, elem_prim);

        scope.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );
        scope.add_local(
            counter_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );
        scope.add_local(
            guard_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );

        scope.protected_vars.push(counter_name.clone());
        scope.protected_vars.push(guard_name.clone());
        scope.protected_vars.push(acc_name.clone());
        scope.protected_vars.push(arr_name);

        let indent = emit.indent_str();
        let inner = format!("{}    ", indent);

        Some(format!(
            "var {} = 0\n\
             {}let mut {} = 0\n\
             {}let mut {} = 0\n\
             {}while {} < {} {{\n\
             {}{} = {} + 1\n\
             {}if {} > {} {{ break }}\n\
             {}{} = {} + {}\n\
             {}{} = {} + 1\n\
             {}}}",
            acc_name,
            indent,
            counter_name,
            indent,
            guard_name,
            indent,
            counter_name,
            limit,
            inner,
            guard_name,
            guard_name,
            inner,
            guard_name,
            guard_limit,
            inner,
            acc_name,
            acc_name,
            iter_expr,
            inner,
            counter_name,
            counter_name,
            indent,
        ))
    }
}

/// Build one of three iterator chain expressions over a numeric array.
fn build_iter_expr(
    emit: &mut Emit,
    arr_name: &str,
    counter_name: &str,
    elem_prim: PrimitiveType,
) -> String {
    match emit.gen_range(0..3) {
        0 => {
            let filter_body = filter_body(emit, elem_prim);
            format!("{}.iter().filter((x) => {}).count()", arr_name, filter_body)
        }
        1 => {
            let map_body = map_body(emit, elem_prim);
            format!("{}.iter().map((x) => {}).sum()", arr_name, map_body)
        }
        _ => {
            format!(
                "{}.iter().filter((x) => x > {}).count()",
                arr_name, counter_name
            )
        }
    }
}

/// Generate a filter closure body for the given primitive type.
fn filter_body(emit: &mut Emit, prim: PrimitiveType) -> String {
    match prim {
        PrimitiveType::I64 => match emit.gen_range(0..3) {
            0 => {
                let n = emit.gen_i64_range(-5, 2);
                format!("x > {}", n)
            }
            1 => {
                let n = emit.gen_i64_range(5, 20);
                format!("x < {}", n)
            }
            _ => "x % 2 == 0".to_string(),
        },
        PrimitiveType::I32 => match emit.gen_range(0..3) {
            0 => {
                let n = emit.gen_i64_range(-5, 2);
                format!("x > {}_i32", n)
            }
            1 => {
                let n = emit.gen_i64_range(5, 20);
                format!("x < {}_i32", n)
            }
            _ => "x % 2_i32 == 0_i32".to_string(),
        },
        _ => "true".to_string(),
    }
}

/// Generate a map closure body for the given primitive type.
fn map_body(emit: &mut Emit, prim: PrimitiveType) -> String {
    match prim {
        PrimitiveType::I64 => match emit.gen_range(0..3) {
            0 => {
                let n = emit.random_in(2, 5);
                format!("x * {}", n)
            }
            1 => {
                let n = emit.random_in(1, 10);
                format!("x + {}", n)
            }
            _ => {
                let n = emit.random_in(1, 3);
                format!("x - {}", n)
            }
        },
        PrimitiveType::I32 => match emit.gen_range(0..3) {
            0 => {
                let n = emit.random_in(2, 5);
                format!("x * {}_i32", n)
            }
            1 => {
                let n = emit.random_in(1, 10);
                format!("x + {}_i32", n)
            }
            _ => {
                let n = emit.random_in(1, 3);
                format!("x - {}_i32", n)
            }
        },
        _ => "x".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{ParamInfo, SymbolTable};
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
        assert_eq!(IterWhileAccum.name(), "iter_while_accum");
    }

    #[test]
    fn generates_while_loop() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "arr".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            has_default: false,
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterWhileAccum.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("while"), "got: {text}");
        assert!(text.contains(".iter()"), "got: {text}");
    }
}
