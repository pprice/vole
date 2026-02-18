//! Rule: iterator chunks/windows let-binding.
//!
//! Generates `.chunks(N).count()` or `.windows(N).flatten().collect()` on arrays.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct IterChunksWindows;

impl StmtRule for IterChunksWindows {
    fn name(&self) -> &'static str {
        "iter_chunks_windows"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let array_vars: Vec<(String, PrimitiveType)> = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Array(_)))
            .into_iter()
            .filter_map(|v| {
                if let TypeInfo::Array(inner) = &v.type_info {
                    if let TypeInfo::Primitive(p) = inner.as_ref() {
                        if matches!(
                            p,
                            PrimitiveType::I64
                                | PrimitiveType::I32
                                | PrimitiveType::F64
                                | PrimitiveType::Bool
                                | PrimitiveType::String
                        ) {
                            return Some((v.name, *p));
                        }
                    }
                }
                None
            })
            .collect();

        if array_vars.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..array_vars.len());
        let (arr_name, elem_prim) = &array_vars[idx];
        let elem_prim = *elem_prim;
        let result_name = scope.fresh_name();

        let method = if emit.gen_bool(0.5) {
            "chunks"
        } else {
            "windows"
        };

        let size = emit.random_in(1, 3);

        // Optional prefix: ~20% sorted or filter for numeric
        let is_numeric = matches!(elem_prim, PrimitiveType::I64 | PrimitiveType::F64);
        let prefix = if emit.gen_bool(0.20) && is_numeric {
            match emit.gen_range(0..2) {
                0 => ".sorted()".to_string(),
                _ => {
                    let n = emit.gen_i64_range(-5, 2);
                    format!(".filter((x) => x > {})", n)
                }
            }
        } else {
            String::new()
        };

        // Terminal: count (50%) or flatten().collect() (50%)
        let (terminal, result_type) = if emit.gen_bool(0.5) {
            (
                ".count()".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            )
        } else {
            (
                ".flatten().collect()".to_string(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_prim))),
            )
        };

        scope.add_local(result_name.clone(), result_type, false);
        Some(format!(
            "let {} = {}.iter(){}.{}({}){}",
            result_name, arr_name, prefix, method, size, terminal
        ))
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
        assert_eq!(IterChunksWindows.name(), "iter_chunks_windows");
    }

    #[test]
    fn generates_chunks_or_windows() {
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

        let result = IterChunksWindows.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".chunks(") || text.contains(".windows("),
            "got: {text}"
        );
    }
}
