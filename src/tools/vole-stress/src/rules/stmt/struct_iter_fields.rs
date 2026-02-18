//! Rule: struct construction with iterator terminal field values.
//!
//! Finds a struct with i64 fields and an array variable, then constructs the
//! struct using iterator terminals (`.count()`, `.sum()`, `.filter(...).count()`)
//! for the i64 fields:
//! ```vole
//! let s = MyStruct { count: arr.iter().count(), total: arr.iter().sum() }
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, StructInfo, SymbolId, SymbolKind, TypeInfo};

pub struct StructIterFields;

impl StmtRule for StructIterFields {
    fn name(&self) -> &'static str {
        "struct_iter_fields"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let module_id = scope.module_id?;
        let module = scope.table.get_module(module_id)?;

        // Find numeric arrays in scope
        let numeric_arrays = find_numeric_arrays(scope);
        if numeric_arrays.is_empty() {
            return None;
        }

        // Find structs with i64 fields
        let struct_candidates: Vec<(SymbolId, String, StructInfo)> = module
            .structs()
            .filter_map(|sym| {
                if let SymbolKind::Struct(ref info) = sym.kind
                    && info
                        .fields
                        .iter()
                        .any(|f| matches!(f.field_type, TypeInfo::Primitive(PrimitiveType::I64)))
                {
                    Some((sym.id, sym.name.clone(), info.clone()))
                } else {
                    None
                }
            })
            .collect();

        if struct_candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..struct_candidates.len());
        let (sym_id, struct_name, struct_info) = &struct_candidates[idx];
        let sym_id = *sym_id;
        let struct_name = struct_name.clone();

        let arr_idx = emit.gen_range(0..numeric_arrays.len());
        let arr_name = numeric_arrays[arr_idx].clone();

        let result_name = scope.fresh_name();

        let field_strs: Vec<String> = struct_info
            .fields
            .iter()
            .map(|f| {
                if matches!(f.field_type, TypeInfo::Primitive(PrimitiveType::I64)) {
                    let terminal = gen_iter_terminal(emit, &arr_name);
                    format!("{}: {}", f.name, terminal)
                } else {
                    let value = emit.literal(&f.field_type);
                    format!("{}: {}", f.name, value)
                }
            })
            .collect();

        scope.add_local(
            result_name.clone(),
            TypeInfo::Struct(module_id, sym_id),
            false,
        );

        Some(format!(
            "let {} = {} {{ {} }}",
            result_name,
            struct_name,
            field_strs.join(", ")
        ))
    }
}

fn find_numeric_arrays(scope: &Scope) -> Vec<String> {
    scope
        .vars_matching(|v| {
            matches!(
                &v.type_info,
                TypeInfo::Array(elem)
                    if matches!(elem.as_ref(), TypeInfo::Primitive(PrimitiveType::I64 | PrimitiveType::I32))
            )
        })
        .into_iter()
        .map(|v| v.name)
        .collect()
}

fn gen_iter_terminal(emit: &mut Emit, arr_name: &str) -> String {
    match emit.gen_range(0..3) {
        0 => format!("{}.iter().count()", arr_name),
        1 => format!("{}.iter().sum()", arr_name),
        _ => {
            let threshold = emit.gen_i64_range(-10, 10);
            format!(
                "{}.iter().filter((x) => x > {}).count()",
                arr_name, threshold
            )
        }
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
        assert_eq!(StructIterFields.name(), "struct_iter_fields");
    }

    #[test]
    fn returns_none_without_arrays_or_structs() {
        let mut table = SymbolTable::new();
        let _mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StructIterFields.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
