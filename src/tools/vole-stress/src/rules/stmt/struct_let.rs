//! Rule: let-bind a struct instance via construction.
//!
//! Finds a struct in the current module and generates:
//!   `let localN = StructName { field1: val1, field2: val2 }`

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{StructInfo, SymbolId, SymbolKind, TypeInfo};

pub struct StructLet;

impl StmtRule for StructLet {
    fn name(&self) -> &'static str {
        "struct_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.10)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let module_id = scope.module_id?;
        let module = scope.table.get_module(module_id)?;

        let candidates: Vec<(SymbolId, String, StructInfo)> = module
            .structs()
            .filter_map(|sym| {
                if let SymbolKind::Struct(ref info) = sym.kind {
                    Some((sym.id, sym.name.clone(), info.clone()))
                } else {
                    None
                }
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (sym_id, struct_name, struct_info) = &candidates[idx];
        let sym_id = *sym_id;
        let struct_name = struct_name.clone();
        let struct_info = struct_info.clone();

        // Generate field values
        let fields: Vec<String> = struct_info
            .fields
            .iter()
            .map(|f| {
                let value = emit.literal(&f.field_type);
                format!("{}: {}", f.name, value)
            })
            .collect();
        let fields_str = fields.join(", ");

        let name = scope.fresh_name();
        let ty = TypeInfo::Struct(module_id, sym_id);
        scope.add_local(name.clone(), ty, false);

        Some(format!(
            "let {} = {} {{ {} }}",
            name, struct_name, fields_str
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
        assert_eq!(StructLet.name(), "struct_let");
    }

    #[test]
    fn returns_none_without_structs() {
        let mut table = SymbolTable::new();
        let _mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StructLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
