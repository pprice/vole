//! Rule: struct destructuring statement.
//!
//! Looks for struct-typed variables in scope and generates:
//!   `let { field1: local1, field2: local2 } = structVar`

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{ModuleId, SymbolId, SymbolKind};

pub struct StructDestructure;

impl StmtRule for StructDestructure {
    fn name(&self) -> &'static str {
        "struct_destructure"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let _ = scope.module_id?;

        let all_structs = collect_struct_vars(scope);
        if all_structs.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..all_structs.len());
        let (var_name, struct_mod_id, struct_sym_id) = &all_structs[idx];
        let var_name = var_name.clone();

        let symbol = scope.table.get_symbol(*struct_mod_id, *struct_sym_id)?;
        let struct_info = match &symbol.kind {
            SymbolKind::Struct(info) => info.clone(),
            _ => return None,
        };

        if struct_info.fields.is_empty() {
            return None;
        }

        // Decide whether to do full or partial destructuring
        let do_partial = emit.gen_bool(0.3);
        let fields_to_destruct = if do_partial && struct_info.fields.len() > 1 {
            let count = emit.gen_range(1..struct_info.fields.len());
            let mut indices: Vec<usize> = (0..struct_info.fields.len()).collect();
            emit.shuffle(&mut indices);
            indices.truncate(count);
            indices.sort();
            indices
        } else {
            (0..struct_info.fields.len()).collect()
        };

        // Build the pattern and collect new locals
        let mut pattern_parts = Vec::new();
        for &field_idx in &fields_to_destruct {
            let field = &struct_info.fields[field_idx];
            let new_name = scope.fresh_name();
            pattern_parts.push(format!("{}: {}", field.name, new_name));
            scope.add_local(new_name, field.field_type.clone(), false);
        }

        let pattern = format!("{{ {} }}", pattern_parts.join(", "));
        Some(format!("let {} = {}", pattern, var_name))
    }
}

/// Collect struct-typed variables from both locals and params.
fn collect_struct_vars(scope: &Scope) -> Vec<(String, ModuleId, SymbolId)> {
    let mut all = Vec::new();

    for (name, ty, _) in &scope.locals {
        if let crate::symbols::TypeInfo::Struct(mod_id, sym_id) = ty {
            all.push((name.clone(), *mod_id, *sym_id));
        }
    }
    for param in scope.params {
        if let crate::symbols::TypeInfo::Struct(mod_id, sym_id) = &param.param_type {
            all.push((param.name.clone(), *mod_id, *sym_id));
        }
    }

    all
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(StructDestructure.name(), "struct_destructure");
    }

    #[test]
    fn returns_none_without_struct_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StructDestructure.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
