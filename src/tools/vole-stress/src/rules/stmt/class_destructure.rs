//! Rule: class destructuring statement.
//!
//! Looks for class-typed variables in scope and generates:
//!   `let { field1: local1, field2: local2 } = classVar`
//! Only non-generic classes with primitive fields are considered.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{ModuleId, SymbolId, SymbolKind};

pub struct ClassDestructure;

impl StmtRule for ClassDestructure {
    fn name(&self) -> &'static str {
        "class_destructure"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let _ = scope.module_id?;

        let all_classes = collect_class_vars(scope);
        if all_classes.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..all_classes.len());
        let (var_name, class_mod_id, class_sym_id) = &all_classes[idx];
        let var_name = var_name.clone();

        let symbol = scope.table.get_symbol(*class_mod_id, *class_sym_id)?;
        let class_info = match &symbol.kind {
            SymbolKind::Class(info) => info.clone(),
            _ => return None,
        };

        // Only destructure non-generic classes with primitive fields
        if !class_info.type_params.is_empty() {
            return None;
        }

        // Filter to primitive-typed fields
        let primitive_fields: Vec<usize> = class_info
            .fields
            .iter()
            .enumerate()
            .filter(|(_, f)| f.field_type.is_primitive())
            .map(|(i, _)| i)
            .collect();

        if primitive_fields.is_empty() {
            return None;
        }

        // Decide whether to do full or partial destructuring
        let do_partial = emit.gen_bool(0.3);
        let fields_to_destruct = if do_partial && primitive_fields.len() > 1 {
            let count = emit.gen_range(1..primitive_fields.len());
            let mut indices = primitive_fields;
            emit.shuffle(&mut indices);
            indices.truncate(count);
            indices.sort();
            indices
        } else {
            primitive_fields
        };

        // Build the pattern and collect new locals
        let mut pattern_parts = Vec::new();
        for &field_idx in &fields_to_destruct {
            let field = &class_info.fields[field_idx];
            let new_name = scope.fresh_name();
            pattern_parts.push(format!("{}: {}", field.name, new_name));
            scope.add_local(new_name, field.field_type.clone(), false);
        }

        let pattern = format!("{{ {} }}", pattern_parts.join(", "));
        Some(format!("let {} = {}", pattern, var_name))
    }
}

/// Collect class-typed variables from both locals and params.
fn collect_class_vars(scope: &Scope) -> Vec<(String, ModuleId, SymbolId)> {
    let mut all = Vec::new();

    for (name, ty, _) in &scope.locals {
        if let crate::symbols::TypeInfo::Class(mod_id, sym_id) = ty {
            all.push((name.clone(), *mod_id, *sym_id));
        }
    }
    for param in scope.params {
        if let crate::symbols::TypeInfo::Class(mod_id, sym_id) = &param.param_type {
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
        assert_eq!(ClassDestructure.name(), "class_destructure");
    }

    #[test]
    fn returns_none_without_class_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClassDestructure.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
