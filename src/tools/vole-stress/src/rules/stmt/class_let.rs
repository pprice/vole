//! Rule: let-bind a class instance via construction.
//!
//! Finds a non-generic class with primitive fields in the current module,
//! generates field value literals, and produces:
//!   `let localN = ClassName { field1: val1, field2: val2 }`

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{ClassInfo, SymbolId, SymbolKind, TypeInfo};

pub struct ClassLet;

impl StmtRule for ClassLet {
    fn name(&self) -> &'static str {
        "class_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.15)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let module_id = scope.module_id?;
        let module = scope.table.get_module(module_id)?;

        // Collect non-generic classes with at least one primitive field
        let candidates: Vec<(SymbolId, String, ClassInfo)> = module
            .classes()
            .filter_map(|sym| {
                if let SymbolKind::Class(ref info) = sym.kind
                    && info.type_params.is_empty()
                    && info.fields.iter().any(|f| f.field_type.is_primitive())
                {
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
        let (sym_id, class_name, class_info) = &candidates[idx];
        let sym_id = *sym_id;
        let class_name = class_name.clone();
        let class_info = class_info.clone();

        // Generate field values for construction
        let fields = generate_field_values(&class_info.fields, emit);

        let name = scope.fresh_name();
        let ty = TypeInfo::Class(module_id, sym_id);
        scope.add_local(name.clone(), ty, false);

        Some(format!("let {} = {} {{ {} }}", name, class_name, fields))
    }
}

/// Generate field value literals for class/struct construction.
fn generate_field_values(fields: &[crate::symbols::FieldInfo], emit: &mut Emit) -> String {
    fields
        .iter()
        .map(|f| {
            let value = emit.literal(&f.field_type);
            format!("{}: {}", f.name, value)
        })
        .collect::<Vec<_>>()
        .join(", ")
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
        assert_eq!(ClassLet.name(), "class_let");
    }

    #[test]
    fn returns_none_without_classes() {
        let mut table = SymbolTable::new();
        let _mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClassLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
