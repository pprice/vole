//! Rule: class/struct construction expression.
//!
//! Generates `ClassName { field1: val1, field2: val2, ... }` for class
//! or struct types. Skips generic classes.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::SymbolKind;

pub struct ClassConstruction;

impl ExprRule for ClassConstruction {
    fn name(&self) -> &'static str {
        "class_construction"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.15)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        let (mod_id, sym_id) = match expected_type {
            TypeInfo::Class(m, s) | TypeInfo::Struct(m, s) => (*m, *s),
            _ => return None,
        };

        let sym = scope.table.get_symbol(mod_id, sym_id)?;

        let (type_name, fields) = match &sym.kind {
            SymbolKind::Class(info) => {
                if !info.type_params.is_empty() {
                    return None; // Skip generic classes
                }
                (sym.name.clone(), info.fields.clone())
            }
            SymbolKind::Struct(info) => (sym.name.clone(), info.fields.clone()),
            _ => return None,
        };

        let field_values: Vec<String> = fields
            .iter()
            .map(|f| {
                let value = emit.sub_expr(&f.field_type, scope);
                format!("{}: {}", f.name, value)
            })
            .collect();

        Some(format!("{} {{ {} }}", type_name, field_values.join(", ")))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ParamValue, StmtRule};
    use crate::symbols::{PrimitiveType, SymbolTable};
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(ClassConstruction.name(), "class_construction");
    }

    #[test]
    fn returns_none_for_non_class() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClassConstruction.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }
}
