//! Rule: field access expression.
//!
//! Generates `local.field` for class or struct typed variables with
//! fields matching the expected primitive type.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, SymbolKind};

pub struct FieldAccess;

impl ExprRule for FieldAccess {
    fn name(&self) -> &'static str {
        "field_access"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.15)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Class(..) | TypeInfo::Struct(..)))
            .first()
            .is_some()
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        let prim = match expected_type {
            TypeInfo::Primitive(p) => *p,
            _ => return None,
        };
        let target = TypeInfo::Primitive(prim);

        // Collect (var_name, field_name) pairs matching target
        let mut candidates: Vec<(String, String)> = Vec::new();

        let class_struct_vars = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Class(..) | TypeInfo::Struct(..)));

        for var in &class_struct_vars {
            let (mod_id, sym_id) = match &var.type_info {
                TypeInfo::Class(m, s) | TypeInfo::Struct(m, s) => (*m, *s),
                _ => continue,
            };

            let Some(sym) = scope.table.get_symbol(mod_id, sym_id) else {
                continue;
            };

            let fields = match &sym.kind {
                SymbolKind::Class(info) => {
                    if !info.type_params.is_empty() {
                        continue; // Skip generic classes
                    }
                    &info.fields
                }
                SymbolKind::Struct(info) => &info.fields,
                _ => continue,
            };

            for f in fields {
                if f.field_type == target {
                    candidates.push((var.name.clone(), f.name.clone()));
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, field_name) = &candidates[idx];
        Some(format!("{}.{}", var_name, field_name))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ParamValue, StmtRule};
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
        assert_eq!(FieldAccess.name(), "field_access");
    }

    #[test]
    fn returns_none_without_struct_vars() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = FieldAccess.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }
}
