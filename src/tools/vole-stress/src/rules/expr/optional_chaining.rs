//! Rule: optional chaining expression.
//!
//! Generates `optVar?.fieldName` for optional-class-typed variables.
//! The result type is `Optional(field_type)`, so this rule fires when
//! the expected type is `Optional(T)` and a matching optional-class
//! variable with a field of type `T` is in scope.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::SymbolKind;

pub struct OptionalChaining;

impl ExprRule for OptionalChaining {
    fn name(&self) -> &'static str {
        "optional_chaining"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.15)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Need at least one optional-class-typed variable
        scope
            .vars_matching(|v| {
                matches!(&v.type_info, TypeInfo::Optional(inner) if matches!(inner.as_ref(), TypeInfo::Class(..)))
            })
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
        // Expected type must be Optional(T)
        let inner_target = match expected_type {
            TypeInfo::Optional(inner) => inner.as_ref(),
            _ => return None,
        };

        // Find optional-class-typed variables and collect matching fields
        let opt_class_vars = scope.vars_matching(|v| {
            matches!(&v.type_info, TypeInfo::Optional(inner) if matches!(inner.as_ref(), TypeInfo::Class(..)))
        });

        let mut candidates: Vec<(String, String)> = Vec::new();

        for var in &opt_class_vars {
            let (mod_id, sym_id) = match &var.type_info {
                TypeInfo::Optional(inner) => match inner.as_ref() {
                    TypeInfo::Class(m, s) => (*m, *s),
                    _ => continue,
                },
                _ => continue,
            };

            let Some(sym) = scope.table.get_symbol(mod_id, sym_id) else {
                continue;
            };

            let SymbolKind::Class(ref info) = sym.kind else {
                continue;
            };

            // Skip generic classes
            if !info.type_params.is_empty() {
                continue;
            }

            for field in &info.fields {
                if &field.field_type == inner_target {
                    candidates.push((var.name.clone(), field.name.clone()));
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, field_name) = &candidates[idx];
        Some(format!("{}?.{}", var_name, field_name))
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
        assert_eq!(OptionalChaining.name(), "optional_chaining");
    }

    #[test]
    fn returns_none_for_non_optional() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = OptionalChaining.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }
}
