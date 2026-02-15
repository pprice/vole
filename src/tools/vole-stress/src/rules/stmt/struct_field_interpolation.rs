//! Rule: struct field in string interpolation.
//!
//! Finds a struct-typed local with numeric or string fields and generates
//! a string interpolation using a struct field access:
//! ```vole
//! let s = "val={structVar.fieldName}"
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, SymbolKind, TypeInfo};

pub struct StructFieldInterpolation;

impl StmtRule for StructFieldInterpolation {
    fn name(&self) -> &'static str {
        "struct_field_interpolation"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let candidates = find_interpolatable_fields(scope);
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, field_name) = &candidates[idx];

        let result_name = scope.fresh_name();
        let prefixes = ["val=", "", "f:"];
        let prefix = prefixes[emit.gen_range(0..prefixes.len())];

        scope.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        Some(format!(
            "let {} = \"{}{{{}.{}}}\"",
            result_name, prefix, var_name, field_name
        ))
    }
}

fn find_interpolatable_fields(scope: &Scope) -> Vec<(String, String)> {
    let mut candidates = Vec::new();

    for (name, ty, _) in &scope.locals {
        if let TypeInfo::Struct(mod_id, sym_id) = ty
            && let Some(sym) = scope.table.get_symbol(*mod_id, *sym_id)
            && let SymbolKind::Struct(ref info) = sym.kind
        {
            for f in &info.fields {
                if let TypeInfo::Primitive(p) = &f.field_type
                    && matches!(
                        p,
                        PrimitiveType::I64
                            | PrimitiveType::I32
                            | PrimitiveType::F64
                            | PrimitiveType::String
                            | PrimitiveType::Bool
                    )
                {
                    candidates.push((name.clone(), f.name.clone()));
                }
            }
        }
    }

    candidates
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
        assert_eq!(
            StructFieldInterpolation.name(),
            "struct_field_interpolation"
        );
    }

    #[test]
    fn returns_none_without_struct_vars() {
        let mut table = SymbolTable::new();
        let _mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StructFieldInterpolation.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
