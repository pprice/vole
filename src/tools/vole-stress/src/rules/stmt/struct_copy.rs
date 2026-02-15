//! Rule: struct copy statement.
//!
//! Looks for struct-typed variables in scope and generates a copy:
//!   `let copy = structVar`
//! This exercises struct value-type copy semantics.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::TypeInfo;

pub struct StructCopy;

impl StmtRule for StructCopy {
    fn name(&self) -> &'static str {
        "struct_copy"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.08)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let mut all_structs: Vec<(String, TypeInfo)> = Vec::new();

        for (name, ty, _) in &scope.locals {
            if matches!(ty, TypeInfo::Struct(_, _)) {
                all_structs.push((name.clone(), ty.clone()));
            }
        }
        for param in scope.params {
            if matches!(&param.param_type, TypeInfo::Struct(_, _)) {
                all_structs.push((param.name.clone(), param.param_type.clone()));
            }
        }

        if all_structs.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..all_structs.len());
        let (var_name, struct_type) = &all_structs[idx];

        let copy_name = scope.fresh_name();
        scope.add_local(copy_name.clone(), struct_type.clone(), false);

        Some(format!("let {} = {}", copy_name, var_name))
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(StructCopy.name(), "struct_copy");
    }

    #[test]
    fn returns_none_without_struct_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StructCopy.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
