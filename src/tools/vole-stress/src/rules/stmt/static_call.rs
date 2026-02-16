//! Rule: standalone static method call statement.
//!
//! Searches the current module for classes or structs with static methods
//! and generates `let localN = TypeName.staticMethod(args)`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{StaticMethodInfo, SymbolId, SymbolKind, TypeInfo};

pub struct StaticCall;

impl StmtRule for StaticCall {
    fn name(&self) -> &'static str {
        "static_call"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let module_id = scope.module_id?;
        let module = scope.table.get_module(module_id)?;

        // Collect all types with static methods
        let mut candidates: Vec<(SymbolId, String, Vec<StaticMethodInfo>, bool)> = Vec::new();

        // Classes: non-generic with primitive fields and static methods
        for sym in module.classes() {
            if let SymbolKind::Class(ref info) = sym.kind
                && info.type_params.is_empty()
                && has_primitive_field(info)
                && !info.static_methods.is_empty()
            {
                candidates.push((sym.id, sym.name.clone(), info.static_methods.clone(), true));
            }
        }

        // Structs with static methods
        for sym in module.structs() {
            if let SymbolKind::Struct(ref info) = sym.kind
                && !info.static_methods.is_empty()
            {
                candidates.push((sym.id, sym.name.clone(), info.static_methods.clone(), false));
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (sym_id, type_name, static_methods, is_class) = &candidates[idx];
        let sym_id = *sym_id;
        let type_name = type_name.clone();
        let is_class = *is_class;

        // Pick a random static method
        let method_idx = emit.gen_range(0..static_methods.len());
        let static_method = &static_methods[method_idx];

        // Generate arguments
        let args: Vec<String> = static_method
            .params
            .iter()
            .map(|p| emit.literal(&p.param_type))
            .collect();

        let call_expr = format!("{}.{}({})", type_name, static_method.name, args.join(", "));

        let name = scope.fresh_name();
        let ty = if is_class {
            TypeInfo::Class(module_id, sym_id)
        } else {
            TypeInfo::Struct(module_id, sym_id)
        };

        scope.add_local(name.clone(), ty, false);

        Some(format!("let {} = {}", name, call_expr))
    }
}

/// Check if a class has at least one primitive-typed field.
fn has_primitive_field(info: &crate::symbols::ClassInfo) -> bool {
    info.fields.iter().any(|f| f.field_type.is_primitive())
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
        assert_eq!(StaticCall.name(), "static_call");
    }

    #[test]
    fn returns_none_without_module() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StaticCall.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn returns_none_with_empty_module() {
        let mut table = SymbolTable::new();
        let _mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StaticCall.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
