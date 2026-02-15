//! Rule: call a fallible function with match-based error handling.
//!
//! Finds fallible functions in the current module and generates a guarded
//! call wrapped in `when { false => match func() { ... }, _ => default }`.
//! The `false` guard prevents mutual recursion at runtime while still
//! exercising the type checker and codegen.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{FunctionInfo, SymbolKind, TypeInfo};

pub struct TryLet;

impl StmtRule for TryLet {
    fn name(&self) -> &'static str {
        "try_let"
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

        // Find fallible functions: non-generic, excluding current function,
        // only lower-indexed to prevent mutual recursion.
        let current_name = scope.current_function_name.as_deref();
        let current_fn_sym_id = scope.current_function_sym_id;
        let fallible_funcs: Vec<(String, FunctionInfo)> = module
            .functions()
            .filter_map(|sym| {
                if let SymbolKind::Function(ref info) = sym.kind
                    && info.type_params.is_empty()
                    && info.return_type.is_fallible()
                    && current_name != Some(sym.name.as_str())
                {
                    if let Some(cur_id) = current_fn_sym_id
                        && sym.id.0 >= cur_id.0
                    {
                        return None;
                    }
                    return Some((sym.name.clone(), info.clone()));
                }
                None
            })
            .collect();

        if fallible_funcs.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..fallible_funcs.len());
        let (func_name, func_info) = fallible_funcs[idx].clone();

        // Generate simple arguments for the call
        let args: Vec<String> = func_info
            .params
            .iter()
            .map(|p| emit.literal(&p.param_type))
            .collect();
        let args_str = args.join(", ");

        let success_type = func_info.return_type.success_type().clone();
        let default_val = emit.literal(&success_type);

        let name = scope.fresh_name();
        scope.add_local(name.clone(), success_type, false);

        // Use `match` inside a `when` guard with `false` to prevent
        // mutual recursion while exercising type checking.
        let call_expr = format!(
            "match {}({}) {{ success x => x, error => {}, _ => {} }}",
            func_name, args_str, default_val, default_val
        );

        Some(format!(
            "let {} = when {{ false => {}, _ => {} }}",
            name, call_expr, default_val
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(TryLet.name(), "try_let");
    }

    #[test]
    fn returns_none_without_module() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = TryLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn returns_none_with_empty_module() {
        use crate::symbols::ModuleId;

        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(mod_id);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = TryLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
