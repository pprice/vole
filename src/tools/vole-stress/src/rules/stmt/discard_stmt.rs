//! Rule: discard statement `_ = func()`.
//!
//! Finds non-generic functions in the current module with non-void,
//! non-fallible return types and generates a guarded discard call.
//! The `if false` guard prevents mutual recursion at runtime.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{FunctionInfo, SymbolKind, TypeInfo};

pub struct DiscardStmt;

impl StmtRule for DiscardStmt {
    fn name(&self) -> &'static str {
        "discard_stmt"
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

        // Find non-generic functions with non-void, non-fallible return types.
        // Exclude the current function and only allow lower-indexed functions
        // to prevent mutual recursion.
        let current_name = scope.current_function_name.as_deref();
        let current_fn_sym_id = scope.current_function_sym_id;
        let candidates: Vec<(String, FunctionInfo)> = module
            .functions()
            .filter_map(|sym| {
                if let SymbolKind::Function(ref info) = sym.kind {
                    if info.type_params.is_empty()
                        && !matches!(info.return_type, TypeInfo::Void | TypeInfo::Never)
                        && !info.return_type.is_fallible()
                        && !info.return_type.is_iterator()
                        && current_name != Some(sym.name.as_str())
                    {
                        if let Some(cur_id) = current_fn_sym_id
                            && sym.id.0 >= cur_id.0
                        {
                            return None;
                        }
                        return Some((sym.name.clone(), info.clone()));
                    }
                }
                None
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (func_name, func_info) = candidates[idx].clone();

        // Generate simple arguments for the call
        let args: Vec<String> = func_info
            .params
            .iter()
            .map(|p| emit.literal(&p.param_type))
            .collect();
        let args_str = args.join(", ");

        // Wrap in `if false { _ = func(args) }` to prevent mutual recursion
        let indent = emit.indent_str();
        let inner_indent = format!("{}    ", indent);

        Some(format!(
            "if false {{\n{}_ = {}({})\n{}}}",
            inner_indent, func_name, args_str, indent,
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
        assert_eq!(DiscardStmt.name(), "discard_stmt");
    }

    #[test]
    fn returns_none_without_module() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = DiscardStmt.generate(&mut scope, &mut emit, &rule_params);
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

        let result = DiscardStmt.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
