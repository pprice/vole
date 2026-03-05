//! Rule: call extend methods on struct-typed locals.
//!
//! Finds struct-typed variables in scope that have extend methods (from
//! standalone implement blocks in the same module), generates type-correct
//! arguments, and produces calls including method chaining.
//!
//! Generated output shapes:
//! - `let local5 = s.getter6()` (getter call, i64 result)
//! - `let local5 = s.selfMethod19(42_i64, true)` (transformer call, struct result)
//! - `let local5 = s.selfMethod19(...).getter6()` (chained call)

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{MethodInfo, SymbolId, SymbolKind, TypeInfo};

pub struct StructExtendMethods;

impl StmtRule for StructExtendMethods {
    fn name(&self) -> &'static str {
        "struct_extend_methods"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let _ = scope.module_id?;

        // Find struct-typed locals that have extend methods in this module
        let candidates = find_struct_with_extend_methods(scope);
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, struct_type, methods) = &candidates[idx];
        let var_name = var_name.clone();
        let struct_type = struct_type.clone();
        let methods = methods.clone();

        // Separate methods by return type category
        let self_methods: Vec<&MethodInfo> = methods
            .iter()
            .filter(|m| matches!(m.return_type, TypeInfo::Void))
            .collect();
        let getter_methods: Vec<&MethodInfo> = methods
            .iter()
            .filter(|m| !matches!(m.return_type, TypeInfo::Void))
            .collect();

        // Choose a generation pattern
        let pattern = emit.gen_range(0..3);

        match pattern {
            0 if !getter_methods.is_empty() => {
                // Simple getter call: let result = s.getter()
                let method = getter_methods[emit.gen_range(0..getter_methods.len())];
                let args: Vec<String> = method
                    .params
                    .iter()
                    .map(|p| emit.literal(&p.param_type))
                    .collect();
                let result_name = scope.fresh_name();
                scope.add_local(result_name.clone(), method.return_type.clone(), false);
                Some(format!(
                    "let {} = {}.{}({})",
                    result_name,
                    var_name,
                    method.name,
                    args.join(", "),
                ))
            }
            1 if !self_methods.is_empty() => {
                // Transformer call: let result = s.transform(...)
                let method = self_methods[emit.gen_range(0..self_methods.len())];
                let args: Vec<String> = method
                    .params
                    .iter()
                    .map(|p| emit.literal(&p.param_type))
                    .collect();
                let result_name = scope.fresh_name();
                // Self-returning methods return the struct type
                scope.add_local(result_name.clone(), struct_type.clone(), false);
                Some(format!(
                    "let {} = {}.{}({})",
                    result_name,
                    var_name,
                    method.name,
                    args.join(", "),
                ))
            }
            _ if !self_methods.is_empty() && !getter_methods.is_empty() => {
                // Chained call: let result = s.transform(...).getter()
                let transform = self_methods[emit.gen_range(0..self_methods.len())];
                let getter = getter_methods[emit.gen_range(0..getter_methods.len())];

                let transform_args: Vec<String> = transform
                    .params
                    .iter()
                    .map(|p| emit.literal(&p.param_type))
                    .collect();
                let getter_args: Vec<String> = getter
                    .params
                    .iter()
                    .map(|p| emit.literal(&p.param_type))
                    .collect();

                let result_name = scope.fresh_name();
                scope.add_local(result_name.clone(), getter.return_type.clone(), false);
                Some(format!(
                    "let {} = {}.{}({}).{}({})",
                    result_name,
                    var_name,
                    transform.name,
                    transform_args.join(", "),
                    getter.name,
                    getter_args.join(", "),
                ))
            }
            _ => {
                // Fallback: call any available method
                let method = &methods[emit.gen_range(0..methods.len())];
                let args: Vec<String> = method
                    .params
                    .iter()
                    .map(|p| emit.literal(&p.param_type))
                    .collect();

                if matches!(method.return_type, TypeInfo::Void) {
                    // Self-returning method
                    let result_name = scope.fresh_name();
                    scope.add_local(result_name.clone(), struct_type.clone(), false);
                    Some(format!(
                        "let {} = {}.{}({})",
                        result_name,
                        var_name,
                        method.name,
                        args.join(", "),
                    ))
                } else {
                    let result_name = scope.fresh_name();
                    scope.add_local(result_name.clone(), method.return_type.clone(), false);
                    Some(format!(
                        "let {} = {}.{}({})",
                        result_name,
                        var_name,
                        method.name,
                        args.join(", "),
                    ))
                }
            }
        }
    }
}

/// Find struct-typed variables in scope that have extend methods.
///
/// Returns `(var_name, struct_type, extend_methods)` triples.
/// Only considers standalone implement blocks (no interface) in the
/// same module as the struct.
fn find_struct_with_extend_methods(scope: &Scope) -> Vec<(String, TypeInfo, Vec<MethodInfo>)> {
    let module_id = match scope.module_id {
        Some(id) => id,
        None => return Vec::new(),
    };

    let mut candidates = Vec::new();

    // Collect struct-typed variables (locals + params)
    let mut struct_vars: Vec<(String, SymbolId)> = Vec::new();
    for (name, ty, _) in &scope.locals {
        if let TypeInfo::Struct(mod_id, sym_id) = ty {
            if *mod_id == module_id {
                struct_vars.push((name.clone(), *sym_id));
            }
        }
    }
    for param in scope.params {
        if let TypeInfo::Struct(mod_id, sym_id) = &param.param_type {
            if *mod_id == module_id {
                struct_vars.push((param.name.clone(), *sym_id));
            }
        }
    }

    // For each struct var, find extend methods from implement blocks
    for (var_name, struct_sym_id) in struct_vars {
        let mut methods = Vec::new();

        if let Some(module) = scope.table.get_module(module_id) {
            for symbol in module.implement_blocks() {
                if let SymbolKind::ImplementBlock(ref info) = symbol.kind {
                    // Only standalone extend blocks (no interface) targeting this struct
                    if info.interface.is_none()
                        && info.target_type.0 == module_id
                        && info.target_type.1 == struct_sym_id
                    {
                        methods.extend(info.methods.iter().cloned());
                    }
                }
            }
        }

        if !methods.is_empty() {
            candidates.push((
                var_name,
                TypeInfo::Struct(module_id, struct_sym_id),
                methods,
            ));
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
        assert_eq!(StructExtendMethods.name(), "struct_extend_methods");
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

        let result = StructExtendMethods.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn returns_none_without_module() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!StructExtendMethods.precondition(&scope, &params));
    }
}
