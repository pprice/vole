//! Rule: call a free function that has an interface-typed parameter.
//!
//! Finds non-generic functions in the current module that have at least one
//! `TypeInfo::Interface` parameter, picks one, and generates a call with
//! literal arguments. This exercises the codegen path where a concrete class
//! would be implicitly upcast to an interface type at the call site.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{ModuleId, ParamInfo, SymbolId, SymbolKind, TypeInfo};

pub struct IfaceFunctionCall;

impl StmtRule for IfaceFunctionCall {
    fn name(&self) -> &'static str {
        "iface_function_call"
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

        // Collect interfaces implemented by the current class (if in a method body).
        // We avoid calling functions whose interface params overlap with these
        // to prevent cross-function/method mutual recursion.
        let current_class_ifaces: Vec<(ModuleId, SymbolId)> =
            if let Some((cls_mod, cls_sym)) = scope.current_class_sym_id {
                scope
                    .table
                    .get_symbol(cls_mod, cls_sym)
                    .and_then(|s| match &s.kind {
                        SymbolKind::Class(info) => Some(info.implements.clone()),
                        _ => None,
                    })
                    .unwrap_or_default()
            } else {
                Vec::new()
            };

        let current_fn_sym_id = scope.current_function_sym_id;
        let candidates: Vec<(String, Vec<ParamInfo>, TypeInfo)> = module
            .functions()
            .filter_map(|s| {
                if let SymbolKind::Function(ref info) = s.kind {
                    if info.type_params.is_empty()
                        && !matches!(info.return_type, TypeInfo::Never)
                        && info
                            .params
                            .iter()
                            .any(|p| p.param_type.contains_interface())
                        && Some(s.name.as_str()) != scope.current_function_name.as_deref()
                    {
                        // Only call lower-indexed functions to prevent cycles
                        if let Some(cur_id) = current_fn_sym_id
                            && s.id.0 >= cur_id.0
                        {
                            return None;
                        }

                        // Skip functions whose interface params overlap with
                        // the current class's implemented interfaces
                        if !current_class_ifaces.is_empty() {
                            let mut func_ifaces = Vec::new();
                            for p in &info.params {
                                p.param_type.collect_interface_ids(&mut func_ifaces);
                            }
                            if func_ifaces
                                .iter()
                                .any(|id| current_class_ifaces.contains(id))
                            {
                                return None;
                            }
                        }

                        Some((
                            s.name.clone(),
                            info.params.clone(),
                            info.return_type.clone(),
                        ))
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (func_name, params, return_type) = &candidates[idx];
        let func_name = func_name.clone();
        let return_type = return_type.clone();

        // Generate arguments
        let args: Vec<String> = params.iter().map(|p| emit.literal(&p.param_type)).collect();
        let call_expr = format!("{}({})", func_name, args.join(", "));

        // When inside a method body, guard with `if false` to prevent
        // mutual recursion.
        let in_method_body = scope.current_class_sym_id.is_some();

        if in_method_body {
            let indent = emit.indent_str();
            let inner_indent = format!("{}    ", indent);
            let stmt = match &return_type {
                TypeInfo::Void => call_expr,
                _ => format!("_ = {}", call_expr),
            };
            Some(format!(
                "if false {{\n{}{}\n{}}}",
                inner_indent, stmt, indent,
            ))
        } else {
            match &return_type {
                TypeInfo::Void => Some(call_expr),
                TypeInfo::Primitive(_) | TypeInfo::Optional(_) => {
                    let name = scope.fresh_name();
                    let ty = return_type;
                    scope.add_local(name.clone(), ty, false);
                    Some(format!("let {} = {}", name, call_expr))
                }
                _ => Some(format!("_ = {}", call_expr)),
            }
        }
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
        assert_eq!(IfaceFunctionCall.name(), "iface_function_call");
    }

    #[test]
    fn returns_none_without_module() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IfaceFunctionCall.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
