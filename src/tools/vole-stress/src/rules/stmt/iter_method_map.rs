//! Rule: iterator map using class method call.
//!
//! Finds an i64 array and a class instance with an i64-returning method,
//! then generates:
//! ```vole
//! let r = arr.iter().map((x: i64) -> i64 => instance.method(x)).collect()
//! ```
//! or `.sum()` instead of `.collect()`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{ParamInfo, PrimitiveType, SymbolKind, TypeInfo};

pub struct IterMethodMap;

impl StmtRule for IterMethodMap {
    fn name(&self) -> &'static str {
        "iter_method_map"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Skip in method bodies to avoid mutual recursion
        scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        if scope.current_class_sym_id.is_some() {
            return None;
        }

        // Find i64 array variables
        let array_candidates: Vec<String> = scope
            .vars_matching(|v| {
                matches!(
                    &v.type_info,
                    TypeInfo::Array(elem)
                        if matches!(elem.as_ref(), TypeInfo::Primitive(PrimitiveType::I64))
                )
            })
            .into_iter()
            .map(|v| v.name)
            .collect();

        if array_candidates.is_empty() {
            return None;
        }

        // Find class instances with i64-returning methods that have an i64 param
        let method_candidates = find_method_candidates(scope);
        if method_candidates.is_empty() {
            return None;
        }

        let arr_idx = emit.gen_range(0..array_candidates.len());
        let arr_name = &array_candidates[arr_idx];

        let meth_idx = emit.gen_range(0..method_candidates.len());
        let candidate = &method_candidates[meth_idx];

        // Build argument list: first i64 param gets `x`, others get literals
        let mut x_used = false;
        let args: Vec<String> = candidate
            .params
            .iter()
            .map(|p| {
                if !x_used && matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)) {
                    x_used = true;
                    "x".to_string()
                } else {
                    emit.literal(&p.param_type)
                }
            })
            .collect();

        let closure_body = format!(
            "{}.{}({})",
            candidate.instance_name,
            candidate.method_name,
            args.join(", ")
        );

        let result_name = scope.fresh_name();
        let use_sum = emit.gen_bool(0.4);

        if use_sum {
            scope.add_local(
                result_name.clone(),
                TypeInfo::Primitive(PrimitiveType::I64),
                false,
            );
            Some(format!(
                "let {} = {}.iter().map((x: i64) -> i64 => {}).sum()",
                result_name, arr_name, closure_body
            ))
        } else {
            scope.add_local(
                result_name.clone(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                false,
            );
            Some(format!(
                "let {} = {}.iter().map((x: i64) -> i64 => {}).collect()",
                result_name, arr_name, closure_body
            ))
        }
    }
}

struct MethodCandidate {
    instance_name: String,
    method_name: String,
    params: Vec<ParamInfo>,
}

fn find_method_candidates(scope: &Scope) -> Vec<MethodCandidate> {
    let mut candidates = Vec::new();

    for (name, ty, _) in &scope.locals {
        scan_class_methods(scope, name, ty, &mut candidates);
    }
    for param in scope.params {
        scan_class_methods(scope, &param.name, &param.param_type, &mut candidates);
    }

    candidates
}

fn scan_class_methods(
    scope: &Scope,
    name: &str,
    ty: &TypeInfo,
    candidates: &mut Vec<MethodCandidate>,
) {
    if let TypeInfo::Class(mod_id, sym_id) = ty
        && let Some(sym) = scope.table.get_symbol(*mod_id, *sym_id)
        && let SymbolKind::Class(ref info) = sym.kind
        && info.type_params.is_empty()
    {
        for method in &info.methods {
            if !matches!(method.return_type, TypeInfo::Primitive(PrimitiveType::I64)) {
                continue;
            }
            let has_i64 = method
                .params
                .iter()
                .any(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)));
            if has_i64 && !method.params.is_empty() {
                candidates.push(MethodCandidate {
                    instance_name: name.to_string(),
                    method_name: method.name.clone(),
                    params: method.params.clone(),
                });
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
        assert_eq!(IterMethodMap.name(), "iter_method_map");
    }

    #[test]
    fn returns_none_without_arrays_or_classes() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterMethodMap.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
