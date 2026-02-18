//! Rule: type parameter method call expression.
//!
//! Generates `varName.methodName(args)` on variables whose type is a
//! constrained type parameter. Finds methods from the constraining
//! interfaces whose return type matches the expected type.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::{ParamInfo, SymbolKind};

pub struct TypeParamMethod;

impl ExprRule for TypeParamMethod {
    fn name(&self) -> &'static str {
        "type_param_method"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.15)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        !scope.constrained_type_param_vars().is_empty()
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        let constrained_vars = scope.constrained_type_param_vars();
        if constrained_vars.is_empty() {
            return None;
        }

        // Collect (var_name, method_name, params) candidates where return matches expected
        let mut candidates: Vec<(String, String, Vec<ParamInfo>)> = Vec::new();

        for (var_name, _tp_name, constraints) in &constrained_vars {
            let methods = get_constraint_methods(scope, constraints);
            for (method_name, method_params, return_type) in methods {
                if &return_type == expected_type {
                    candidates.push((var_name.clone(), method_name, method_params));
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, method_name, params) = &candidates[idx];

        // Generate arguments
        let args: Vec<String> = params
            .iter()
            .map(|p| emit.sub_expr(&p.param_type, scope))
            .collect();

        Some(format!("{}.{}({})", var_name, method_name, args.join(", ")))
    }
}

/// Get methods from constraint interfaces with their return types.
fn get_constraint_methods(
    scope: &Scope,
    constraints: &[(crate::symbols::ModuleId, crate::symbols::SymbolId)],
) -> Vec<(String, Vec<ParamInfo>, TypeInfo)> {
    let mut methods = Vec::new();
    let mut seen_names = std::collections::HashSet::new();

    for &(mod_id, iface_id) in constraints {
        let iface_methods = get_all_interface_methods(scope, mod_id, iface_id);
        for (name, params, return_type) in iface_methods {
            if seen_names.insert(name.clone()) {
                methods.push((name, params, return_type));
            }
        }
    }

    methods
}

/// Get all methods from an interface, including inherited ones.
fn get_all_interface_methods(
    scope: &Scope,
    mod_id: crate::symbols::ModuleId,
    iface_id: crate::symbols::SymbolId,
) -> Vec<(String, Vec<ParamInfo>, TypeInfo)> {
    let mut all_methods = Vec::new();
    let mut seen_names = std::collections::HashSet::new();
    let mut stack = vec![(mod_id, iface_id)];
    let mut visited = std::collections::HashSet::new();

    while let Some((mid, sid)) = stack.pop() {
        if !visited.insert((mid, sid)) {
            continue;
        }

        if let Some(symbol) = scope.table.get_symbol(mid, sid)
            && let SymbolKind::Interface(ref info) = symbol.kind
        {
            for method in &info.methods {
                if seen_names.insert(method.name.clone()) {
                    all_methods.push((
                        method.name.clone(),
                        method.params.clone(),
                        method.return_type.clone(),
                    ));
                }
            }
            for &(parent_mid, parent_sid) in &info.extends {
                stack.push((parent_mid, parent_sid));
            }
        }
    }

    all_methods
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
        assert_eq!(TypeParamMethod.name(), "type_param_method");
    }

    #[test]
    fn returns_none_without_constrained_vars() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = TypeParamMethod.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }
}
