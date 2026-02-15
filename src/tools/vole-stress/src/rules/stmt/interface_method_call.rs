//! Rule: method call on an interface-typed variable (vtable dispatch).
//!
//! Finds interface-typed locals or params in scope, looks up the interface
//! methods, and generates a call. This exercises the codegen's vtable
//! dispatch path.
//!
//! Generated output shapes:
//! - `let local6 = ifaceVar.methodName(42_i64)` (primitive return)
//! - `ifaceVar.methodName(42_i64)` (void return)
//! - `if false { _ = ifaceVar.methodName(...) }` (inside method body, guarded)

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{SymbolKind, TypeInfo};

pub struct InterfaceMethodCall;

impl StmtRule for InterfaceMethodCall {
    fn name(&self) -> &'static str {
        "interface_method_call"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let iface_vars = scope.interface_typed_vars();
        if iface_vars.is_empty() {
            return None;
        }

        // Pick a random interface-typed variable
        let idx = emit.gen_range(0..iface_vars.len());
        let (var_name, mod_id, sym_id) = &iface_vars[idx];
        let var_name = var_name.clone();
        let mod_id = *mod_id;
        let sym_id = *sym_id;

        // Look up the interface to get its methods
        let sym = scope.table.get_symbol(mod_id, sym_id)?;
        let iface_info = match &sym.kind {
            SymbolKind::Interface(info) => info.clone(),
            _ => return None,
        };

        // Pick a random method, excluding the current method
        let current_name = scope.current_function_name.as_deref();
        let eligible: Vec<_> = iface_info
            .methods
            .iter()
            .filter(|m| Some(m.name.as_str()) != current_name)
            .collect();
        if eligible.is_empty() {
            return None;
        }
        let method = eligible[emit.gen_range(0..eligible.len())].clone();

        // Generate type-correct arguments
        let args: Vec<String> = method
            .params
            .iter()
            .map(|p| emit.literal(&p.param_type))
            .collect();

        let call_expr = format!("{}.{}({})", var_name, method.name, args.join(", "));

        // When inside a method body, guard with `if false` to prevent
        // cross-class mutual recursion via vtable dispatch.
        let in_method_body = scope.current_class_sym_id.is_some();

        if in_method_body {
            let indent = emit.indent_str();
            let inner_indent = format!("{}    ", indent);
            let stmt = match &method.return_type {
                TypeInfo::Void => call_expr,
                _ => format!("_ = {}", call_expr),
            };
            Some(format!(
                "if false {{\n{}{}\n{}}}",
                inner_indent, stmt, indent,
            ))
        } else {
            match &method.return_type {
                TypeInfo::Primitive(_) | TypeInfo::Optional(_) => {
                    let name = scope.fresh_name();
                    let ty = method.return_type.clone();
                    scope.add_local(name.clone(), ty, false);
                    Some(format!("let {} = {}", name, call_expr))
                }
                TypeInfo::Void => Some(call_expr),
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
        assert_eq!(InterfaceMethodCall.name(), "interface_method_call");
    }

    #[test]
    fn returns_none_without_interface_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = InterfaceMethodCall.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
