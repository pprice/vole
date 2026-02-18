//! Rule: instance method call on a class-typed local.
//!
//! Finds class-typed locals in scope, picks a non-generic class method,
//! generates type-correct arguments, and binds the result to a new local
//! when the return type is primitive or optional.
//!
//! Generated output shapes:
//! - `let local5 = instance.methodName(42_i64, true)` (primitive return)
//! - `instance.methodName(42_i64)` (void return)
//! - `if false { _ = instance.methodName(...) }` (inside method body, guarded)

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{MethodInfo, SymbolKind, TypeInfo};

pub struct MethodCall;

impl StmtRule for MethodCall {
    fn name(&self) -> &'static str {
        "method_call"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let _ = scope.module_id?;

        // Find class-typed locals in scope (non-generic classes only).
        // Exclude instances of the class whose method body we are currently
        // generating to avoid mutual recursion.
        let current_class = scope.current_class_sym_id;
        let class_locals: Vec<_> = scope
            .locals
            .iter()
            .filter_map(|(name, ty, _)| {
                if let TypeInfo::Class(mod_id, sym_id) = ty {
                    if current_class == Some((*mod_id, *sym_id)) {
                        return None;
                    }
                    let sym = scope.table.get_symbol(*mod_id, *sym_id)?;
                    if let SymbolKind::Class(ref info) = sym.kind
                        && info.type_params.is_empty()
                        && !info.methods.is_empty()
                    {
                        return Some((name.clone(), info.methods.clone()));
                    }
                }
                None
            })
            .collect();

        if class_locals.is_empty() {
            return None;
        }

        // Pick a random class-typed local
        let idx = emit.gen_range(0..class_locals.len());
        let (instance_name, methods) = &class_locals[idx];
        let instance_name = instance_name.clone();
        let methods = methods.clone();

        // Pick a random method, excluding the current method
        let current_name = scope.current_function_name.as_deref();
        let eligible: Vec<&MethodInfo> = methods
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

        let call_expr = format!("{}.{}({})", instance_name, method.name, args.join(", "));

        // When inside a method body, guard with `if false` to prevent
        // cross-class mutual recursion.
        let in_method_body = current_class.is_some();

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
        assert_eq!(MethodCall.name(), "method_call");
    }

    #[test]
    fn returns_none_without_class_locals() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = MethodCall.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
