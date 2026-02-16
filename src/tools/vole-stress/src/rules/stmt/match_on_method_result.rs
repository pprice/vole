//! Rule: match on the result of a method call.
//!
//! Finds a class instance in scope with a method returning i64, calls it,
//! and matches on the result with 2-3 literal arms + wildcard:
//!
//! ```vole
//! let result = match instance.method(args) {
//!     0 => 100
//!     1 => 200
//!     _ => 300
//! }
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, SymbolKind, TypeInfo};

pub struct MatchOnMethodResult;

impl StmtRule for MatchOnMethodResult {
    fn name(&self) -> &'static str {
        "match_on_method_result"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.04)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Must have module_id and NOT be in a class method body
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let _ = scope.module_id?;

        // Skip in method bodies to avoid mutual recursion
        if scope.current_class_sym_id.is_some() {
            return None;
        }

        let candidates = find_i64_method_candidates(scope);
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let candidate = &candidates[idx];
        let instance_name = candidate.instance_name.clone();
        let method_name = candidate.method_name.clone();
        let params = candidate.params.clone();

        // Generate arguments
        let args: Vec<String> = params.iter().map(|p| emit.literal(&p.param_type)).collect();

        let call_expr = format!("{}.{}({})", instance_name, method_name, args.join(", "));

        // Generate 2-3 match arms + wildcard
        let num_arms = emit.random_in(2, 3);
        let indent = emit.indented(|e| e.indent_str());
        let close_indent = emit.indent_str();

        let result_type = TypeInfo::Primitive(PrimitiveType::I64);
        let mut arms = Vec::new();
        let mut used_values = std::collections::HashSet::new();

        for _ in 0..num_arms {
            let val = loop {
                let v = emit.gen_i64_range(-5, 20);
                if used_values.insert(v) {
                    break v;
                }
            };
            let arm_expr = emit.literal(&result_type);
            arms.push(format!("{}{} => {}", indent, val, arm_expr));
        }

        // Wildcard arm
        let wildcard_expr = emit.literal(&result_type);
        arms.push(format!("{}_ => {}", indent, wildcard_expr));

        let result_name = scope.fresh_name();
        scope.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        Some(format!(
            "let {} = match {} {{\n{}\n{}}}",
            result_name,
            call_expr,
            arms.join("\n"),
            close_indent,
        ))
    }
}

struct MethodCandidate {
    instance_name: String,
    method_name: String,
    params: Vec<crate::symbols::ParamInfo>,
}

fn find_i64_method_candidates(scope: &Scope) -> Vec<MethodCandidate> {
    let mut candidates = Vec::new();

    for (name, ty, _) in &scope.locals {
        if let TypeInfo::Class(mod_id, sym_id) = ty
            && let Some(sym) = scope.table.get_symbol(*mod_id, *sym_id)
            && let SymbolKind::Class(ref info) = sym.kind
            && info.type_params.is_empty()
        {
            for method in &info.methods {
                if matches!(method.return_type, TypeInfo::Primitive(PrimitiveType::I64)) {
                    candidates.push(MethodCandidate {
                        instance_name: name.clone(),
                        method_name: method.name.clone(),
                        params: method.params.clone(),
                    });
                }
            }
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(MatchOnMethodResult.name(), "match_on_method_result");
    }

    #[test]
    fn returns_none_without_class_vars() {
        let mut table = SymbolTable::new();
        let _mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = MatchOnMethodResult.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
