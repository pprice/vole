//! Rule: match on method call result.
//!
//! Finds a class instance in scope with a method returning i64, calls it,
//! and matches on the result:
//! ```vole
//! let result = match instance.method(args) {
//!     0 => 100
//!     1 => 200
//!     _ => 300
//! }
//! ```
//! Skips in method bodies to avoid mutual recursion.

use std::collections::HashSet;

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{ParamInfo, PrimitiveType, SymbolKind, TypeInfo};

pub struct MatchMethodResult;

impl StmtRule for MatchMethodResult {
    fn name(&self) -> &'static str {
        "match_method_result"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.10)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Skip in method bodies to avoid mutual recursion
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let candidates = collect_method_candidates(scope);
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (instance_name, method_name, method_params) = &candidates[idx];

        // Generate arguments
        let args: Vec<String> = method_params
            .iter()
            .map(|p| emit.literal(&p.param_type))
            .collect();

        let call_expr = format!("{}.{}({})", instance_name, method_name, args.join(", "));

        // Generate 2-3 match arms + wildcard
        let num_arms = emit.random_in(2, 3);
        let indent = emit.indent_str();

        let result_type = TypeInfo::Primitive(PrimitiveType::I64);
        let mut arms = Vec::new();
        let mut used_values = HashSet::new();
        for _ in 0..num_arms {
            let val = loop {
                let v = emit.gen_i64_range(-5, 20);
                if used_values.insert(v) {
                    break v;
                }
            };
            let arm_expr = emit.literal(&result_type);
            arms.push(format!("{}    {} => {}", indent, val, arm_expr));
        }
        let wildcard_expr = emit.literal(&result_type);
        arms.push(format!("{}    _ => {}", indent, wildcard_expr));

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
            indent,
        ))
    }
}

/// Collect (instance_name, method_name, params) triples for class-typed locals
/// with methods that return i64.
fn collect_method_candidates(scope: &Scope) -> Vec<(String, String, Vec<ParamInfo>)> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if let TypeInfo::Class(mod_id, sym_id) = ty {
            if let Some(sym) = scope.table.get_symbol(*mod_id, *sym_id) {
                if let SymbolKind::Class(ref info) = sym.kind {
                    if !info.type_params.is_empty() {
                        continue;
                    }
                    for method in &info.methods {
                        if matches!(method.return_type, TypeInfo::Primitive(PrimitiveType::I64)) {
                            out.push((name.clone(), method.name.clone(), method.params.clone()));
                        }
                    }
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{ClassInfo, FieldInfo, MethodInfo, SymbolKind, SymbolTable};
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(MatchMethodResult.name(), "match_method_result");
    }

    #[test]
    fn returns_none_without_class_locals() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            MatchMethodResult
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn precondition_false_in_class_method() {
        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test".into(), "test.vole".into());
        let module = table.get_module_mut(mod_id).unwrap();
        let sym_id = module.add_symbol(
            "Foo".into(),
            SymbolKind::Class(ClassInfo {
                type_params: vec![],
                fields: vec![],
                methods: vec![],
                implements: vec![],
                static_methods: vec![],
            }),
        );

        let mut scope = Scope::with_module(&[], &table, mod_id);
        scope.current_class_sym_id = Some((mod_id, sym_id));
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(!MatchMethodResult.precondition(&scope, &params));
    }

    #[test]
    fn generates_with_class_having_i64_method() {
        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test".into(), "test.vole".into());
        let module = table.get_module_mut(mod_id).unwrap();
        let cls_sym_id = module.add_symbol(
            "Counter".into(),
            SymbolKind::Class(ClassInfo {
                type_params: vec![],
                fields: vec![FieldInfo {
                    name: "count".into(),
                    field_type: TypeInfo::Primitive(PrimitiveType::I64),
                }],
                methods: vec![MethodInfo {
                    name: "value".into(),
                    params: vec![],
                    return_type: TypeInfo::Primitive(PrimitiveType::I64),
                }],
                implements: vec![],
                static_methods: vec![],
            }),
        );

        let mut scope = Scope::with_module(&[], &table, mod_id);
        scope.add_local("ctr".into(), TypeInfo::Class(mod_id, cls_sym_id), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = MatchMethodResult.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match ctr.value()"), "got: {text}");
        assert!(text.contains("_ =>"), "got: {text}");
    }
}
