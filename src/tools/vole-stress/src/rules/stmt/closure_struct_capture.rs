//! Rule: closure capturing struct fields.
//!
//! Finds a struct-typed variable with 2+ numeric fields and generates either:
//! - A direct closure invocation: `let r = ((x: i64) -> i64 => x + s.f1 + s.f2)(42)`
//! - An iterator map: `let r = [1, 2, 3].iter().map((x: i64) -> i64 => x + s.f1).collect()`

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, SymbolKind, TypeInfo};

pub struct ClosureStructCapture;

impl StmtRule for ClosureStructCapture {
    fn name(&self) -> &'static str {
        "closure_struct_capture"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Skip in generic class method contexts
        if scope.is_in_generic_class_method() {
            return false;
        }
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        if scope.is_in_generic_class_method() {
            return None;
        }
        let _ = scope.module_id?;

        let candidates = find_struct_numeric_candidates(scope);
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (struct_name, numeric_fields) = &candidates[idx];
        let struct_name = struct_name.clone();
        let mut chosen_fields = numeric_fields.clone();

        let num_fields = std::cmp::min(chosen_fields.len(), emit.random_in(2, 3));
        emit.shuffle(&mut chosen_fields);
        chosen_fields.truncate(num_fields);

        // Check if any chosen field is i32
        let has_i32 = chosen_fields
            .iter()
            .any(|(_, p)| matches!(p, PrimitiveType::I32));

        // Build body: x + struct.field1 + struct.field2 [+ 0_i64]
        let mut body_parts: Vec<String> = vec!["x".to_string()];
        for (field_name, _) in &chosen_fields {
            body_parts.push(format!("{}.{}", struct_name, field_name));
        }
        let mut body_expr = body_parts.join(" + ");
        if has_i32 {
            body_expr = format!("{} + 0_i64", body_expr);
        }

        let use_iter = emit.gen_bool(0.4);
        if use_iter {
            let arr_size = emit.random_in(2, 4);
            let arr_elems: Vec<String> = (0..arr_size)
                .map(|_| format!("{}", emit.random_in(1, 20)))
                .collect();

            let result_name = scope.fresh_name();
            scope.add_local(
                result_name.clone(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                false,
            );

            Some(format!(
                "let {} = [{}].iter().map((x: i64) -> i64 => {}).collect()",
                result_name,
                arr_elems.join(", "),
                body_expr,
            ))
        } else {
            let arg_val = emit.random_in(1, 50);
            let result_name = scope.fresh_name();
            scope.add_local(
                result_name.clone(),
                TypeInfo::Primitive(PrimitiveType::I64),
                false,
            );

            Some(format!(
                "let {} = ((x: i64) -> i64 => {})({})",
                result_name, body_expr, arg_val,
            ))
        }
    }
}

fn find_struct_numeric_candidates(scope: &Scope) -> Vec<(String, Vec<(String, PrimitiveType)>)> {
    let mut candidates = Vec::new();

    for (name, ty, _) in &scope.locals {
        if let TypeInfo::Struct(mod_id, sym_id) = ty
            && let Some(sym) = scope.table.get_symbol(*mod_id, *sym_id)
            && let SymbolKind::Struct(ref info) = sym.kind
        {
            let numeric_fields: Vec<(String, PrimitiveType)> = info
                .fields
                .iter()
                .filter_map(|f| {
                    if let TypeInfo::Primitive(p) = &f.field_type
                        && matches!(p, PrimitiveType::I64 | PrimitiveType::I32)
                    {
                        Some((f.name.clone(), *p))
                    } else {
                        None
                    }
                })
                .collect();
            if numeric_fields.len() >= 2 {
                candidates.push((name.clone(), numeric_fields));
            }
        }
    }

    // Also check params
    for p in scope.params {
        if let TypeInfo::Struct(mod_id, sym_id) = &p.param_type
            && let Some(sym) = scope.table.get_symbol(*mod_id, *sym_id)
            && let SymbolKind::Struct(ref info) = sym.kind
        {
            let numeric_fields: Vec<(String, PrimitiveType)> = info
                .fields
                .iter()
                .filter_map(|f| {
                    if let TypeInfo::Primitive(pt) = &f.field_type
                        && matches!(pt, PrimitiveType::I64 | PrimitiveType::I32)
                    {
                        Some((f.name.clone(), *pt))
                    } else {
                        None
                    }
                })
                .collect();
            if numeric_fields.len() >= 2 {
                candidates.push((p.name.clone(), numeric_fields));
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
        assert_eq!(ClosureStructCapture.name(), "closure_struct_capture");
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

        let result = ClosureStructCapture.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
