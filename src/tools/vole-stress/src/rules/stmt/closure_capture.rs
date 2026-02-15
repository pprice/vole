//! Rule: closure that captures a whole struct and accesses multiple fields.
//!
//! Finds a struct-typed local with at least 2 numeric fields (i64 or i32),
//! then generates a closure body that adds `x + struct.field1 + struct.field2`.
//!
//! **Pattern A -- direct invocation:**
//! ```vole
//! let result = ((x: i64) -> i64 => x + my_struct.fieldA + my_struct.fieldB)(5)
//! ```
//!
//! **Pattern B -- iterator chain:**
//! ```vole
//! let result = [1, 2, 3].iter().map((x: i64) -> i64 => x + my_struct.fieldA).collect()
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, SymbolKind, TypeInfo};

pub struct ClosureCapture;

impl StmtRule for ClosureCapture {
    fn name(&self) -> &'static str {
        "closure_capture"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.12)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        !scope.is_in_generic_class_method()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let _module_id = scope.module_id?;

        let candidates = collect_struct_candidates(scope);
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (struct_name, numeric_fields) = &candidates[idx];
        let struct_name = struct_name.clone();

        // Pick 2-3 fields to use inside the closure
        let num_fields = std::cmp::min(numeric_fields.len(), emit.random_in(2, 3));
        let mut chosen_fields = numeric_fields.clone();
        emit.shuffle(&mut chosen_fields);
        chosen_fields.truncate(num_fields);

        let body_expr = build_body_expr(&struct_name, &chosen_fields);

        let use_iter = emit.gen_bool(0.4);
        if use_iter {
            emit_iter_pattern(scope, emit, &body_expr)
        } else {
            emit_invoke_pattern(scope, emit, &body_expr)
        }
    }
}

/// Collect struct-typed locals/params with at least 2 numeric (i64/i32) fields.
fn collect_struct_candidates(scope: &Scope) -> Vec<(String, Vec<(String, PrimitiveType)>)> {
    let mut candidates = Vec::new();

    for (name, ty, _) in &scope.locals {
        if let Some(fields) = extract_numeric_fields(scope, ty) {
            if fields.len() >= 2 {
                candidates.push((name.clone(), fields));
            }
        }
    }
    for p in scope.params {
        if let Some(fields) = extract_numeric_fields(scope, &p.param_type) {
            if fields.len() >= 2 {
                candidates.push((p.name.clone(), fields));
            }
        }
    }

    candidates
}

/// Extract numeric (i64/i32) fields from a struct type.
fn extract_numeric_fields(scope: &Scope, ty: &TypeInfo) -> Option<Vec<(String, PrimitiveType)>> {
    if let TypeInfo::Struct(mod_id, sym_id) = ty
        && let Some(sym) = scope.table.get_symbol(*mod_id, *sym_id)
        && let SymbolKind::Struct(ref info) = sym.kind
    {
        let fields: Vec<(String, PrimitiveType)> = info
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
        return Some(fields);
    }
    None
}

/// Build the closure body expression: `x + struct.field1 + struct.field2 [+ 0_i64]`.
fn build_body_expr(struct_name: &str, chosen_fields: &[(String, PrimitiveType)]) -> String {
    let has_i32 = chosen_fields
        .iter()
        .any(|(_, p)| matches!(p, PrimitiveType::I32));

    let mut parts: Vec<String> = vec!["x".to_string()];
    for (field_name, _) in chosen_fields {
        parts.push(format!("{}.{}", struct_name, field_name));
    }
    let mut expr = parts.join(" + ");
    if has_i32 {
        expr = format!("{} + 0_i64", expr);
    }
    expr
}

/// Pattern A: direct invocation of inline closure.
fn emit_invoke_pattern(scope: &mut Scope, emit: &mut Emit, body_expr: &str) -> Option<String> {
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

/// Pattern B: iterator chain with closure capturing struct.
fn emit_iter_pattern(scope: &mut Scope, emit: &mut Emit, body_expr: &str) -> Option<String> {
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{FieldInfo, StructInfo, SymbolKind, SymbolTable};
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    fn make_scope_with_struct(table: &SymbolTable, mod_id: crate::symbols::ModuleId) -> Scope<'_> {
        let mut scope = Scope::with_module(&[], table, mod_id);
        // Find the struct symbol we added
        let module = table.get_module(mod_id).unwrap();
        let sym = module.symbols().find(|s| s.name == "Point").unwrap();
        scope.add_local("pt".into(), TypeInfo::Struct(mod_id, sym.id), false);
        scope
    }

    fn make_table_with_struct() -> (SymbolTable, crate::symbols::ModuleId) {
        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test".into(), "test.vole".into());
        let module = table.get_module_mut(mod_id).unwrap();
        module.add_symbol(
            "Point".into(),
            SymbolKind::Struct(StructInfo {
                fields: vec![
                    FieldInfo {
                        name: "x".into(),
                        field_type: TypeInfo::Primitive(PrimitiveType::I64),
                    },
                    FieldInfo {
                        name: "y".into(),
                        field_type: TypeInfo::Primitive(PrimitiveType::I64),
                    },
                ],
                static_methods: vec![],
            }),
        );
        (table, mod_id)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(ClosureCapture.name(), "closure_capture");
    }

    #[test]
    fn returns_none_without_struct_locals() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            ClosureCapture
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_with_struct_in_scope() {
        let (table, mod_id) = make_table_with_struct();
        let mut scope = make_scope_with_struct(&table, mod_id);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClosureCapture.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("pt."), "got: {text}");
        assert!(text.contains("let local"), "got: {text}");
    }
}
