//! Rule: closure that captures a field value from a class/struct instance.
//!
//! Finds a class- or struct-typed local, extracts a primitive field value,
//! then creates a closure that captures the field value. The closure is either
//! immediately invoked or passed to an iterator `.map()` chain on a small
//! literal array.
//!
//! **Pattern A -- direct invocation:**
//! ```vole
//! let field_val = instance.field1
//! let closure = (x: i64) -> i64 => x + field_val
//! let result = closure(5)
//! ```
//!
//! **Pattern B -- iterator chain:**
//! ```vole
//! let field_val = instance.field1
//! let result = [1, 2, 3].iter().map((x: i64) -> i64 => x + field_val).collect()
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, SymbolKind, TypeInfo};

/// Accepted primitive field types for closure body generation.
const HANDLED_PRIMS: [PrimitiveType; 5] = [
    PrimitiveType::I64,
    PrimitiveType::I32,
    PrimitiveType::F64,
    PrimitiveType::String,
    PrimitiveType::Bool,
];

pub struct FieldClosure;

impl StmtRule for FieldClosure {
    fn name(&self) -> &'static str {
        "field_closure"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.08)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        !scope.is_in_generic_class_method()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let _module_id = scope.module_id?;

        let candidates = collect_field_candidates(scope);
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (instance_name, field_name, field_prim) = candidates[idx].clone();

        // Step 1: Extract the field value into a local
        let field_local = scope.fresh_name();
        scope.add_local(field_local.clone(), TypeInfo::Primitive(field_prim), false);
        let field_stmt = format!("let {} = {}.{}", field_local, instance_name, field_name);

        // Step 2: Determine closure type and build the operation
        let (closure_prim, closure_type_name) = closure_type_for(field_prim);
        let op = build_operation(field_prim, &field_local, emit);

        let indent = emit.indent_str();
        let use_iter = emit.gen_bool(0.5);

        if use_iter {
            emit_iter_pattern(
                scope,
                emit,
                &field_stmt,
                &indent,
                closure_prim,
                closure_type_name,
                &op,
            )
        } else {
            emit_invoke_pattern(
                scope,
                emit,
                &field_stmt,
                &indent,
                closure_prim,
                closure_type_name,
                &op,
            )
        }
    }
}

/// A candidate field: (local_name, field_name, primitive_type).
type FieldCandidate = (String, String, PrimitiveType);

/// Collect class/struct locals with at least one primitive field of a handled type.
fn collect_field_candidates(scope: &Scope) -> Vec<FieldCandidate> {
    let mut candidates = Vec::new();
    for (name, ty, _) in &scope.locals {
        collect_fields_from_type(scope, name, ty, &mut candidates);
    }
    candidates
}

/// Inspect a single type and push any matching fields.
fn collect_fields_from_type(
    scope: &Scope,
    name: &str,
    ty: &TypeInfo,
    candidates: &mut Vec<FieldCandidate>,
) {
    match ty {
        TypeInfo::Class(mod_id, sym_id) => {
            if let Some(sym) = scope.table.get_symbol(*mod_id, *sym_id)
                && let SymbolKind::Class(ref info) = sym.kind
                && info.type_params.is_empty()
            {
                push_prim_fields(name, &info.fields, candidates);
            }
        }
        TypeInfo::Struct(mod_id, sym_id) => {
            if let Some(sym) = scope.table.get_symbol(*mod_id, *sym_id)
                && let SymbolKind::Struct(ref info) = sym.kind
            {
                push_prim_fields(name, &info.fields, candidates);
            }
        }
        _ => {}
    }
}

/// Push (local_name, field_name, prim) for each primitive field of an accepted type.
fn push_prim_fields(
    local_name: &str,
    fields: &[crate::symbols::FieldInfo],
    candidates: &mut Vec<FieldCandidate>,
) {
    for field in fields {
        if let TypeInfo::Primitive(p) = &field.field_type {
            if HANDLED_PRIMS.contains(p) {
                candidates.push((local_name.to_string(), field.name.clone(), *p));
            }
        }
    }
}

/// Map a field primitive type to the closure parameter/return type.
fn closure_type_for(field_prim: PrimitiveType) -> (PrimitiveType, &'static str) {
    match field_prim {
        PrimitiveType::I64 => (PrimitiveType::I64, "i64"),
        PrimitiveType::I32 => (PrimitiveType::I32, "i32"),
        PrimitiveType::F64 => (PrimitiveType::F64, "f64"),
        _ => (PrimitiveType::I64, "i64"),
    }
}

/// Build the closure body operation combining `x` with the captured field.
fn build_operation(field_prim: PrimitiveType, field_local: &str, emit: &mut Emit) -> String {
    let is_numeric = matches!(
        field_prim,
        PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64
    );

    if is_numeric {
        match emit.gen_range(0..4) {
            0 => format!("x + {}", field_local),
            1 => format!("x * {}", field_local),
            2 => format!("x - {}", field_local),
            _ => format!("{} + x", field_local),
        }
    } else if matches!(field_prim, PrimitiveType::String) {
        format!("x + {}.length()", field_local)
    } else if matches!(field_prim, PrimitiveType::Bool) {
        let indent = emit.indent_str();
        format!(
            "x + when {{\n{indent}    {} => 1\n{indent}    _ => 0\n{indent}    }}",
            field_local,
        )
    } else {
        unreachable!(
            "unexpected field type in field-closure-let: {:?}",
            field_prim
        )
    }
}

/// Generate a literal for a small array element of the given type.
fn literal_elem(closure_prim: PrimitiveType, emit: &mut Emit) -> String {
    match closure_prim {
        PrimitiveType::I32 => format!("{}_i32", emit.random_in(1, 10)),
        PrimitiveType::F64 => format!("{}.0", emit.random_in(1, 10)),
        _ => format!("{}", emit.random_in(1, 10)),
    }
}

/// Generate a literal argument for direct closure invocation.
fn literal_arg(closure_prim: PrimitiveType, emit: &mut Emit) -> String {
    match closure_prim {
        PrimitiveType::I64 => format!("{}", emit.random_in(1, 20)),
        PrimitiveType::I32 => format!("{}_i32", emit.random_in(1, 20)),
        PrimitiveType::F64 => format!("{}.0", emit.random_in(1, 20)),
        _ => "0".to_string(),
    }
}

/// Pattern B: iterator chain with inline closure.
fn emit_iter_pattern(
    scope: &mut Scope,
    emit: &mut Emit,
    field_stmt: &str,
    indent: &str,
    closure_prim: PrimitiveType,
    closure_type_name: &str,
    op: &str,
) -> Option<String> {
    let arr_size = emit.random_in(2, 4);
    let arr_elems: Vec<String> = (0..arr_size)
        .map(|_| literal_elem(closure_prim, emit))
        .collect();

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Array(Box::new(TypeInfo::Primitive(closure_prim))),
        false,
    );

    Some(format!(
        "{}\n{}let {} = [{}].iter().map((x: {}) -> {} => {}).collect()",
        field_stmt,
        indent,
        result_name,
        arr_elems.join(", "),
        closure_type_name,
        closure_type_name,
        op,
    ))
}

/// Pattern A: bind closure, then invoke directly.
fn emit_invoke_pattern(
    scope: &mut Scope,
    emit: &mut Emit,
    field_stmt: &str,
    indent: &str,
    closure_prim: PrimitiveType,
    closure_type_name: &str,
    op: &str,
) -> Option<String> {
    let fn_name = scope.fresh_name();
    let closure_type = TypeInfo::Function {
        param_types: vec![TypeInfo::Primitive(closure_prim)],
        return_type: Box::new(TypeInfo::Primitive(closure_prim)),
    };

    let closure_stmt = format!(
        "let {} = (x: {}) -> {} => {}",
        fn_name, closure_type_name, closure_type_name, op,
    );

    let result_name = scope.fresh_name();
    let arg = literal_arg(closure_prim, emit);

    scope.add_local(fn_name.clone(), closure_type, false);
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(closure_prim),
        false,
    );

    let call_stmt = format!("let {} = {}({})", result_name, fn_name, arg);
    Some(format!(
        "{}\n{}{}\n{}{}",
        field_stmt, indent, closure_stmt, indent, call_stmt
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
        Emit::new(
            rng,
            EMPTY_STMT,
            EMPTY_EXPR,
            resolved,
            crate::symbols::SymbolTable::empty_ref(),
        )
    }

    fn make_table_with_struct() -> (SymbolTable, crate::symbols::ModuleId) {
        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test".into(), "test.vole".into());
        let module = table.get_module_mut(mod_id).unwrap();
        module.add_symbol(
            "Vec2".into(),
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
        assert_eq!(FieldClosure.name(), "field_closure");
    }

    #[test]
    fn returns_none_without_class_or_struct() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            FieldClosure
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_with_struct_in_scope() {
        let (table, mod_id) = make_table_with_struct();
        let mut scope = Scope::with_module(&[], &table, mod_id);
        let module = table.get_module(mod_id).unwrap();
        let sym = module.symbols().find(|s| s.name == "Vec2").unwrap();
        scope.add_local("v".into(), TypeInfo::Struct(mod_id, sym.id), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = FieldClosure.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("v."), "got: {text}");
        assert!(text.contains("let local"), "got: {text}");
    }
}
