//! Rule: call a generic function with a struct parameter and a closure.
//!
//! Stresses the monomorphizer with struct type arguments flowing through
//! generic functions combined with closures that operate on struct field
//! values.
//!
//! The helper function is emitted at module level via
//! [`Scope::add_module_decl`] because nested `func<T>` is rewritten to
//! `let = lambda` by vole-fmt, and lambdas don't support type parameters.
//!
//! **Variant 1 -- i64 result:**
//! ```vole
//! func helper_local0<T>(p: StructName, f: (i64) -> T) -> T {
//!     return f(p.field1 + p.field2)
//! }
//! let local1 = StructName { field1: 10, field2: 20 }
//! let local2 = helper_local0(local1, (x: i64) => x * 2)
//! ```
//!
//! **Variant 2 -- string result:**
//! ```vole
//! func helper_local0<T>(p: StructName, f: (i64) -> T) -> T {
//!     return f(p.field1 + p.field2)
//! }
//! let local1 = StructName { field1: 10, field2: 20 }
//! let local2 = helper_local0(local1, (x: i64) => "sum=" + x.to_string())
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, StructInfo, SymbolId, SymbolKind, TypeInfo};

pub struct GenericStructClosure;

/// Find non-generic structs with 2+ fields that are ALL i64.
fn find_i64_only_structs(scope: &Scope, emit: &mut Emit) -> Option<(SymbolId, String, StructInfo)> {
    let module_id = scope.module_id?;
    let module = scope.table.get_module(module_id)?;

    let candidates: Vec<(SymbolId, String, StructInfo)> = module
        .structs()
        .filter_map(|sym| {
            if let SymbolKind::Struct(ref info) = sym.kind {
                if info.fields.len() >= 2
                    && info
                        .fields
                        .iter()
                        .all(|f| matches!(f.field_type, TypeInfo::Primitive(PrimitiveType::I64)))
                {
                    Some((sym.id, sym.name.clone(), info.clone()))
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
    Some(candidates[idx].clone())
}

/// Generate a struct literal with small i64 values or existing scope vars.
fn gen_struct_literal(
    struct_name: &str,
    struct_info: &StructInfo,
    scope: &Scope,
    emit: &mut Emit,
) -> String {
    let i64_ty = TypeInfo::Primitive(PrimitiveType::I64);
    let i64_vars: Vec<String> = scope
        .vars_of_type(&i64_ty)
        .into_iter()
        .map(|v| v.name)
        .collect();

    let fields: Vec<String> = struct_info
        .fields
        .iter()
        .map(|f| {
            let value = if !i64_vars.is_empty() && emit.gen_bool(0.3) {
                let idx = emit.gen_range(0..i64_vars.len());
                i64_vars[idx].clone()
            } else {
                format!("{}", emit.gen_i64_range(0, 99))
            };
            format!("{}: {}", f.name, value)
        })
        .collect();

    format!("{} {{ {} }}", struct_name, fields.join(", "))
}

impl StmtRule for GenericStructClosure {
    fn name(&self) -> &'static str {
        "generic_struct_closure"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Must be at module level (not inside a class method) and have a module
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let (_sym_id, struct_name, struct_info) = find_i64_only_structs(scope, emit)?;

        // Pick two i64 fields for the addition in the helper body
        let f0_idx = emit.gen_range(0..struct_info.fields.len());
        let mut f1_idx = emit.gen_range(0..struct_info.fields.len());
        if f1_idx == f0_idx && struct_info.fields.len() > 1 {
            f1_idx = (f0_idx + 1) % struct_info.fields.len();
        }
        let field0 = &struct_info.fields[f0_idx].name;
        let field1 = &struct_info.fields[f1_idx].name;

        let variant = emit.gen_range(0..2);
        match variant {
            0 => emit_i64_variant(scope, emit, &struct_name, &struct_info, field0, field1),
            _ => emit_string_variant(scope, emit, &struct_name, &struct_info, field0, field1),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 1: generic transform returning i64
// ---------------------------------------------------------------------------

fn emit_i64_variant(
    scope: &mut Scope,
    emit: &mut Emit,
    struct_name: &str,
    struct_info: &StructInfo,
    field0: &str,
    field1: &str,
) -> Option<String> {
    let fn_id = emit.gen_range(10000..99999);
    let fn_name = format!("helper_{}", fn_id);

    // Module-level generic function declaration
    let decl = format!(
        "func {fn}<T>(p: {sn}, f: (i64) -> T) -> T {{\n    return f(p.{f0} + p.{f1})\n}}",
        fn = fn_name,
        sn = struct_name,
        f0 = field0,
        f1 = field1,
    );
    scope.add_module_decl(decl);

    // Build the struct literal
    let struct_var = scope.fresh_name();
    let struct_literal = gen_struct_literal(struct_name, struct_info, scope, emit);

    // Pick a multiplier for the closure body
    let multiplier = emit.gen_i64_range(2, 10);

    let result_name = scope.fresh_name();

    let indent = emit.indent_str();
    let code = format!(
        "let {sv} = {sl}\n{indent}let {rn} = {fn}({sv}, (x: i64) => x * {mul})",
        sv = struct_var,
        sl = struct_literal,
        rn = result_name,
        fn = fn_name,
        mul = multiplier,
        indent = indent,
    );

    Some(code)
}

// ---------------------------------------------------------------------------
// Variant 2: generic transform returning string
// ---------------------------------------------------------------------------

fn emit_string_variant(
    scope: &mut Scope,
    emit: &mut Emit,
    struct_name: &str,
    struct_info: &StructInfo,
    field0: &str,
    field1: &str,
) -> Option<String> {
    let fn_id = emit.gen_range(10000..99999);
    let fn_name = format!("helper_{}", fn_id);

    // Module-level generic function declaration
    let decl = format!(
        "func {fn}<T>(p: {sn}, f: (i64) -> T) -> T {{\n    return f(p.{f0} + p.{f1})\n}}",
        fn = fn_name,
        sn = struct_name,
        f0 = field0,
        f1 = field1,
    );
    scope.add_module_decl(decl);

    // Build the struct literal
    let struct_var = scope.fresh_name();
    let struct_literal = gen_struct_literal(struct_name, struct_info, scope, emit);

    // Pick a label prefix for the closure body
    let prefixes = ["sum=", "total=", "result=", "ans="];
    let prefix_idx = emit.gen_range(0..prefixes.len());
    let prefix = prefixes[prefix_idx];

    let result_name = scope.fresh_name();

    let indent = emit.indent_str();
    let code = format!(
        "let {sv} = {sl}\n{indent}let {rn} = {fn}({sv}, (x: i64) => \"{pfx}\" + x.to_string())",
        sv = struct_var,
        sl = struct_literal,
        rn = result_name,
        fn = fn_name,
        pfx = prefix,
        indent = indent,
    );

    Some(code)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{FieldInfo, SymbolTable};
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

    fn make_table_with_struct() -> SymbolTable {
        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let module = table.get_module_mut(mod_id).unwrap();
        module.add_symbol(
            "Point".to_string(),
            SymbolKind::Struct(StructInfo {
                fields: vec![
                    FieldInfo {
                        name: "x".to_string(),
                        field_type: TypeInfo::Primitive(PrimitiveType::I64),
                    },
                    FieldInfo {
                        name: "y".to_string(),
                        field_type: TypeInfo::Primitive(PrimitiveType::I64),
                    },
                ],
                static_methods: vec![],
            }),
        );
        table
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(GenericStructClosure.name(), "generic_struct_closure");
    }

    #[test]
    fn precondition_rejects_class_methods() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        // No class => precondition passes (but module_id is None so it fails)
        assert!(!GenericStructClosure.precondition(&scope, &params));
        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(GenericStructClosure.precondition(&scope, &params));
        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!GenericStructClosure.precondition(&scope, &params));
    }

    #[test]
    fn returns_none_without_module() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = GenericStructClosure.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn returns_none_without_structs() {
        let mut table = SymbolTable::new();
        let _mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = GenericStructClosure.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn generates_i64_variant() {
        let table = make_table_with_struct();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericStructClosure.generate(&mut scope, &mut emit, &params) {
                if text.contains("=> x *") {
                    found = true;
                    assert!(
                        !scope.module_decls.is_empty(),
                        "expected module_decl for i64 variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("<T>"),
                        "expected generic param in decl: {decl}"
                    );
                    assert!(
                        decl.contains("Point"),
                        "expected struct name in decl: {decl}"
                    );
                    assert!(
                        text.contains("(x: i64)"),
                        "expected typed lambda param: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated i64 variant in 100 seeds");
    }

    #[test]
    fn generates_string_variant() {
        let table = make_table_with_struct();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericStructClosure.generate(&mut scope, &mut emit, &params) {
                if text.contains("to_string()") {
                    found = true;
                    assert!(
                        !scope.module_decls.is_empty(),
                        "expected module_decl for string variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("<T>"),
                        "expected generic param in decl: {decl}"
                    );
                    assert!(
                        text.contains("(x: i64)"),
                        "expected typed lambda param: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated string variant in 100 seeds");
    }

    #[test]
    fn module_decl_contains_struct_field_access() {
        let table = make_table_with_struct();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if GenericStructClosure
                .generate(&mut scope, &mut emit, &params)
                .is_some()
            {
                let decl = &scope.module_decls[0];
                // Should access struct fields with p.x or p.y
                assert!(
                    decl.contains("p.x") || decl.contains("p.y"),
                    "expected field access in decl: {decl}"
                );
                return;
            }
        }
        panic!("never generated output in 50 seeds");
    }
}
