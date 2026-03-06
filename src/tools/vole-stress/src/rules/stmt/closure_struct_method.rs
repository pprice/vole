//! Rule: closures calling methods on struct instances via extend blocks.
//!
//! Stresses closure capture/parameter passing combined with extend block
//! method dispatch.
//!
//! **Variant 1 -- closure calling struct method directly:**
//! ```vole
//! extend StructName {
//!     func compute_42918(self: StructName) -> i64 {
//!         return self.field1 + self.field2
//!     }
//! }
//! let local0 = StructName { field1: 10, field2: 20 }
//! let compute_fn = (s: StructName) => s.compute_42918()
//! let local1 = compute_fn(local0)
//! ```
//!
//! **Variant 2 -- generic function applying closure to struct:**
//! ```vole
//! extend StructName {
//!     func compute_42918(self: StructName) -> i64 {
//!         return self.field1 * self.field2
//!     }
//! }
//! func apply_struct_42918<T>(s: StructName, f: (StructName) -> T) -> T {
//!     return f(s)
//! }
//! let local0 = StructName { field1: 5, field2: 3 }
//! let local1 = apply_struct_42918(local0, (s: StructName) => s.compute_42918())
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, StructInfo, SymbolId, SymbolKind, TypeInfo};

pub struct ClosureStructMethod;

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

/// Pick a method name base from a set of candidates.
fn pick_method_name(emit: &mut Emit) -> &'static str {
    let names = ["compute", "measure", "evaluate", "calculate"];
    let idx = emit.gen_range(0..names.len());
    names[idx]
}

impl StmtRule for ClosureStructMethod {
    fn name(&self) -> &'static str {
        "closure_struct_method"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let (_sym_id, struct_name, struct_info) = find_i64_only_structs(scope, emit)?;

        let variant = emit.gen_range(0..2);
        match variant {
            0 => emit_direct_closure(scope, emit, &struct_name, &struct_info),
            _ => emit_generic_apply(scope, emit, &struct_name, &struct_info),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 1: closure calling struct method directly
// ---------------------------------------------------------------------------

fn emit_direct_closure(
    scope: &mut Scope,
    emit: &mut Emit,
    struct_name: &str,
    struct_info: &StructInfo,
) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let method_base = pick_method_name(emit);
    let method_name = format!("{}_{}", method_base, uid);

    // Pick two fields for the method body
    let f0_idx = emit.gen_range(0..struct_info.fields.len());
    let mut f1_idx = emit.gen_range(0..struct_info.fields.len());
    if f1_idx == f0_idx && struct_info.fields.len() > 1 {
        f1_idx = (f0_idx + 1) % struct_info.fields.len();
    }
    let field0 = &struct_info.fields[f0_idx].name;
    let field1 = &struct_info.fields[f1_idx].name;

    // Pick an operator for the method body
    let ops = ["+", "*"];
    let body_op = ops[emit.gen_range(0..ops.len())];

    // Module decl: extend block with method
    let extend_decl = format!(
        "extend {sn} {{\n    func {method}(self: {sn}) -> i64 {{\n        return self.{f0} {op} self.{f1}\n    }}\n}}",
        sn = struct_name,
        method = method_name,
        f0 = field0,
        op = body_op,
        f1 = field1,
    );
    scope.add_module_decl(extend_decl);

    // Build the struct literal
    let struct_var = scope.fresh_name();
    let struct_literal = gen_struct_literal(struct_name, struct_info, scope, emit);

    // Create closure that calls the method
    let closure_var = scope.fresh_name();
    let result_var = scope.fresh_name();

    scope.add_local(
        result_var.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();
    let code = format!(
        "let {sv} = {sl}\n{indent}let {cv} = (s: {sn}) => s.{method}()\n{indent}let {rv} = {cv}({sv})",
        sv = struct_var,
        sl = struct_literal,
        cv = closure_var,
        sn = struct_name,
        method = method_name,
        rv = result_var,
        indent = indent,
    );

    Some(code)
}

// ---------------------------------------------------------------------------
// Variant 2: generic function applying closure to struct
// ---------------------------------------------------------------------------

fn emit_generic_apply(
    scope: &mut Scope,
    emit: &mut Emit,
    struct_name: &str,
    struct_info: &StructInfo,
) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let method_base = pick_method_name(emit);
    let method_name = format!("{}_{}", method_base, uid);
    let fn_name = format!("apply_struct_{}", uid);

    // Pick two fields for the method body
    let f0_idx = emit.gen_range(0..struct_info.fields.len());
    let mut f1_idx = emit.gen_range(0..struct_info.fields.len());
    if f1_idx == f0_idx && struct_info.fields.len() > 1 {
        f1_idx = (f0_idx + 1) % struct_info.fields.len();
    }
    let field0 = &struct_info.fields[f0_idx].name;
    let field1 = &struct_info.fields[f1_idx].name;

    // Pick an operator for the method body
    let ops = ["+", "*"];
    let body_op = ops[emit.gen_range(0..ops.len())];

    // Module decl 1: extend block with method
    let extend_decl = format!(
        "extend {sn} {{\n    func {method}(self: {sn}) -> i64 {{\n        return self.{f0} {op} self.{f1}\n    }}\n}}",
        sn = struct_name,
        method = method_name,
        f0 = field0,
        op = body_op,
        f1 = field1,
    );
    scope.add_module_decl(extend_decl);

    // Module decl 2: generic function
    let func_decl = format!(
        "func {fn_name}<T>(s: {sn}, f: ({sn}) -> T) -> T {{\n    return f(s)\n}}",
        fn_name = fn_name,
        sn = struct_name,
    );
    scope.add_module_decl(func_decl);

    // Build the struct literal
    let struct_var = scope.fresh_name();
    let struct_literal = gen_struct_literal(struct_name, struct_info, scope, emit);

    let result_var = scope.fresh_name();

    // Choose sub-variant: i64 result or string result
    let sub_variant = emit.gen_range(0..2);

    match sub_variant {
        0 => {
            // i64 result: closure calls method directly
            scope.add_local(
                result_var.clone(),
                TypeInfo::Primitive(PrimitiveType::I64),
                false,
            );

            let indent = emit.indent_str();
            let code = format!(
                "let {sv} = {sl}\n{indent}let {rv} = {fn_name}({sv}, (s: {sn}) => s.{method}())",
                sv = struct_var,
                sl = struct_literal,
                rv = result_var,
                fn_name = fn_name,
                sn = struct_name,
                method = method_name,
                indent = indent,
            );

            Some(code)
        }
        _ => {
            // string result: closure calls method and converts to string
            scope.add_local(
                result_var.clone(),
                TypeInfo::Primitive(PrimitiveType::String),
                false,
            );

            let prefixes = ["val=", "res=", "out=", "ans="];
            let prefix_idx = emit.gen_range(0..prefixes.len());
            let prefix = prefixes[prefix_idx];

            let indent = emit.indent_str();
            let code = format!(
                "let {sv} = {sl}\n{indent}let {rv} = {fn_name}({sv}, (s: {sn}) => \"{pfx}\" + s.{method}().to_string())",
                sv = struct_var,
                sl = struct_literal,
                rv = result_var,
                fn_name = fn_name,
                sn = struct_name,
                method = method_name,
                pfx = prefix,
                indent = indent,
            );

            Some(code)
        }
    }
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
        assert_eq!(ClosureStructMethod.name(), "closure_struct_method");
    }

    #[test]
    fn precondition_rejects_class_methods() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        // No module => precondition fails
        assert!(!ClosureStructMethod.precondition(&scope, &params));
        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(ClosureStructMethod.precondition(&scope, &params));
        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!ClosureStructMethod.precondition(&scope, &params));
    }

    #[test]
    fn returns_none_without_module() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClosureStructMethod.generate(&mut scope, &mut emit, &rule_params);
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

        let result = ClosureStructMethod.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn generates_direct_closure_variant() {
        let table = make_table_with_struct();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ClosureStructMethod.generate(&mut scope, &mut emit, &params) {
                // Direct closure variant has no apply_struct_ function
                if !text.contains("apply_struct_") {
                    found = true;
                    // Should have 1 module decl: extend block
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for direct variant, got {}",
                        scope.module_decls.len()
                    );
                    // Extend decl
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("extend Point"),
                        "expected extend decl: {decl}"
                    );
                    assert!(
                        decl.contains("self: Point"),
                        "expected explicit self param: {decl}"
                    );
                    // Inline code should have closure with typed param
                    assert!(
                        text.contains("(s: Point) =>"),
                        "expected typed lambda param: {text}"
                    );
                    // Should call the method on the struct
                    assert!(
                        text.contains(".compute_")
                            || text.contains(".measure_")
                            || text.contains(".evaluate_")
                            || text.contains(".calculate_"),
                        "expected method call: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated direct closure variant in 100 seeds");
    }

    #[test]
    fn generates_generic_apply_i64_variant() {
        let table = make_table_with_struct();
        let mut found = false;
        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ClosureStructMethod.generate(&mut scope, &mut emit, &params) {
                if text.contains("apply_struct_") && !text.contains("to_string()") {
                    found = true;
                    // Should have 2 module decls: extend block + generic function
                    assert_eq!(
                        scope.module_decls.len(),
                        2,
                        "expected 2 module_decls for generic variant, got {}",
                        scope.module_decls.len()
                    );
                    // Extend decl
                    let extend = &scope.module_decls[0];
                    assert!(
                        extend.contains("extend Point"),
                        "expected extend decl: {extend}"
                    );
                    // Generic function decl
                    let func = &scope.module_decls[1];
                    assert!(
                        func.contains("<T>"),
                        "expected generic param in func: {func}"
                    );
                    assert!(
                        func.contains("(Point) -> T"),
                        "expected closure param type in func: {func}"
                    );
                    // Inline code should have typed closure
                    assert!(
                        text.contains("(s: Point) =>"),
                        "expected typed lambda param: {text}"
                    );
                    break;
                }
            }
        }
        assert!(
            found,
            "never generated generic apply i64 variant in 200 seeds"
        );
    }

    #[test]
    fn generates_generic_apply_string_variant() {
        let table = make_table_with_struct();
        let mut found = false;
        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ClosureStructMethod.generate(&mut scope, &mut emit, &params) {
                if text.contains("to_string()") {
                    found = true;
                    // Should have 2 module decls: extend block + generic function
                    assert_eq!(
                        scope.module_decls.len(),
                        2,
                        "expected 2 module_decls for string variant, got {}",
                        scope.module_decls.len()
                    );
                    // Inline code should have typed closure and string conversion
                    assert!(
                        text.contains("(s: Point) =>"),
                        "expected typed lambda param: {text}"
                    );
                    // Result type should be string
                    let result_local = scope.locals.last().expect("should add result local");
                    assert_eq!(
                        result_local.1,
                        TypeInfo::Primitive(PrimitiveType::String),
                        "string variant result must be string"
                    );
                    break;
                }
            }
        }
        assert!(
            found,
            "never generated generic apply string variant in 200 seeds"
        );
    }

    #[test]
    fn extend_decl_contains_field_access() {
        let table = make_table_with_struct();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if ClosureStructMethod
                .generate(&mut scope, &mut emit, &params)
                .is_some()
            {
                // The extend block (decl[0]) should access struct fields with self.x or self.y
                let extend_decl = &scope.module_decls[0];
                assert!(
                    extend_decl.contains("self.x") || extend_decl.contains("self.y"),
                    "expected field access in extend decl: {extend_decl}"
                );
                return;
            }
        }
        panic!("never generated output in 50 seeds");
    }

    #[test]
    fn method_names_are_unique() {
        let table = make_table_with_struct();
        for seed in 0..20 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if ClosureStructMethod
                .generate(&mut scope, &mut emit, &params)
                .is_some()
            {
                // Method name in extend decl should have numeric suffix
                let extend_decl = &scope.module_decls[0];
                assert!(
                    extend_decl.contains("compute_")
                        || extend_decl.contains("measure_")
                        || extend_decl.contains("evaluate_")
                        || extend_decl.contains("calculate_"),
                    "expected suffixed method name in extend decl: {extend_decl}"
                );
                return;
            }
        }
        panic!("never generated output in 20 seeds");
    }
}
