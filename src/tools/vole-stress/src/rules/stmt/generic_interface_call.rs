//! Rule: call a generic function with an interface-bounded type parameter.
//!
//! Stresses the intersection of generics and interface dispatch by generating
//! a fresh interface, an extend block implementing it for an existing struct,
//! and a generic function with an interface-bounded type parameter that calls
//! an interface method.
//!
//! The interface, extend block, and generic function are all emitted at module
//! level via [`Scope::add_module_decl`].
//!
//! **Variant 1 -- simple generic interface call:**
//! ```vole
//! interface Meas_42918 {
//!     func compute() -> i64
//! }
//! extend Point with Meas_42918 {
//!     func compute() -> i64 {
//!         return self.x + self.y
//!     }
//! }
//! func describe_42918<T: Meas_42918>(item: T) -> i64 {
//!     return item.compute() * 2
//! }
//! let local0 = Point { x: 10, y: 20 }
//! let local1 = describe_42918(local0)
//! ```
//!
//! **Variant 2 -- generic interface + closure:**
//! ```vole
//! interface Meas_42918 {
//!     func compute() -> i64
//! }
//! extend Point with Meas_42918 {
//!     func compute() -> i64 {
//!         return self.x + self.y
//!     }
//! }
//! func apply_42918<T: Meas_42918, U>(item: T, f: (i64) -> U) -> U {
//!     return f(item.compute())
//! }
//! let local0 = Point { x: 10, y: 20 }
//! let local1 = apply_42918(local0, (x: i64) => x + 100)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, StructInfo, SymbolKind, TypeInfo};

pub struct GenericInterfaceCall;

/// Find non-generic structs with 2+ fields that are ALL i64.
fn find_i64_only_structs(scope: &Scope, emit: &mut Emit) -> Option<(String, StructInfo)> {
    let module_id = scope.module_id?;
    let module = scope.table.get_module(module_id)?;

    let candidates: Vec<(String, StructInfo)> = module
        .structs()
        .filter_map(|sym| {
            if let SymbolKind::Struct(ref info) = sym.kind {
                if info.fields.len() >= 2
                    && info
                        .fields
                        .iter()
                        .all(|f| matches!(f.field_type, TypeInfo::Primitive(PrimitiveType::I64)))
                {
                    Some((sym.name.clone(), info.clone()))
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

/// Pick an interface method name from a set of candidates.
fn pick_method_name(emit: &mut Emit) -> &'static str {
    let names = [
        "compute",
        "measure",
        "evaluate",
        "score",
        "rank",
        "magnitude",
        "weight",
        "total",
    ];
    let idx = emit.gen_range(0..names.len());
    names[idx]
}

/// Pick an interface name prefix from a set of candidates.
fn pick_iface_prefix(emit: &mut Emit) -> &'static str {
    let prefixes = ["Meas", "Eval", "Score", "Calc", "Metric"];
    let idx = emit.gen_range(0..prefixes.len());
    prefixes[idx]
}

impl StmtRule for GenericInterfaceCall {
    fn name(&self) -> &'static str {
        "generic_interface_call"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Must be at module level (not inside a class method) and have a module
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let (struct_name, struct_info) = find_i64_only_structs(scope, emit)?;

        let variant = emit.gen_range(0..2);
        match variant {
            0 => emit_simple_variant(scope, emit, &struct_name, &struct_info),
            _ => emit_closure_variant(scope, emit, &struct_name, &struct_info),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 1: simple generic interface call
// ---------------------------------------------------------------------------

fn emit_simple_variant(
    scope: &mut Scope,
    emit: &mut Emit,
    struct_name: &str,
    struct_info: &StructInfo,
) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let method_name = pick_method_name(emit);
    let iface_prefix = pick_iface_prefix(emit);
    let iface_name = format!("{}_{}", iface_prefix, uid);
    let fn_name = format!("describe_{}", uid);

    // Pick two fields for the method body
    let f0_idx = emit.gen_range(0..struct_info.fields.len());
    let mut f1_idx = emit.gen_range(0..struct_info.fields.len());
    if f1_idx == f0_idx && struct_info.fields.len() > 1 {
        f1_idx = (f0_idx + 1) % struct_info.fields.len();
    }
    let field0 = &struct_info.fields[f0_idx].name;
    let field1 = &struct_info.fields[f1_idx].name;

    // Pick an operator for the method body
    let ops = ["+", "-", "*"];
    let body_op = ops[emit.gen_range(0..ops.len())];

    // Pick a multiplier for the generic function body
    let multiplier = emit.gen_i64_range(2, 10);

    // Module decl 1: interface
    let iface_decl = format!(
        "interface {iface} {{\n    func {method}() -> i64\n}}",
        iface = iface_name,
        method = method_name,
    );
    scope.add_module_decl(iface_decl);

    // Module decl 2: extend block
    let extend_decl = format!(
        "extend {sn} with {iface} {{\n    func {method}() -> i64 {{\n        return self.{f0} {op} self.{f1}\n    }}\n}}",
        sn = struct_name,
        iface = iface_name,
        method = method_name,
        f0 = field0,
        op = body_op,
        f1 = field1,
    );
    scope.add_module_decl(extend_decl);

    // Module decl 3: generic function
    let func_decl = format!(
        "func {fn_name}<T: {iface}>(item: T) -> i64 {{\n    return item.{method}() * {mul}\n}}",
        fn_name = fn_name,
        iface = iface_name,
        method = method_name,
        mul = multiplier,
    );
    scope.add_module_decl(func_decl);

    // Build the struct literal and call
    let struct_var = scope.fresh_name();
    let struct_literal = gen_struct_literal(struct_name, struct_info, scope, emit);

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();
    let code = format!(
        "let {sv} = {sl}\n{indent}let {rn} = {fn_name}({sv})",
        sv = struct_var,
        sl = struct_literal,
        rn = result_name,
        fn_name = fn_name,
        indent = indent,
    );

    Some(code)
}

// ---------------------------------------------------------------------------
// Variant 2: generic interface + closure
// ---------------------------------------------------------------------------

fn emit_closure_variant(
    scope: &mut Scope,
    emit: &mut Emit,
    struct_name: &str,
    struct_info: &StructInfo,
) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let method_name = pick_method_name(emit);
    let iface_prefix = pick_iface_prefix(emit);
    let iface_name = format!("{}_{}", iface_prefix, uid);
    let fn_name = format!("apply_{}", uid);

    // Pick two fields for the method body
    let f0_idx = emit.gen_range(0..struct_info.fields.len());
    let mut f1_idx = emit.gen_range(0..struct_info.fields.len());
    if f1_idx == f0_idx && struct_info.fields.len() > 1 {
        f1_idx = (f0_idx + 1) % struct_info.fields.len();
    }
    let field0 = &struct_info.fields[f0_idx].name;
    let field1 = &struct_info.fields[f1_idx].name;

    // Pick an operator for the method body
    let ops = ["+", "-", "*"];
    let body_op = ops[emit.gen_range(0..ops.len())];

    // Module decl 1: interface
    let iface_decl = format!(
        "interface {iface} {{\n    func {method}() -> i64\n}}",
        iface = iface_name,
        method = method_name,
    );
    scope.add_module_decl(iface_decl);

    // Module decl 2: extend block
    let extend_decl = format!(
        "extend {sn} with {iface} {{\n    func {method}() -> i64 {{\n        return self.{f0} {op} self.{f1}\n    }}\n}}",
        sn = struct_name,
        iface = iface_name,
        method = method_name,
        f0 = field0,
        op = body_op,
        f1 = field1,
    );
    scope.add_module_decl(extend_decl);

    // Choose sub-variant: i64 closure or string closure
    let sub_variant = emit.gen_range(0..2);

    match sub_variant {
        0 => {
            // i64 closure variant
            let func_decl = format!(
                "func {fn_name}<T: {iface}, U>(item: T, f: (i64) -> U) -> U {{\n    return f(item.{method}())\n}}",
                fn_name = fn_name,
                iface = iface_name,
                method = method_name,
            );
            scope.add_module_decl(func_decl);

            let struct_var = scope.fresh_name();
            let struct_literal = gen_struct_literal(struct_name, struct_info, scope, emit);

            let addend = emit.gen_i64_range(10, 200);
            let result_name = scope.fresh_name();
            scope.add_local(
                result_name.clone(),
                TypeInfo::Primitive(PrimitiveType::I64),
                false,
            );

            let indent = emit.indent_str();
            let code = format!(
                "let {sv} = {sl}\n{indent}let {rn} = {fn_name}({sv}, (x: i64) => x + {addend})",
                sv = struct_var,
                sl = struct_literal,
                rn = result_name,
                fn_name = fn_name,
                addend = addend,
                indent = indent,
            );

            Some(code)
        }
        _ => {
            // string closure variant
            let func_decl = format!(
                "func {fn_name}<T: {iface}, U>(item: T, f: (i64) -> U) -> U {{\n    return f(item.{method}())\n}}",
                fn_name = fn_name,
                iface = iface_name,
                method = method_name,
            );
            scope.add_module_decl(func_decl);

            let struct_var = scope.fresh_name();
            let struct_literal = gen_struct_literal(struct_name, struct_info, scope, emit);

            let prefixes = ["val=", "res=", "out=", "ans="];
            let prefix_idx = emit.gen_range(0..prefixes.len());
            let prefix = prefixes[prefix_idx];

            let result_name = scope.fresh_name();
            scope.add_local(
                result_name.clone(),
                TypeInfo::Primitive(PrimitiveType::String),
                false,
            );

            let indent = emit.indent_str();
            let code = format!(
                "let {sv} = {sl}\n{indent}let {rn} = {fn_name}({sv}, (x: i64) => \"{pfx}\" + x.to_string())",
                sv = struct_var,
                sl = struct_literal,
                rn = result_name,
                fn_name = fn_name,
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
        assert_eq!(GenericInterfaceCall.name(), "generic_interface_call");
    }

    #[test]
    fn precondition_rejects_class_methods() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        // No module => precondition fails
        assert!(!GenericInterfaceCall.precondition(&scope, &params));
        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(GenericInterfaceCall.precondition(&scope, &params));
        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!GenericInterfaceCall.precondition(&scope, &params));
    }

    #[test]
    fn returns_none_without_module() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = GenericInterfaceCall.generate(&mut scope, &mut emit, &rule_params);
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

        let result = GenericInterfaceCall.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn generates_simple_variant() {
        let table = make_table_with_struct();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericInterfaceCall.generate(&mut scope, &mut emit, &params) {
                if text.contains("describe_") {
                    found = true;
                    // Should have 3 module decls: interface, extend, generic func
                    assert_eq!(
                        scope.module_decls.len(),
                        3,
                        "expected 3 module_decls for simple variant, got {}",
                        scope.module_decls.len()
                    );
                    // Interface decl
                    assert!(
                        scope.module_decls[0].contains("interface"),
                        "expected interface decl: {}",
                        scope.module_decls[0]
                    );
                    // Extend decl
                    assert!(
                        scope.module_decls[1].contains("extend Point with"),
                        "expected extend decl: {}",
                        scope.module_decls[1]
                    );
                    // Generic func decl with interface bound
                    assert!(
                        scope.module_decls[2].contains("<T:"),
                        "expected interface-bounded generic: {}",
                        scope.module_decls[2]
                    );
                    // Inline code should have struct literal and call
                    assert!(
                        text.contains("Point {"),
                        "expected struct literal in code: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated simple variant in 100 seeds");
    }

    #[test]
    fn generates_closure_variant() {
        let table = make_table_with_struct();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericInterfaceCall.generate(&mut scope, &mut emit, &params) {
                if text.contains("apply_") {
                    found = true;
                    // Should have 3 module decls: interface, extend, generic func
                    assert_eq!(
                        scope.module_decls.len(),
                        3,
                        "expected 3 module_decls for closure variant, got {}",
                        scope.module_decls.len()
                    );
                    // Generic func should have two type params: T bounded, U unbounded
                    let func_decl = &scope.module_decls[2];
                    assert!(
                        func_decl.contains("<T:") && func_decl.contains(", U>"),
                        "expected <T: Iface, U> in func decl: {func_decl}"
                    );
                    // Inline code should have closure
                    assert!(
                        text.contains("(x: i64) =>"),
                        "expected closure in code: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated closure variant in 100 seeds");
    }

    #[test]
    fn generates_string_closure_subvariant() {
        let table = make_table_with_struct();
        let mut found = false;
        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericInterfaceCall.generate(&mut scope, &mut emit, &params) {
                if text.contains("to_string()") {
                    found = true;
                    assert!(
                        text.contains("(x: i64) =>"),
                        "expected closure in code: {text}"
                    );
                    // Result type should be string
                    let result_local = scope.locals.last().expect("should add result local");
                    assert_eq!(
                        result_local.1,
                        TypeInfo::Primitive(PrimitiveType::String),
                        "string closure result must be string"
                    );
                    break;
                }
            }
        }
        assert!(
            found,
            "never generated string closure sub-variant in 200 seeds"
        );
    }

    #[test]
    fn module_decls_contain_field_access() {
        let table = make_table_with_struct();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if GenericInterfaceCall
                .generate(&mut scope, &mut emit, &params)
                .is_some()
            {
                // The extend block (decl[1]) should access struct fields with self.x or self.y
                let extend_decl = &scope.module_decls[1];
                assert!(
                    extend_decl.contains("self.x") || extend_decl.contains("self.y"),
                    "expected field access in extend decl: {extend_decl}"
                );
                return;
            }
        }
        panic!("never generated output in 50 seeds");
    }
}
