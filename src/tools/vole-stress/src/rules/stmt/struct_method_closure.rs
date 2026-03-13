//! Rule: struct extend methods that return closures capturing local variables.
//!
//! Exercises the intersection of struct method dispatch + closure creation +
//! value capture from method context.
//!
//! **Variant 1 -- getter**: Method returning `() -> i64` capturing a single field:
//! ```vole
//! extend Point {
//!     func get_x_getter_12345() -> () -> i64 {
//!         let captured_x = self.x
//!         return () => captured_x
//!     }
//! }
//! let p = Point { x: 10, y: 20 }
//! let getter = p.get_x_getter_12345()
//! let local0 = getter()
//! ```
//!
//! **Variant 2 -- adder**: Method returning `(i64) -> i64` capturing a computation:
//! ```vole
//! extend Point {
//!     func get_adder_12345() -> (i64) -> i64 {
//!         let base = self.x + self.y
//!         return (n: i64) => base + n
//!     }
//! }
//! let p = Point { x: 10, y: 20 }
//! let adder = p.get_adder_12345()
//! let local0 = adder(5_i64)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, StructInfo, SymbolId, SymbolKind, TypeInfo};

pub struct StructMethodClosure;

/// Find non-generic structs with 2+ i64 fields.
fn find_i64_structs(scope: &Scope, emit: &mut Emit) -> Option<(SymbolId, String, StructInfo)> {
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

/// Generate a struct literal with small i64 values.
fn gen_struct_literal(struct_name: &str, struct_info: &StructInfo, emit: &mut Emit) -> String {
    let fields: Vec<String> = struct_info
        .fields
        .iter()
        .map(|f| format!("{}: {}", f.name, emit.gen_i64_range(1, 50)))
        .collect();

    format!("{} {{ {} }}", struct_name, fields.join(", "))
}

/// Variant 1: getter -- method returning `() -> i64` that captures a single field.
///
/// ```vole
/// extend Point {
///     func get_x_getter_UID() -> () -> i64 {
///         let captured_x = self.x
///         return () => captured_x
///     }
/// }
/// let p = Point { x: 10, y: 20 }
/// let getter = p.get_x_getter_UID()
/// let local0 = getter()
/// ```
fn emit_getter_variant(
    scope: &mut Scope,
    emit: &mut Emit,
    struct_name: &str,
    struct_info: &StructInfo,
) -> Option<String> {
    let uid = emit.gen_range(10000..99999);

    // Pick a field to capture
    let field_idx = emit.gen_range(0..struct_info.fields.len());
    let field = &struct_info.fields[field_idx];
    let field_name = &field.name;

    let method_name = format!("get_{}_getter_{}", field_name, uid);

    // Build the extend block
    let extend_decl = format!(
        "extend {sn} {{\n\
         \x20   func {method}() -> () -> i64 {{\n\
         \x20       let captured_{f} = self.{f}\n\
         \x20       return () => captured_{f}\n\
         \x20   }}\n\
         }}",
        sn = struct_name,
        method = method_name,
        f = field_name,
    );
    scope.add_module_decl(extend_decl);

    // Build inline code: create struct, call method, invoke returned closure
    let struct_var = scope.fresh_name();
    let struct_literal = gen_struct_literal(struct_name, struct_info, emit);
    let closure_var = scope.fresh_name();
    let result_var = scope.fresh_name();

    scope.add_local(
        result_var.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();
    Some(format!(
        "let {sv} = {sl}\n\
         {indent}let {cv} = {sv}.{method}()\n\
         {indent}let {rv} = {cv}()",
        sv = struct_var,
        sl = struct_literal,
        cv = closure_var,
        method = method_name,
        rv = result_var,
        indent = indent,
    ))
}

/// Variant 2: adder -- method returning `(i64) -> i64` that captures a computation
/// from two fields.
///
/// ```vole
/// extend Point {
///     func get_adder_UID() -> (i64) -> i64 {
///         let base = self.x + self.y
///         return (n: i64) => base + n
///     }
/// }
/// let p = Point { x: 10, y: 20 }
/// let adder = p.get_adder_UID()
/// let local0 = adder(5_i64)
/// ```
fn emit_adder_variant(
    scope: &mut Scope,
    emit: &mut Emit,
    struct_name: &str,
    struct_info: &StructInfo,
) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let method_name = format!("get_adder_{}", uid);

    // Pick two fields for the computation
    let f0_idx = emit.gen_range(0..struct_info.fields.len());
    let mut f1_idx = emit.gen_range(0..struct_info.fields.len());
    if f1_idx == f0_idx && struct_info.fields.len() > 1 {
        f1_idx = (f0_idx + 1) % struct_info.fields.len();
    }
    let field0 = &struct_info.fields[f0_idx].name;
    let field1 = &struct_info.fields[f1_idx].name;

    // Pick an operator for the base computation
    let ops = ["+", "*"];
    let base_op = ops[emit.gen_range(0..ops.len())];

    // Build the extend block
    let extend_decl = format!(
        "extend {sn} {{\n\
         \x20   func {method}() -> (i64) -> i64 {{\n\
         \x20       let base = self.{f0} {op} self.{f1}\n\
         \x20       return (n: i64) => base + n\n\
         \x20   }}\n\
         }}",
        sn = struct_name,
        method = method_name,
        f0 = field0,
        op = base_op,
        f1 = field1,
    );
    scope.add_module_decl(extend_decl);

    // Build inline code: create struct, call method, invoke returned closure with arg
    let struct_var = scope.fresh_name();
    let struct_literal = gen_struct_literal(struct_name, struct_info, emit);
    let closure_var = scope.fresh_name();
    let result_var = scope.fresh_name();
    let arg = emit.gen_i64_range(1, 50);

    scope.add_local(
        result_var.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();
    Some(format!(
        "let {sv} = {sl}\n\
         {indent}let {cv} = {sv}.{method}()\n\
         {indent}let {rv} = {cv}({arg}_i64)",
        sv = struct_var,
        sl = struct_literal,
        cv = closure_var,
        method = method_name,
        rv = result_var,
        arg = arg,
        indent = indent,
    ))
}

impl StmtRule for StructMethodClosure {
    fn name(&self) -> &'static str {
        "struct_method_closure"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let (_sym_id, struct_name, struct_info) = find_i64_structs(scope, emit)?;

        let variant = emit.gen_range(0..2);
        match variant {
            0 => emit_getter_variant(scope, emit, &struct_name, &struct_info),
            _ => emit_adder_variant(scope, emit, &struct_name, &struct_info),
        }
    }
}

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
        assert_eq!(StructMethodClosure.name(), "struct_method_closure");
    }

    #[test]
    fn returns_none_without_module() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!StructMethodClosure.precondition(&scope, &params));
    }

    #[test]
    fn precondition_rejects_class_context() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(StructMethodClosure.precondition(&scope, &params));
        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!StructMethodClosure.precondition(&scope, &params));
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

        let result = StructMethodClosure.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn generates_getter_variant() {
        let table = make_table_with_struct();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = StructMethodClosure.generate(&mut scope, &mut emit, &params) {
                if text.contains("get_x_getter_") || text.contains("get_y_getter_") {
                    found = true;
                    // Should have 1 module decl: extend block
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for getter variant, got {}",
                        scope.module_decls.len()
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("extend Point"),
                        "expected extend decl: {decl}"
                    );
                    assert!(
                        decl.contains("-> () -> i64"),
                        "expected closure return type: {decl}"
                    );
                    assert!(
                        decl.contains("captured_"),
                        "expected local capture in method: {decl}"
                    );
                    // Inline code should invoke the returned closure
                    assert!(text.contains("()"), "expected closure invocation: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated getter variant in 100 seeds");
    }

    #[test]
    fn generates_adder_variant() {
        let table = make_table_with_struct();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = StructMethodClosure.generate(&mut scope, &mut emit, &params) {
                if text.contains("get_adder_") {
                    found = true;
                    // Should have 1 module decl: extend block
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for adder variant, got {}",
                        scope.module_decls.len()
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("extend Point"),
                        "expected extend decl: {decl}"
                    );
                    assert!(
                        decl.contains("-> (i64) -> i64"),
                        "expected closure return type: {decl}"
                    );
                    assert!(
                        decl.contains("let base ="),
                        "expected base computation in method: {decl}"
                    );
                    assert!(
                        decl.contains("(n: i64) => base + n"),
                        "expected adder closure: {decl}"
                    );
                    // Inline code should pass an i64 arg to the closure
                    assert!(
                        text.contains("_i64)"),
                        "expected i64 arg in closure call: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated adder variant in 100 seeds");
    }

    #[test]
    fn result_var_is_i64() {
        let table = make_table_with_struct();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if StructMethodClosure
                .generate(&mut scope, &mut emit, &params)
                .is_some()
            {
                let result_local = scope.locals.last().expect("should add result local");
                assert_eq!(
                    result_local.1,
                    TypeInfo::Primitive(PrimitiveType::I64),
                    "result must be i64"
                );
                return;
            }
        }
        panic!("never generated output in 50 seeds");
    }
}
