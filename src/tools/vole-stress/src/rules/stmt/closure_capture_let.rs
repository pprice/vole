//! Rule: closure that captures primitive variables from outer scope.
//!
//! Finds 1-2 primitive-typed variables (i64, i32, f64, string, bool) in scope
//! and generates a lambda whose body references them. The closure is then
//! immediately invoked or bound and invoked.
//!
//! **Pattern A -- numeric capture, direct invoke:**
//! ```vole
//! let result = ((x: i64) -> i64 => x + outer_n)(5)
//! ```
//!
//! **Pattern B -- string capture, bind + invoke:**
//! ```vole
//! let f = (s: string) -> string => prefix + " " + s
//! let result = f("world")
//! ```
//!
//! **Pattern C -- multi-capture numeric:**
//! ```vole
//! let result = ((x: i64) -> i64 => x + a + b)(10)
//! ```
//!
//! Only captures safe primitive types (i64, i32, f64, string, bool).
//! Avoids Optional, Class instances, and i128 per journal safety notes.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

/// Primitive types safe to capture in closures.
const SAFE_CAPTURE_PRIMS: [PrimitiveType; 5] = [
    PrimitiveType::I64,
    PrimitiveType::I32,
    PrimitiveType::F64,
    PrimitiveType::String,
    PrimitiveType::Bool,
];

pub struct ClosureCaptureLet;

impl StmtRule for ClosureCaptureLet {
    fn name(&self) -> &'static str {
        "closure_capture_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.06)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Skip in generic class methods (closure capture bug)
        !scope.is_in_generic_class_method()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Collect all primitive-typed variables safe for capture
        let candidates = collect_capturable_vars(scope);
        if candidates.is_empty() {
            return None;
        }

        // Pick 1-2 variables to capture
        let capture_count = std::cmp::min(candidates.len(), emit.random_in(1, 2));
        let mut chosen = candidates;
        emit.shuffle(&mut chosen);
        chosen.truncate(capture_count);

        // Classify captured types to decide closure shape
        let has_string = chosen
            .iter()
            .any(|(_, p)| matches!(p, PrimitiveType::String));
        let has_numeric = chosen.iter().any(|(_, p)| {
            matches!(
                p,
                PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64
            )
        });

        if has_string && !has_numeric {
            // String-only capture: (s: string) -> string => captured + " " + s
            emit_string_capture(scope, emit, &chosen)
        } else {
            // Numeric capture (possibly with bool): (x: i64) -> i64 => x + captured
            emit_numeric_capture(scope, emit, &chosen)
        }
    }
}

/// Collect variables from scope that have safe-to-capture primitive types.
fn collect_capturable_vars(scope: &Scope) -> Vec<(String, PrimitiveType)> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if let TypeInfo::Primitive(p) = ty {
            if SAFE_CAPTURE_PRIMS.contains(p) {
                out.push((name.clone(), *p));
            }
        }
    }
    for param in scope.params {
        if let TypeInfo::Primitive(p) = &param.param_type {
            if SAFE_CAPTURE_PRIMS.contains(p) {
                out.push((param.name.clone(), *p));
            }
        }
    }
    out
}

/// Generate a closure that captures numeric (and possibly bool) variables.
///
/// Produces either a direct-invoke or bind-then-invoke pattern.
fn emit_numeric_capture(
    scope: &mut Scope,
    emit: &mut Emit,
    captured: &[(String, PrimitiveType)],
) -> Option<String> {
    // Build the body expression: x + captured1 [+ captured2] [+ when { bool => 1, _ => 0 }]
    let mut body_parts: Vec<String> = vec!["x".to_string()];

    // Determine if we need i64 widening (when mixing i32 or bool with i64)
    let has_i32 = captured
        .iter()
        .any(|(_, p)| matches!(p, PrimitiveType::I32));
    let has_bool = captured
        .iter()
        .any(|(_, p)| matches!(p, PrimitiveType::Bool));

    for (name, prim) in captured {
        match prim {
            PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64 => {
                body_parts.push(name.clone());
            }
            PrimitiveType::Bool => {
                body_parts.push(format!(
                    "when {{ {} => 1, _ => 0 }}",
                    name,
                ));
            }
            PrimitiveType::String => {
                // String in a numeric context: use its length
                body_parts.push(format!("{}.length()", name));
            }
            _ => {}
        }
    }

    let mut body_expr = body_parts.join(" + ");

    // If mixing i32 or bool, widen to i64
    if has_i32 || has_bool {
        body_expr = format!("{} + 0_i64", body_expr);
    }

    // Determine the closure param/return type
    let has_f64 = captured
        .iter()
        .any(|(_, p)| matches!(p, PrimitiveType::F64));
    let (closure_type_str, closure_prim) = if has_f64 {
        ("f64", PrimitiveType::F64)
    } else {
        ("i64", PrimitiveType::I64)
    };

    let use_bind = emit.gen_bool(0.5);

    if use_bind {
        // Pattern B: bind closure then invoke
        let fn_name = scope.fresh_name();
        let result_name = scope.fresh_name();
        let arg = literal_for_prim(closure_prim, emit);

        scope.add_local(
            fn_name.clone(),
            TypeInfo::Function {
                param_types: vec![TypeInfo::Primitive(closure_prim)],
                return_type: Box::new(TypeInfo::Primitive(closure_prim)),
            },
            false,
        );
        scope.add_local(
            result_name.clone(),
            TypeInfo::Primitive(closure_prim),
            false,
        );

        let indent = emit.indent_str();
        Some(format!(
            "let {} = (x: {}) -> {} => {}\n{}let {} = {}({})",
            fn_name, closure_type_str, closure_type_str, body_expr, indent, result_name, fn_name,
            arg,
        ))
    } else {
        // Pattern A: direct invoke
        let result_name = scope.fresh_name();
        let arg = literal_for_prim(closure_prim, emit);

        scope.add_local(
            result_name.clone(),
            TypeInfo::Primitive(closure_prim),
            false,
        );

        Some(format!(
            "let {} = ((x: {}) -> {} => {})({})",
            result_name, closure_type_str, closure_type_str, body_expr, arg,
        ))
    }
}

/// Generate a closure that captures string variables.
///
/// Produces: `(s: string) -> string => captured + " " + s`
fn emit_string_capture(
    scope: &mut Scope,
    emit: &mut Emit,
    captured: &[(String, PrimitiveType)],
) -> Option<String> {
    // Pick the first string capture as the prefix
    let string_var = captured
        .iter()
        .find(|(_, p)| matches!(p, PrimitiveType::String))?;

    // Build body: captured + " " + s  (or s + " " + captured for variety)
    let body_expr = if emit.gen_bool(0.5) {
        format!("{} + \" \" + s", string_var.0)
    } else {
        format!("s + \" \" + {}", string_var.0)
    };

    let use_bind = emit.gen_bool(0.5);

    if use_bind {
        // Bind then invoke
        let fn_name = scope.fresh_name();
        let result_name = scope.fresh_name();

        scope.add_local(
            fn_name.clone(),
            TypeInfo::Function {
                param_types: vec![TypeInfo::Primitive(PrimitiveType::String)],
                return_type: Box::new(TypeInfo::Primitive(PrimitiveType::String)),
            },
            false,
        );
        scope.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let indent = emit.indent_str();
        Some(format!(
            "let {} = (s: string) -> string => {}\n{}let {} = {}(\"test\")",
            fn_name, body_expr, indent, result_name, fn_name,
        ))
    } else {
        // Direct invoke
        let result_name = scope.fresh_name();

        scope.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        Some(format!(
            "let {} = ((s: string) -> string => {})(\"test\")",
            result_name, body_expr,
        ))
    }
}

/// Generate a literal argument for the given primitive type.
fn literal_for_prim(prim: PrimitiveType, emit: &mut Emit) -> String {
    match prim {
        PrimitiveType::I64 => format!("{}", emit.random_in(1, 50)),
        PrimitiveType::I32 => format!("{}_i32", emit.random_in(1, 50)),
        PrimitiveType::F64 => format!("{}.0", emit.random_in(1, 50)),
        _ => format!("{}", emit.random_in(1, 50)),
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
        assert_eq!(ClosureCaptureLet.name(), "closure_capture_let");
    }

    #[test]
    fn returns_none_without_primitives_in_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(ClosureCaptureLet
            .generate(&mut scope, &mut emit, &params)
            .is_none());
    }

    #[test]
    fn generates_with_i64_in_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("n".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClosureCaptureLet.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("=>"), "expected lambda, got: {text}");
        assert!(text.contains("n"), "expected captured var, got: {text}");
    }

    #[test]
    fn generates_with_string_in_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "prefix".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClosureCaptureLet.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("=>"), "expected lambda, got: {text}");
        assert!(text.contains("prefix"), "expected captured var, got: {text}");
    }

    #[test]
    fn generates_with_bool_in_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "flag".into(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClosureCaptureLet.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("=>"), "expected lambda, got: {text}");
        assert!(text.contains("flag"), "expected captured var, got: {text}");
    }

    #[test]
    fn generates_with_multiple_captures() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("a".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        scope.add_local("b".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClosureCaptureLet.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("=>"), "expected lambda, got: {text}");
        // At least one captured var should appear
        assert!(
            text.contains("a") || text.contains("b"),
            "expected captured var, got: {text}"
        );
    }

    #[test]
    fn adds_result_local() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("n".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        ClosureCaptureLet.generate(&mut scope, &mut emit, &params);
        // Should add at least one local (the result variable)
        assert!(scope.locals.len() > initial_len);
    }

    #[test]
    fn precondition_rejects_generic_class_method() {
        use crate::symbols::{ClassInfo, ModuleId, SymbolId, SymbolKind, TypeParam};

        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test".into(), "test.vole".into());
        let module = table.get_module_mut(mod_id).unwrap();
        let sym_id = module.add_symbol(
            "GenericClass".into(),
            SymbolKind::Class(ClassInfo {
                fields: vec![],
                methods: vec![],
                static_methods: vec![],
                implements: vec![],
                type_params: vec![TypeParam {
                    name: "T".into(),
                    constraints: vec![],
                }],
            }),
        );

        let mut scope = Scope::with_module(&[], &table, mod_id);
        scope.current_class_sym_id = Some((mod_id, sym_id));

        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!ClosureCaptureLet.precondition(&scope, &params));
    }
}
