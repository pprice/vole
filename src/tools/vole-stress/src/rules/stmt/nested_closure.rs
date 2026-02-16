//! Rule: nested closure capture where one closure captures and invokes another.
//!
//! Finds a closure-typed local `(i64) -> i64` already in scope, creates an
//! outer closure that captures and calls it, then invokes the outer closure.
//!
//! ```vole
//! let f = (x: i64) -> i64 => x + 1
//! let g = (y: i64) -> i64 => f(y) + 2
//! let result = g(5)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct NestedClosure;

impl StmtRule for NestedClosure {
    fn name(&self) -> &'static str {
        "nested_closure"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.10)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        !scope.is_in_generic_class_method()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Find closure-typed locals: (i64) -> i64
        let candidates: Vec<String> = scope
            .vars_matching(|v| {
                matches!(
                    &v.type_info,
                    TypeInfo::Function { param_types, return_type }
                    if param_types.len() == 1
                        && matches!(param_types[0], TypeInfo::Primitive(PrimitiveType::I64))
                        && matches!(return_type.as_ref(), TypeInfo::Primitive(PrimitiveType::I64))
                )
            })
            .into_iter()
            .map(|v| v.name)
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let inner_fn = candidates[idx].clone();

        // Create the outer closure that captures the inner closure
        let outer_fn = scope.fresh_name();
        let offset_val = emit.random_in(1, 20);
        let op = match emit.gen_range(0..3) {
            0 => format!("{}(y) + {}", inner_fn, offset_val),
            1 => format!("{}(y) * {}", inner_fn, offset_val),
            _ => format!("{}(y + {})", inner_fn, offset_val),
        };

        let outer_closure = format!("let {} = (y: i64) -> i64 => {}", outer_fn, op);
        scope.add_local(
            outer_fn.clone(),
            TypeInfo::Function {
                param_types: vec![TypeInfo::Primitive(PrimitiveType::I64)],
                return_type: Box::new(TypeInfo::Primitive(PrimitiveType::I64)),
            },
            false,
        );

        // Invoke the outer closure
        let result_name = scope.fresh_name();
        let arg_val = emit.random_in(1, 50);
        let call_stmt = format!("let {} = {}({})", result_name, outer_fn, arg_val);
        scope.add_local(result_name, TypeInfo::Primitive(PrimitiveType::I64), false);

        let indent = emit.indent_str();
        Some(format!("{}\n{}{}", outer_closure, indent, call_stmt))
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(NestedClosure.name(), "nested_closure");
    }

    #[test]
    fn returns_none_without_closure_in_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            NestedClosure
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_with_closure_in_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "f".into(),
            TypeInfo::Function {
                param_types: vec![TypeInfo::Primitive(PrimitiveType::I64)],
                return_type: Box::new(TypeInfo::Primitive(PrimitiveType::I64)),
            },
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = NestedClosure.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("f("), "got: {text}");
        assert!(text.contains("let local"), "got: {text}");
    }

    #[test]
    fn adds_two_locals() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "f".into(),
            TypeInfo::Function {
                param_types: vec![TypeInfo::Primitive(PrimitiveType::I64)],
                return_type: Box::new(TypeInfo::Primitive(PrimitiveType::I64)),
            },
            false,
        );
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        NestedClosure.generate(&mut scope, &mut emit, &params);
        // Should add outer closure + result = 2 new locals
        assert_eq!(scope.locals.len(), initial_len + 2);
    }
}
