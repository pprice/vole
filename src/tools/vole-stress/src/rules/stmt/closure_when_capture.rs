//! Rule: closure with `when` expression that captures an outer variable.
//!
//! Generates a closure taking one i64 parameter whose body is a `when`
//! expression with 2-3 arms, at least one of which references a captured
//! variable from the enclosing scope.  The closure is immediately invoked.
//!
//! ```vole
//! let local5 = (p0: i64) -> i64 => when {
//!     p0 > captured_var => p0 * 2
//!     _ => p0 + captured_var
//! }
//! let local6 = local5(some_val)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ClosureWhenCapture;

impl StmtRule for ClosureWhenCapture {
    fn name(&self) -> &'static str {
        "closure_when_capture"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.08)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        !scope.is_in_generic_class_method()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Find an i64 variable in scope to capture.
        let i64_ty = TypeInfo::Primitive(PrimitiveType::I64);
        let candidates: Vec<String> = scope
            .vars_of_type(&i64_ty)
            .into_iter()
            .map(|v| v.name)
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let captured_var = candidates[idx].clone();

        // Decide number of arms: 2 or 3.
        let num_arms = if emit.gen_bool(0.4) { 3 } else { 2 };

        // Build when arms.  The last arm is always `_ => ...`.
        let mut arms = Vec::new();
        let param_name = "p0";

        // First arm: condition referencing the captured variable.
        let cond1 = match emit.gen_range(0..3) {
            0 => format!("{} > {}", param_name, captured_var),
            1 => format!("{} < {}", param_name, captured_var),
            _ => format!("{} == {}", param_name, captured_var),
        };
        let body1 = match emit.gen_range(0..3) {
            0 => format!("{} * 2", param_name),
            1 => format!("{} + {}", param_name, captured_var),
            _ => format!("{} - {}", captured_var, param_name),
        };
        arms.push(format!("{} => {}", cond1, body1));

        // Optional second condition arm (when num_arms == 3).
        if num_arms == 3 {
            let threshold = emit.random_in(1, 10);
            let cond2 = format!("{} > {}", param_name, threshold);
            let offset = emit.random_in(1, 5);
            let body2 = format!("{} + {}", param_name, offset);
            arms.push(format!("{} => {}", cond2, body2));
        }

        // Wildcard arm (always last) -- references captured_var.
        let wildcard_body = match emit.gen_range(0..2) {
            0 => format!("{} + {}", param_name, captured_var),
            _ => captured_var.clone(),
        };
        arms.push(format!("_ => {}", wildcard_body));

        // Build the closure.
        let closure_name = scope.fresh_name();
        let indent = emit.indent_str();
        let inner_indent = format!("{}    ", indent);

        let arms_str: Vec<String> = arms
            .iter()
            .map(|a| format!("{}{}", inner_indent, a))
            .collect();

        let closure_stmt = format!(
            "let {} = ({}: i64) -> i64 => when {{\n{}\n{}}}",
            closure_name,
            param_name,
            arms_str.join("\n"),
            indent,
        );

        scope.add_local(
            closure_name.clone(),
            TypeInfo::Function {
                param_types: vec![TypeInfo::Primitive(PrimitiveType::I64)],
                return_type: Box::new(TypeInfo::Primitive(PrimitiveType::I64)),
            },
            false,
        );

        // Invoke the closure with a simple argument.
        let result_name = scope.fresh_name();
        let arg_val = emit.random_in(1, 50);
        let call_stmt = format!("let {} = {}({})", result_name, closure_name, arg_val);
        scope.add_local(result_name, TypeInfo::Primitive(PrimitiveType::I64), false);

        Some(format!("{}\n{}{}", closure_stmt, indent, call_stmt))
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
        assert_eq!(ClosureWhenCapture.name(), "closure_when_capture");
    }

    #[test]
    fn returns_none_without_i64_in_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "s".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            ClosureWhenCapture
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_with_i64_in_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClosureWhenCapture.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains("when {"),
            "expected when expression, got: {text}"
        );
        assert!(text.contains("_ =>"), "expected wildcard arm, got: {text}");
        assert!(
            text.contains("(p0: i64) -> i64"),
            "expected closure signature, got: {text}"
        );
        assert!(
            text.contains("x"),
            "expected captured variable reference, got: {text}"
        );
    }

    #[test]
    fn adds_two_locals() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("n".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        ClosureWhenCapture.generate(&mut scope, &mut emit, &params);
        // Should add closure + result = 2 new locals.
        assert_eq!(scope.locals.len(), initial_len + 2);
    }

    #[test]
    fn closure_local_is_function_type() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("v".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(99);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        ClosureWhenCapture.generate(&mut scope, &mut emit, &params);

        // First added local should be the closure (Function type).
        let (_, ty, _) = &scope.locals[1];
        assert!(
            matches!(
                ty,
                TypeInfo::Function { param_types, return_type }
                if param_types.len() == 1
                    && matches!(param_types[0], TypeInfo::Primitive(PrimitiveType::I64))
                    && matches!(return_type.as_ref(), TypeInfo::Primitive(PrimitiveType::I64))
            ),
            "expected (i64) -> i64 function type, got: {:?}",
            ty
        );

        // Second added local should be the result (i64).
        let (_, ty2, _) = &scope.locals[2];
        assert_eq!(*ty2, TypeInfo::Primitive(PrimitiveType::I64));
    }
}
