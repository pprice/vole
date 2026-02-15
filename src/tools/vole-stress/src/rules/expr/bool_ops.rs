//! Rule: boolean operation expressions.
//!
//! Generates boolean binary (`&&`, `||`), negated compound, and compound
//! boolean expressions. Only produces `bool` type.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

// ---------------------------------------------------------------------------
// BinaryBool: (a && b) or (a || b)
// ---------------------------------------------------------------------------

pub struct BinaryBool;

impl ExprRule for BinaryBool {
    fn name(&self) -> &'static str {
        "binary_bool"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.15)]
    }

    fn precondition(&self, _scope: &Scope, _params: &Params) -> bool {
        true
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        if !matches!(expected_type, TypeInfo::Primitive(PrimitiveType::Bool)) {
            return None;
        }

        let bool_ty = TypeInfo::Primitive(PrimitiveType::Bool);
        let left = emit.sub_expr(&bool_ty, scope);
        let right = emit.sub_expr(&bool_ty, scope);
        let op = if emit.gen_bool(0.5) { "&&" } else { "||" };

        Some(format!("({} {} {})", left, op, right))
    }
}

// ---------------------------------------------------------------------------
// NegatedCompoundBool: !(a > b) or !(a && b)
// ---------------------------------------------------------------------------

pub struct NegatedCompoundBool;

impl ExprRule for NegatedCompoundBool {
    fn name(&self) -> &'static str {
        "negated_compound_bool"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.08)]
    }

    fn precondition(&self, _scope: &Scope, _params: &Params) -> bool {
        true
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        if !matches!(expected_type, TypeInfo::Primitive(PrimitiveType::Bool)) {
            return None;
        }

        let bool_ty = TypeInfo::Primitive(PrimitiveType::Bool);
        let inner = emit.sub_expr(&bool_ty, scope);

        Some(format!("(!{})", inner))
    }
}

// ---------------------------------------------------------------------------
// CompoundBool: (a > 0 && b < 10) || c
// ---------------------------------------------------------------------------

pub struct CompoundBool;

impl ExprRule for CompoundBool {
    fn name(&self) -> &'static str {
        "compound_bool"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.08)]
    }

    fn precondition(&self, _scope: &Scope, _params: &Params) -> bool {
        true
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        if !matches!(expected_type, TypeInfo::Primitive(PrimitiveType::Bool)) {
            return None;
        }

        let top_op = if emit.gen_bool(0.5) { "||" } else { "&&" };
        let inner_op = if top_op == "||" { "&&" } else { "||" };

        let group_count = emit.random_in(2, 3);
        let bool_ty = TypeInfo::Primitive(PrimitiveType::Bool);

        let groups: Vec<String> = (0..group_count)
            .map(|_| {
                if emit.gen_bool(0.65) {
                    let a = emit.sub_expr(&bool_ty, scope);
                    let b = emit.sub_expr(&bool_ty, scope);
                    format!("({} {} {})", a, inner_op, b)
                } else {
                    emit.sub_expr(&bool_ty, scope)
                }
            })
            .collect();

        Some(format!("({})", groups.join(&format!(" {} ", top_op))))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ParamValue, StmtRule};
    use crate::symbols::SymbolTable;
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn names_are_correct() {
        assert_eq!(BinaryBool.name(), "binary_bool");
        assert_eq!(NegatedCompoundBool.name(), "negated_compound_bool");
        assert_eq!(CompoundBool.name(), "compound_bool");
    }

    #[test]
    fn returns_none_for_non_bool() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let i64_ty = TypeInfo::Primitive(PrimitiveType::I64);
        assert!(
            BinaryBool
                .generate(&scope, &mut emit, &params, &i64_ty)
                .is_none()
        );
        assert!(
            NegatedCompoundBool
                .generate(&scope, &mut emit, &params, &i64_ty)
                .is_none()
        );
        assert!(
            CompoundBool
                .generate(&scope, &mut emit, &params, &i64_ty)
                .is_none()
        );
    }

    #[test]
    fn generates_binary_bool() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let bool_ty = TypeInfo::Primitive(PrimitiveType::Bool);
        let result = BinaryBool.generate(&scope, &mut emit, &params, &bool_ty);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains("&&") || text.contains("||"),
            "expected bool op, got: {text}"
        );
    }

    #[test]
    fn generates_negated_compound_bool() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let bool_ty = TypeInfo::Primitive(PrimitiveType::Bool);
        let result = NegatedCompoundBool.generate(&scope, &mut emit, &params, &bool_ty);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains('!'), "expected negation, got: {text}");
    }
}
