//! Rule: compound assignment statement (+=, -=, *=, %=).
//!
//! Picks a random mutable numeric local, a random compound operator,
//! and generates a simple numeric literal RHS of the same type.
//! Avoids /= to prevent division by zero; uses non-zero literal for %=.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct CompoundAssignment;

impl StmtRule for CompoundAssignment {
    fn name(&self) -> &'static str {
        "compound_assignment"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.10)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        has_mutable_numeric_locals(scope)
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let candidates: Vec<(String, PrimitiveType)> = scope
            .locals
            .iter()
            .filter_map(|(name, ty, is_mut)| {
                if !is_mut || scope.protected_vars.contains(name) {
                    return None;
                }
                if let TypeInfo::Primitive(p) = ty {
                    if matches!(
                        p,
                        PrimitiveType::I8
                            | PrimitiveType::I16
                            | PrimitiveType::I32
                            | PrimitiveType::I64
                            | PrimitiveType::I128
                            | PrimitiveType::U8
                            | PrimitiveType::U16
                            | PrimitiveType::U32
                            | PrimitiveType::U64
                            | PrimitiveType::F32
                            | PrimitiveType::F64
                    ) {
                        return Some((name.clone(), *p));
                    }
                }
                None
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, prim) = &candidates[idx];
        let prim = *prim;

        let op = match emit.gen_range(0..4) {
            0 => "+=",
            1 => "-=",
            2 => "*=",
            _ => "%=",
        };

        let rhs = if op == "%=" {
            emit.nonzero_literal(prim)
        } else {
            emit.literal(&TypeInfo::Primitive(prim))
        };

        Some(format!("{} {} {}", var_name, op, rhs))
    }
}

fn has_mutable_numeric_locals(scope: &Scope) -> bool {
    scope.locals.iter().any(|(name, ty, is_mut)| {
        *is_mut
            && !scope.protected_vars.contains(name)
            && matches!(ty, TypeInfo::Primitive(p) if matches!(
                p,
                PrimitiveType::I8
                    | PrimitiveType::I16
                    | PrimitiveType::I32
                    | PrimitiveType::I64
                    | PrimitiveType::I128
                    | PrimitiveType::U8
                    | PrimitiveType::U16
                    | PrimitiveType::U32
                    | PrimitiveType::U64
                    | PrimitiveType::F32
                    | PrimitiveType::F64
            ))
    })
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
        assert_eq!(CompoundAssignment.name(), "compound_assignment");
    }

    #[test]
    fn generates_compound_assignment() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), true);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = CompoundAssignment.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("x "), "got: {text}");
        assert!(
            text.contains("+=")
                || text.contains("-=")
                || text.contains("*=")
                || text.contains("%="),
            "got: {text}"
        );
    }

    #[test]
    fn returns_none_without_mutable_locals() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        // Immutable local
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            CompoundAssignment
                .generate(&mut scope, &mut emit, &rule_params)
                .is_none()
        );
    }
}
