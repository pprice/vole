//! Rule: binary arithmetic expression.
//!
//! Generates binary arithmetic (`+`, `-`, `*`, `%`) for numeric primitives.
//! For integer types, 25% chance to delegate to a bitwise operation instead.
//! Modulo uses a safe non-zero RHS to avoid division-by-zero.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct BinaryArith;

impl ExprRule for BinaryArith {
    fn name(&self) -> &'static str {
        "binary_arith"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.35)]
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
        let prim = match expected_type {
            TypeInfo::Primitive(
                p @ (PrimitiveType::I32 | PrimitiveType::I64 | PrimitiveType::F64),
            ) => *p,
            _ => return None,
        };

        // For integer types, 25% chance to generate a bitwise op
        if matches!(prim, PrimitiveType::I32 | PrimitiveType::I64) && emit.gen_bool(0.25) {
            return Some(gen_bitwise(scope, emit, prim));
        }

        let ty = TypeInfo::Primitive(prim);
        let left = emit.sub_expr(&ty, scope);
        let right = emit.sub_expr(&ty, scope);

        // ~20% chance to generate modulo with a safe non-zero RHS
        if emit.gen_bool(0.20) {
            let rhs = emit.nonzero_literal(prim);
            return Some(format!("({} % {})", left, rhs));
        }

        let op = match emit.gen_range(0..4_usize) {
            0 => "+",
            1 => "-",
            2 => "*",
            _ => "+",
        };

        Some(format!("({} {} {})", left, op, right))
    }
}

/// Generate a binary bitwise expression (integer types only).
///
/// Produces `&`, `|`, `^`, `<<`, or `>>`. For shift operators the RHS
/// is constrained to a small literal to avoid undefined behaviour.
fn gen_bitwise(scope: &Scope, emit: &mut Emit, prim: PrimitiveType) -> String {
    let ty = TypeInfo::Primitive(prim);
    let left = emit.sub_expr(&ty, scope);

    let op = match emit.gen_range(0..5_usize) {
        0 => "&",
        1 => "|",
        2 => "^",
        3 => "<<",
        _ => ">>",
    };

    let right = if op == "<<" || op == ">>" {
        let max_shift: i64 = match prim {
            PrimitiveType::I32 => 15,
            PrimitiveType::I64 => 31,
            _ => unreachable!(),
        };
        let shift_amount = emit.gen_i64_range(0, max_shift);
        let suffix = match prim {
            PrimitiveType::I32 => "_i32",
            PrimitiveType::I64 => "_i64",
            _ => unreachable!(),
        };
        format!("{}{}", shift_amount, suffix)
    } else {
        emit.sub_expr(&ty, scope)
    };

    format!("({} {} {})", left, op, right)
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
    fn name_is_correct() {
        assert_eq!(BinaryArith.name(), "binary_arith");
    }

    #[test]
    fn returns_none_for_non_numeric() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = BinaryArith.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::String),
        );
        assert!(result.is_none());
    }

    #[test]
    fn generates_arith_for_i64() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = BinaryArith.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with('(') && text.ends_with(')'), "got: {text}");
    }
}
