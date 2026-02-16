//! Rule: checked/wrapping/saturating arithmetic via `std:lowlevel` intrinsics.
//!
//! Picks two numeric values of the same type and applies a random operation:
//! - `wrapping_add/sub/mul`: returns `T` (wraps on overflow)
//! - `saturating_add/sub/mul`: returns `T` (clamps on overflow)
//! - `checked_add/sub/mul/div`: returns `T?` (nil on overflow), unwrapped with `??`
//!
//! Requires `scope.has_lowlevel_import` to be true.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct CheckedArithmetic;

impl StmtRule for CheckedArithmetic {
    fn name(&self) -> &'static str {
        "checked_arithmetic"
    }

    fn params(&self) -> Vec<Param> {
        // Default 0.0 -- only fires when a profile enables it (requires lowlevel import).
        vec![Param::prob("probability", 0.0)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.has_lowlevel_import
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Pick a random integer type to work with
        let int_types = [
            PrimitiveType::I32,
            PrimitiveType::I64,
            PrimitiveType::I8,
            PrimitiveType::I16,
        ];
        let prim_type = int_types[emit.gen_range(0..int_types.len())];
        let type_info = TypeInfo::Primitive(prim_type);
        let type_suffix = match prim_type {
            PrimitiveType::I8 => "_i8",
            PrimitiveType::I16 => "_i16",
            PrimitiveType::I32 => "_i32",
            _ => "_i64",
        };

        // Find existing locals/params of the matching type
        let operand_names: Vec<String> = scope
            .vars_of_type(&type_info)
            .into_iter()
            .map(|v| v.name)
            .collect();

        // Generate operand expressions: use existing vars or fresh literals
        let (a_expr, b_expr) = make_operands(&operand_names, type_suffix, emit);

        // Pick operation category: 40% wrapping, 30% saturating, 30% checked
        let category = emit.gen_range(0..10);
        let (func_name, is_checked) = pick_operation(category, emit);

        let name = scope.fresh_name();
        scope.add_local(name.clone(), type_info, false);

        if is_checked {
            let default_val = format!("0{}", type_suffix);
            Some(format!(
                "let {} = {}({}, {}) ?? {}",
                name, func_name, a_expr, b_expr, default_val
            ))
        } else {
            Some(format!(
                "let {} = {}({}, {})",
                name, func_name, a_expr, b_expr
            ))
        }
    }
}

/// Build operand expressions from scope variables or fresh literals.
fn make_operands(operand_names: &[String], type_suffix: &str, emit: &mut Emit) -> (String, String) {
    if operand_names.len() >= 2 {
        let idx_a = emit.gen_range(0..operand_names.len());
        let mut idx_b = emit.gen_range(0..operand_names.len());
        // Allow same var for both operands (wrapping_add(x, x) is valid)
        if operand_names.len() > 2 {
            while idx_b == idx_a {
                idx_b = emit.gen_range(0..operand_names.len());
            }
        }
        (operand_names[idx_a].clone(), operand_names[idx_b].clone())
    } else if operand_names.len() == 1 {
        let lit = emit.random_in(1, 50);
        (operand_names[0].clone(), format!("{}{}", lit, type_suffix))
    } else {
        // Generate two fresh literals. Use absolute value for `a` range boundaries
        // to keep things simple with unsigned formatting.
        let a_val = emit.random_in(0, 50);
        let b_val = emit.random_in(1, 50);
        // Randomly negate `a` ~50% of the time for variety.
        let a_str = if emit.gen_bool(0.5) {
            format!("-{}{}", a_val, type_suffix)
        } else {
            format!("{}{}", a_val, type_suffix)
        };
        (a_str, format!("{}{}", b_val, type_suffix))
    }
}

/// Pick an operation name and whether it is a checked variant.
fn pick_operation(category: usize, emit: &mut Emit) -> (&'static str, bool) {
    if category < 4 {
        let ops = ["wrapping_add", "wrapping_sub", "wrapping_mul"];
        (ops[emit.gen_range(0..ops.len())], false)
    } else if category < 7 {
        let ops = ["saturating_add", "saturating_sub", "saturating_mul"];
        (ops[emit.gen_range(0..ops.len())], false)
    } else {
        let ops = ["checked_add", "checked_sub", "checked_mul", "checked_div"];
        (ops[emit.gen_range(0..ops.len())], true)
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
    fn precondition_requires_lowlevel() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!CheckedArithmetic.precondition(&scope, &params));
    }

    #[test]
    fn precondition_passes_with_lowlevel() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.has_lowlevel_import = true;
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(CheckedArithmetic.precondition(&scope, &params));
    }

    #[test]
    fn generates_arithmetic_call() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.has_lowlevel_import = true;
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = CheckedArithmetic.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let local0 = "));
        // Should contain one of the arithmetic function names
        let has_arith =
            text.contains("wrapping_") || text.contains("saturating_") || text.contains("checked_");
        assert!(has_arith, "got: {text}");
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(CheckedArithmetic.name(), "checked_arithmetic");
    }
}
