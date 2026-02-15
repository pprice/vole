//! Arithmetic-related statement generators.
//!
//! Contains generators for checked/wrapping/saturating arithmetic operations.

use rand::Rng;

use crate::symbols::{PrimitiveType, TypeInfo};

use super::{StmtContext, StmtGenerator};

impl<'a, R: Rng> StmtGenerator<'a, R> {
    /// Generate a checked/wrapping/saturating arithmetic call using `std:lowlevel` intrinsics.
    ///
    /// Picks two numeric values of the same type and applies a random operation:
    /// - wrapping_add/sub/mul: returns T (wraps on overflow)
    /// - saturating_add/sub/mul: returns T (clamps on overflow)
    /// - checked_add/sub/mul/div: returns T? (nil on overflow), unwrapped with ??
    ///
    /// Requires `ctx.has_lowlevel_import` to be true.
    pub(super) fn generate_checked_arithmetic_let(&mut self, ctx: &mut StmtContext) -> String {
        // Pick a random integer type to work with
        let int_types = [
            PrimitiveType::I32,
            PrimitiveType::I64,
            PrimitiveType::I8,
            PrimitiveType::I16,
        ];
        let prim_type = int_types[self.rng.gen_range(0..int_types.len())];
        let type_info = TypeInfo::Primitive(prim_type);
        let type_suffix = match prim_type {
            PrimitiveType::I8 => "_i8",
            PrimitiveType::I16 => "_i16",
            PrimitiveType::I32 => "_i32",
            PrimitiveType::I64 => "_i64",
            _ => "_i64",
        };

        // Find existing locals/params of the matching type
        let mut operand_names: Vec<String> = Vec::new();
        for (name, ty, _) in &ctx.locals {
            if *ty == type_info {
                operand_names.push(name.clone());
            }
        }
        for param in ctx.params {
            if param.param_type == type_info {
                operand_names.push(param.name.clone());
            }
        }

        // Generate operand expressions: use existing vars or fresh literals
        let (a_expr, b_expr) = if operand_names.len() >= 2 {
            let idx_a = self.rng.gen_range(0..operand_names.len());
            let mut idx_b = self.rng.gen_range(0..operand_names.len());
            // Allow same var for both operands (wrapping_add(x, x) is valid)
            if operand_names.len() > 2 {
                while idx_b == idx_a {
                    idx_b = self.rng.gen_range(0..operand_names.len());
                }
            }
            (operand_names[idx_a].clone(), operand_names[idx_b].clone())
        } else if operand_names.len() == 1 {
            // Use the one var + a literal
            let lit = self.rng.gen_range(1..=50);
            (operand_names[0].clone(), format!("{}{}", lit, type_suffix))
        } else {
            // Generate two fresh literals
            let a = self.rng.gen_range(-50..=50);
            let b = self.rng.gen_range(1..=50);
            (
                format!("{}{}", a, type_suffix),
                format!("{}{}", b, type_suffix),
            )
        };

        // Pick operation category: 40% wrapping, 30% saturating, 30% checked
        let category = self.rng.gen_range(0..10);
        let (func_name, is_checked) = if category < 4 {
            // Wrapping
            let ops = ["wrapping_add", "wrapping_sub", "wrapping_mul"];
            (ops[self.rng.gen_range(0..ops.len())], false)
        } else if category < 7 {
            // Saturating
            let ops = ["saturating_add", "saturating_sub", "saturating_mul"];
            (ops[self.rng.gen_range(0..ops.len())], false)
        } else {
            // Checked (returns T?)
            let ops = ["checked_add", "checked_sub", "checked_mul", "checked_div"];
            (ops[self.rng.gen_range(0..ops.len())], true)
        };

        let name = ctx.new_local_name();

        if is_checked {
            // checked_* returns T?, use ?? to unwrap
            let default_val = format!("0{}", type_suffix);
            ctx.add_local(name.clone(), type_info, false);
            format!(
                "let {} = {}({}, {}) ?? {}",
                name, func_name, a_expr, b_expr, default_val
            )
        } else {
            // wrapping_*/saturating_* returns T directly
            ctx.add_local(name.clone(), type_info, false);
            format!("let {} = {}({}, {})", name, func_name, a_expr, b_expr)
        }
    }
}
