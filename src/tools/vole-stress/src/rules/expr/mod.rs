//! Expression rule registration.
//!
//! Each expression rule struct is listed in [`all`] -- the single source of
//! truth for which expression rules exist.  Adding a new rule means creating
//! its implementation file and adding one line here.

mod array_index;
mod array_length;
mod binary_arith;
mod bool_ops;
mod comparison;
mod if_expr;
mod is_expr;
mod string_bool;
mod string_concat;
mod string_length;
mod string_transform;
mod to_string;
mod when_expr;

use crate::rule::ExprRule;

/// Return every registered expression rule.
///
/// Rules are listed explicitly (no inventory magic) so that the set of active
/// rules is visible at a glance.
pub fn all() -> Vec<Box<dyn ExprRule>> {
    vec![
        // -- batch 1: arithmetic, comparison, boolean --------------------------
        Box::new(binary_arith::BinaryArith),
        Box::new(comparison::Comparison),
        Box::new(bool_ops::BinaryBool),
        Box::new(bool_ops::NegatedCompoundBool),
        Box::new(bool_ops::CompoundBool),
        // -- batch 1: control flow expressions ---------------------------------
        Box::new(if_expr::IfExpr),
        Box::new(when_expr::WhenExpr),
        // -- batch 1: array/string methods ------------------------------------
        Box::new(array_index::ArrayIndex),
        Box::new(array_length::ArrayLength),
        Box::new(string_length::StringLength),
        Box::new(string_bool::StringBool),
        Box::new(string_transform::StringTransform),
        Box::new(string_concat::StringConcat),
        Box::new(to_string::ToString),
        Box::new(is_expr::IsExpr),
    ]
}
