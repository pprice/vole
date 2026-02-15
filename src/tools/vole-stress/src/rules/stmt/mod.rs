//! Statement rule registration.
//!
//! Each statement rule struct is listed in [`all`] -- the single source of
//! truth for which statement rules exist.  Adding a new rule means creating
//! its implementation file and adding one line here.

mod checked_arithmetic;
mod i32_boundary;
mod interpolation_concat;
mod modulo_edge;
mod range_tostring;
mod range_when_accum;
mod string_build_match;
mod string_char_at;
mod string_split;
mod while_string_build;

use crate::rule::StmtRule;

/// Return every registered statement rule.
///
/// Rules are listed explicitly (no inventory magic) so that the set of active
/// rules is visible at a glance.
pub fn all() -> Vec<Box<dyn StmtRule>> {
    vec![
        // -- String rules -------------------------------------------------------
        Box::new(string_char_at::StringCharAt),
        Box::new(string_split::StringSplitLet),
        Box::new(string_split::StringSplitFor),
        Box::new(interpolation_concat::InterpolationConcat),
        Box::new(range_tostring::RangeTostring),
        Box::new(range_when_accum::RangeWhenAccum),
        Box::new(string_build_match::StringBuildMatch),
        Box::new(while_string_build::WhileStringBuild),
        // -- Arithmetic rules ---------------------------------------------------
        Box::new(checked_arithmetic::CheckedArithmetic),
        Box::new(modulo_edge::ModuloEdge),
        Box::new(i32_boundary::I32Boundary),
    ]
}
