//! Statement rule registration.
//!
//! Each statement rule struct is listed in [`all`] -- the single source of
//! truth for which statement rules exist.  Adding a new rule means creating
//! its implementation file and adding one line here.

mod checked_arithmetic;
mod closure_capture;
mod closure_concat;
mod field_closure;
mod generic_closure_chain;
mod i32_boundary;
mod interpolation_concat;
mod match_array;
mod match_array_length;
mod match_closure;
mod match_computation;
mod match_iter;
mod match_let;
mod match_method;
mod match_method_result;
mod match_optional;
mod match_sorted;
mod match_string_length;
mod modulo_edge;
mod nested_closure;
mod range_tostring;
mod range_when_accum;
mod sentinel_closure;
mod string_build_match;
mod string_char_at;
mod string_split;
mod while_string_build;
mod wildcard_match;

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
        // -- Closure rules ------------------------------------------------------
        Box::new(closure_concat::ClosureConcat),
        Box::new(closure_capture::ClosureCapture),
        Box::new(nested_closure::NestedClosure),
        Box::new(sentinel_closure::SentinelClosure),
        Box::new(field_closure::FieldClosure),
        Box::new(generic_closure_chain::GenericClosureChain),
        // -- Match rules --------------------------------------------------------
        Box::new(match_let::MatchLet),
        Box::new(match_method::MatchMethod),
        Box::new(wildcard_match::WildcardMatch),
        Box::new(match_array::MatchArray),
        Box::new(match_array_length::MatchArrayLength),
        Box::new(match_string_length::MatchStringLength),
        Box::new(match_computation::MatchComputation),
        Box::new(match_closure::MatchClosure),
        Box::new(match_optional::MatchOptional),
        Box::new(match_sorted::MatchSorted),
        Box::new(match_iter::MatchIter),
        Box::new(match_method_result::MatchMethodResult),
    ]
}
