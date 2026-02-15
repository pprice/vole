//! Statement rule registration.
//!
//! Each statement rule struct is listed in [`all`] -- the single source of
//! truth for which statement rules exist.  Adding a new rule means creating
//! its implementation file and adding one line here.

mod array_compound_assign;
mod array_from_vars;
mod array_index_assign;
mod array_length_guard;
mod array_length_zero_check;
mod array_push;
mod array_uniform_ops;
mod assert_stmt;
mod bool_chain;
mod bool_chain_edge;
mod bool_match_let;
mod bool_negation;
mod break_continue;
mod chained_literal_method;
mod chained_string_methods;
mod checked_arithmetic;
mod closure_capture;
mod closure_concat;
mod closure_result_concat;
mod comparison_chain;
mod compound_assignment;
mod compound_bool;
mod dead_code;
mod early_return;
mod edge_case_for_loop;
mod edge_case_split;
mod empty_array_iter;
mod empty_iter_edge;
mod empty_range;
mod empty_string_concat;
mod empty_string_iter_let;
mod empty_string_ops;
mod f64_comparison_edge;
mod f64_literal_ops;
mod field_closure;
mod filter_iter_tostring;
mod fn_param_call;
mod for_each_stmt;
mod for_in_match_accum;
mod for_interpolation_concat;
mod for_iter_when_string_body;
mod for_length_indexed;
mod for_push_collect;
mod for_range_tostring_build;
mod for_range_when_accum;
mod for_reduce_pattern;
mod for_when_accumulate;
mod generic_closure_chain;
mod i32_boundary;
mod identity_arithmetic;
mod interpolation_concat;
mod interpolation_expr;
mod interpolation_with_iter;
mod iter_chunks_windows;
mod iter_in_when_arms;
mod iter_map_filter_let;
mod iter_predicate_let;
mod iter_reduce_let;
mod iter_take_skip_collect;
mod iter_terminal_chain;
mod iter_while_accum;
mod last_elem_access;
mod length_comparison;
mod literal_method;
mod manual_minmax;
mod map_tostring_reduce;
mod match_array;
mod match_array_elem;
mod match_array_length;
mod match_closure;
mod match_computation;
mod match_interpolation_length;
mod match_iter;
mod match_iter_terminal;
mod match_let;
mod match_method;
mod match_method_result;
mod match_on_method;
mod match_optional;
mod match_sorted;
mod match_sorted_length;
mod match_string_length;
mod match_to_string_arms;
mod match_tostring_arms;
mod match_when_arm;
mod modulo_edge;
mod multi_arm_when;
mod multi_push;
mod nested_closure;
mod nested_match;
mod nested_tostring;
mod nested_when;
mod nested_when_let;
mod nested_when_string;
mod nth_let;
mod numeric_to_string;
mod power_of_two_div;
mod range_check;
mod range_iter_map_collect;
mod range_tostring;
mod range_when_accum;
mod reassign_from_when;
mod reassignment;
mod reiterate_let;
mod repeat_literal;
mod repeated_string_ops;
mod reverse_collect;
mod sentinel_closure;
mod single_char_string_ops;
mod single_elem_array_ops;
mod single_elem_range;
mod sorted_collect;
mod sorted_iter_accum;
mod split_for_loop;
mod string_build_match;
mod string_char_at;
mod string_concat;
mod string_equality;
mod string_iter_let;
mod string_length_edge;
mod string_predicate;
mod string_replace;
mod string_split;
mod substring_let;
mod tautological_when;
mod to_string_let;
mod tostring_length;
mod variable_shadow;
mod when_concat_arms;
mod when_f64_cond;
mod when_iter_predicate;
mod when_length_compare;
mod when_match_combo;
mod when_replace_result;
mod when_result_method;
mod when_string_method_conds;
mod when_tostring_arms;
mod when_with_contains;
mod while_false;
mod while_string_build;
mod whitespace_string_ops;
mod widening_let;
mod wildcard_match;
mod zero_division_guard;

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
        // -- Let-binding rules --------------------------------------------------
        Box::new(dead_code::DeadCodeAssert),
        Box::new(while_false::WhileFalse),
        Box::new(power_of_two_div::PowerOfTwoDiv),
        Box::new(string_predicate::StringPredicate),
        Box::new(identity_arithmetic::IdentityArithmetic),
        Box::new(string_equality::StringEquality),
        Box::new(string_concat::StringConcat),
        Box::new(to_string_let::ToStringLet),
        Box::new(literal_method::LiteralMethod),
        Box::new(array_from_vars::ArrayFromVars),
        Box::new(compound_bool::CompoundBool),
        Box::new(length_comparison::LengthComparison),
        Box::new(string_replace::StringReplace),
        Box::new(nested_match::NestedMatch),
        Box::new(string_length_edge::StringLengthEdge),
        Box::new(range_check::RangeCheck),
        Box::new(assert_stmt::AssertStmt),
        Box::new(edge_case_for_loop::EdgeCaseForLoop),
        Box::new(empty_array_iter::EmptyArrayIter),
        Box::new(edge_case_split::EdgeCaseSplit),
        Box::new(bool_negation::BoolNegation),
        Box::new(chained_literal_method::ChainedLiteralMethod),
        Box::new(empty_string_concat::EmptyStringConcat),
        Box::new(tautological_when::TautologicalWhen),
        Box::new(single_elem_array_ops::SingleElemArrayOps),
        Box::new(array_uniform_ops::ArrayUniformOps),
        Box::new(empty_string_ops::EmptyStringOps),
        Box::new(repeat_literal::RepeatLiteral),
        Box::new(nested_when::NestedWhen),
        Box::new(multi_push::MultiPush),
        Box::new(variable_shadow::VariableShadow),
        Box::new(iter_terminal_chain::IterTerminalChain),
        Box::new(when_string_method_conds::WhenStringMethodConds),
        Box::new(last_elem_access::LastElemAccess),
        Box::new(interpolation_with_iter::InterpolationWithIter),
        Box::new(reassign_from_when::ReassignFromWhen),
        Box::new(when_with_contains::WhenWithContains),
        Box::new(zero_division_guard::ZeroDivisionGuard),
        Box::new(single_char_string_ops::SingleCharStringOps),
        Box::new(f64_literal_ops::F64LiteralOps),
        Box::new(f64_comparison_edge::F64ComparisonEdge),
        Box::new(repeated_string_ops::RepeatedStringOps),
        Box::new(bool_chain_edge::BoolChainEdge),
        Box::new(whitespace_string_ops::WhitespaceStringOps),
        Box::new(manual_minmax::ManualMinmax),
        Box::new(tostring_length::TostringLength),
        Box::new(bool_chain::BoolChain),
        Box::new(comparison_chain::ComparisonChain),
        Box::new(multi_arm_when::MultiArmWhen),
        Box::new(substring_let::SubstringLet),
        Box::new(when_concat_arms::WhenConcatArms),
        Box::new(when_result_method::WhenResultMethod),
        Box::new(nested_when_string::NestedWhenString),
        Box::new(numeric_to_string::NumericToString),
        Box::new(match_to_string_arms::MatchToStringArms),
        Box::new(for_interpolation_concat::ForInterpolationConcat),
        Box::new(when_tostring_arms::WhenTostringArms),
        Box::new(single_elem_range::SingleElemRange),
        Box::new(empty_range::EmptyRange),
        Box::new(when_replace_result::WhenReplaceResult),
        Box::new(match_tostring_arms::MatchTostringArms),
        Box::new(nested_tostring::NestedTostring),
        Box::new(when_f64_cond::WhenF64Cond),
        Box::new(for_range_tostring_build::ForRangeTostringBuild),
        Box::new(for_range_when_accum::ForRangeWhenAccum),
        Box::new(range_iter_map_collect::RangeIterMapCollect),
        Box::new(interpolation_expr::InterpolationExpr),
        Box::new(when_match_combo::WhenMatchCombo),
        Box::new(match_when_arm::MatchWhenArm),
        Box::new(match_interpolation_length::MatchInterpolationLength),
        Box::new(when_length_compare::WhenLengthCompare),
        Box::new(split_for_loop::SplitForLoop),
        Box::new(closure_result_concat::ClosureResultConcat),
        // -- Array-dependent rules (batch 8) ------------------------------------
        Box::new(map_tostring_reduce::MapTostringReduce),
        Box::new(when_iter_predicate::WhenIterPredicate),
        Box::new(iter_in_when_arms::IterInWhenArms),
        Box::new(sorted_collect::SortedCollect),
        Box::new(reverse_collect::ReverseCollect),
        Box::new(iter_take_skip_collect::IterTakeSkipCollect),
        Box::new(array_length_guard::ArrayLengthGuard),
        Box::new(array_length_zero_check::ArrayLengthZeroCheck),
        Box::new(match_sorted_length::MatchSortedLength),
        Box::new(for_when_accumulate::ForWhenAccumulate),
        Box::new(for_iter_when_string_body::ForIterWhenStringBody),
        // -- Complex array loop rules (batch 9) ---------------------------------
        Box::new(iter_while_accum::IterWhileAccum),
        Box::new(for_in_match_accum::ForInMatchAccum),
        Box::new(for_push_collect::ForPushCollect),
        Box::new(for_length_indexed::ForLengthIndexed),
        Box::new(iter_reduce_let::IterReduceLet),
        Box::new(for_reduce_pattern::ForReducePattern),
        Box::new(sorted_iter_accum::SortedIterAccum),
        Box::new(filter_iter_tostring::FilterIterTostring),
        Box::new(widening_let::WideningLet),
        Box::new(empty_string_iter_let::EmptyStringIterLet),
        // -- Additional let_bindings rules (batch 10) ---------------------------
        Box::new(match_on_method::MatchOnMethod),
        Box::new(empty_iter_edge::EmptyIterEdge),
        Box::new(chained_string_methods::ChainedStringMethods),
        // -- Iterator rules from iterators.rs (batch 11) --------------------------
        Box::new(iter_predicate_let::IterPredicateLet),
        Box::new(iter_chunks_windows::IterChunksWindows),
        Box::new(for_each_stmt::ForEachStmt),
        Box::new(nth_let::NthLet),
        Box::new(string_iter_let::StringIterLet),
        Box::new(reiterate_let::ReiterateLet),
        Box::new(iter_map_filter_let::IterMapFilterLet),
        // -- Mutation rules from stmt/mod.rs (batch 12) ---------------------------
        Box::new(compound_assignment::CompoundAssignment),
        Box::new(reassignment::Reassignment),
        Box::new(array_push::ArrayPush),
        Box::new(array_index_assign::ArrayIndexAssign),
        Box::new(array_compound_assign::ArrayCompoundAssign),
        // -- Control flow & call rules (batch 13) ---------------------------------
        Box::new(early_return::EarlyReturn),
        Box::new(break_continue::BreakContinue),
        Box::new(fn_param_call::FnParamCall),
        Box::new(bool_match_let::BoolMatchLet),
        // -- Match/when expression rules (batch 14) --------------------------------
        Box::new(match_iter_terminal::MatchIterTerminal),
        Box::new(match_array_elem::MatchArrayElem),
        Box::new(nested_when_let::NestedWhenLet),
    ]
}
