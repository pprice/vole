//! Expression rule registration.
//!
//! Each expression rule struct is listed in [`all`] -- the single source of
//! truth for which expression rules exist.  Adding a new rule means creating
//! its implementation file and adding one line here.

mod array_index;
mod array_length;
mod binary_arith;
mod bool_ops;
mod class_construction;
mod comparison;
mod field_access;
mod fixed_array_index;
mod if_expr;
mod interface_value;
mod is_expr;
mod iter_any_all;
mod iter_chain_collect;
mod iter_collect;
mod iter_count;
mod iter_filter_collect;
mod iter_first_last_nth;
mod iter_flat_map_collect;
mod iter_map_collect;
mod iter_reduce;
mod iter_sum;
mod lambda_expr;
mod match_expr;
mod method_interpolation;
mod null_coalesce;
mod optional_chaining;
mod string_bool;
mod string_chars;
mod string_concat;
mod string_length;
mod string_split;
mod string_transform;
mod to_string;
mod tuple_index;
mod type_param_method;
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
        // -- batch 2: null coalesce, match, iterators -------------------------
        Box::new(null_coalesce::NullCoalesce),
        Box::new(match_expr::MatchExpr),
        Box::new(method_interpolation::MethodInterpolation),
        Box::new(string_split::StringSplit),
        Box::new(string_chars::StringChars),
        Box::new(iter_count::IterCount),
        Box::new(iter_sum::IterSum),
        Box::new(iter_reduce::IterReduce),
        Box::new(iter_any_all::IterAnyAll),
        // -- batch 3: field access, construction, lambda, iterators -----------
        Box::new(field_access::FieldAccess),
        Box::new(class_construction::ClassConstruction),
        Box::new(interface_value::InterfaceValue),
        Box::new(lambda_expr::LambdaExpr),
        Box::new(iter_collect::IterCollect),
        // -- batch 4: fixed array, tuple, optional chain, type params, more iterators
        Box::new(fixed_array_index::FixedArrayIndex),
        Box::new(tuple_index::TupleIndex),
        Box::new(optional_chaining::OptionalChaining),
        Box::new(type_param_method::TypeParamMethod),
        Box::new(iter_map_collect::IterMapCollect),
        Box::new(iter_filter_collect::IterFilterCollect),
        Box::new(iter_chain_collect::IterChainCollect),
        Box::new(iter_flat_map_collect::IterFlatMapCollect),
        Box::new(iter_first_last_nth::IterFirstLastNth),
    ]
}
