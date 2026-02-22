// src/sema/analyzer/expr/mod.rs

mod access;
mod array;
mod as_cast;
mod assign;
mod binary;
mod call;
mod control_flow;
mod expect;
mod identifier;
mod index;
mod infer;
mod is_expr;
mod match_expr;
mod meta_access;
mod null_coalesce;
mod struct_literal;
mod unary;
mod yield_expr;

/// Context passed through expression checking to control behavior
/// without mutable state on the Analyzer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) enum ExprContext {
    #[default]
    Standard,
    /// Inside a when/match arm body — trailing block expressions are allowed.
    ArmBody,
}
