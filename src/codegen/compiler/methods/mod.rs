// src/codegen/compiler/methods/mod.rs
//
// Method call and try/error propagation codegen.

mod builtin;
mod call;
mod external;
mod iterators;
mod try_expr;

pub(crate) use call::compile_method_call;
pub(crate) use try_expr::compile_try_propagate;
