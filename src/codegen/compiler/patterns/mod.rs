// src/codegen/compiler/patterns/mod.rs
//
// Pattern matching codegen helpers.

mod captures;
mod expr;
mod type_check;

pub(crate) use expr::compile_expr;
