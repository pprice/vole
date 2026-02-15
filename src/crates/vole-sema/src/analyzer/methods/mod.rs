// src/sema/analyzer/methods/mod.rs

mod builtin;
mod call_args;
mod compatibility;
mod instance_call;
mod interface;
mod monomorph;
mod resolution;

pub(crate) use monomorph::GenericContext;
