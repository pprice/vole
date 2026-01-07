// src/codegen/mod.rs
mod calls;
pub mod compiler;
mod context;
mod expr;
mod function_registry;
pub mod jit;
mod lambda;
mod ops;
mod stmt;
mod structs;
mod types;

pub use compiler::{Compiler, ControlFlowCtx, TestInfo};
pub use function_registry::{FunctionKey, FunctionRegistry, RuntimeFn};
pub use jit::JitContext;
pub use types::CompiledValue;
