//! Vole code generation: Cranelift JIT compilation.

mod analyzed;
mod calls;
pub mod compiler;
mod context;
pub mod errors;
mod expr;
mod function_registry;
mod interface_vtable;
pub mod jit;
mod lambda;
mod method_resolution;
mod ops;
mod stmt;
mod structs;
mod types;
mod vtable_ctx;

pub use compiler::{Compiler, ControlFlowCtx, TestInfo};
pub use function_registry::{FunctionKey, FunctionRegistry, RuntimeFn};
pub use jit::{CompiledModules, JitContext, JitOptions};
pub use types::CompiledValue;

// Error types
pub use errors::CodegenError;

// Analysis types
pub use analyzed::AnalyzedProgram;
