//! Vole code generation: Cranelift JIT compilation.

mod analyzed;
mod calls;
mod cfg_cleanup;
pub mod compiler;
mod context;
pub mod errors;
mod expr;
mod function_registry;
mod interface_vtable;
mod intrinsics;
pub mod jit;
mod lambda;
pub mod loop_analysis;
pub mod loop_param_opt;
mod match_switch;
mod method_resolution;
mod ops;
mod stmt;
mod structs;
mod types;
mod vtable_ctx;

pub use compiler::{Compiler, ControlFlowCtx, TestInfo};
pub use function_registry::{FunctionKey, FunctionRegistry, RuntimeFn};
pub use intrinsics::{FloatConstant, IntrinsicHandler, IntrinsicKey, IntrinsicsRegistry};
pub use jit::{CompiledModules, JitContext, JitOptions};
pub use types::CompiledValue;

// Error types
pub use errors::CodegenError;

// Analysis types
pub use analyzed::AnalyzedProgram;

// Loop analysis
pub use loop_analysis::{FunctionLoopInfo, InductionInfo, InductionStep, LoopInfo, analyze_loops};

// Loop parameter optimization
pub use loop_param_opt::{LoopParamOptStats, optimize_loop_params};
