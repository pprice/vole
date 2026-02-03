//! Vole code generation: Cranelift JIT compilation.

mod analyzed;
mod calls;
pub mod compiler;
mod context;
pub mod errors;
mod expr;
mod function_registry;
mod intrinsics;
pub mod jit;
mod lambda;
mod method_resolution;
mod ops;
mod rc_cleanup;
mod rc_state;
mod stmt;
mod structs;
mod types;

// Organized submodules
mod control_flow;
mod interfaces;

pub use compiler::{Compiler, ControlFlowCtx, TestInfo};
pub use function_registry::{FunctionKey, FunctionRegistry, RuntimeFn};
pub use intrinsics::{FloatConstant, IntrinsicHandler, IntrinsicKey, IntrinsicsRegistry};
pub use jit::{CompiledModules, JitContext, JitOptions};
pub use types::CompiledValue;

// Error types
pub use errors::{CodegenError, CodegenResult};

// Analysis types
pub use analyzed::AnalyzedProgram;

// Loop analysis (re-exported from control_flow)
pub use control_flow::{
    FunctionLoopInfo, InductionInfo, InductionStep, LoopInfo, LoopParamOptStats, analyze_loops,
    optimize_loop_params,
};

// Public access to control_flow submodules (preserves original pub mod interface)
pub mod loop_analysis {
    pub use super::control_flow::loop_analysis::*;
}
pub mod loop_param_opt {
    pub use super::control_flow::loop_param_opt::*;
}
