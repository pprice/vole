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

/// Maximum number of flat struct fields that can be returned in registers.
/// Structs with more fields use the sret (struct return pointer) convention.
pub(crate) const MAX_SMALL_STRUCT_FIELDS: usize = 2;

/// Union memory layout constants used across the compiler.
pub(crate) mod union_layout {
    /// Byte size of a tag-only (sentinel) union — no payload.
    /// Unions with `type_size > TAG_ONLY_SIZE` have payload data at offset 8.
    pub const TAG_ONLY_SIZE: u32 = 8;
}

/// Named trap codes for Cranelift traps used across the compiler.
pub(crate) mod trap_codes {
    use cranelift::prelude::TrapCode;

    /// Unreachable code (divergent match/if arms, exhaustion, panic handlers)
    pub const UNREACHABLE: TrapCode = TrapCode::unwrap_user(1);
    /// Array/slice bounds check failure
    pub const BOUNDS_CHECK: TrapCode = TrapCode::unwrap_user(2);
    /// Explicit panic() call
    pub const PANIC: TrapCode = TrapCode::unwrap_user(3);
}
