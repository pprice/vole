//! Vole code generation: Cranelift JIT compilation.

mod analyzed;
mod callable_registry;
mod calls;
mod coercion_ops;
pub mod compiler;
mod compound_assign;
mod context;
pub mod errors;
mod expr;
mod function_registry;
mod generator;
mod intrinsic_compiler;
mod intrinsics;
pub mod jit;
mod lambda;
mod method_resolution;
mod ops;
mod rc_cleanup;
mod rc_ops;
mod rc_state;
mod runtime_registry;
mod stmt;
mod structs;
mod type_ops;
mod types;
mod value_builders;

// Organized submodules
mod control_flow;
mod interfaces;

pub use callable_registry::{
    CallableBackendPreference, CallableKey, CallableResolutionError, ResolvedCallable,
    resolve_callable_with_preference,
};
pub use compiler::{Compiler, TestInfo};
pub use function_registry::{FunctionKey, FunctionRegistry};
pub use intrinsics::{FloatConstant, IntrinsicHandler, IntrinsicKey, IntrinsicsRegistry};
pub use jit::{CompiledModules, JitContext, JitOptions};
pub use runtime_registry::{RuntimeKey, all_symbols as all_runtime_symbols};
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
///
/// Union layout: `[tag: i8 (1 byte)][pad (7 bytes)][payload (8 bytes)]`
pub(crate) mod union_layout {
    /// Byte size of a tag-only (sentinel) union — no payload.
    /// Unions with `type_size > TAG_ONLY_SIZE` have payload data.
    pub const TAG_ONLY_SIZE: u32 = 8;

    /// Byte offset of the payload within a union or optional value.
    /// After the 1-byte tag and 7 bytes of padding.
    pub const PAYLOAD_OFFSET: i32 = 8;

    /// Standard union allocation size: tag (8 bytes) + single i64 payload (8 bytes).
    /// Used for stack/heap allocations of standard-layout unions and optionals.
    pub const STANDARD_SIZE: u32 = 16;

    /// Byte offset of the is_rc flag within a union value.
    /// Layout: `[tag:i8, is_rc:i8, pad(6), payload:i64]`.
    /// Used by heap promotion to decide whether to rc_inc the payload.
    pub const IS_RC_OFFSET: i32 = 1;
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
