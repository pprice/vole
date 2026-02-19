//! Control flow analysis and optimization passes for Cranelift IR.
//!
//! This module contains:
//! - CFG cleanup (dead block elimination)
//! - Loop analysis (detecting loop structure and induction variables)
//! - Loop parameter optimization (hoisting loop-invariant computations)
//! - Match switch optimization (converting match expressions to jump tables)

mod block_fusion;
mod cfg_cleanup;
pub mod loop_analysis;
pub mod loop_param_opt;
pub(crate) mod match_switch;

pub(crate) use cfg_cleanup::cleanup_cfg;
pub use loop_analysis::{FunctionLoopInfo, InductionInfo, InductionStep, LoopInfo, analyze_loops};
pub use loop_param_opt::{LoopParamOptStats, optimize_loop_params};
