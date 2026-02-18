//! Optimizer passes for the Vole compiler.
//!
//! This module contains optimization passes that run after semantic analysis
//! and before code generation. The passes transform the AST to improve runtime
//! performance.
//!
//! # Architecture
//!
//! Vole has a two-level optimization pipeline:
//!
//! ## Level 1: AST-level optimizations (vole-sema/optimizer)
//!
//! These run on the typed AST before code generation:
//!
//! ```text
//! Parse -> Sema (type check) -> AST Optimizer -> Codegen
//!                                     |
//!                               ConstantFolding
//!                               (future: CSE, DCE at AST level)
//! ```
//!
//! ## Level 2: IR-level optimizations (vole-codegen)
//!
//! These run on Cranelift IR after basic code generation:
//!
//! ```text
//! Codegen -> IR Build -> CFG Cleanup -> Loop Param Opt -> Define Function
//!                             |              |
//!                    (trampoline removal)   (LICM foundation)
//! ```
//!
//! # Pass Dependency Graph
//!
//! ```text
//!                    AST Optimizations
//!                    =================
//!
//!                    ConstantFolding
//!                         |
//!              +----------+----------+
//!              |                     |
//!              v                     v
//!            CSE*                  DCE*
//!
//!
//!                    IR Optimizations
//!                    ================
//!
//!                    CFG Cleanup
//!                         |
//!                         v
//!                  Loop Param Opt (foundation for LICM)
//!                         |
//!                         v
//!                    Cranelift opt_level=speed
//!
//! (* = planned, not yet implemented)
//! ```
//!
//! # Available AST Passes
//!
//! - [`constant_folding`]: Evaluate constant expressions at compile time
//!   - Fold binary ops with constant operands (e.g., `2 + 3` -> `5`)
//!   - Replace division by constant with multiplication by reciprocal
//!   - Replace division by power-of-2 with bit shifts (unsigned integers)
//!   - Constant propagation for immutable bindings
//!
//! # Planned AST Passes
//!
//! - **CSE (Common Subexpression Elimination)**: Detect and reuse repeated expressions
//! - **DCE (Dead Code Elimination)**: Remove unused variables and unreachable code
//!
//! # IR Passes (in vole-codegen)
//!
//! - **CFG Cleanup**: Remove trampoline blocks (single-jump blocks)
//! - **Loop Parameter Optimization**: Remove invariant block parameters from loops
//!
//! # Measurement Strategy
//!
//! Optimization effectiveness is measured using:
//! 1. Benchmarks in `test/bench/` (mandelbrot, fib)
//! 2. `vole bench` command for timing
//! 3. `vole inspect ir` for IR quality analysis
//! 4. OptimizerStats for pass-level metrics

pub mod constant_folding;

use crate::ExpressionData;
use vole_frontend::Program;

/// Configuration for the optimizer.
#[derive(Debug, Clone, Default)]
struct OptimizerConfig {
    /// Enable constant folding pass
    constant_folding: bool,
}

impl OptimizerConfig {
    /// Create a new config with all optimizations enabled
    fn all() -> Self {
        Self {
            constant_folding: true,
        }
    }
}

/// Statistics from optimization passes.
#[derive(Debug, Clone, Default)]
pub struct OptimizerStats {
    /// Number of constant expressions folded
    pub constants_folded: usize,
    /// Number of divisions replaced with multiplication
    pub div_to_mul: usize,
    /// Number of divisions replaced with bit shifts
    pub div_to_shift: usize,
    /// Number of constant propagations (variable references replaced with literals)
    pub constants_propagated: usize,
    /// Number of pure intrinsic calls folded (e.g., f64.sqrt(4.0) -> 2.0)
    pub intrinsics_folded: usize,
}

/// Run all enabled optimization passes on the program.
///
/// This function should be called after semantic analysis completes,
/// before code generation begins. It may modify both the AST (program)
/// and the expression data (type information).
///
/// # Arguments
///
/// * `program` - The parsed program AST (will be modified in place)
/// * `expr_data` - Expression type information from sema (may be updated)
/// * `config` - Which optimizations to enable
///
/// # Returns
///
/// Statistics about what optimizations were applied.
fn optimize(
    program: &mut Program,
    expr_data: &mut ExpressionData,
    config: &OptimizerConfig,
) -> OptimizerStats {
    let mut stats = OptimizerStats::default();

    if config.constant_folding {
        let folding_stats = constant_folding::fold_constants(program, expr_data);
        stats.constants_folded = folding_stats.constants_folded;
        stats.div_to_mul = folding_stats.div_to_mul;
        stats.div_to_shift = folding_stats.div_to_shift;
        stats.constants_propagated = folding_stats.constants_propagated;
        stats.intrinsics_folded = folding_stats.intrinsics_folded;
    }

    stats
}

/// Run all optimizations with default configuration (all enabled).
pub fn optimize_all(program: &mut Program, expr_data: &mut ExpressionData) -> OptimizerStats {
    optimize(program, expr_data, &OptimizerConfig::all())
}
