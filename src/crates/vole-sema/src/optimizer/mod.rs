//! Optimizer passes for the Vole compiler.
//!
//! This module contains optimization passes that run after semantic analysis
//! and before code generation. The passes transform the AST to improve runtime
//! performance.
//!
//! # Architecture
//!
//! ```text
//! Parse -> Sema (type check) -> Optimizer (constant fold) -> Codegen
//! ```
//!
//! # Available Passes
//!
//! - `constant_folding`: Evaluate constant expressions at compile time
//!   - Fold binary ops with constant operands
//!   - Replace division by constant with multiplication by reciprocal
//!   - Replace division by power-of-2 with bit shifts (unsigned integers)

pub mod constant_folding;

use crate::ExpressionData;
use vole_frontend::{Interner, Program};

/// Configuration for the optimizer.
#[derive(Debug, Clone, Default)]
pub struct OptimizerConfig {
    /// Enable constant folding pass
    pub constant_folding: bool,
}

impl OptimizerConfig {
    /// Create a new config with all optimizations enabled
    pub fn all() -> Self {
        Self {
            constant_folding: true,
        }
    }

    /// Create a new config with no optimizations
    pub fn none() -> Self {
        Self::default()
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
/// * `interner` - String interner for symbol resolution
/// * `expr_data` - Expression type information from sema (may be updated)
/// * `config` - Which optimizations to enable
///
/// # Returns
///
/// Statistics about what optimizations were applied.
pub fn optimize(
    program: &mut Program,
    interner: &Interner,
    expr_data: &mut ExpressionData,
    config: &OptimizerConfig,
) -> OptimizerStats {
    let mut stats = OptimizerStats::default();

    if config.constant_folding {
        let folding_stats = constant_folding::fold_constants(program, interner, expr_data);
        stats.constants_folded = folding_stats.constants_folded;
        stats.div_to_mul = folding_stats.div_to_mul;
        stats.div_to_shift = folding_stats.div_to_shift;
    }

    stats
}

/// Run all optimizations with default configuration (all enabled).
pub fn optimize_all(
    program: &mut Program,
    interner: &Interner,
    expr_data: &mut ExpressionData,
) -> OptimizerStats {
    optimize(program, interner, expr_data, &OptimizerConfig::all())
}
