// src/codegen/rc_cleanup.rs
//
// RC scope tracking and cleanup emission for reference-counted variables.
//
// Each RC local gets a "drop flag" (i8 Cranelift Variable, 0 or 1).
// At scope exit, we emit conditional rc_dec calls for all live RC locals.
// Cranelift's SSA construction handles phi nodes when initialization is
// conditional (e.g., variable set in one branch of an if but not the other).

use cranelift::prelude::{FunctionBuilder, InstBuilder, IntCC, Variable, types};
use vole_sema::type_arena::TypeId;

/// A single RC local variable with its drop flag.
#[allow(dead_code)] // Fields used when rc_dec emission is enabled (v-37ea)
#[derive(Debug, Clone, Copy)]
pub(crate) struct RcLocal {
    /// The Cranelift Variable holding the RC pointer.
    pub variable: Variable,
    /// A Cranelift i8 Variable: 1 = live (needs rc_dec), 0 = not yet initialized / moved.
    pub drop_flag: Variable,
    /// The Vole type of this variable (for diagnostics / future use).
    pub type_id: TypeId,
}

/// A scope that tracks RC locals introduced within it.
///
/// Pushed when entering a block, popped when leaving.
#[derive(Debug, Default)]
pub(crate) struct RcScope {
    pub locals: Vec<RcLocal>,
}

/// Stack of RC scopes. The outermost scope is index 0.
#[derive(Debug, Default)]
pub(crate) struct RcScopeStack {
    scopes: Vec<RcScope>,
}

impl RcScopeStack {
    pub fn new() -> Self {
        Self { scopes: Vec::new() }
    }

    /// Push a new scope (entering a block).
    pub fn push_scope(&mut self) {
        self.scopes.push(RcScope::default());
    }

    /// Pop the current scope, returning its RC locals for cleanup emission.
    pub fn pop_scope(&mut self) -> Option<RcScope> {
        self.scopes.pop()
    }

    /// Register an RC local in the current (innermost) scope.
    ///
    /// Panics if no scope is active (should never happen if push/pop are balanced).
    pub fn register_rc_local(&mut self, variable: Variable, drop_flag: Variable, type_id: TypeId) {
        let scope = self
            .scopes
            .last_mut()
            .expect("register_rc_local called with no active RC scope");
        scope.locals.push(RcLocal {
            variable,
            drop_flag,
            type_id,
        });
    }

    /// Returns true if there is at least one active scope.
    pub fn has_active_scope(&self) -> bool {
        !self.scopes.is_empty()
    }

    /// Iterate all RC locals from all active scopes (innermost first).
    /// Used for return statements that must clean up everything.
    #[allow(dead_code)] // Used when rc_dec emission is enabled (v-37ea)
    pub fn all_locals_innermost_first(&self) -> impl Iterator<Item = &RcLocal> {
        self.scopes.iter().rev().flat_map(|s| s.locals.iter())
    }

    /// Iterate RC locals from scopes above (and including) the given depth.
    /// Used for break/continue that clean up scopes down to the loop level.
    ///
    /// `target_depth` is the scope depth of the loop body. All scopes at
    /// index >= target_depth are cleaned up (innermost first).
    #[allow(dead_code)] // Used when rc_dec emission is enabled (v-37ea)
    pub fn locals_from_depth(&self, target_depth: usize) -> impl Iterator<Item = &RcLocal> {
        self.scopes[target_depth..]
            .iter()
            .rev()
            .flat_map(|s| s.locals.iter())
    }

    /// Current scope depth (number of active scopes).
    pub fn depth(&self) -> usize {
        self.scopes.len()
    }

    /// Get RC locals for the current (innermost) scope only.
    /// Used for normal block exit cleanup.
    #[allow(dead_code)] // Used when rc_dec emission is enabled (v-37ea)
    pub fn current_scope_locals(&self) -> &[RcLocal] {
        self.scopes
            .last()
            .map(|s| s.locals.as_slice())
            .unwrap_or(&[])
    }
}

/// Emit cleanup code for a slice of RC locals.
///
/// For each local, emits:
/// ```text
/// flag_val = use_var(drop_flag)
/// if flag_val != 0:
///     rc_dec(use_var(variable))
/// ```
///
/// Each conditional requires its own Cranelift block pair.
#[allow(dead_code)] // Used when rc_dec emission is enabled (v-37ea)
pub(crate) fn emit_rc_cleanup(
    builder: &mut FunctionBuilder,
    locals: &[RcLocal],
    rc_dec_ref: cranelift::codegen::ir::FuncRef,
) {
    for local in locals {
        let flag_val = builder.use_var(local.drop_flag);
        let is_live = builder.ins().icmp_imm(IntCC::NotEqual, flag_val, 0);

        let cleanup_block = builder.create_block();
        let after_block = builder.create_block();

        builder
            .ins()
            .brif(is_live, cleanup_block, &[], after_block, &[]);

        builder.switch_to_block(cleanup_block);
        builder.seal_block(cleanup_block);
        let val = builder.use_var(local.variable);
        builder.ins().call(rc_dec_ref, &[val]);
        builder.ins().jump(after_block, &[]);

        builder.switch_to_block(after_block);
        builder.seal_block(after_block);
    }
}

/// Allocate and initialize a drop flag variable to 0 (not yet initialized).
/// Returns the new Variable.
pub(crate) fn alloc_drop_flag(builder: &mut FunctionBuilder) -> Variable {
    let drop_flag = builder.declare_var(types::I8);
    let zero = builder.ins().iconst(types::I8, 0);
    builder.def_var(drop_flag, zero);
    drop_flag
}

/// Set a drop flag to 1 (variable is now live and needs cleanup).
pub(crate) fn set_drop_flag_live(builder: &mut FunctionBuilder, drop_flag: Variable) {
    let one = builder.ins().iconst(types::I8, 1);
    builder.def_var(drop_flag, one);
}
