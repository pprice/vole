// src/codegen/rc_cleanup.rs
//
// RC scope tracking and cleanup emission for reference-counted variables.
//
// Each RC local gets a "drop flag" (i8 Cranelift Variable, 0 or 1).
// At scope exit, we emit conditional rc_dec calls for all live RC locals.
// Cranelift's SSA construction handles phi nodes when initialization is
// conditional (e.g., variable set in one branch of an if but not the other).

use cranelift::prelude::{FunctionBuilder, InstBuilder, IntCC, MemFlags, Variable, types};
use vole_sema::type_arena::TypeId;

/// A single RC local variable with its drop flag.
#[derive(Debug, Clone, Copy)]
pub(crate) struct RcLocal {
    /// The Cranelift Variable holding the RC pointer.
    pub variable: Variable,
    /// A Cranelift i8 Variable: 1 = live (needs rc_dec), 0 = not yet initialized / moved.
    pub drop_flag: Variable,
    /// The Vole type of this variable (for diagnostics / future use).
    #[allow(dead_code)]
    pub type_id: TypeId,
    /// True if this is an interface (fat pointer) local. For interfaces, the
    /// actual RC-managed data word is at offset 0 of the fat pointer, so cleanup
    /// must load it before calling rc_dec.
    pub is_interface: bool,
}

/// A composite local (struct, fixed array, tuple) that contains RC fields.
/// At scope exit, each RC field/element is loaded from the base pointer and rc_dec'd.
#[derive(Debug, Clone)]
pub(crate) struct CompositeRcLocal {
    /// The Cranelift Variable holding the base pointer (struct/array/tuple).
    pub variable: Variable,
    /// Drop flag: 1 = live, 0 = not yet initialized.
    pub drop_flag: Variable,
    /// Byte offsets of RC fields within the composite, relative to base pointer.
    pub rc_field_offsets: Vec<i32>,
}

/// A scope that tracks RC locals introduced within it.
///
/// Pushed when entering a block, popped when leaving.
#[derive(Debug, Default)]
pub(crate) struct RcScope {
    pub locals: Vec<RcLocal>,
    pub composites: Vec<CompositeRcLocal>,
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
    pub fn register_rc_local(
        &mut self,
        variable: Variable,
        drop_flag: Variable,
        type_id: TypeId,
        is_interface: bool,
    ) {
        let scope = self
            .scopes
            .last_mut()
            .expect("register_rc_local called with no active RC scope");
        scope.locals.push(RcLocal {
            variable,
            drop_flag,
            type_id,
            is_interface,
        });
    }

    /// Returns true if there is at least one active scope.
    pub fn has_active_scope(&self) -> bool {
        !self.scopes.is_empty()
    }

    /// Iterate all RC locals from all active scopes (innermost first).
    /// Used for return statements that must clean up everything.
    pub fn all_locals_innermost_first(&self) -> impl Iterator<Item = &RcLocal> {
        self.scopes.iter().rev().flat_map(|s| s.locals.iter())
    }

    /// Iterate RC locals from scopes above (and including) the given depth.
    /// Used for break/continue that clean up scopes down to the loop level.
    ///
    /// `target_depth` is the scope depth of the loop body. All scopes at
    /// index >= target_depth are cleaned up (innermost first).
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

    /// Returns true if `variable` is registered as an RC local in any scope.
    pub fn is_rc_local(&self, variable: Variable) -> bool {
        self.scopes
            .iter()
            .any(|s| s.locals.iter().any(|l| l.variable == variable))
    }

    /// Returns true if `variable` is registered as a composite RC local in any scope.
    pub fn is_composite_rc_local(&self, variable: Variable) -> bool {
        self.scopes
            .iter()
            .any(|s| s.composites.iter().any(|c| c.variable == variable))
    }

    /// Register a composite RC local in the current scope.
    pub fn register_composite(
        &mut self,
        variable: Variable,
        drop_flag: Variable,
        rc_field_offsets: Vec<i32>,
    ) {
        let scope = self
            .scopes
            .last_mut()
            .expect("register_composite called with no active RC scope");
        scope.composites.push(CompositeRcLocal {
            variable,
            drop_flag,
            rc_field_offsets,
        });
    }

    /// Update the RC field offsets for an existing composite RC local.
    /// Used when a mutable composite variable is reassigned and the
    /// scope-exit cleanup needs to cover nested RC fields.
    pub fn update_composite_offsets(&mut self, variable: Variable, new_offsets: Vec<i32>) {
        for scope in self.scopes.iter_mut().rev() {
            for composite in scope.composites.iter_mut() {
                if composite.variable == variable {
                    composite.rc_field_offsets = new_offsets;
                    return;
                }
            }
        }
    }

    /// Iterate all composite RC locals from all active scopes (innermost first).
    pub fn all_composites_innermost_first(&self) -> impl Iterator<Item = &CompositeRcLocal> {
        self.scopes.iter().rev().flat_map(|s| s.composites.iter())
    }

    /// Iterate composite RC locals from scopes at or above the given depth.
    pub fn composites_from_depth(
        &self,
        target_depth: usize,
    ) -> impl Iterator<Item = &CompositeRcLocal> {
        self.scopes[target_depth..]
            .iter()
            .rev()
            .flat_map(|s| s.composites.iter())
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
pub(crate) fn emit_rc_cleanup(
    builder: &mut FunctionBuilder,
    locals: &[RcLocal],
    rc_dec_ref: cranelift::codegen::ir::FuncRef,
) {
    // Iterate in reverse (LIFO) so that closures are dec'd before their
    // captured variables. A closure destructor dec's its captures, so the
    // closure must be freed first to avoid double-freeing a capture that
    // was already dec'd by direct scope cleanup.
    for local in locals.iter().rev() {
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
        if local.is_interface {
            // Interface locals are fat pointers: [data_word, vtable_ptr].
            // The RC-managed value is the data word at offset 0.
            let data_word = builder.ins().load(types::I64, MemFlags::new(), val, 0);
            builder.ins().call(rc_dec_ref, &[data_word]);
        } else {
            builder.ins().call(rc_dec_ref, &[val]);
        }
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

/// Emit cleanup code for composite RC locals.
///
/// For each composite, checks the drop flag, then loads and rc_dec's each
/// RC field at its byte offset from the base pointer.
pub(crate) fn emit_composite_rc_cleanup(
    builder: &mut FunctionBuilder,
    composites: &[CompositeRcLocal],
    rc_dec_ref: cranelift::codegen::ir::FuncRef,
) {
    // Reverse order (LIFO) for consistency with emit_rc_cleanup.
    for composite in composites.iter().rev() {
        let flag_val = builder.use_var(composite.drop_flag);
        let is_live = builder.ins().icmp_imm(IntCC::NotEqual, flag_val, 0);

        let cleanup_block = builder.create_block();
        let after_block = builder.create_block();

        builder
            .ins()
            .brif(is_live, cleanup_block, &[], after_block, &[]);

        builder.switch_to_block(cleanup_block);
        builder.seal_block(cleanup_block);

        let base_ptr = builder.use_var(composite.variable);
        for &offset in &composite.rc_field_offsets {
            let field_val = builder
                .ins()
                .load(types::I64, MemFlags::new(), base_ptr, offset);
            builder.ins().call(rc_dec_ref, &[field_val]);
        }
        builder.ins().jump(after_block, &[]);

        builder.switch_to_block(after_block);
        builder.seal_block(after_block);
    }
}
