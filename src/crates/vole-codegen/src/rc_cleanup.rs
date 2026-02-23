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

use crate::context::Cg;
use crate::ops::try_constant_value;

/// A single RC local variable with its drop flag.
#[derive(Debug, Clone, Copy)]
pub(crate) struct RcLocal {
    /// The Cranelift Variable holding the RC pointer.
    pub variable: Variable,
    /// A Cranelift i8 Variable: 1 = live (needs rc_dec), 0 = not yet initialized / moved.
    pub drop_flag: Variable,
    /// The Vole type of this variable, stored for debugging and future type-aware
    /// cleanup logic (e.g., specialized cleanup for nested RC types).
    #[expect(
        dead_code,
        reason = "stored for debugging and future type-aware cleanup"
    )]
    pub type_id: TypeId,
    /// True if this is an interface (fat pointer) local. For interfaces, the
    /// actual RC-managed data word is at offset 0 of the fat pointer, so cleanup
    /// must load it before calling rc_dec.
    pub is_interface: bool,
    /// True if this is an unknown-typed (heap-allocated TaggedValue) local.
    /// Cleanup calls `unknown_heap_cleanup` instead of `rc_dec` to free the
    /// 16-byte buffer and conditionally rc_dec the inner payload.
    pub is_unknown: bool,
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
    /// Inline union fields that need tag-based conditional RC cleanup.
    /// Each entry is (byte_offset, rc_variant_tags) where the union buffer
    /// is stored at `byte_offset` from the base pointer.
    ///
    /// NOTE: Cleanup emission is currently disabled because existing structs
    /// (e.g. ParseResult in json.vole) share RC values between the union field
    /// and typed fields, causing double-dec. Proper fix requires rc_inc at
    /// construction time for the union copy. Tracked as follow-up.
    pub union_field_offsets: Vec<(i32, Vec<(u8, bool)>)>,
}

/// A union local that may contain RC variants. At scope exit, we check the tag
/// and rc_dec the payload only when the active variant is an RC type.
///
/// Union layout: `[tag: i8, pad(7), value: i64]`
#[derive(Debug, Clone)]
pub(crate) struct UnionRcLocal {
    /// The Cranelift Variable holding the pointer to the union stack slot.
    pub variable: Variable,
    /// Drop flag: 1 = live, 0 = not yet initialized.
    pub drop_flag: Variable,
    /// Tag indices of variants that are RC-managed (need rc_dec at offset 8).
    /// Each entry is (tag_index, is_interface).
    pub rc_variant_tags: Vec<(u8, bool)>,
}

/// A scope that tracks RC locals introduced within it.
///
/// Pushed when entering a block, popped when leaving.
#[derive(Debug, Default)]
pub(crate) struct RcScope {
    pub locals: Vec<RcLocal>,
    pub composites: Vec<CompositeRcLocal>,
    pub unions: Vec<UnionRcLocal>,
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
        is_unknown: bool,
    ) {
        let scope = self
            .scopes
            .last_mut()
            .expect("INTERNAL: register_rc_local: no active RC scope");
        scope.locals.push(RcLocal {
            variable,
            drop_flag,
            type_id,
            is_interface,
            is_unknown,
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

    /// Returns true if `variable` is registered as a union RC local in any scope.
    pub fn is_union_rc_local(&self, variable: Variable) -> bool {
        self.scopes
            .iter()
            .any(|s| s.unions.iter().any(|u| u.variable == variable))
    }

    /// Register a composite RC local in the current scope.
    pub fn register_composite(
        &mut self,
        variable: Variable,
        drop_flag: Variable,
        rc_field_offsets: Vec<i32>,
        union_field_offsets: Vec<(i32, Vec<(u8, bool)>)>,
    ) {
        let scope = self
            .scopes
            .last_mut()
            .expect("INTERNAL: register_composite: no active RC scope");
        scope.composites.push(CompositeRcLocal {
            variable,
            drop_flag,
            rc_field_offsets,
            union_field_offsets,
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

    /// Register a union RC local in the current scope.
    pub fn register_union(
        &mut self,
        variable: Variable,
        drop_flag: Variable,
        rc_variant_tags: Vec<(u8, bool)>,
    ) {
        let scope = self
            .scopes
            .last_mut()
            .expect("INTERNAL: register_union: no active RC scope");
        scope.unions.push(UnionRcLocal {
            variable,
            drop_flag,
            rc_variant_tags,
        });
    }

    /// Iterate all union RC locals from all active scopes (innermost first).
    pub fn all_unions_innermost_first(&self) -> impl Iterator<Item = &UnionRcLocal> {
        self.scopes.iter().rev().flat_map(|s| s.unions.iter())
    }

    /// Iterate union RC locals from scopes at or above the given depth.
    pub fn unions_from_depth(&self, target_depth: usize) -> impl Iterator<Item = &UnionRcLocal> {
        self.scopes[target_depth..]
            .iter()
            .rev()
            .flat_map(|s| s.unions.iter())
    }
}

/// Emit cleanup code for a slice of RC locals.
///
/// For each local, emits:
/// ```text
/// flag_val = use_var(drop_flag)
/// if flag_val != 0:
///     rc_dec(use_var(variable))       // or unknown_heap_cleanup for unknown locals
/// ```
///
/// Each conditional requires its own Cranelift block pair.
pub(crate) fn emit_rc_cleanup(
    cg: &mut Cg,
    locals: &[RcLocal],
    rc_dec_ref: cranelift::codegen::ir::FuncRef,
    skip_var: Option<Variable>,
) {
    // Lazily resolve unknown_heap_cleanup func ref only if needed.
    let mut unknown_cleanup_ref: Option<cranelift::codegen::ir::FuncRef> = None;

    // Iterate in reverse (LIFO) so that closures are dec'd before their
    // captured variables. A closure destructor dec's its captures, so the
    // closure must be freed first to avoid double-freeing a capture that
    // was already dec'd by direct scope cleanup.
    for local in locals.iter().rev() {
        if skip_var == Some(local.variable) {
            continue;
        }

        // Resolve the appropriate cleanup func ref for this local.
        let cleanup_ref = if local.is_unknown {
            *unknown_cleanup_ref.get_or_insert_with(|| {
                cg.runtime_func_ref(crate::RuntimeKey::UnknownHeapCleanup)
                    .expect("INTERNAL: UnknownHeapCleanup func ref")
            })
        } else {
            rc_dec_ref
        };

        let flag_val = cg.builder.use_var(local.drop_flag);

        // Constant-fold: skip the branch diamond when the drop flag is known.
        if let Some(const_val) = try_constant_value(cg.builder.func, flag_val) {
            if const_val == 0 {
                // Flag is known-dead: skip cleanup entirely.
                continue;
            }
            // Flag is known-live: emit cleanup unconditionally (no branch).
            emit_single_cleanup(cg.builder, local, cleanup_ref);
            let zero = cg.iconst_cached(types::I8, 0);
            cg.builder.def_var(local.drop_flag, zero);
            continue;
        }

        // Unknown flag: emit the full conditional diamond.
        // `flag_val` is an i8 boolean (0 = dead, nonzero = live); `brif` already
        // treats nonzero as true, so no icmp_imm needed.
        let cleanup_block = cg.builder.create_block();
        let after_block = cg.builder.create_block();

        cg.builder
            .ins()
            .brif(flag_val, cleanup_block, &[], after_block, &[]);

        cg.switch_to_block(cleanup_block);
        cg.builder.seal_block(cleanup_block);
        emit_single_cleanup(cg.builder, local, cleanup_ref);
        // Reset drop flag to 0 after cleanup. This prevents double-free when
        // the variable is conditionally initialized inside a loop: without
        // this, the stale flag=1 propagates via SSA phi nodes to the next
        // iteration, causing rc_dec on already-freed memory.
        let zero = cg.iconst_cached(types::I8, 0);
        cg.builder.def_var(local.drop_flag, zero);
        cg.builder.ins().jump(after_block, &[]);

        cg.switch_to_block(after_block);
        cg.builder.seal_block(after_block);
    }
}

/// Emit a single cleanup call for an RC local.
///
/// For interface locals, loads the data word from the fat pointer.
/// For unknown locals, calls `unknown_heap_cleanup` to free the TaggedValue buffer.
/// For other RC locals, calls `rc_dec` directly.
fn emit_single_cleanup(
    builder: &mut FunctionBuilder,
    local: &RcLocal,
    cleanup_ref: cranelift::codegen::ir::FuncRef,
) {
    let val = builder.use_var(local.variable);
    if local.is_interface {
        // Interface locals are fat pointers: [data_word, vtable_ptr].
        // The RC-managed value is the data word at offset 0.
        let data_word = builder.ins().load(types::I64, MemFlags::new(), val, 0);
        builder.ins().call(cleanup_ref, &[data_word]);
    } else {
        builder.ins().call(cleanup_ref, &[val]);
    }
}

/// Allocate and initialize a drop flag variable to 0 (not yet initialized).
/// Returns the new Variable.
pub(crate) fn alloc_drop_flag(cg: &mut Cg) -> Variable {
    let drop_flag = cg.builder.declare_var(types::I8);
    let zero = cg.iconst_cached(types::I8, 0);
    cg.builder.def_var(drop_flag, zero);
    drop_flag
}

/// Set a drop flag to 1 (variable is now live and needs cleanup).
pub(crate) fn set_drop_flag_live(cg: &mut Cg, drop_flag: Variable) {
    let one = cg.iconst_cached(types::I8, 1);
    cg.builder.def_var(drop_flag, one);
}

/// Emit cleanup code for union RC locals.
///
/// For each union, checks the drop flag, then loads the tag byte at offset 0.
/// For each RC variant, checks if the tag matches and if so, rc_dec's the
/// payload at offset 8.
pub(crate) fn emit_union_rc_cleanup(
    cg: &mut Cg,
    unions: &[UnionRcLocal],
    rc_dec_ref: cranelift::codegen::ir::FuncRef,
    skip_var: Option<Variable>,
) {
    for union_local in unions.iter().rev() {
        if skip_var == Some(union_local.variable) {
            continue;
        }
        let flag_val = cg.builder.use_var(union_local.drop_flag);

        // Constant-fold: skip the branch diamond when the drop flag is known.
        if let Some(const_val) = try_constant_value(cg.builder.func, flag_val) {
            if const_val == 0 {
                continue;
            }
            // Flag is known-live: emit tag checks unconditionally (no outer branch).
            emit_union_tag_checks(cg, union_local, rc_dec_ref);
            let zero = cg.iconst_cached(types::I8, 0);
            cg.builder.def_var(union_local.drop_flag, zero);
            continue;
        }

        // Unknown flag: emit the full conditional diamond.
        // `flag_val` is an i8 boolean; `brif` treats nonzero as true directly.
        let cleanup_block = cg.builder.create_block();
        let after_block = cg.builder.create_block();

        cg.builder
            .ins()
            .brif(flag_val, cleanup_block, &[], after_block, &[]);

        cg.switch_to_block(cleanup_block);
        cg.builder.seal_block(cleanup_block);

        emit_union_tag_checks(cg, union_local, rc_dec_ref);

        // Reset drop flag after cleanup (same reason as emit_rc_cleanup).
        let zero = cg.iconst_cached(types::I8, 0);
        cg.builder.def_var(union_local.drop_flag, zero);
        cg.builder.ins().jump(after_block, &[]);

        cg.switch_to_block(after_block);
        cg.builder.seal_block(after_block);
    }
}

/// Emit the tag-check cascade for a single union's RC variants.
///
/// Loads the tag, then for each RC variant emits a conditional rc_dec of the payload.
fn emit_union_tag_checks(
    cg: &mut Cg,
    union_local: &UnionRcLocal,
    rc_dec_ref: cranelift::codegen::ir::FuncRef,
) {
    let base_ptr = cg.builder.use_var(union_local.variable);
    let tag = cg
        .builder
        .ins()
        .load(types::I8, MemFlags::new(), base_ptr, 0);

    for &(variant_tag, is_interface) in &union_local.rc_variant_tags {
        let is_match = cg
            .builder
            .ins()
            .icmp_imm(IntCC::Equal, tag, variant_tag as i64);
        let dec_block = cg.builder.create_block();
        let next_block = cg.builder.create_block();

        cg.builder
            .ins()
            .brif(is_match, dec_block, &[], next_block, &[]);

        cg.switch_to_block(dec_block);
        cg.builder.seal_block(dec_block);
        let payload = cg.builder.ins().load(
            types::I64,
            MemFlags::new(),
            base_ptr,
            crate::union_layout::PAYLOAD_OFFSET,
        );
        if is_interface {
            let data_word = cg
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), payload, 0);
            cg.builder.ins().call(rc_dec_ref, &[data_word]);
        } else {
            cg.builder.ins().call(rc_dec_ref, &[payload]);
        }
        cg.builder.ins().jump(next_block, &[]);

        cg.switch_to_block(next_block);
        cg.builder.seal_block(next_block);
    }
}

/// Emit cleanup code for composite RC locals.
///
/// For each composite, checks the drop flag, then loads and rc_dec's each
/// RC field at its byte offset from the base pointer.
pub(crate) fn emit_composite_rc_cleanup(
    cg: &mut Cg,
    composites: &[CompositeRcLocal],
    rc_dec_ref: cranelift::codegen::ir::FuncRef,
    skip_var: Option<Variable>,
) {
    // Reverse order (LIFO) for consistency with emit_rc_cleanup.
    for composite in composites.iter().rev() {
        if skip_var == Some(composite.variable) {
            continue;
        }
        let flag_val = cg.builder.use_var(composite.drop_flag);

        // Constant-fold: skip the branch diamond when the drop flag is known.
        if let Some(const_val) = try_constant_value(cg.builder.func, flag_val) {
            if const_val == 0 {
                continue;
            }
            // Flag is known-live: emit field cleanup unconditionally (no branch).
            emit_composite_field_cleanup(cg.builder, composite, rc_dec_ref);
            // TODO: emit_composite_union_cleanup disabled pending fix for
            // ParseResult double-dec issue (value: Json overlaps str_val/obj_val/arr_val)
            let zero = cg.iconst_cached(types::I8, 0);
            cg.builder.def_var(composite.drop_flag, zero);
            continue;
        }

        // Unknown flag: emit the full conditional diamond.
        // `flag_val` is an i8 boolean; `brif` treats nonzero as true directly.
        let cleanup_block = cg.builder.create_block();
        let after_block = cg.builder.create_block();

        cg.builder
            .ins()
            .brif(flag_val, cleanup_block, &[], after_block, &[]);

        cg.switch_to_block(cleanup_block);
        cg.builder.seal_block(cleanup_block);

        emit_composite_field_cleanup(cg.builder, composite, rc_dec_ref);
        // TODO: emit_composite_union_cleanup disabled pending fix
        // Reset drop flag after cleanup (same reason as emit_rc_cleanup).
        let zero = cg.iconst_cached(types::I8, 0);
        cg.builder.def_var(composite.drop_flag, zero);
        cg.builder.ins().jump(after_block, &[]);

        cg.switch_to_block(after_block);
        cg.builder.seal_block(after_block);
    }
}

/// Emit rc_dec calls for each RC field of a composite at its byte offset.
fn emit_composite_field_cleanup(
    builder: &mut FunctionBuilder,
    composite: &CompositeRcLocal,
    rc_dec_ref: cranelift::codegen::ir::FuncRef,
) {
    let base_ptr = builder.use_var(composite.variable);
    for &offset in &composite.rc_field_offsets {
        let field_val = builder
            .ins()
            .load(types::I64, MemFlags::new(), base_ptr, offset);
        builder.ins().call(rc_dec_ref, &[field_val]);
    }
}

/// Emit tag-based conditional rc_dec for inline union fields within a composite.
/// For each union field, loads the tag from `base_ptr + field_offset`, checks each
/// RC variant, and conditionally rc_dec's the payload.
///
/// NOTE: Currently unused because existing structs (e.g. ParseResult) share RC
/// values between the union field and typed fields. Will be enabled once union
/// field construction properly rc_inc's the payload.
#[expect(
    dead_code,
    reason = "pending proper rc_inc at union field construction"
)]
fn emit_composite_union_cleanup(
    cg: &mut Cg,
    composite: &CompositeRcLocal,
    rc_dec_ref: cranelift::codegen::ir::FuncRef,
) {
    for (field_offset, rc_tags) in &composite.union_field_offsets {
        let base_ptr = cg.builder.use_var(composite.variable);
        let union_ptr = if *field_offset == 0 {
            base_ptr
        } else {
            cg.builder.ins().iadd_imm(base_ptr, *field_offset as i64)
        };
        // Load tag byte from offset 0 within the inline union buffer
        let tag = cg
            .builder
            .ins()
            .load(types::I8, MemFlags::new(), union_ptr, 0);

        for &(variant_tag, is_interface) in rc_tags {
            let is_match = cg
                .builder
                .ins()
                .icmp_imm(IntCC::Equal, tag, variant_tag as i64);
            let dec_block = cg.builder.create_block();
            let next_block = cg.builder.create_block();

            cg.builder
                .ins()
                .brif(is_match, dec_block, &[], next_block, &[]);

            cg.switch_to_block(dec_block);
            cg.builder.seal_block(dec_block);
            let payload = cg.builder.ins().load(
                types::I64,
                MemFlags::new(),
                union_ptr,
                crate::union_layout::PAYLOAD_OFFSET,
            );
            if is_interface {
                let data_word = cg
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), payload, 0);
                cg.builder.ins().call(rc_dec_ref, &[data_word]);
            } else {
                cg.builder.ins().call(rc_dec_ref, &[payload]);
            }
            cg.builder.ins().jump(next_block, &[]);

            cg.switch_to_block(next_block);
            cg.builder.seal_block(next_block);
        }
    }
}
