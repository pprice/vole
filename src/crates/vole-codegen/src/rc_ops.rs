// src/codegen/rc_ops.rs
//
// RC lifecycle methods - impl Cg methods for reference counting.
//
// Handles RC scope management, cleanup emission, inc/dec operations,
// union RC ops, and RC state queries. Split from context.rs.

use cranelift::prelude::{InstBuilder, IntCC, MemFlags, Value, Variable, types};

use rustc_hash::FxHashMap;

use vole_identity::NameId;
use vole_sema::type_arena::TypeId;

use crate::RuntimeKey;
use crate::errors::CodegenResult;
use crate::union_layout;

use super::context::Cg;
use super::rc_state::{RcState, compute_rc_state};
use super::types::{CompiledValue, RcLifecycle};

impl<'a, 'b, 'ctx> Cg<'a, 'b, 'ctx> {
    // ========== RC scope tracking ==========

    /// Get or create a runtime type_id for a monomorphized generic class instance.
    ///
    /// For generic classes like `Wrapper<T>`, the base class is registered with
    /// field type tags based on TypeParam placeholders (which are tagged as Value).
    /// When a concrete instantiation like `Wrapper<Tag>` is created, the fields
    /// may actually be RC types that need cleanup. This method creates a unique
    /// runtime type_id for each (base_class, type_args) combination and registers
    /// the correct field type tags based on the concrete type arguments.
    ///
    /// Returns the base type_id unchanged if:
    /// - The class has no type args (non-generic)
    /// - None of the field types involve type parameters
    pub fn mono_instance_type_id(&self, base_type_id: u32, result_type_id: TypeId) -> u32 {
        let arena = self.arena();
        let Some((type_def_id, type_args)) = arena.unwrap_class(result_type_id) else {
            return base_type_id;
        };
        if type_args.is_empty() {
            return base_type_id;
        }
        self.mono_instance_type_id_with_args(base_type_id, type_def_id, type_args.to_vec())
    }

    /// Resolve a monomorphized runtime type_id for a generic class instance
    /// using explicit concrete type arguments.
    ///
    /// This variant is used when the caller already has the correct concrete
    /// type args (e.g., from substituting type params in a monomorphized context).
    pub fn mono_instance_type_id_with_args(
        &self,
        base_type_id: u32,
        type_def_id: vole_identity::TypeDefId,
        concrete_type_args: Vec<TypeId>,
    ) -> u32 {
        if concrete_type_args.is_empty() {
            return base_type_id;
        }

        let arena = self.arena();

        // Check if any field type is a TypeParam that maps to an RC type
        let type_def = self.query().get_type(type_def_id);
        let Some(generic_info) = &type_def.generic_info else {
            return base_type_id;
        };
        if generic_info.type_params.is_empty() {
            return base_type_id;
        }

        // Build substitution map: type_param NameId -> concrete TypeId
        let subs: FxHashMap<NameId, TypeId> = generic_info
            .type_params
            .iter()
            .zip(concrete_type_args.iter())
            .map(|(param, &arg)| (param.name_id, arg))
            .collect();

        // Substitute field types to get concrete types
        let concrete_field_types: Vec<TypeId> = generic_info
            .field_types
            .iter()
            .map(|&ft| arena.expect_substitute(ft, &subs, "mono_instance_type_id"))
            .collect();

        // Check if any field type changes its cleanup tag after substitution.
        // If all concrete field types have the same tag as the base registration,
        // we can reuse the base type_id.
        let base_tags: Vec<_> = generic_info
            .field_types
            .iter()
            .map(|&ft| self.field_type_tag(ft))
            .collect();
        let concrete_tags: Vec<_> = concrete_field_types
            .iter()
            .map(|&ft| self.field_type_tag(ft))
            .collect();
        if base_tags == concrete_tags {
            return base_type_id;
        }

        // Need a monomorphized type_id. Check cache first.
        let key = (type_def_id, concrete_type_args);
        if let Some(&cached_id) = self.env.state.mono_type_ids.borrow().get(&key) {
            return cached_id;
        }

        // Allocate a new globally-unique type_id
        let new_type_id = vole_runtime::type_registry::alloc_type_id();

        // Compute field type tags from concrete types
        let field_type_tags: Vec<vole_runtime::type_registry::FieldTypeTag> = concrete_field_types
            .iter()
            .map(|&ft| self.field_type_tag(ft))
            .collect();

        // Register in the runtime type registry
        vole_runtime::type_registry::register_instance_type(new_type_id, field_type_tags);

        // Cache for future use
        self.env
            .state
            .mono_type_ids
            .borrow_mut()
            .insert(key, new_type_id);

        new_type_id
    }

    /// Push a new RC scope (called when entering a block).
    pub fn push_rc_scope(&mut self) {
        self.rc_scopes.push_scope();
    }

    /// Pop the current RC scope and emit cleanup for its RC locals and composites.
    /// `skip_var` optionally specifies a variable whose ownership is being
    /// transferred out (e.g., the block result) and should NOT be dec'd.
    pub fn pop_rc_scope_with_cleanup(&mut self, skip_var: Option<Variable>) -> CodegenResult<()> {
        if let Some(scope) = self.rc_scopes.pop_scope() {
            self.emit_rc_cleanup_for_collections(
                &scope.locals,
                &scope.composites,
                &scope.unions,
                skip_var,
            )?;
        }
        Ok(())
    }

    /// Emit cleanup for ALL active RC scopes (for return statements).
    /// `skip_var` optionally specifies a variable being returned.
    pub fn emit_rc_cleanup_all_scopes(&mut self, skip_var: Option<Variable>) -> CodegenResult<()> {
        let locals: Vec<_> = self
            .rc_scopes
            .all_locals_innermost_first()
            .copied()
            .collect();
        let composites: Vec<_> = self
            .rc_scopes
            .all_composites_innermost_first()
            .cloned()
            .collect();
        let unions: Vec<_> = self
            .rc_scopes
            .all_unions_innermost_first()
            .cloned()
            .collect();
        self.emit_rc_cleanup_for_collections(&locals, &composites, &unions, skip_var)
    }

    /// Emit cleanup for scopes from the given depth upward (for break/continue).
    /// `target_depth` is the depth of the loop scope.
    pub fn emit_rc_cleanup_from_depth(&mut self, target_depth: usize) -> CodegenResult<()> {
        let locals: Vec<_> = self
            .rc_scopes
            .locals_from_depth(target_depth)
            .copied()
            .collect();
        let composites: Vec<_> = self
            .rc_scopes
            .composites_from_depth(target_depth)
            .cloned()
            .collect();
        let unions: Vec<_> = self
            .rc_scopes
            .unions_from_depth(target_depth)
            .cloned()
            .collect();
        self.emit_rc_cleanup_for_collections(&locals, &composites, &unions, None)
    }

    /// Emit RC cleanup for a collection of locals, composites, and unions.
    ///
    /// This is the centralized helper for all RC cleanup scenarios. The cleanup
    /// ordering is critical: unions must be cleaned up first, before locals and
    /// composites. This is because union payloads may reference values owned by
    /// containers (arrays, classes) tracked as regular RC locals. Decrementing
    /// the union payload before the container prevents use-after-free when the
    /// container's drop cascades to free the same value.
    ///
    /// `skip_var` optionally specifies a variable whose ownership is being
    /// transferred out (e.g., the block/function result) and should NOT be dec'd.
    fn emit_rc_cleanup_for_collections(
        &mut self,
        locals: &[super::rc_cleanup::RcLocal],
        composites: &[super::rc_cleanup::CompositeRcLocal],
        unions: &[super::rc_cleanup::UnionRcLocal],
        skip_var: Option<Variable>,
    ) -> CodegenResult<()> {
        let has_work = !locals.is_empty() || !composites.is_empty() || !unions.is_empty();
        if !has_work {
            return Ok(());
        }

        let rc_dec_ref = self.runtime_func_ref(RuntimeKey::RcDec)?;

        // 1. Unions first: payloads may reference container-owned values.
        super::rc_cleanup::emit_union_rc_cleanup(self.builder, unions, rc_dec_ref, skip_var);

        // 2. Locals.
        super::rc_cleanup::emit_rc_cleanup(self.builder, locals, rc_dec_ref, skip_var);

        // 3. Composites last.
        super::rc_cleanup::emit_composite_rc_cleanup(
            self.builder,
            composites,
            rc_dec_ref,
            skip_var,
        );

        Ok(())
    }

    /// Emit rc_inc(value) to increment the reference count.
    /// Used when creating a new reference to an existing RC value.
    #[inline]
    pub fn emit_rc_inc(&mut self, value: Value) -> CodegenResult<()> {
        self.call_runtime_void(RuntimeKey::RcInc, &[value])
    }

    /// Emit rc_inc for a value, handling interface fat pointers by loading the
    /// data word at offset 0 before incrementing.
    pub fn emit_rc_inc_for_type(&mut self, value: Value, type_id: TypeId) -> CodegenResult<()> {
        self.emit_rc_op_for_type(value, type_id, RuntimeKey::RcInc)
    }

    /// Increment RC for a borrowed value being stored into a container.
    ///
    /// When placing a borrowed value into an array, tuple, or similar container,
    /// the container needs its own reference. Without this, the element's original
    /// binding and the container would share a single refcount, causing double-free
    /// on scope exit.
    ///
    /// After calling this, the caller should store the value and then call
    /// `compiled.mark_consumed()` to indicate the value has been transferred
    /// to the container.
    pub fn rc_inc_borrowed_for_container(&mut self, compiled: &CompiledValue) -> CodegenResult<()> {
        if self.rc_scopes.has_active_scope()
            && self.rc_state(compiled.type_id).needs_cleanup()
            && compiled.is_borrowed()
        {
            self.emit_rc_inc_for_type(compiled.value, compiled.type_id)?;
        }
        Ok(())
    }

    /// Emit rc_inc for the RC payload inside a union value.
    ///
    /// Loads the tag, checks each RC variant, and rc_inc's the payload at
    /// offset 8 for the matching variant. For interface variants, loads the
    /// data word at offset 0 of the payload before inc'ing.
    pub fn emit_union_rc_inc(
        &mut self,
        union_ptr: Value,
        rc_tags: &[(u8, bool)],
    ) -> CodegenResult<()> {
        self.emit_union_rc_op(union_ptr, rc_tags, RuntimeKey::RcInc)
    }

    /// Emit rc_dec for the RC payload of a union value, based on its current tag.
    /// For each RC variant, checks if the tag matches and rc_dec's the payload.
    /// Used when a union variable is reassigned (to clean up the old value).
    pub fn emit_union_rc_dec(
        &mut self,
        union_ptr: Value,
        rc_tags: &[(u8, bool)],
    ) -> CodegenResult<()> {
        self.emit_union_rc_op(union_ptr, rc_tags, RuntimeKey::RcDec)
    }

    /// Shared implementation for `emit_union_rc_inc` and `emit_union_rc_dec`.
    ///
    /// Loads the tag, checks each RC variant, and applies the given `rc_fn`
    /// to the payload at offset 8 for the matching variant. For interface
    /// variants, loads the data word at offset 0 of the payload first.
    fn emit_union_rc_op(
        &mut self,
        union_ptr: Value,
        rc_tags: &[(u8, bool)],
        rc_fn: RuntimeKey,
    ) -> CodegenResult<()> {
        let tag = self
            .builder
            .ins()
            .load(types::I8, MemFlags::new(), union_ptr, 0);
        let rc_fn_ref = self.runtime_func_ref(rc_fn)?;

        for &(variant_tag, is_interface) in rc_tags {
            let is_match = self
                .builder
                .ins()
                .icmp_imm(IntCC::Equal, tag, variant_tag as i64);
            let op_block = self.builder.create_block();
            let next_block = self.builder.create_block();

            self.emit_brif(is_match, op_block, next_block);

            self.switch_to_block(op_block);
            self.builder.seal_block(op_block);
            let payload = self.builder.ins().load(
                types::I64,
                MemFlags::new(),
                union_ptr,
                union_layout::PAYLOAD_OFFSET,
            );
            if is_interface {
                let data_word = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), payload, 0);
                self.builder.ins().call(rc_fn_ref, &[data_word]);
            } else {
                self.builder.ins().call(rc_fn_ref, &[payload]);
            }
            self.builder.ins().jump(next_block, &[]);

            self.switch_to_block(next_block);
            self.builder.seal_block(next_block);
        }
        Ok(())
    }

    /// Shared implementation for `emit_rc_inc_for_type` and `emit_rc_dec_for_type`.
    ///
    /// For interface types, loads the data word at offset 0 before applying
    /// the given `rc_fn`. For other types, applies `rc_fn` directly.
    fn emit_rc_op_for_type(
        &mut self,
        value: Value,
        type_id: TypeId,
        rc_fn: RuntimeKey,
    ) -> CodegenResult<()> {
        if self.arena().is_interface(type_id) {
            let data_word = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), value, 0);
            self.call_runtime_void(rc_fn, &[data_word])
        } else {
            self.call_runtime_void(rc_fn, &[value])
        }
    }

    /// Emit rc_dec(value) to decrement the reference count.
    /// Used when destroying a reference (e.g., reassignment).
    #[inline]
    pub fn emit_rc_dec(&mut self, value: Value) -> CodegenResult<()> {
        self.call_runtime_void(RuntimeKey::RcDec, &[value])
    }

    /// Emit rc_dec for a value, handling interface fat pointers by loading the
    /// data word at offset 0 before decrementing.
    pub fn emit_rc_dec_for_type(&mut self, value: Value, type_id: TypeId) -> CodegenResult<()> {
        self.emit_rc_op_for_type(value, type_id, RuntimeKey::RcDec)
    }

    /// Emit rc_dec for an owned RC value and mark it as consumed.
    /// No-op if the value is not Owned (Borrowed, Consumed, or Untracked).
    /// For interface types, extracts the data word before decrementing.
    pub fn consume_rc_value(&mut self, cv: &mut CompiledValue) -> CodegenResult<()> {
        if cv.is_owned() {
            if self.rc_state(cv.type_id).needs_cleanup() {
                self.emit_rc_dec_for_type(cv.value, cv.type_id)?;
            } else if let Some(rc_tags) = self.rc_state(cv.type_id).union_variants() {
                self.emit_union_rc_dec(cv.value, rc_tags)?;
            }
            cv.mark_consumed();
        } else if cv.is_borrowed() {
            // Borrowed values don't need RC decrement — they reference an
            // existing binding whose scope handles cleanup.  Just mark
            // consumed so the lifecycle assertion passes.
            cv.mark_consumed();
        }
        Ok(())
    }

    /// Consume all tracked RC values in a slice.
    pub fn consume_rc_args(&mut self, args: &mut [CompiledValue]) -> CodegenResult<()> {
        for cv in args.iter_mut() {
            self.consume_rc_value(cv)?;
        }
        Ok(())
    }

    /// Register an RC local in the current scope. Allocates a drop flag,
    /// initializes it to 0, and adds it to the current scope.
    /// Returns the drop flag Variable so the caller can set it to 1 after assignment.
    pub fn register_rc_local(&mut self, variable: Variable, type_id: TypeId) -> Variable {
        let drop_flag = super::rc_cleanup::alloc_drop_flag(self.builder);
        let is_interface = self.arena().is_interface(type_id);
        self.rc_scopes
            .register_rc_local(variable, drop_flag, type_id, is_interface);
        drop_flag
    }

    /// Register a composite RC local (struct/fixed-array/tuple with RC fields)
    /// in the current scope. Returns the drop flag Variable.
    pub fn register_composite_rc_local(
        &mut self,
        variable: Variable,
        rc_field_offsets: Vec<i32>,
    ) -> Variable {
        let drop_flag = super::rc_cleanup::alloc_drop_flag(self.builder);
        self.rc_scopes
            .register_composite(variable, drop_flag, rc_field_offsets);
        drop_flag
    }

    /// Register a union RC local in the current scope. Returns the drop flag Variable.
    pub fn register_union_rc_local(
        &mut self,
        variable: Variable,
        rc_variant_tags: Vec<(u8, bool)>,
    ) -> Variable {
        let drop_flag = super::rc_cleanup::alloc_drop_flag(self.builder);
        self.rc_scopes
            .register_union(variable, drop_flag, rc_variant_tags);
        drop_flag
    }

    /// Get the current RC scope depth (for break/continue target tracking).
    pub fn rc_scope_depth(&self) -> usize {
        self.rc_scopes.depth()
    }

    // ========== RC state queries ==========

    /// Get the RC state for a type. Results are cached.
    ///
    /// Returns information about how this type handles reference counting:
    /// - `RcState::None`: Type does not need RC cleanup
    /// - `RcState::Simple`: Direct RC type (String, Array, closure, etc.)
    /// - `RcState::Composite`: Struct/tuple with RC fields
    /// - `RcState::Union`: Union with some RC variants
    ///
    pub fn rc_state(&self, type_id: TypeId) -> RcState {
        // Check cache first
        if let Some(state) = self.rc_state_cache.borrow().get(&type_id) {
            return state.clone();
        }
        // Compute and cache
        let state = compute_rc_state(self.arena(), self.registry(), type_id);
        self.rc_state_cache
            .borrow_mut()
            .insert(type_id, state.clone());
        state
    }

    /// Get the field type tag for a type, determining how instance fields of this
    /// type should be cleaned up. Interface types get `FieldTypeTag::Interface`,
    /// other RC types get `FieldTypeTag::Rc`, union types that contain RC variants
    /// get `FieldTypeTag::UnionHeap`, everything else is `Value`.
    pub fn field_type_tag(&self, type_id: TypeId) -> vole_runtime::type_registry::FieldTypeTag {
        use vole_runtime::type_registry::FieldTypeTag;
        if self.arena().is_interface(type_id) {
            FieldTypeTag::Interface
        } else if self.rc_state(type_id).needs_cleanup() {
            FieldTypeTag::Rc
        } else if let Some(variants) = self.arena().unwrap_union(type_id) {
            for &variant in variants {
                if self.rc_state(variant).needs_cleanup() {
                    return FieldTypeTag::UnionHeap;
                }
            }
            FieldTypeTag::Value
        } else {
            FieldTypeTag::Value
        }
    }

    /// Mark a CompiledValue as owned if its type needs RC cleanup.
    /// Use this for fresh allocations (function returns, operator results) — NOT for
    /// borrowed values (variable reads, field access, index operations).
    pub fn mark_rc_owned(&self, mut cv: CompiledValue) -> CompiledValue {
        if self.rc_state(cv.type_id).needs_cleanup() {
            cv.rc_lifecycle = RcLifecycle::Owned;
        }
        cv
    }

    /// Mark a CompiledValue as borrowed if its type is RC-managed, is a union
    /// with RC variants, or is a composite type (tuple, fixed array, struct)
    /// with RC fields.
    /// This sets lifecycle metadata without emitting any rc_inc/rc_dec.
    pub fn mark_borrowed_if_rc(&self, cv: &mut CompiledValue) {
        let state = self.rc_state(cv.type_id);
        if state.needs_cleanup()
            || state.union_variants().is_some()
            || state.shallow_offsets().is_some()
        {
            cv.mark_borrowed();
        }
    }
}
