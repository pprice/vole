// src/codegen/type_ops.rs
//
// Type-related methods - impl Cg methods for type resolution, conversion,
// and layout queries.
//
// Handles type substitution, Cranelift type mapping, union array storage
// policy, type resolution, and error type lookup. Split from context.rs.

use cranelift::prelude::{InstBuilder, IntCC, Type, Value, types};
use cranelift_codegen::ir::FuncRef;

use vole_identity::{TypeDefId, TypeId, VirTypeId};

use super::context::Cg;
use super::types::{CompiledValue, type_id_size, type_id_to_cranelift, value_to_word};

impl<'a, 'b, 'ctx> Cg<'a, 'b, 'ctx> {
    // ========== Type context & substitution ==========

    /// Substitute type parameters using current substitutions
    ///
    /// Uses expect_substitute for read-only lookup since sema pre-computes all
    /// substituted types when creating MonomorphInstance.
    #[inline]
    pub fn substitute_type(&self, ty: TypeId) -> TypeId {
        if let Some(substitutions) = self.substitutions {
            // Check cache first
            if let Some(&cached) = self.substitution_cache.borrow().get(&ty) {
                return cached;
            }
            let result = self.vir_query_expect_substitute(ty, substitutions, "Cg::substitute_type");
            // Cache the result
            self.substitution_cache.borrow_mut().insert(ty, result);
            result
        } else {
            ty
        }
    }

    /// Try to substitute a type, returning the original if substitution fails.
    /// This is a best-effort version that doesn't panic if the substituted type
    /// doesn't exist in the arena.
    pub fn try_substitute_type(&self, ty: TypeId) -> TypeId {
        if let Some(substitutions) = self.substitutions {
            // Check cache first
            if let Some(&cached) = self.substitution_cache.borrow().get(&ty) {
                return cached;
            }
            if let Some(result) = self.vir_query_lookup_substitute(ty, substitutions) {
                self.substitution_cache.borrow_mut().insert(ty, result);
                result
            } else {
                // Substituted type doesn't exist in arena; return original
                ty
            }
        } else {
            ty
        }
    }

    // ========== Cranelift type mapping ==========

    /// Convert a TypeId to a Cranelift type
    pub fn cranelift_type(&self, ty: TypeId) -> Type {
        self.vir_query_type_to_cranelift(ty)
    }

    /// Convert a `VirTypeId` to a Cranelift type via the VIR type table.
    #[allow(dead_code)] // Convenience for downstream VIR migration tickets.
    pub fn vir_cranelift_type(&self, vir_ty: VirTypeId) -> Type {
        super::types::vir_conversions::vir_type_to_cranelift(
            vir_ty,
            self.vir_type_table(),
            self.ptr_type(),
        )
    }

    /// Temporary bridge from `VirTypeId` to sema `TypeId` for legacy code paths.
    #[inline]
    pub fn sema_type_from_vir(&self, vir_ty: VirTypeId) -> TypeId {
        let sema_ty = super::types::vir_conversions::vir_to_sema_type_id(
            vir_ty,
            self.vir_type_table(),
            self.arena(),
        );
        self.try_substitute_type(sema_ty)
    }

    /// Convert a slice of TypeIds to Cranelift types
    pub fn cranelift_types(&self, type_ids: &[TypeId]) -> Vec<Type> {
        let arena = self.arena();
        type_ids
            .iter()
            .map(|&ty| type_id_to_cranelift(ty, arena, self.ptr_type()))
            .collect()
    }

    /// Get the size (in bits) of a TypeId
    pub fn type_size(&self, ty: TypeId) -> u32 {
        type_id_size(ty, self.ptr_type(), self.analyzed(), self.arena())
    }

    /// Compute the memory layout for a tuple type.
    ///
    /// Returns (total_size_bytes, per_element_byte_offsets).
    pub fn tuple_layout(&self, elem_type_ids: &[TypeId]) -> (u32, Vec<i32>) {
        super::types::tuple_layout_id(
            elem_type_ids,
            self.ptr_type(),
            self.analyzed(),
            self.arena(),
        )
    }

    /// Convert a typed value to its word (i64) representation for generic dispatch.
    ///
    /// Wrapper around `value_to_word` that internalizes ptr_type/analyzed/arena
    /// parameters for call sites.
    pub fn emit_word(
        &mut self,
        compiled: &CompiledValue,
        heap_alloc_ref: Option<FuncRef>,
    ) -> crate::errors::CodegenResult<Value> {
        let ptr_type = self.ptr_type();
        let analyzed = self.analyzed();
        let arena = self.arena();
        value_to_word(
            self.builder,
            compiled,
            ptr_type,
            heap_alloc_ref,
            arena,
            analyzed,
        )
    }

    /// Convert an i64 value back to its proper type (reverse of convert_to_i64_for_storage)
    pub fn convert_from_i64_storage(&mut self, word: Value, type_id: TypeId) -> Value {
        use super::types::word_to_value_type_id;
        let ptr_type = self.ptr_type();
        let analyzed = self.analyzed();
        let arena = self.arena();
        word_to_value_type_id(self.builder, word, type_id, ptr_type, analyzed, arena)
    }

    // ========== Type resolution ==========

    /// Find the nil variant index in a union (for optional handling)
    pub fn find_nil_variant(&self, ty: TypeId) -> Option<usize> {
        if let Some(variants) = self.vir_query_unwrap_union(ty) {
            variants.iter().position(|&id| id.is_nil())
        } else {
            None
        }
    }

    /// Unwrap an interface type, returning the TypeDefId if it is one
    pub fn interface_type_def_id(&self, ty: TypeId) -> Option<TypeDefId> {
        self.vir_query_unwrap_interface(ty).map(|(id, _)| id)
    }

    // ========== Union array storage policy ==========

    /// Returns true when a union array can be stored inline as (runtime_tag, payload)
    /// without losing variant identity.
    ///
    /// If two variants map to the same runtime tag (e.g. `i64 | nil` -> RuntimeTypeId::I64),
    /// inline storage cannot recover the original union variant on read, so we must
    /// fall back to heap-boxed union buffers.
    pub fn union_array_prefers_inline_storage(&self, union_type_id: TypeId) -> bool {
        use rustc_hash::FxHashSet;
        use vole_runtime::value::RuntimeTypeId;

        let resolved_union_id = self.try_substitute_type(union_type_id);
        let Some(variants) = self.vir_query_unwrap_union(resolved_union_id) else {
            return false;
        };

        let mut seen_tags: FxHashSet<u64> = FxHashSet::default();
        for &variant in &variants {
            if !self.supports_inline_union_array_variant(variant) {
                return false;
            }

            let tag = self.vir_query_unknown_type_tag(variant);
            if tag == RuntimeTypeId::I64 as u64
                && !self.vir_query_is_integer(variant)
                && !self.vir_query_is_sentinel(variant)
            {
                return false;
            }
            if !seen_tags.insert(tag) {
                return false;
            }
        }
        true
    }

    fn supports_inline_union_array_variant(&self, variant: TypeId) -> bool {
        // Codegen/runtime layout policy: inline union array slots store only
        // (runtime_tag, payload_bits), so variants that need richer tagging or
        // heap-backed payload wrappers must use boxed union storage.
        !(self.vir_query_is_union(variant)
            || self.vir_query_is_interface(variant)
            || self.vir_query_is_class(variant)
            || self.vir_query_is_struct(variant)
            || self.vir_query_is_unknown(variant)
            || self.vir_query_unwrap_tuple(variant).is_some()
            || self.vir_query_unwrap_fallible(variant).is_some()
            || self.vir_query_unwrap_type_param(variant).is_some())
    }

    pub(crate) fn union_variant_index_to_array_tag(
        &mut self,
        variant_idx: Value,
        variants: &[TypeId],
    ) -> Value {
        let variant_tags: Vec<i64> = {
            let arena = self.arena();
            variants
                .iter()
                .map(|&variant| crate::types::array_element_tag_id(variant, arena))
                .collect()
        };
        let default_tag = variant_tags[0];
        let mut runtime_tag = self.iconst_cached(types::I64, default_tag);

        for (idx, &tag) in variant_tags.iter().enumerate().skip(1) {
            let idx_val = self.iconst_cached(types::I8, idx as i64);
            let is_match = self.builder.ins().icmp(IntCC::Equal, variant_idx, idx_val);
            let tag_val = self.iconst_cached(types::I64, tag);
            runtime_tag = self.builder.ins().select(is_match, tag_val, runtime_tag);
        }

        runtime_tag
    }

    pub(crate) fn array_tag_to_union_variant_index(
        &mut self,
        array_tag: Value,
        variants: &[TypeId],
    ) -> Value {
        let variant_tags: Vec<i64> = {
            let arena = self.arena();
            variants
                .iter()
                .map(|&variant| crate::types::array_element_tag_id(variant, arena))
                .collect()
        };
        let mut variant_idx = self.iconst_cached(types::I8, 0);
        let first_match = self
            .builder
            .ins()
            .icmp_imm(IntCC::Equal, array_tag, variant_tags[0]);
        let mut matched_any = first_match;

        for (idx, &runtime_tag) in variant_tags.iter().enumerate().skip(1) {
            let is_match = self
                .builder
                .ins()
                .icmp_imm(IntCC::Equal, array_tag, runtime_tag);
            let idx_val = self.iconst_cached(types::I8, idx as i64);
            variant_idx = self.builder.ins().select(is_match, idx_val, variant_idx);
            matched_any = self.builder.ins().bor(matched_any, is_match);
        }

        // Strict contract: unknown tags are a hard runtime fault.
        self.builder
            .ins()
            .trapz(matched_any, crate::trap_codes::PANIC);

        variant_idx
    }
}
