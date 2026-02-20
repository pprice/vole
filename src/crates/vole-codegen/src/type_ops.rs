// src/codegen/type_ops.rs
//
// Type-related methods - impl Cg methods for type resolution, conversion,
// and layout queries.
//
// Handles type substitution, Cranelift type mapping, union array storage
// policy, type resolution, and error type lookup. Split from context.rs.

use cranelift::prelude::{InstBuilder, IntCC, Type, Value, types};

use vole_frontend::Symbol;
use vole_identity::TypeDefId;
use vole_sema::implement_registry::ImplTypeId;
use vole_sema::type_arena::TypeId;

use super::context::Cg;
use super::types::{type_id_size, type_id_to_cranelift};

impl<'a, 'b, 'ctx> Cg<'a, 'b, 'ctx> {
    // ========== Type context & substitution ==========

    /// Get a TypeCtx view
    #[inline]
    pub fn type_ctx(&self) -> super::types::TypeCtx<'_> {
        super::types::TypeCtx::new(self.env.analyzed.query(), self.codegen_ctx.ptr_type())
    }

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
            let arena = self.arena();
            let result = arena.expect_substitute(ty, substitutions, "Cg::substitute_type");
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
            let arena = self.arena();
            if let Some(result) = arena.lookup_substitute(ty, substitutions) {
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
        type_id_to_cranelift(ty, self.arena(), self.ptr_type())
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
        type_id_size(ty, self.ptr_type(), self.registry(), self.arena())
    }

    /// Convert a TypeId to an ImplTypeId if the type supports implementation blocks.
    ///
    /// Wrapper around `ImplTypeId::from_type_id` that internalizes the registry/arena
    /// lookups, keeping call sites free of self.registry() passes.
    pub fn impl_type_id_for(&self, ty: TypeId) -> Option<ImplTypeId> {
        ImplTypeId::from_type_id(ty, self.arena(), self.registry())
    }

    /// Convert an i64 value back to its proper type (reverse of convert_to_i64_for_storage)
    pub fn convert_from_i64_storage(&mut self, word: Value, type_id: TypeId) -> Value {
        use super::types::word_to_value_type_id;
        let ptr_type = self.ptr_type();
        let registry = self.registry();
        let arena = self.arena();
        word_to_value_type_id(self.builder, word, type_id, ptr_type, registry, arena)
    }

    // ========== Type resolution ==========

    /// Find the nil variant index in a union (for optional handling)
    pub fn find_nil_variant(&self, ty: TypeId) -> Option<usize> {
        let arena = self.arena();
        if let Some(variants) = arena.unwrap_union(ty) {
            variants.iter().position(|&id| id.is_nil())
        } else {
            None
        }
    }

    /// Unwrap an interface type, returning the TypeDefId if it is one
    pub fn interface_type_def_id(&self, ty: TypeId) -> Option<TypeDefId> {
        self.arena().unwrap_interface(ty).map(|(id, _)| id)
    }

    /// Resolve a type name Symbol to its TypeDefId using the full resolution chain.
    ///
    /// This uses the same resolution path as sema: primitives, current module,
    /// imports, builtin module, and interface/class fallback.
    /// Note: We convert the Symbol to string first because the current interner
    /// may be module-specific while the query uses the main program's interner.
    pub fn resolve_type(&self, sym: Symbol) -> Option<TypeDefId> {
        self.resolve_type_str_or_interface(self.interner().resolve(sym))
    }

    /// Resolve a type name string to its TypeDefId using the full resolution chain.
    ///
    /// This uses the same resolution path as sema: primitives, current module,
    /// imports, builtin module, and interface/class fallback.
    pub fn resolve_type_str_or_interface(&self, name: &str) -> Option<TypeDefId> {
        let query = self.query();
        let module_id = self
            .current_module_id()
            .unwrap_or(self.env.analyzed.module_id);
        query.resolve_type_def_by_str(module_id, name)
    }

    /// Find an error type in a union by its short name.
    ///
    /// Used to resolve error types from imported modules when matching
    /// fallible error patterns (e.g., `error NotFound { path: p }`).
    pub fn find_error_type_in_union(
        &self,
        error_union_id: TypeId,
        name: &str,
    ) -> Option<TypeDefId> {
        let arena = self.arena();
        let name_table = self.name_table();
        let registry = self.registry();

        let check_variant = |type_def_id: TypeDefId| -> bool {
            name_table
                .last_segment_str(registry.name_id(type_def_id))
                .is_some_and(|seg| seg == name)
        };

        // Check single error type
        if let Some(type_def_id) = arena.unwrap_error(error_union_id)
            && check_variant(type_def_id)
        {
            return Some(type_def_id);
        }

        // Check union variants
        if let Some(variants) = arena.unwrap_union(error_union_id) {
            for &variant in variants {
                if let Some(type_def_id) = arena.unwrap_error(variant)
                    && check_variant(type_def_id)
                {
                    return Some(type_def_id);
                }
            }
        }

        None
    }

    // ========== Union array storage policy ==========

    /// Returns true when a union array can be stored inline as (runtime_tag, payload)
    /// without losing variant identity.
    ///
    /// If two variants map to the same runtime tag (e.g. `i64 | nil` -> RuntimeTypeId::I64),
    /// inline storage cannot recover the original union variant on read, so we must
    /// fall back to heap-boxed union buffers.
    pub fn union_array_prefers_inline_storage(&self, union_type_id: TypeId) -> bool {
        use crate::types::unknown_type_tag;
        use rustc_hash::FxHashSet;
        use vole_runtime::value::RuntimeTypeId;

        let resolved_union_id = self.try_substitute_type(union_type_id);
        let Some(variants) = self.arena().unwrap_union(resolved_union_id) else {
            return false;
        };

        let arena = self.arena();
        let mut seen_tags: FxHashSet<u64> = FxHashSet::default();
        for &variant in variants {
            if !self.supports_inline_union_array_variant(variant) {
                return false;
            }

            let tag = unknown_type_tag(variant, arena);
            if tag == RuntimeTypeId::I64 as u64
                && !arena.is_integer(variant)
                && !arena.is_sentinel(variant)
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
        let arena = self.arena();
        // Codegen/runtime layout policy: inline union array slots store only
        // (runtime_tag, payload_bits), so variants that need richer tagging or
        // heap-backed payload wrappers must use boxed union storage.
        !(arena.is_union(variant)
            || arena.is_interface(variant)
            || arena.is_class(variant)
            || arena.is_struct(variant)
            || arena.is_unknown(variant)
            || arena.unwrap_tuple(variant).is_some()
            || arena.unwrap_fallible(variant).is_some()
            || arena.unwrap_type_param(variant).is_some())
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
