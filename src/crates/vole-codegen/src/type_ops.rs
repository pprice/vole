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
use super::types::CompiledValue;

/// Pre-computed metadata for optional types (nil position + inner type).
///
/// Cached per `VirTypeId` to avoid repeated `find_nil_variant_vir()` and
/// `vir_query_unwrap_optional_v()` calls during optional comparison, coalescing,
/// and chaining codegen.
#[derive(Clone, Copy, Debug)]
pub(crate) struct OptionalMeta {
    /// Index of the nil variant in the union's variant list (the nil tag value).
    pub nil_position: usize,
    /// VirTypeId of the non-nil inner type.
    pub inner_type: VirTypeId,
}

impl<'a, 'b, 'ctx> Cg<'a, 'b, 'ctx> {
    // ========== Type context & substitution ==========

    /// Substitute type parameters using current substitutions (TypeId level).
    ///
    /// Derives a sema `TypeId` substitution map from the VirTypeId-native
    /// `self.substitutions` and delegates to `vir_query_expect_substitute`.
    #[inline]
    pub fn substitute_type(&self, ty: TypeId) -> TypeId {
        if let Some(sema_subs) = self.sema_substitutions() {
            // Check cache first
            if let Some(&cached) = self.substitution_cache.borrow().get(&ty) {
                return cached;
            }
            let result = self.vir_query_expect_substitute(ty, &sema_subs, "Cg::substitute_type");
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
        if let Some(sema_subs) = self.sema_substitutions() {
            // Check cache first
            if let Some(&cached) = self.substitution_cache.borrow().get(&ty) {
                return cached;
            }
            if let Some(result) = self.vir_query_lookup_substitute(ty, &sema_subs) {
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

    /// VIR-native substitution: try to substitute a `VirTypeId`, returning
    /// the original if no substitution applies or the result is not interned.
    ///
    /// Also substitutes `VirTypeId::UNKNOWN` with `self_vir_type` when set
    /// (interface default method bodies where `Self` lowered to UNKNOWN).
    pub fn try_substitute_type_v(&self, vir_ty: VirTypeId) -> VirTypeId {
        // Self placeholder: UNKNOWN → concrete self type in default method bodies.
        if vir_ty == VirTypeId::UNKNOWN
            && let Some(self_ty) = self.self_vir_type
        {
            return self_ty;
        }
        if let Some(substitutions) = self.substitutions {
            self.vir_type_table()
                .substitute_vir_ids(vir_ty, substitutions)
                .unwrap_or(vir_ty)
        } else {
            vir_ty
        }
    }

    // ========== Cranelift type mapping ==========

    /// Convert a TypeId to a Cranelift type
    pub fn cranelift_type(&self, ty: TypeId) -> Type {
        self.vir_query_type_to_cranelift(ty)
    }

    /// Convert a `VirTypeId` to a Cranelift type via the VIR type table.
    pub fn cranelift_type_v(&self, vir_ty: VirTypeId) -> Type {
        self.vir_query_type_to_cranelift_v(vir_ty)
    }

    /// Convert a slice of TypeIds to Cranelift types
    pub fn cranelift_types(&self, type_ids: &[TypeId]) -> Vec<Type> {
        type_ids
            .iter()
            .map(|&ty| self.vir_query_type_to_cranelift(ty))
            .collect()
    }

    /// Get the size (in bytes) of a TypeId.
    pub fn type_size(&self, ty: TypeId) -> u32 {
        self.type_size_v(self.vir_lookup(ty))
    }

    /// Get the size (in bytes) of a `VirTypeId` via the VIR type table.
    pub fn type_size_v(&self, vir_ty: VirTypeId) -> u32 {
        super::types::vir_conversions::vir_type_id_size(
            vir_ty,
            self.ptr_type(),
            self.analyzed(),
            self.vir_type_table(),
        )
    }

    /// Compute the memory layout for a tuple type from `VirTypeId` elements.
    ///
    /// Returns (total_size_bytes, per_element_byte_offsets).
    pub fn tuple_layout_v(&self, elems: &[VirTypeId]) -> (u32, Vec<i32>) {
        super::types::vir_conversions::vir_tuple_layout(
            elems,
            self.ptr_type(),
            self.analyzed(),
            self.vir_type_table(),
        )
    }

    /// Convert a typed value to its word (i64) representation for generic dispatch.
    ///
    /// Wrapper around `vir_value_to_word` that internalizes ptr_type/analyzed/table
    /// parameters for call sites.
    pub fn emit_word(
        &mut self,
        compiled: &CompiledValue,
        heap_alloc_ref: Option<FuncRef>,
    ) -> crate::errors::CodegenResult<Value> {
        let ptr_type = self.codegen_ctx.ptr_type();
        let analyzed = self.env.analyzed;
        let table = &self.env.analyzed.type_table;
        super::types::vir_conversions::vir_value_to_word(
            self.builder,
            compiled,
            ptr_type,
            heap_alloc_ref,
            analyzed,
            table,
        )
    }

    /// Convert an i64 value back to its proper type (reverse of convert_to_i64_for_storage)
    pub fn convert_from_i64_storage(&mut self, word: Value, type_id: TypeId) -> Value {
        self.convert_from_i64_storage_v(word, self.vir_lookup(type_id))
    }

    /// VirTypeId variant: convert a value from i64 storage representation.
    pub fn convert_from_i64_storage_v(&mut self, word: Value, vir_ty: VirTypeId) -> Value {
        let ptr_type = self.codegen_ctx.ptr_type();
        let analyzed = self.env.analyzed;
        let table = &self.env.analyzed.type_table;
        super::types::vir_conversions::vir_word_to_value(
            self.builder,
            word,
            vir_ty,
            ptr_type,
            analyzed,
            table,
        )
    }

    // ========== Type resolution ==========

    /// Find the nil variant index in a union (for optional handling).
    ///
    /// Uses the VirTypeId path when available for correct variant ordering.
    /// The round-tripped sema TypeId from `cv_type_id()` can have reversed
    /// variant order because `arena.lookup_optional()` non-deterministically
    /// picks among interned unions.
    pub fn find_nil_variant_vir(&self, vir_ty: VirTypeId) -> Option<usize> {
        use vole_vir::types::VirType;

        let table = self.vir_type_table();
        if vir_ty != VirTypeId::UNKNOWN && (vir_ty.raw() as usize) < table.len() {
            match table.get(vir_ty) {
                VirType::Optional { inner } => {
                    let variants = table.expand_optional_variants(*inner);
                    return variants.iter().position(|&id| id == VirTypeId::NIL);
                }
                VirType::Union { variants } => {
                    return variants.iter().position(|&id| id == VirTypeId::NIL);
                }
                _ => {}
            }
        }

        // Fallback to sema TypeId path (reverse lookup)
        let sema_ty = self.vir_type_table().vir_to_type_id(vir_ty);
        self.find_nil_variant(sema_ty)
    }

    /// Find the nil variant index using a sema TypeId directly.
    pub fn find_nil_variant(&self, ty: TypeId) -> Option<usize> {
        if let Some(variants) = self.vir_query_unwrap_union(ty) {
            variants.iter().position(|&id| id.is_nil())
        } else {
            None
        }
    }

    /// Cached lookup of optional metadata (nil position + inner type).
    ///
    /// Returns `Some(OptionalMeta)` when `vir_ty` is an optional (or union
    /// containing nil).  The result is cached per `VirTypeId` since VirTypeTable
    /// is immutable during codegen.
    pub fn cached_optional_meta(&self, vir_ty: VirTypeId) -> Option<OptionalMeta> {
        if let Some(cached) = self.optional_meta_cache.borrow().get(&vir_ty) {
            return Some(*cached);
        }
        let nil_position = self.find_nil_variant_vir(vir_ty)?;
        let inner_type = self
            .vir_query_unwrap_optional_v(vir_ty)
            .unwrap_or(VirTypeId::I64);
        let meta = OptionalMeta {
            nil_position,
            inner_type,
        };
        self.optional_meta_cache.borrow_mut().insert(vir_ty, meta);
        Some(meta)
    }

    /// Unwrap an interface `VirTypeId`, returning the `TypeDefId` if it is one.
    pub fn interface_type_def_id_v(&self, vir_ty: VirTypeId) -> Option<TypeDefId> {
        self.vir_query_unwrap_interface_v(vir_ty).map(|(id, _)| id)
    }

    // ========== Union array storage policy ==========

    /// Returns true when a union array can be stored inline as (runtime_tag, payload)
    /// without losing variant identity.
    ///
    /// If two variants map to the same runtime tag (e.g. `i64 | nil` -> RuntimeTypeId::I64),
    /// inline storage cannot recover the original union variant on read, so we must
    /// fall back to heap-boxed union buffers.
    pub fn union_array_prefers_inline_storage(&self, union_type_id: TypeId) -> bool {
        let resolved_union_id = self.try_substitute_type(union_type_id);
        let vir_ty = self.vir_lookup(resolved_union_id);
        self.union_array_prefers_inline_storage_v(vir_ty)
    }

    /// Returns true when a union array can be stored inline as (runtime_tag, payload)
    /// without losing variant identity.
    ///
    /// VirTypeId types are post-monomorphization, so no substitution is needed.
    pub fn union_array_prefers_inline_storage_v(&self, vir_ty: VirTypeId) -> bool {
        use rustc_hash::FxHashSet;
        use vole_runtime::value::RuntimeTypeId;

        let Some(variants) = self.vir_query_unwrap_union_v(vir_ty) else {
            return false;
        };

        let mut seen_tags: FxHashSet<u64> = FxHashSet::default();
        for &variant in &variants {
            if !self.supports_inline_union_array_variant_v(variant) {
                return false;
            }

            let tag = self.vir_query_unknown_type_tag_v(variant);
            if tag == RuntimeTypeId::I64 as u64
                && !self.vir_query_is_integer_v(variant)
                && !self.vir_query_is_sentinel_v(variant)
            {
                return false;
            }
            if !seen_tags.insert(tag) {
                return false;
            }
        }
        true
    }

    fn supports_inline_union_array_variant_v(&self, variant: VirTypeId) -> bool {
        !(self.vir_query_is_union_v(variant)
            || self.vir_query_is_interface_v(variant)
            || self.vir_query_is_class_v(variant)
            || self.vir_query_is_struct_v(variant)
            || self.vir_query_is_unknown_v(variant)
            || self.vir_query_unwrap_tuple_v(variant).is_some()
            || self.vir_query_unwrap_fallible_v(variant).is_some()
            || self.vir_query_unwrap_type_param_v(variant).is_some())
    }

    pub(crate) fn union_variant_index_to_array_tag_v(
        &mut self,
        variant_idx: Value,
        variants: &[VirTypeId],
    ) -> Value {
        let variant_tags: Vec<i64> = variants
            .iter()
            .map(|&v| self.vir_query_array_element_tag_id_v(v))
            .collect();
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

    pub(crate) fn array_tag_to_union_variant_index_v(
        &mut self,
        array_tag: Value,
        variants: &[VirTypeId],
    ) -> Value {
        let variant_tags: Vec<i64> = variants
            .iter()
            .map(|&v| self.vir_query_array_element_tag_id_v(v))
            .collect();
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
