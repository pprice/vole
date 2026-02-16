// src/codegen/rc_state.rs
//
// Unified RC state computation for reference-counted types.
//
// This module provides a single enum (RcState) that captures all the different
// ways a type can be reference-counted, along with a compute function that
// analyzes a type once and returns the appropriate state.
//
// All RC queries go through `CodegenContext::rc_state(type_id)` which caches
// the result per TypeId. Accessors on RcState:
// - needs_cleanup() -> bool
// - is_capture() -> bool
// - shallow_offsets() -> Option<&[i32]>
// - deep_offsets() -> Option<&[i32]>
// - union_variants() -> Option<&[(u8, bool)]>

use rustc_hash::FxHashMap;
use vole_sema::entity_registry::EntityRegistry;
use vole_sema::type_arena::{SemaType, TypeArena, TypeId};

/// Reference counting state for a type.
///
/// Each variant captures a distinct RC management strategy:
/// - `None`: Type is not reference-counted (primitives, sentinels, etc.)
/// - `Simple`: Type is directly RC-managed (string, array, function, class, etc.)
/// - `Composite`: Type contains RC fields at specific byte offsets (struct, tuple, fixed array)
/// - `Union`: Type is a union where some variants are RC-managed
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RcState {
    /// Type is not reference-counted.
    None,

    /// Type is a simple RC value (single pointer to RcHeader-managed heap object).
    ///
    /// `is_capture` indicates whether this type qualifies for capture RC management
    /// in closures (string, array, function, class - but not handles or iterators).
    Simple { is_capture: bool },

    /// Type is a composite (struct, tuple, fixed array) with RC fields.
    ///
    /// - `shallow_offsets`: Byte offsets of direct RC fields (one level deep)
    /// - `deep_offsets`: Byte offsets of all RC fields, including nested struct fields
    ///
    /// For non-struct composites (tuple, fixed array), shallow and deep are identical.
    /// For structs with nested struct fields, deep includes offsets within those nested structs.
    Composite {
        shallow_offsets: Vec<i32>,
        deep_offsets: Vec<i32>,
    },

    /// Type is a union with some RC variants.
    ///
    /// Each entry is (tag_index, is_interface) where:
    /// - `tag_index`: The variant's tag byte value (0-255)
    /// - `is_interface`: Whether the variant is an interface type (fat pointer)
    Union { rc_variants: Vec<(u8, bool)> },
}

impl RcState {
    /// Returns true if this type itself requires RC cleanup (rc_inc/rc_dec).
    ///
    /// This returns true ONLY for simple RC types:
    /// - `Simple`: Direct RC types (String, Array, Class, etc.)
    ///
    /// This returns false for:
    /// - `None`: Non-RC types
    /// - `Composite`: Structs/tuples with RC fields (stack-allocated; fields managed individually)
    /// - `Union`: Unions with RC variants (unions themselves are NOT rc_inc/dec'd;
    ///   cleanup of RC variants is handled by union-specific RC cleanup logic)
    #[inline]
    pub fn needs_cleanup(&self) -> bool {
        matches!(self, RcState::Simple { .. })
    }

    /// Returns true if this is a capture-eligible RC type.
    ///
    /// Capture-eligible types are simple RC types (String, Array, Function, Class)
    /// that can be captured by closures with special RC management.
    /// Handles and iterators are RC but not capture-eligible.
    #[inline]
    pub fn is_capture(&self) -> bool {
        matches!(self, RcState::Simple { is_capture: true })
    }

    /// Returns the shallow RC field offsets for composite types.
    ///
    /// Shallow offsets are direct RC fields at the top level of the struct/tuple.
    /// Returns `None` for non-composite types.
    #[inline]
    pub fn shallow_offsets(&self) -> Option<&[i32]> {
        match self {
            RcState::Composite {
                shallow_offsets, ..
            } => Some(shallow_offsets),
            RcState::None | RcState::Simple { .. } | RcState::Union { .. } => None,
        }
    }

    /// Returns the deep RC field offsets for composite types.
    ///
    /// Deep offsets include all RC fields, including those in nested structs.
    /// For non-struct composites (tuple, fixed array), this equals shallow offsets.
    /// Returns `None` for non-composite types.
    #[inline]
    pub fn deep_offsets(&self) -> Option<&[i32]> {
        match self {
            RcState::Composite { deep_offsets, .. } => Some(deep_offsets),
            RcState::None | RcState::Simple { .. } | RcState::Union { .. } => None,
        }
    }

    /// Returns the RC variant information for union types.
    ///
    /// Each entry is (tag_index, is_interface) where:
    /// - `tag_index`: The variant's tag byte value
    /// - `is_interface`: Whether the variant is an interface (fat pointer)
    ///
    /// Returns `None` for non-union types.
    #[inline]
    pub fn union_variants(&self) -> Option<&[(u8, bool)]> {
        match self {
            RcState::Union { rc_variants } => Some(rc_variants),
            RcState::None | RcState::Simple { .. } | RcState::Composite { .. } => None,
        }
    }
}

/// Compute the RC state for a type.
///
/// This is a pure function that analyzes the type structure and returns
/// the appropriate RcState variant. The result can be cached per TypeId.
///
/// # Arguments
/// * `arena` - The type arena for type lookups
/// * `registry` - The entity registry for type definitions (structs, classes, etc.)
/// * `type_id` - The type to analyze
pub fn compute_rc_state(arena: &TypeArena, registry: &EntityRegistry, type_id: TypeId) -> RcState {
    // Check for simple RC types first (most common case for RC values)
    if is_simple_rc_type(arena, type_id) {
        let is_capture = is_capture_rc_type(arena, type_id);
        return RcState::Simple { is_capture };
    }

    // Check for union types with RC variants
    if let Some(variants) = arena.unwrap_union(type_id) {
        let rc_variants = compute_union_rc_variants(arena, variants);
        if !rc_variants.is_empty() {
            return RcState::Union { rc_variants };
        }
        return RcState::None;
    }

    // Check for composite types (struct, tuple, fixed array) with RC fields
    if let Some((shallow_offsets, deep_offsets)) =
        compute_composite_rc_offsets(arena, registry, type_id)
    {
        return RcState::Composite {
            shallow_offsets,
            deep_offsets,
        };
    }

    RcState::None
}

/// Check if a type is a simple RC type (single pointer to RC-managed heap object).
///
/// Simple RC types are those where the runtime representation is a single pointer
/// to an RcHeader-managed allocation. Cleanup involves a single rc_dec call.
fn is_simple_rc_type(arena: &TypeArena, type_id: TypeId) -> bool {
    // Strings: atomic RC values, no child references
    // Arrays: drop function handles element cleanup internally
    // Functions/Closures: closure_drop decs captured RC values when
    //   refcount reaches zero, so scope-exit rc_dec cascades correctly
    // Classes: instance_drop walks fields and decs RC children when refcount
    //   reaches zero. Field values are rc_inc'd at construction time when
    //   borrowed, so the instance owns its references
    // Handles: opaque RC pointers (Map, Set, Rng, etc.) with their own drop fns
    // Iterators: iterator_drop frees source iterators, closures, and
    //   underlying arrays via iterator_drop_sources when refcount hits zero
    // Interfaces: fat pointers to RC-managed implementor objects
    //
    // NOT simple RC types:
    // - Structs: stack-allocated value types (may have composite RC fields)
    // - Sentinels: i8 zero values, not heap pointers
    // - Primitives: value types
    arena.is_string(type_id)
        || arena.is_array(type_id)
        || arena.is_function(type_id)
        || arena.is_class(type_id)
        || arena.is_handle(type_id)
        || arena.is_interface(type_id)
        || arena.is_runtime_iterator(type_id)
}

/// Check if a type qualifies for capture RC management in closures.
///
/// A capture is considered RC if its runtime representation is a pointer to an
/// RcHeader-managed heap object. This is a subset of simple RC types - excludes
/// handles and iterators which aren't typically captured in closures.
fn is_capture_rc_type(arena: &TypeArena, type_id: TypeId) -> bool {
    arena.is_string(type_id)
        || arena.is_array(type_id)
        || arena.is_function(type_id)
        || arena.is_class(type_id)
}

/// Compute which union variant tags correspond to RC types.
fn compute_union_rc_variants(arena: &TypeArena, variants: &[TypeId]) -> Vec<(u8, bool)> {
    let mut rc_tags = Vec::new();
    for (i, &variant_type_id) in variants.iter().enumerate() {
        if is_simple_rc_type(arena, variant_type_id) {
            let is_interface = arena.is_interface(variant_type_id);
            rc_tags.push((i as u8, is_interface));
        }
    }
    rc_tags
}

/// Compute the byte offsets of RC fields within a composite type.
///
/// Returns `Some((shallow_offsets, deep_offsets))` if the type has RC fields,
/// or `None` if the type has no RC fields needing cleanup.
///
/// - `shallow_offsets`: Direct RC fields only (one level deep)
/// - `deep_offsets`: All RC fields, including those in nested structs
fn compute_composite_rc_offsets(
    arena: &TypeArena,
    registry: &EntityRegistry,
    type_id: TypeId,
) -> Option<(Vec<i32>, Vec<i32>)> {
    // Struct: iterate fields, collect offsets of RC-typed fields
    if let Some((type_def_id, type_args)) = arena.unwrap_struct(type_id) {
        let type_def = registry.get_type(type_def_id);
        let generic_info = type_def.generic_info.as_ref()?;
        let field_types: Vec<TypeId> = if !type_args.is_empty()
            && !generic_info.type_params.is_empty()
        {
            let subs: FxHashMap<_, _> = generic_info
                .type_params
                .iter()
                .zip(type_args.iter())
                .map(|(param, &arg)| (param.name_id, arg))
                .collect();
            generic_info
                .field_types
                .iter()
                .map(|&field_ty| arena.expect_substitute(field_ty, &subs, "rc_state struct fields"))
                .collect()
        } else {
            generic_info.field_types.clone()
        };

        let mut shallow_offsets = Vec::new();
        let mut deep_offsets = Vec::new();
        let mut byte_offset = 0i32;

        for field_type in &field_types {
            let slots = crate::structs::field_flat_slots(*field_type, arena, registry);

            // Shallow: only direct RC fields
            if is_simple_rc_type(arena, *field_type) {
                shallow_offsets.push(byte_offset);
                deep_offsets.push(byte_offset);
            } else {
                // Deep: recursively collect from nested structs
                if let Some((_, nested_deep)) =
                    compute_composite_rc_offsets(arena, registry, *field_type)
                {
                    for off in nested_deep {
                        deep_offsets.push(byte_offset + off);
                    }
                }
            }

            byte_offset += (slots as i32) * 8;
        }

        if shallow_offsets.is_empty() && deep_offsets.is_empty() {
            return None;
        }
        return Some((shallow_offsets, deep_offsets));
    }

    // Fixed array: if element type is RC, all elements need cleanup
    if let Some((elem_type_id, size)) = arena.unwrap_fixed_array(type_id) {
        if is_simple_rc_type(arena, elem_type_id) {
            let offsets: Vec<i32> = (0..size).map(|i| (i as i32) * 8).collect();
            return Some((offsets.clone(), offsets));
        }
        return None;
    }

    // Tuple: compute offsets based on element sizes, then filter RC elements
    if let Some(elem_types) = arena.unwrap_tuple(type_id) {
        let all_offsets = compute_tuple_offsets(arena, registry, elem_types);
        let mut rc_offsets = Vec::new();

        for (i, elem_type) in elem_types.iter().enumerate() {
            if is_simple_rc_type(arena, *elem_type) {
                rc_offsets.push(all_offsets[i]);
            }
        }

        if rc_offsets.is_empty() {
            return None;
        }
        return Some((rc_offsets.clone(), rc_offsets));
    }

    None
}

/// Compute byte offsets for tuple elements.
///
/// Each element is aligned to 8 bytes. This matches the behavior of
/// `types::tuple_layout_id` but doesn't require a Cranelift pointer type.
fn compute_tuple_offsets(
    arena: &TypeArena,
    registry: &EntityRegistry,
    elem_types: &[TypeId],
) -> Vec<i32> {
    let mut offsets = Vec::with_capacity(elem_types.len());
    let mut offset = 0i32;

    for &elem in elem_types {
        offsets.push(offset);
        let elem_size = compute_type_size_aligned(arena, registry, elem);
        offset += elem_size;
    }

    offsets
}

/// Compute the size of a type in bytes, aligned to 8 bytes.
///
/// This is a simplified version of `type_id_size` that assumes 64-bit pointers
/// and aligns all sizes to 8 bytes (matching tuple layout behavior).
fn compute_type_size_aligned(arena: &TypeArena, registry: &EntityRegistry, type_id: TypeId) -> i32 {
    use vole_sema::PrimitiveType;

    // Sentinel types are zero-sized
    if arena.is_sentinel(type_id) {
        return 0;
    }

    let raw_size: i32 = match arena.get(type_id) {
        SemaType::Primitive(PrimitiveType::I8)
        | SemaType::Primitive(PrimitiveType::U8)
        | SemaType::Primitive(PrimitiveType::Bool) => 1,
        SemaType::Primitive(PrimitiveType::I16) | SemaType::Primitive(PrimitiveType::U16) => 2,
        SemaType::Primitive(PrimitiveType::I32)
        | SemaType::Primitive(PrimitiveType::U32)
        | SemaType::Primitive(PrimitiveType::F32) => 4,
        SemaType::Primitive(PrimitiveType::I64)
        | SemaType::Primitive(PrimitiveType::U64)
        | SemaType::Primitive(PrimitiveType::F64) => 8,
        SemaType::Primitive(PrimitiveType::I128) => 16,
        SemaType::Primitive(PrimitiveType::String) | SemaType::Array(_) => 8, // pointer
        SemaType::Handle => 8,                                                // pointer
        SemaType::Interface { .. } => 8,                                      // pointer
        SemaType::Void => 0,
        SemaType::Range => 16, // start + end
        SemaType::Union(variants) => {
            // Tag byte + max variant payload, aligned
            let max_payload = variants
                .iter()
                .map(|&v| compute_type_size_aligned(arena, registry, v))
                .max()
                .unwrap_or(0);
            crate::union_layout::TAG_ONLY_SIZE as i32 + max_payload
        }
        SemaType::Tuple(elements) => {
            // Sum of aligned element sizes
            elements
                .iter()
                .map(|&e| compute_type_size_aligned(arena, registry, e))
                .sum()
        }
        SemaType::FixedArray { element, size } => {
            let elem_size = compute_type_size_aligned(arena, registry, *element);
            elem_size * (*size as i32)
        }
        SemaType::Struct { .. } => {
            // Use struct_total_byte_size helper
            crate::structs::struct_total_byte_size(type_id, arena, registry)
                .expect("INTERNAL: valid struct must have computable size") as i32
        }
        SemaType::Unknown => 16, // TaggedValue: 8-byte tag + 8-byte value
        _ => 8,                  // Default to pointer size for other types
    };

    // Align to 8 bytes
    ((raw_size + 7) / 8) * 8
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper to create a test arena and registry for basic tests
    fn setup_test_arena() -> (TypeArena, EntityRegistry) {
        let arena = TypeArena::new();
        let registry = EntityRegistry::default();
        (arena, registry)
    }

    #[test]
    fn test_primitive_types_are_not_rc() {
        let (arena, registry) = setup_test_arena();

        // All primitive types should return RcState::None
        assert_eq!(
            compute_rc_state(&arena, &registry, TypeId::I8),
            RcState::None
        );
        assert_eq!(
            compute_rc_state(&arena, &registry, TypeId::I16),
            RcState::None
        );
        assert_eq!(
            compute_rc_state(&arena, &registry, TypeId::I32),
            RcState::None
        );
        assert_eq!(
            compute_rc_state(&arena, &registry, TypeId::I64),
            RcState::None
        );
        assert_eq!(
            compute_rc_state(&arena, &registry, TypeId::U8),
            RcState::None
        );
        assert_eq!(
            compute_rc_state(&arena, &registry, TypeId::U16),
            RcState::None
        );
        assert_eq!(
            compute_rc_state(&arena, &registry, TypeId::U32),
            RcState::None
        );
        assert_eq!(
            compute_rc_state(&arena, &registry, TypeId::U64),
            RcState::None
        );
        assert_eq!(
            compute_rc_state(&arena, &registry, TypeId::F32),
            RcState::None
        );
        assert_eq!(
            compute_rc_state(&arena, &registry, TypeId::F64),
            RcState::None
        );
        assert_eq!(
            compute_rc_state(&arena, &registry, TypeId::BOOL),
            RcState::None
        );
    }

    #[test]
    fn test_string_is_simple_rc() {
        let (arena, registry) = setup_test_arena();

        let state = compute_rc_state(&arena, &registry, TypeId::STRING);
        assert_eq!(state, RcState::Simple { is_capture: true });
    }

    #[test]
    fn test_handle_is_simple_rc_not_capture() {
        let (arena, registry) = setup_test_arena();

        let state = compute_rc_state(&arena, &registry, TypeId::HANDLE);
        assert_eq!(state, RcState::Simple { is_capture: false });
    }

    #[test]
    fn test_void_is_not_rc() {
        let (arena, registry) = setup_test_arena();

        assert_eq!(
            compute_rc_state(&arena, &registry, TypeId::VOID),
            RcState::None
        );
    }

    #[test]
    fn test_rc_state_has_accessor_methods() {
        // Test that we can check various properties of RcState
        let none = RcState::None;
        let simple = RcState::Simple { is_capture: true };
        let composite = RcState::Composite {
            shallow_offsets: vec![0, 8],
            deep_offsets: vec![0, 8, 16],
        };
        let union = RcState::Union {
            rc_variants: vec![(0, false), (2, true)],
        };

        // Basic equality checks
        assert_eq!(none, RcState::None);
        assert_ne!(simple, RcState::None);
        assert_ne!(composite, RcState::None);
        assert_ne!(union, RcState::None);
    }

    #[test]
    fn test_array_is_simple_rc() {
        let (mut arena, registry) = setup_test_arena();

        // Create an array of i64 (element type doesn't matter for RC-ness of array itself)
        let array_type = arena.array(TypeId::I64);
        let state = compute_rc_state(&arena, &registry, array_type);
        assert_eq!(state, RcState::Simple { is_capture: true });
    }

    #[test]
    fn test_union_with_no_rc_variants() {
        let (mut arena, registry) = setup_test_arena();

        // Union of i64 | bool - no RC types
        let union_type = arena.union(vec![TypeId::I64, TypeId::BOOL]);
        let state = compute_rc_state(&arena, &registry, union_type);
        assert_eq!(state, RcState::None);
    }

    #[test]
    fn test_union_with_rc_variant() {
        let (mut arena, registry) = setup_test_arena();

        // Union of i64 | String - String is RC
        let union_type = arena.union(vec![TypeId::I64, TypeId::STRING]);
        let state = compute_rc_state(&arena, &registry, union_type);

        // Union should have RC variants
        match state {
            RcState::Union { rc_variants } => {
                // String should be one of the RC variants (index depends on sorting)
                assert!(!rc_variants.is_empty());
            }
            _ => panic!("Expected RcState::Union, got {:?}", state),
        }
    }

    #[test]
    fn test_fixed_array_of_rc_type() {
        let (mut arena, registry) = setup_test_arena();

        // Fixed array of 3 strings
        let fixed_array = arena.fixed_array(TypeId::STRING, 3);
        let state = compute_rc_state(&arena, &registry, fixed_array);

        // Should be a composite with 3 RC offsets at 0, 8, 16
        match state {
            RcState::Composite {
                shallow_offsets,
                deep_offsets,
            } => {
                assert_eq!(shallow_offsets, vec![0, 8, 16]);
                assert_eq!(deep_offsets, vec![0, 8, 16]);
            }
            _ => panic!("Expected RcState::Composite, got {:?}", state),
        }
    }

    #[test]
    fn test_fixed_array_of_non_rc_type() {
        let (mut arena, registry) = setup_test_arena();

        // Fixed array of 3 i64s - no RC cleanup needed
        let fixed_array = arena.fixed_array(TypeId::I64, 3);
        let state = compute_rc_state(&arena, &registry, fixed_array);
        assert_eq!(state, RcState::None);
    }

    #[test]
    fn test_tuple_with_mixed_types() {
        let (mut arena, registry) = setup_test_arena();

        // Tuple of (i64, String, bool) - only String needs RC
        let tuple_type = arena.tuple(vec![TypeId::I64, TypeId::STRING, TypeId::BOOL]);
        let state = compute_rc_state(&arena, &registry, tuple_type);

        // Should be a composite with only the String offset (8 bytes after i64)
        match state {
            RcState::Composite {
                shallow_offsets,
                deep_offsets,
            } => {
                assert_eq!(shallow_offsets, vec![8]); // String is at offset 8
                assert_eq!(deep_offsets, vec![8]);
            }
            _ => panic!("Expected RcState::Composite, got {:?}", state),
        }
    }

    #[test]
    fn test_tuple_with_no_rc_types() {
        let (mut arena, registry) = setup_test_arena();

        // Tuple of (i64, bool) - no RC types
        let tuple_type = arena.tuple(vec![TypeId::I64, TypeId::BOOL]);
        let state = compute_rc_state(&arena, &registry, tuple_type);
        assert_eq!(state, RcState::None);
    }

    #[test]
    fn test_range_is_not_rc() {
        let (arena, registry) = setup_test_arena();

        assert_eq!(
            compute_rc_state(&arena, &registry, TypeId::RANGE),
            RcState::None
        );
    }

    // =========================================================================
    // Tuple offset equivalence tests: compute_tuple_offsets vs tuple_layout_id
    //
    // These tests verify that the standalone compute_tuple_offsets (used by
    // RcState) produces the same byte offsets as the original tuple_layout_id
    // (used by CodegenContext). If these diverge, the RcState migration in
    // vol-q117 is NOT safe.
    // =========================================================================

    /// Compare compute_tuple_offsets (rc_state.rs) with tuple_layout_id (types/)
    /// for a given set of element types. Panics with a diff on mismatch.
    fn assert_tuple_offsets_equivalent(
        arena: &TypeArena,
        registry: &EntityRegistry,
        elements: &[TypeId],
    ) {
        use cranelift::prelude::types as cl_types;

        let ptr_type = cl_types::I64; // 64-bit pointers, matching compute_type_size_aligned assumption

        let new_offsets = compute_tuple_offsets(arena, registry, elements);
        let (_total, old_offsets) =
            crate::types::tuple_layout_id(elements, ptr_type, registry, arena);

        assert_eq!(
            new_offsets, old_offsets,
            "Tuple offset mismatch for element types {:?}:\n  compute_tuple_offsets: {:?}\n  tuple_layout_id:      {:?}",
            elements, new_offsets, old_offsets,
        );
    }

    /// Also compare per-element sizes directly.
    fn assert_type_size_equivalent(arena: &TypeArena, registry: &EntityRegistry, type_id: TypeId) {
        use cranelift::prelude::types as cl_types;

        let ptr_type = cl_types::I64;

        let new_size = compute_type_size_aligned(arena, registry, type_id);
        let old_size =
            (crate::types::type_id_size(type_id, ptr_type, registry, arena).div_ceil(8) * 8) as i32;

        assert_eq!(
            new_size, old_size,
            "Type size mismatch for {:?}:\n  compute_type_size_aligned: {}\n  type_id_size (aligned):    {}",
            type_id, new_size, old_size,
        );
    }

    #[test]
    fn test_size_equivalence_primitives() {
        let (arena, registry) = setup_test_arena();

        for ty in [
            TypeId::I8,
            TypeId::I16,
            TypeId::I32,
            TypeId::I64,
            TypeId::I128,
            TypeId::U8,
            TypeId::U16,
            TypeId::U32,
            TypeId::U64,
            TypeId::F32,
            TypeId::F64,
            TypeId::BOOL,
            TypeId::STRING,
            TypeId::HANDLE,
            TypeId::VOID,
            TypeId::RANGE,
        ] {
            assert_type_size_equivalent(&arena, &registry, ty);
        }
    }

    #[test]
    fn test_size_equivalence_array() {
        let (mut arena, registry) = setup_test_arena();

        let array_i64 = arena.array(TypeId::I64);
        assert_type_size_equivalent(&arena, &registry, array_i64);

        let array_str = arena.array(TypeId::STRING);
        assert_type_size_equivalent(&arena, &registry, array_str);
    }

    #[test]
    fn test_size_equivalence_union_of_primitives() {
        let (mut arena, registry) = setup_test_arena();

        let union_type = arena.union(vec![TypeId::I64, TypeId::BOOL]);
        assert_type_size_equivalent(&arena, &registry, union_type);

        let union_with_str = arena.union(vec![TypeId::I64, TypeId::STRING]);
        assert_type_size_equivalent(&arena, &registry, union_with_str);
    }

    #[test]
    fn test_size_equivalence_fixed_array() {
        let (mut arena, registry) = setup_test_arena();

        let fa_i32 = arena.fixed_array(TypeId::I32, 4);
        assert_type_size_equivalent(&arena, &registry, fa_i32);

        let fa_str = arena.fixed_array(TypeId::STRING, 3);
        assert_type_size_equivalent(&arena, &registry, fa_str);
    }

    #[test]
    fn test_size_equivalence_tuple() {
        let (mut arena, registry) = setup_test_arena();

        let tuple = arena.tuple(vec![TypeId::I64, TypeId::STRING, TypeId::BOOL]);
        assert_type_size_equivalent(&arena, &registry, tuple);
    }

    #[test]
    fn test_tuple_offsets_all_primitives() {
        let (arena, registry) = setup_test_arena();

        assert_tuple_offsets_equivalent(&arena, &registry, &[TypeId::I64, TypeId::I32]);
        assert_tuple_offsets_equivalent(
            &arena,
            &registry,
            &[TypeId::I8, TypeId::I16, TypeId::I32, TypeId::I64],
        );
        assert_tuple_offsets_equivalent(&arena, &registry, &[TypeId::F32, TypeId::F64]);
        assert_tuple_offsets_equivalent(&arena, &registry, &[TypeId::BOOL, TypeId::I128]);
    }

    #[test]
    fn test_tuple_offsets_with_rc_types() {
        let (arena, registry) = setup_test_arena();

        // (i64, String, bool) — the existing RcState test case
        assert_tuple_offsets_equivalent(
            &arena,
            &registry,
            &[TypeId::I64, TypeId::STRING, TypeId::BOOL],
        );

        // (String, String) — multiple RC types
        assert_tuple_offsets_equivalent(&arena, &registry, &[TypeId::STRING, TypeId::STRING]);

        // (String, i32, String, f64)
        assert_tuple_offsets_equivalent(
            &arena,
            &registry,
            &[TypeId::STRING, TypeId::I32, TypeId::STRING, TypeId::F64],
        );
    }

    #[test]
    fn test_tuple_offsets_with_array_elements() {
        let (mut arena, registry) = setup_test_arena();

        let array_i64 = arena.array(TypeId::I64);
        // (Array<i64>, i32, String)
        assert_tuple_offsets_equivalent(
            &arena,
            &registry,
            &[array_i64, TypeId::I32, TypeId::STRING],
        );
    }

    #[test]
    fn test_tuple_offsets_with_union_elements() {
        let (mut arena, registry) = setup_test_arena();

        // Union of primitives (no struct variants — should be safe)
        let union_prim = arena.union(vec![TypeId::I64, TypeId::BOOL]);
        assert_tuple_offsets_equivalent(&arena, &registry, &[union_prim, TypeId::STRING]);

        // Union with RC variant
        let union_rc = arena.union(vec![TypeId::I64, TypeId::STRING]);
        assert_tuple_offsets_equivalent(&arena, &registry, &[union_rc, TypeId::I32]);
        assert_tuple_offsets_equivalent(&arena, &registry, &[TypeId::BOOL, union_rc, TypeId::F64]);
    }

    #[test]
    fn test_tuple_offsets_with_fixed_array_elements() {
        let (mut arena, registry) = setup_test_arena();

        let fa = arena.fixed_array(TypeId::STRING, 3);
        assert_tuple_offsets_equivalent(&arena, &registry, &[fa, TypeId::I64]);
        assert_tuple_offsets_equivalent(&arena, &registry, &[TypeId::I32, fa]);
    }

    #[test]
    fn test_tuple_offsets_nested_tuple() {
        let (mut arena, registry) = setup_test_arena();

        let inner = arena.tuple(vec![TypeId::I32, TypeId::STRING]);
        assert_tuple_offsets_equivalent(&arena, &registry, &[inner, TypeId::I64]);
        assert_tuple_offsets_equivalent(&arena, &registry, &[TypeId::BOOL, inner, TypeId::F64]);
    }
}
