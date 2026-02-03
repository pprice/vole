// src/codegen/rc_state.rs
//
// Unified RC state computation for reference-counted types.
//
// This module provides a single enum (RcState) that captures all the different
// ways a type can be reference-counted, along with a compute function that
// analyzes a type once and returns the appropriate state.
//
// The goal is to replace the scattered RC query methods with one cached
// computation per TypeId:
// - needs_rc_cleanup(type_id) -> bool
// - is_capture_rc(type_id) -> bool
// - composite_rc_field_offsets(type_id) -> Option<Vec<i32>>
// - deep_rc_field_offsets(type_id) -> Option<Vec<i32>>
// - union_rc_variant_tags(type_id) -> Option<Vec<(u8, bool)>>

// This module is purely additive - callers will be migrated in subsequent tickets.
// The allow(dead_code) will be removed once callers are migrated.
#![allow(dead_code)]

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
    if let Some((type_def_id, _)) = arena.unwrap_struct(type_id) {
        let type_def = registry.get_type(type_def_id);
        let generic_info = type_def.generic_info.as_ref()?;
        let field_types = &generic_info.field_types;

        let mut shallow_offsets = Vec::new();
        let mut deep_offsets = Vec::new();
        let mut byte_offset = 0i32;

        for field_type in field_types {
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
            8 + max_payload // 8 bytes for tag (aligned), then payload
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
            crate::structs::struct_total_byte_size(type_id, arena, registry).unwrap_or(8) as i32
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
}
