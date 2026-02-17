// type_arena/tests.rs
//
// Unit tests for core arena, query, and union simplification.

#[cfg(test)]
mod core_tests {
    use crate::type_arena::*;
    use crate::types::PrimitiveType;
    use vole_identity::TypeDefId;

    #[test]
    fn type_id_is_copy() {
        let id = TypeId::from_raw(42);
        let id2 = id; // Copy
        assert_eq!(id, id2);
    }

    #[test]
    fn type_id_vec_inline_capacity() {
        let vec: TypeIdVec = smallvec::smallvec![
            TypeId::from_raw(1),
            TypeId::from_raw(2),
            TypeId::from_raw(3),
            TypeId::from_raw(4)
        ];
        assert!(!vec.spilled()); // Should be inline
    }

    #[test]
    fn type_id_vec_spills_beyond_4() {
        let vec: TypeIdVec = smallvec::smallvec![
            TypeId::from_raw(1),
            TypeId::from_raw(2),
            TypeId::from_raw(3),
            TypeId::from_raw(4),
            TypeId::from_raw(5)
        ];
        assert!(vec.spilled()); // Should spill to heap
    }

    #[test]
    fn interned_type_size() {
        // Verify SemaType is reasonably sized
        let size = size_of::<SemaType>();
        assert!(size <= 48, "SemaType is {} bytes, expected <= 48", size);
    }

    #[test]
    fn type_id_size() {
        assert_eq!(size_of::<TypeId>(), 4);
    }

    #[test]
    fn primitives_preallocated() {
        let arena = TypeArena::new();
        // All primitives should have stable, distinct IDs
        assert_ne!(arena.primitives.i32, arena.primitives.string);
        assert_ne!(arena.primitives.i32, arena.primitives.i64);
        assert_ne!(arena.primitives.nil, arena.primitives.void);
    }

    #[test]
    fn invalid_is_at_index_zero() {
        let arena = TypeArena::new();
        assert_eq!(arena.primitives.invalid.index(), 0);
        assert!(arena.is_invalid(arena.primitives.invalid));
        assert!(!arena.is_invalid(arena.primitives.i32));
    }

    // ========================================================================
    // Interning and builder methods
    // ========================================================================

    #[test]
    fn interning_deduplicates() {
        let mut arena = TypeArena::new();
        let i32_id = arena.i32();
        let nil_id = arena.nil();
        let a = arena.union(smallvec::smallvec![i32_id, nil_id]);
        let b = arena.union(smallvec::smallvec![i32_id, nil_id]);
        assert_eq!(a, b); // Same TypeId
    }

    #[test]
    fn different_types_different_ids() {
        let mut arena = TypeArena::new();
        let a = arena.array(arena.i32());
        let b = arena.array(arena.string());
        assert_ne!(a, b);
    }

    #[test]
    fn optional_is_union_with_nil() {
        let mut arena = TypeArena::new();
        let i32_id = arena.i32();
        let opt = arena.optional(i32_id);
        match arena.get(opt) {
            SemaType::Union(variants) => {
                assert_eq!(variants.len(), 2);
                assert!(variants.contains(&arena.nil()));
                assert!(variants.contains(&arena.i32()));
            }
            _ => panic!("optional should be union"),
        }
    }

    #[test]
    fn primitive_accessor_matches_enum() {
        let arena = TypeArena::new();
        assert_eq!(arena.primitive(PrimitiveType::I32), arena.i32());
        assert_eq!(arena.primitive(PrimitiveType::String), arena.string());
        assert_eq!(arena.primitive(PrimitiveType::Bool), arena.bool());
        assert_eq!(arena.primitive(PrimitiveType::F128), arena.f128());
    }

    #[test]
    fn array_builder() {
        let mut arena = TypeArena::new();
        let arr = arena.array(arena.i32());
        match arena.get(arr) {
            SemaType::Array(elem) => {
                assert_eq!(*elem, arena.i32());
            }
            _ => panic!("expected array type"),
        }
    }

    #[test]
    fn function_builder() {
        let mut arena = TypeArena::new();
        let i32_id = arena.i32();
        let string_id = arena.string();
        let func = arena.function(smallvec::smallvec![i32_id, string_id], arena.bool(), false);
        match arena.get(func) {
            SemaType::Function {
                params,
                ret,
                is_closure,
            } => {
                assert_eq!(params.len(), 2);
                assert_eq!(params[0], i32_id);
                assert_eq!(params[1], string_id);
                assert_eq!(*ret, arena.bool());
                assert!(!is_closure);
            }
            _ => panic!("expected function type"),
        }
    }

    #[test]
    fn tuple_builder() {
        let mut arena = TypeArena::new();
        let tup = arena.tuple(smallvec::smallvec![
            arena.i32(),
            arena.string(),
            arena.bool()
        ]);
        match arena.get(tup) {
            SemaType::Tuple(elements) => {
                assert_eq!(elements.len(), 3);
            }
            _ => panic!("expected tuple type"),
        }
    }

    #[test]
    fn class_builder() {
        let mut arena = TypeArena::new();
        let type_def_id = TypeDefId::new(42);
        let cls = arena.class(type_def_id, smallvec::smallvec![arena.i32()]);
        match arena.get(cls) {
            SemaType::Class {
                type_def_id: tid,
                type_args,
            } => {
                assert_eq!(*tid, type_def_id);
                assert_eq!(type_args.len(), 1);
                assert_eq!(type_args[0], arena.i32());
            }
            _ => panic!("expected class type"),
        }
    }

    #[test]
    fn invalid_propagates() {
        let mut arena = TypeArena::new();
        let invalid = arena.invalid();

        // Union with invalid returns invalid
        let union_invalid = arena.union(smallvec::smallvec![arena.i32(), invalid]);
        assert!(arena.is_invalid(union_invalid));

        // Array of invalid returns invalid
        let arr_invalid = arena.array(invalid);
        assert!(arena.is_invalid(arr_invalid));

        // Function with invalid param returns invalid
        let func_invalid = arena.function(smallvec::smallvec![invalid], arena.i32(), false);
        assert!(arena.is_invalid(func_invalid));

        // Optional of invalid returns invalid
        let opt_invalid = arena.optional(invalid);
        assert!(arena.is_invalid(opt_invalid));
    }

    // ========================================================================
    // Query methods and Display
    // ========================================================================

    #[test]
    fn is_numeric_primitives() {
        let arena = TypeArena::new();
        assert!(arena.is_numeric(arena.i32()));
        assert!(arena.is_numeric(arena.i64()));
        assert!(arena.is_numeric(arena.f64()));
        assert!(arena.is_numeric(arena.f128()));
        assert!(!arena.is_numeric(arena.string()));
        assert!(!arena.is_numeric(arena.bool()));
    }

    #[test]
    fn is_integer_primitives() {
        let arena = TypeArena::new();
        assert!(arena.is_integer(arena.i32()));
        assert!(arena.is_integer(arena.u64()));
        assert!(!arena.is_integer(arena.f64()));
        assert!(!arena.is_integer(arena.string()));
    }

    #[test]
    fn is_float_primitives() {
        let arena = TypeArena::new();
        assert!(arena.is_float(arena.f32()));
        assert!(arena.is_float(arena.f64()));
        assert!(arena.is_float(arena.f128()));
        assert!(!arena.is_float(arena.i32()));
    }

    #[test]
    fn unwrap_array_works() {
        let mut arena = TypeArena::new();
        let arr = arena.array(arena.i32());
        assert_eq!(arena.unwrap_array(arr), Some(arena.i32()));
        assert_eq!(arena.unwrap_array(arena.i32()), None);
    }

    #[test]
    fn unwrap_optional_works() {
        let mut arena = TypeArena::new();
        let opt = arena.optional(arena.string());
        assert_eq!(arena.unwrap_optional(opt), Some(arena.string()));
        assert_eq!(arena.unwrap_optional(arena.string()), None);
    }

    #[test]
    fn unwrap_function_works() {
        let mut arena = TypeArena::new();
        let func = arena.function(smallvec::smallvec![arena.i32()], arena.string(), true);
        let (params, ret, is_closure) = arena.unwrap_function(func).unwrap();
        assert_eq!(params.len(), 1);
        assert_eq!(params[0], arena.i32());
        assert_eq!(ret, arena.string());
        assert!(is_closure);
    }

    #[test]
    fn type_def_id_extraction() {
        let mut arena = TypeArena::new();
        let type_def_id = TypeDefId::new(42);
        let cls = arena.class(type_def_id, TypeIdVec::new());
        assert_eq!(arena.type_def_id(cls), Some(type_def_id));
        assert_eq!(arena.type_def_id(arena.i32()), None);
    }

    #[test]
    fn type_args_extraction() {
        let mut arena = TypeArena::new();
        let type_def_id = TypeDefId::new(42);
        let cls = arena.class(
            type_def_id,
            smallvec::smallvec![arena.i32(), arena.string()],
        );
        let args = arena.type_args(cls);
        assert_eq!(args.len(), 2);
        assert_eq!(args[0], arena.i32());
        assert_eq!(args[1], arena.string());
    }

    #[test]
    #[should_panic(expected = "Invalid type in codegen")]
    fn expect_valid_panics_on_invalid() {
        let arena = TypeArena::new();
        arena.expect_valid(arena.invalid(), "test context");
    }

    #[test]
    fn expect_valid_returns_valid() {
        let arena = TypeArena::new();
        let i32_id = arena.i32();
        assert_eq!(arena.expect_valid(i32_id, "test"), i32_id);
    }

    #[test]
    fn display_basic_primitives() {
        let arena = TypeArena::new();
        assert_eq!(arena.display_basic(arena.i32()), "i32");
        assert_eq!(arena.display_basic(arena.string()), "string");
        assert_eq!(arena.display_basic(arena.bool()), "bool");
        // Before prelude loads, nil is a placeholder Invalid type
        assert_eq!(
            arena.display_basic(arena.nil()),
            "<invalid: nil_placeholder>"
        );
        assert_eq!(arena.display_basic(arena.void()), "void");
    }

    #[test]
    fn display_basic_compound() {
        let mut arena = TypeArena::new();
        let arr = arena.array(arena.i32());
        assert_eq!(arena.display_basic(arr), "[i32]");

        let opt = arena.optional(arena.string());
        let opt_display = arena.display_basic(opt);
        // Order may vary in union, but should contain both
        assert!(opt_display.contains("string"));
        assert!(opt_display.contains("nil"));
    }

    #[test]
    fn display_basic_function() {
        let mut arena = TypeArena::new();
        let func = arena.function(
            smallvec::smallvec![arena.i32(), arena.string()],
            arena.bool(),
            false,
        );
        assert_eq!(arena.display_basic(func), "(i32, string) -> bool");
    }

    // ========================================================================
    // Union simplification tests for never/unknown
    // ========================================================================

    #[test]
    fn union_never_with_type_removes_never() {
        let mut arena = TypeArena::new();
        let never = TypeId::NEVER;
        let i32_id = arena.i32();

        // never | i32 should be i32
        let result = arena.union(smallvec::smallvec![never, i32_id]);
        assert_eq!(result, i32_id);
    }

    #[test]
    fn union_never_with_multiple_types_removes_never() {
        let mut arena = TypeArena::new();
        let never = TypeId::NEVER;
        let i32_id = arena.i32();
        let string_id = arena.string();

        // never | i32 | string should be i32 | string (without never)
        let result = arena.union(smallvec::smallvec![never, i32_id, string_id]);
        let variants = arena.unwrap_union(result).unwrap();
        assert_eq!(variants.len(), 2);
        assert!(!variants.contains(&never));
        assert!(variants.contains(&i32_id));
        assert!(variants.contains(&string_id));
    }

    #[test]
    fn union_only_never_returns_never() {
        let mut arena = TypeArena::new();
        let never = TypeId::NEVER;

        // never | never should be never
        let result = arena.union(smallvec::smallvec![never, never]);
        assert_eq!(result, TypeId::NEVER);
    }

    #[test]
    fn union_unknown_with_type_returns_unknown() {
        let mut arena = TypeArena::new();
        let unknown = TypeId::UNKNOWN;
        let i32_id = arena.i32();

        // unknown | i32 should be unknown
        let result = arena.union(smallvec::smallvec![unknown, i32_id]);
        assert_eq!(result, TypeId::UNKNOWN);
    }

    #[test]
    fn union_unknown_with_multiple_types_returns_unknown() {
        let mut arena = TypeArena::new();
        let unknown = TypeId::UNKNOWN;
        let i32_id = arena.i32();
        let string_id = arena.string();
        let nil_id = arena.nil();

        // unknown | i32 | string | nil should be unknown
        let result = arena.union(smallvec::smallvec![unknown, i32_id, string_id, nil_id]);
        assert_eq!(result, TypeId::UNKNOWN);
    }

    #[test]
    fn union_unknown_with_never_returns_unknown() {
        let mut arena = TypeArena::new();
        let unknown = TypeId::UNKNOWN;
        let never = TypeId::NEVER;

        // unknown | never should be unknown (unknown absorbs everything, including never)
        let result = arena.union(smallvec::smallvec![unknown, never]);
        assert_eq!(result, TypeId::UNKNOWN);
    }

    #[test]
    fn union_never_with_nil_removes_never() {
        let mut arena = TypeArena::new();
        let never = TypeId::NEVER;
        let nil_id = arena.nil();

        // never | nil should be nil
        let result = arena.union(smallvec::smallvec![never, nil_id]);
        assert_eq!(result, nil_id);
    }

    #[test]
    fn union_nested_with_never_removes_never() {
        let mut arena = TypeArena::new();
        let never = TypeId::NEVER;
        let i32_id = arena.i32();
        let string_id = arena.string();

        // Create inner union: i32 | string
        let inner = arena.union(smallvec::smallvec![i32_id, string_id]);

        // (i32 | string) | never should be i32 | string
        let result = arena.union(smallvec::smallvec![inner, never]);
        let variants = arena.unwrap_union(result).unwrap();
        assert_eq!(variants.len(), 2);
        assert!(!variants.contains(&never));
    }

    #[test]
    fn union_nested_with_unknown_returns_unknown() {
        let mut arena = TypeArena::new();
        let unknown = TypeId::UNKNOWN;
        let i32_id = arena.i32();
        let string_id = arena.string();

        // Create inner union: i32 | string
        let inner = arena.union(smallvec::smallvec![i32_id, string_id]);

        // (i32 | string) | unknown should be unknown
        let result = arena.union(smallvec::smallvec![inner, unknown]);
        assert_eq!(result, TypeId::UNKNOWN);
    }
}
