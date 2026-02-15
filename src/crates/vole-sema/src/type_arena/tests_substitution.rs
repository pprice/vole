// type_arena/tests_substitution.rs
//
// Unit tests for type substitution and lookup_substitute.

#[cfg(test)]
mod substitution_tests {
    use rustc_hash::FxHashMap;

    use crate::type_arena::*;
    use vole_identity::{NameId, TypeDefId};

    // ========================================================================
    // Substitution tests
    // ========================================================================

    #[test]
    fn substitute_type_param() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let t = arena.type_param(name_id);

        let mut subs = FxHashMap::default();
        subs.insert(name_id, arena.i32());

        let result = arena.substitute(t, &subs);
        assert_eq!(result, arena.i32());
    }

    #[test]
    fn substitute_array_of_type_param() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let t = arena.type_param(name_id);
        let arr_t = arena.array(t);

        let mut subs = FxHashMap::default();
        subs.insert(name_id, arena.string());

        let result = arena.substitute(arr_t, &subs);
        let expected = arena.array(arena.string());
        assert_eq!(result, expected);
    }

    #[test]
    fn substitute_caches_via_interning() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let nil = arena.nil();
        let t = arena.type_param(name_id);
        let union_t = arena.union(smallvec::smallvec![t, nil]);

        let mut subs = FxHashMap::default();
        subs.insert(name_id, arena.i32());

        let result1 = arena.substitute(union_t, &subs);
        let result2 = arena.substitute(union_t, &subs);
        assert_eq!(result1, result2); // Same TypeId due to interning

        // Should match direct construction
        let i32_id = arena.i32();
        let nil_id = arena.nil();
        let direct = arena.union(smallvec::smallvec![i32_id, nil_id]);
        assert_eq!(result1, direct);
    }

    #[test]
    fn substitute_empty_is_noop() {
        let mut arena = TypeArena::new();
        let arr = arena.array(arena.i32());
        let empty_subs: FxHashMap<NameId, TypeId> = FxHashMap::default();

        let result = arena.substitute(arr, &empty_subs);
        assert_eq!(result, arr); // Exact same TypeId
    }

    #[test]
    fn substitute_unchanged_returns_interned() {
        let mut arena = TypeArena::new();
        let _name_id = NameId::new_for_test(999);
        let other_id = NameId::new_for_test(888);

        let arr = arena.array(arena.i32()); // No type params

        let mut subs = FxHashMap::default();
        subs.insert(other_id, arena.string()); // Unrelated substitution

        let result = arena.substitute(arr, &subs);
        // Should return equivalent TypeId (may or may not be same due to interning)
        assert_eq!(arena.unwrap_array(result), Some(arena.i32()));
    }

    #[test]
    fn substitute_function_type() {
        let mut arena = TypeArena::new();
        let t_id = NameId::new_for_test(100);
        let u_id = NameId::new_for_test(101);

        let t = arena.type_param(t_id);
        let u = arena.type_param(u_id);
        let func = arena.function(smallvec::smallvec![t], u, false);

        let mut subs = FxHashMap::default();
        subs.insert(t_id, arena.i32());
        subs.insert(u_id, arena.string());

        let result = arena.substitute(func, &subs);
        let (params, ret, _) = arena.unwrap_function(result).unwrap();
        assert_eq!(params[0], arena.i32());
        assert_eq!(ret, arena.string());
    }

    #[test]
    fn substitute_class_type_args() {
        let mut arena = TypeArena::new();
        let t_id = NameId::new_for_test(100);
        let type_def_id = TypeDefId::new(42);

        let t = arena.type_param(t_id);
        let cls = arena.class(type_def_id, smallvec::smallvec![t]);

        let mut subs = FxHashMap::default();
        subs.insert(t_id, arena.i64());

        let result = arena.substitute(cls, &subs);
        let args = arena.type_args(result);
        assert_eq!(args.len(), 1);
        assert_eq!(args[0], arena.i64());
    }

    #[test]
    fn substitute_nested_types() {
        let mut arena = TypeArena::new();
        let t_id = NameId::new_for_test(100);

        // Array<Array<T>>
        let t = arena.type_param(t_id);
        let inner_arr = arena.array(t);
        let outer_arr = arena.array(inner_arr);

        let mut subs = FxHashMap::default();
        subs.insert(t_id, arena.bool());

        let result = arena.substitute(outer_arr, &subs);

        // Should be Array<Array<bool>>
        let inner = arena.unwrap_array(result).unwrap();
        let innermost = arena.unwrap_array(inner).unwrap();
        assert_eq!(innermost, arena.bool());
    }

    // ========================================================================
    // lookup_substitute tests
    // ========================================================================

    #[test]
    fn lookup_substitute_empty_subs() {
        let mut arena = TypeArena::new();
        let arr = arena.array(arena.i32());
        let empty_subs: FxHashMap<NameId, TypeId> = FxHashMap::default();

        // Empty substitutions should return the same type
        let result = arena.lookup_substitute(arr, &empty_subs);
        assert_eq!(result, Some(arr));
    }

    #[test]
    fn lookup_substitute_primitive_unchanged() {
        let arena = TypeArena::new();
        let mut subs = FxHashMap::default();
        let name_id = NameId::new_for_test(999);
        subs.insert(name_id, arena.string());

        // Primitive with unrelated substitution should return unchanged
        let result = arena.lookup_substitute(arena.i32(), &subs);
        assert_eq!(result, Some(arena.i32()));
    }

    #[test]
    fn lookup_substitute_type_param_found() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let t = arena.type_param(name_id);

        let mut subs = FxHashMap::default();
        subs.insert(name_id, arena.i32());

        // Direct type param lookup
        let result = arena.lookup_substitute(t, &subs);
        assert_eq!(result, Some(arena.i32()));
    }

    #[test]
    fn lookup_substitute_type_param_not_in_subs() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let other_id = NameId::new_for_test(888);
        let t = arena.type_param(name_id);

        let mut subs = FxHashMap::default();
        subs.insert(other_id, arena.i32()); // Different name_id

        // Type param not in substitutions should return None
        let result = arena.lookup_substitute(t, &subs);
        assert_eq!(result, None);
    }

    #[test]
    fn lookup_substitute_existing_type() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let t = arena.type_param(name_id);
        let arr_t = arena.array(t);

        // First, create the substituted type so it exists
        let mut subs = FxHashMap::default();
        subs.insert(name_id, arena.string());
        let expected = arena.substitute(arr_t, &subs);

        // Now lookup should find it
        let result = arena.lookup_substitute(arr_t, &subs);
        assert_eq!(result, Some(expected));
    }

    #[test]
    fn lookup_substitute_nonexistent_type() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let t = arena.type_param(name_id);
        let arr_t = arena.array(t);

        // Create a type that substitutes T -> i64, but we'll query T -> f32
        let mut subs1 = FxHashMap::default();
        subs1.insert(name_id, arena.i64());
        let _ = arena.substitute(arr_t, &subs1);

        // Now lookup with a different substitution that wasn't created
        let mut subs2 = FxHashMap::default();
        subs2.insert(name_id, arena.f32());

        let result = arena.lookup_substitute(arr_t, &subs2);
        assert_eq!(result, None); // Array<f32> doesn't exist
    }

    #[test]
    fn lookup_substitute_class_type() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(100);
        let type_def_id = TypeDefId::new(42);

        let t = arena.type_param(name_id);
        let cls = arena.class(type_def_id, smallvec::smallvec![t]);

        // Create the substituted type first
        let mut subs = FxHashMap::default();
        subs.insert(name_id, arena.i64());
        let expected = arena.substitute(cls, &subs);

        // Lookup should find it
        let result = arena.lookup_substitute(cls, &subs);
        assert_eq!(result, Some(expected));
    }

    #[test]
    fn lookup_substitute_function_type() {
        let mut arena = TypeArena::new();
        let t_id = NameId::new_for_test(100);
        let u_id = NameId::new_for_test(101);

        let t = arena.type_param(t_id);
        let u = arena.type_param(u_id);
        let func = arena.function(smallvec::smallvec![t], u, false);

        // Create the substituted type first
        let mut subs = FxHashMap::default();
        subs.insert(t_id, arena.i32());
        subs.insert(u_id, arena.string());
        let expected = arena.substitute(func, &subs);

        // Lookup should find it
        let result = arena.lookup_substitute(func, &subs);
        assert_eq!(result, Some(expected));
    }

    #[test]
    #[should_panic(expected = "Type not found after substitution")]
    fn expect_substitute_panics_on_missing() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let t = arena.type_param(name_id);
        let arr_t = arena.array(t);

        // Don't create the substituted type
        let mut subs = FxHashMap::default();
        subs.insert(name_id, arena.f64());

        // This should panic
        arena.expect_substitute(arr_t, &subs, "test context");
    }

    #[test]
    fn expect_substitute_returns_existing() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let t = arena.type_param(name_id);
        let arr_t = arena.array(t);

        // Create the substituted type first
        let mut subs = FxHashMap::default();
        subs.insert(name_id, arena.string());
        let expected = arena.substitute(arr_t, &subs);

        // expect_substitute should return it
        let result = arena.expect_substitute(arr_t, &subs, "test context");
        assert_eq!(result, expected);
    }
}
