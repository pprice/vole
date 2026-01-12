// src/runtime/collections.rs
//! Runtime support for Map<K,V> and Set<T> collections.
//!
//! These collections store Vole values as i64 words and use the pre-computed
//! hash values from Vole's Hashable interface.

// FFI functions that take raw pointers are called from JIT-compiled code
// which ensures pointers are valid. Marking each function unsafe would be
// cumbersome and add overhead without safety benefits.
#![allow(clippy::not_unsafe_ptr_arg_deref)]
// We intentionally use explicit match for nil sentinel returns to make the
// nil semantics clear rather than relying on Default.
#![allow(clippy::manual_unwrap_or_default)]
#![allow(clippy::manual_unwrap_or)]

use std::cell::RefCell;
use std::rc::Rc;

use hashbrown::HashTable;

use crate::runtime::array::RcArray;
use crate::runtime::iterator::{ArraySource, IteratorKind, IteratorSource, UnifiedIterator};
use crate::runtime::value::TaggedValue;

// =============================================================================
// Equality function type for generic collections
// =============================================================================

/// Type alias for equality function pointers injected from Vole.
/// For primitives, this points to native eq functions (fast path).
/// For custom types, this points to a trampoline that calls Vole's Eq.eq().
pub type EqFn = extern "C" fn(i64, i64) -> bool;

/// Default equality function for i64 values (most common case).
pub extern "C" fn i64_eq(a: i64, b: i64) -> bool {
    a == b
}

// =============================================================================
// VoleMap - Hash map for Vole Map<K, V> type
// =============================================================================

/// A Vole map storing key-value pairs as i64 words.
/// Uses HashTable for full control over hashing and equality.
/// Hash is pre-computed in Vole via Hashable.hash() and stored with entries.
/// Equality is provided via injected eq_fn at construction.
pub struct VoleMap {
    table: HashTable<(u64, i64, i64)>, // (hash, key, value) tuples
    eq_fn: EqFn,
}

impl VoleMap {
    pub fn new(eq_fn: EqFn) -> Self {
        Self {
            table: HashTable::new(),
            eq_fn,
        }
    }

    pub fn with_capacity(capacity: usize, eq_fn: EqFn) -> Self {
        Self {
            table: HashTable::with_capacity(capacity),
            eq_fn,
        }
    }

    pub fn get(&self, key: i64, key_hash: i64) -> Option<i64> {
        let hash = key_hash as u64;
        self.table
            .find(hash, |(_, k, _)| (self.eq_fn)(*k, key))
            .map(|(_, _, v)| *v)
    }

    pub fn set(&mut self, key: i64, key_hash: i64, value: i64) {
        let hash = key_hash as u64;
        let eq_fn = self.eq_fn;

        // Check if key exists and update
        if let Some((_, _, v)) = self.table.find_mut(hash, |(_, k, _)| eq_fn(*k, key)) {
            *v = value;
            return;
        }

        // Insert new entry with stored hash for resize operations
        self.table
            .insert_unique(hash, (hash, key, value), |(h, _, _)| *h);
    }

    pub fn remove(&mut self, key: i64, key_hash: i64) -> Option<i64> {
        let hash = key_hash as u64;
        let eq_fn = self.eq_fn;

        match self.table.find_entry(hash, |(_, k, _)| eq_fn(*k, key)) {
            Ok(entry) => {
                let (_, _, value) = entry.remove().0;
                Some(value)
            }
            Err(_) => None,
        }
    }

    pub fn contains_key(&self, key: i64, key_hash: i64) -> bool {
        let hash = key_hash as u64;
        self.table
            .find(hash, |(_, k, _)| (self.eq_fn)(*k, key))
            .is_some()
    }

    pub fn len(&self) -> usize {
        self.table.len()
    }

    pub fn is_empty(&self) -> bool {
        self.table.is_empty()
    }

    pub fn clear(&mut self) {
        self.table.clear();
    }

    pub fn keys(&self) -> Vec<i64> {
        self.table.iter().map(|(_, k, _)| *k).collect()
    }

    pub fn values(&self) -> Vec<i64> {
        self.table.iter().map(|(_, _, v)| *v).collect()
    }

    pub fn entries(&self) -> Vec<(i64, i64)> {
        self.table.iter().map(|(_, k, v)| (*k, *v)).collect()
    }
}

/// Reference-counted VoleMap for Vole runtime
pub type RcMap = Rc<RefCell<VoleMap>>;

// =============================================================================
// VoleSet - Hash set for Vole Set<T> type
// =============================================================================

/// A Vole set storing elements as i64 words with pre-computed hashes.
/// Uses HashTable for full control over hashing and equality.
pub struct VoleSet {
    table: HashTable<(u64, i64)>, // (hash, value) pairs
    eq_fn: EqFn,
}

impl VoleSet {
    pub fn new(eq_fn: EqFn) -> Self {
        Self {
            table: HashTable::new(),
            eq_fn,
        }
    }

    pub fn with_capacity(capacity: usize, eq_fn: EqFn) -> Self {
        Self {
            table: HashTable::with_capacity(capacity),
            eq_fn,
        }
    }

    pub fn add(&mut self, value: i64, hash: i64) -> bool {
        let hash = hash as u64;
        let eq_fn = self.eq_fn;

        // Check if already present
        if self.table.find(hash, |(_, v)| eq_fn(*v, value)).is_some() {
            return false;
        }

        // Insert new entry
        self.table.insert_unique(hash, (hash, value), |(h, _)| *h);
        true
    }

    pub fn remove(&mut self, value: i64, hash: i64) -> bool {
        let hash = hash as u64;
        let eq_fn = self.eq_fn;

        match self.table.find_entry(hash, |(_, v)| eq_fn(*v, value)) {
            Ok(entry) => {
                entry.remove();
                true
            }
            Err(_) => false,
        }
    }

    pub fn contains(&self, value: i64, hash: i64) -> bool {
        let hash = hash as u64;
        self.table
            .find(hash, |(_, v)| (self.eq_fn)(*v, value))
            .is_some()
    }

    pub fn len(&self) -> usize {
        self.table.len()
    }

    pub fn is_empty(&self) -> bool {
        self.table.is_empty()
    }

    pub fn clear(&mut self) {
        self.table.clear();
    }

    pub fn values(&self) -> Vec<i64> {
        self.table.iter().map(|(_, v)| *v).collect()
    }

    // Set operations - these use self's eq_fn for the result
    pub fn union(&self, other: &VoleSet) -> VoleSet {
        let mut result = VoleSet::new(self.eq_fn);
        // Add all from self
        for (hash, value) in self.table.iter() {
            result
                .table
                .insert_unique(*hash, (*hash, *value), |(h, _)| *h);
        }
        // Add all from other (duplicates handled by eq check)
        for (hash, value) in other.table.iter() {
            if result
                .table
                .find(*hash, |(_, v)| (self.eq_fn)(*v, *value))
                .is_none()
            {
                result
                    .table
                    .insert_unique(*hash, (*hash, *value), |(h, _)| *h);
            }
        }
        result
    }

    pub fn intersection(&self, other: &VoleSet) -> VoleSet {
        let mut result = VoleSet::new(self.eq_fn);
        for (hash, value) in self.table.iter() {
            if other
                .table
                .find(*hash, |(_, v)| (self.eq_fn)(*v, *value))
                .is_some()
            {
                result
                    .table
                    .insert_unique(*hash, (*hash, *value), |(h, _)| *h);
            }
        }
        result
    }

    pub fn difference(&self, other: &VoleSet) -> VoleSet {
        let mut result = VoleSet::new(self.eq_fn);
        for (hash, value) in self.table.iter() {
            if other
                .table
                .find(*hash, |(_, v)| (self.eq_fn)(*v, *value))
                .is_none()
            {
                result
                    .table
                    .insert_unique(*hash, (*hash, *value), |(h, _)| *h);
            }
        }
        result
    }

    pub fn symmetric_difference(&self, other: &VoleSet) -> VoleSet {
        let mut result = VoleSet::new(self.eq_fn);
        // Add elements in self but not in other
        for (hash, value) in self.table.iter() {
            if other
                .table
                .find(*hash, |(_, v)| (self.eq_fn)(*v, *value))
                .is_none()
            {
                result
                    .table
                    .insert_unique(*hash, (*hash, *value), |(h, _)| *h);
            }
        }
        // Add elements in other but not in self
        for (hash, value) in other.table.iter() {
            if self
                .table
                .find(*hash, |(_, v)| (self.eq_fn)(*v, *value))
                .is_none()
            {
                result
                    .table
                    .insert_unique(*hash, (*hash, *value), |(h, _)| *h);
            }
        }
        result
    }

    pub fn is_subset(&self, other: &VoleSet) -> bool {
        for (hash, value) in self.table.iter() {
            if other
                .table
                .find(*hash, |(_, v)| (self.eq_fn)(*v, *value))
                .is_none()
            {
                return false;
            }
        }
        true
    }

    pub fn is_superset(&self, other: &VoleSet) -> bool {
        other.is_subset(self)
    }

    pub fn is_disjoint(&self, other: &VoleSet) -> bool {
        for (hash, value) in self.table.iter() {
            if other
                .table
                .find(*hash, |(_, v)| (self.eq_fn)(*v, *value))
                .is_some()
            {
                return false;
            }
        }
        true
    }
}

/// Reference-counted VoleSet for Vole runtime
pub type RcSet = Rc<RefCell<VoleSet>>;

// =============================================================================
// FFI Functions for Map<K, V>
// =============================================================================

// Note: These FFI functions currently use i64_eq as the default equality function.
// When generic Map<K,V> support is added (vole-9x0.2), codegen will inject the
// appropriate eq_fn based on the type parameter's Eq implementation.

/// Create a new empty map (uses i64 equality by default)
#[unsafe(no_mangle)]
pub extern "C" fn map_new() -> *const RefCell<VoleMap> {
    Rc::into_raw(Rc::new(RefCell::new(VoleMap::new(i64_eq))))
}

/// Create a new map with the given capacity (uses i64 equality by default)
#[unsafe(no_mangle)]
pub extern "C" fn map_with_capacity(capacity: i64) -> *const RefCell<VoleMap> {
    Rc::into_raw(Rc::new(RefCell::new(VoleMap::with_capacity(
        capacity as usize,
        i64_eq,
    ))))
}

/// Get a value from the map. Returns a tagged optional (0 = nil, non-zero = Some).
/// The value is returned in the high bits if present.
#[unsafe(no_mangle)]
pub extern "C" fn map_get(map_ptr: *const RefCell<VoleMap>, key: i64, key_hash: i64) -> i64 {
    let map = unsafe { &*map_ptr };
    match map.borrow().get(key, key_hash) {
        Some(value) => value,
        None => 0, // nil sentinel - caller should check tag
    }
}

/// Check if map has a value for the given key (for optional return)
#[unsafe(no_mangle)]
pub extern "C" fn map_has(map_ptr: *const RefCell<VoleMap>, key: i64, key_hash: i64) -> i8 {
    let map = unsafe { &*map_ptr };
    if map.borrow().contains_key(key, key_hash) {
        1
    } else {
        0
    }
}

/// Set a value in the map
#[unsafe(no_mangle)]
pub extern "C" fn map_set(map_ptr: *const RefCell<VoleMap>, key: i64, key_hash: i64, value: i64) {
    let map = unsafe { &*map_ptr };
    map.borrow_mut().set(key, key_hash, value);
}

/// Remove a key from the map, returning the old value if present
#[unsafe(no_mangle)]
pub extern "C" fn map_remove(map_ptr: *const RefCell<VoleMap>, key: i64, key_hash: i64) -> i64 {
    let map = unsafe { &*map_ptr };
    map.borrow_mut().remove(key, key_hash).unwrap_or(0)
}

/// Check if map contains a key
#[unsafe(no_mangle)]
pub extern "C" fn map_contains_key(
    map_ptr: *const RefCell<VoleMap>,
    key: i64,
    key_hash: i64,
) -> i8 {
    let map = unsafe { &*map_ptr };
    if map.borrow().contains_key(key, key_hash) {
        1
    } else {
        0
    }
}

/// Get the number of entries in the map
#[unsafe(no_mangle)]
pub extern "C" fn map_len(map_ptr: *const RefCell<VoleMap>) -> i64 {
    let map = unsafe { &*map_ptr };
    map.borrow().len() as i64
}

/// Clear all entries from the map
#[unsafe(no_mangle)]
pub extern "C" fn map_clear(map_ptr: *const RefCell<VoleMap>) {
    let map = unsafe { &*map_ptr };
    map.borrow_mut().clear();
}

/// Helper to create an array from a Vec<i64>
fn vec_to_array(values: Vec<i64>) -> *mut RcArray {
    let array = RcArray::with_capacity(values.len());
    for v in values {
        unsafe {
            RcArray::push(array, TaggedValue::from_i64(v));
        }
    }
    array
}

/// Get an iterator over the map's keys
#[unsafe(no_mangle)]
pub extern "C" fn map_keys_iter(map_ptr: *const RefCell<VoleMap>) -> *mut UnifiedIterator {
    let map = unsafe { &*map_ptr };
    let keys: Vec<i64> = map.borrow().keys();
    let array = vec_to_array(keys);
    Box::into_raw(Box::new(UnifiedIterator {
        kind: IteratorKind::Array,
        source: IteratorSource {
            array: ArraySource { array, index: 0 },
        },
    }))
}

/// Get an iterator over the map's values
#[unsafe(no_mangle)]
pub extern "C" fn map_values_iter(map_ptr: *const RefCell<VoleMap>) -> *mut UnifiedIterator {
    let map = unsafe { &*map_ptr };
    let values: Vec<i64> = map.borrow().values();
    let array = vec_to_array(values);
    Box::into_raw(Box::new(UnifiedIterator {
        kind: IteratorKind::Array,
        source: IteratorSource {
            array: ArraySource { array, index: 0 },
        },
    }))
}

/// Get an iterator over the map's entries as [key, value] tuples
#[unsafe(no_mangle)]
pub extern "C" fn map_entries_iter(map_ptr: *const RefCell<VoleMap>) -> *mut UnifiedIterator {
    let map = unsafe { &*map_ptr };
    let entries: Vec<(i64, i64)> = map.borrow().entries();

    // Create an array of tuple pointers
    let tuples: Vec<i64> = entries
        .into_iter()
        .map(|(k, v)| {
            // Create a 2-element tuple as an RcArray
            let tuple = RcArray::with_capacity(2);
            unsafe {
                RcArray::push(tuple, TaggedValue::from_i64(k));
                RcArray::push(tuple, TaggedValue::from_i64(v));
            }
            tuple as i64
        })
        .collect();

    let array = vec_to_array(tuples);
    Box::into_raw(Box::new(UnifiedIterator {
        kind: IteratorKind::Array,
        source: IteratorSource {
            array: ArraySource { array, index: 0 },
        },
    }))
}

/// Increment map reference count
#[unsafe(no_mangle)]
pub extern "C" fn map_inc_ref(map_ptr: *const RefCell<VoleMap>) {
    unsafe {
        Rc::increment_strong_count(map_ptr);
    }
}

/// Decrement map reference count
#[unsafe(no_mangle)]
pub extern "C" fn map_dec_ref(map_ptr: *const RefCell<VoleMap>) {
    unsafe {
        Rc::decrement_strong_count(map_ptr);
    }
}

// =============================================================================
// FFI Functions for Set<T>
// =============================================================================

// Note: These FFI functions currently use i64_eq as the default equality function.
// When generic Set<T> support is added (vole-9x0.2), codegen will inject the
// appropriate eq_fn based on the type parameter's Eq implementation.

/// Create a new empty set (uses i64 equality by default)
#[unsafe(no_mangle)]
pub extern "C" fn set_new() -> *const RefCell<VoleSet> {
    Rc::into_raw(Rc::new(RefCell::new(VoleSet::new(i64_eq))))
}

/// Create a new set with the given capacity (uses i64 equality by default)
#[unsafe(no_mangle)]
pub extern "C" fn set_with_capacity(capacity: i64) -> *const RefCell<VoleSet> {
    Rc::into_raw(Rc::new(RefCell::new(VoleSet::with_capacity(
        capacity as usize,
        i64_eq,
    ))))
}

/// Add a value to the set, returns true if it was newly inserted
#[unsafe(no_mangle)]
pub extern "C" fn set_add(set_ptr: *const RefCell<VoleSet>, value: i64, hash: i64) -> i8 {
    let set = unsafe { &*set_ptr };
    if set.borrow_mut().add(value, hash) {
        1
    } else {
        0
    }
}

/// Remove a value from the set, returns true if it was present
#[unsafe(no_mangle)]
pub extern "C" fn set_remove(set_ptr: *const RefCell<VoleSet>, value: i64, hash: i64) -> i8 {
    let set = unsafe { &*set_ptr };
    if set.borrow_mut().remove(value, hash) {
        1
    } else {
        0
    }
}

/// Check if set contains a value
#[unsafe(no_mangle)]
pub extern "C" fn set_contains(set_ptr: *const RefCell<VoleSet>, value: i64, hash: i64) -> i8 {
    let set = unsafe { &*set_ptr };
    if set.borrow().contains(value, hash) {
        1
    } else {
        0
    }
}

/// Get the number of elements in the set
#[unsafe(no_mangle)]
pub extern "C" fn set_len(set_ptr: *const RefCell<VoleSet>) -> i64 {
    let set = unsafe { &*set_ptr };
    set.borrow().len() as i64
}

/// Clear all elements from the set
#[unsafe(no_mangle)]
pub extern "C" fn set_clear(set_ptr: *const RefCell<VoleSet>) {
    let set = unsafe { &*set_ptr };
    set.borrow_mut().clear();
}

/// Get an iterator over the set's values
#[unsafe(no_mangle)]
pub extern "C" fn set_iter(set_ptr: *const RefCell<VoleSet>) -> *mut UnifiedIterator {
    let set = unsafe { &*set_ptr };
    let values: Vec<i64> = set.borrow().values();
    let array = vec_to_array(values);
    Box::into_raw(Box::new(UnifiedIterator {
        kind: IteratorKind::Array,
        source: IteratorSource {
            array: ArraySource { array, index: 0 },
        },
    }))
}

/// Compute union of two sets
#[unsafe(no_mangle)]
pub extern "C" fn set_union(
    a_ptr: *const RefCell<VoleSet>,
    b_ptr: *const RefCell<VoleSet>,
) -> *const RefCell<VoleSet> {
    let a = unsafe { &*a_ptr };
    let b = unsafe { &*b_ptr };
    let result = a.borrow().union(&b.borrow());
    Rc::into_raw(Rc::new(RefCell::new(result)))
}

/// Compute intersection of two sets
#[unsafe(no_mangle)]
pub extern "C" fn set_intersection(
    a_ptr: *const RefCell<VoleSet>,
    b_ptr: *const RefCell<VoleSet>,
) -> *const RefCell<VoleSet> {
    let a = unsafe { &*a_ptr };
    let b = unsafe { &*b_ptr };
    let result = a.borrow().intersection(&b.borrow());
    Rc::into_raw(Rc::new(RefCell::new(result)))
}

/// Compute difference of two sets (a - b)
#[unsafe(no_mangle)]
pub extern "C" fn set_difference(
    a_ptr: *const RefCell<VoleSet>,
    b_ptr: *const RefCell<VoleSet>,
) -> *const RefCell<VoleSet> {
    let a = unsafe { &*a_ptr };
    let b = unsafe { &*b_ptr };
    let result = a.borrow().difference(&b.borrow());
    Rc::into_raw(Rc::new(RefCell::new(result)))
}

/// Compute symmetric difference of two sets
#[unsafe(no_mangle)]
pub extern "C" fn set_symmetric_difference(
    a_ptr: *const RefCell<VoleSet>,
    b_ptr: *const RefCell<VoleSet>,
) -> *const RefCell<VoleSet> {
    let a = unsafe { &*a_ptr };
    let b = unsafe { &*b_ptr };
    let result = a.borrow().symmetric_difference(&b.borrow());
    Rc::into_raw(Rc::new(RefCell::new(result)))
}

/// Check if a is subset of b
#[unsafe(no_mangle)]
pub extern "C" fn set_is_subset(
    a_ptr: *const RefCell<VoleSet>,
    b_ptr: *const RefCell<VoleSet>,
) -> i8 {
    let a = unsafe { &*a_ptr };
    let b = unsafe { &*b_ptr };
    if a.borrow().is_subset(&b.borrow()) {
        1
    } else {
        0
    }
}

/// Check if a is superset of b
#[unsafe(no_mangle)]
pub extern "C" fn set_is_superset(
    a_ptr: *const RefCell<VoleSet>,
    b_ptr: *const RefCell<VoleSet>,
) -> i8 {
    let a = unsafe { &*a_ptr };
    let b = unsafe { &*b_ptr };
    if a.borrow().is_superset(&b.borrow()) {
        1
    } else {
        0
    }
}

/// Check if two sets are disjoint (no common elements)
#[unsafe(no_mangle)]
pub extern "C" fn set_is_disjoint(
    a_ptr: *const RefCell<VoleSet>,
    b_ptr: *const RefCell<VoleSet>,
) -> i8 {
    let a = unsafe { &*a_ptr };
    let b = unsafe { &*b_ptr };
    if a.borrow().is_disjoint(&b.borrow()) {
        1
    } else {
        0
    }
}

/// Increment set reference count
#[unsafe(no_mangle)]
pub extern "C" fn set_inc_ref(set_ptr: *const RefCell<VoleSet>) {
    unsafe {
        Rc::increment_strong_count(set_ptr);
    }
}

/// Decrement set reference count
#[unsafe(no_mangle)]
pub extern "C" fn set_dec_ref(set_ptr: *const RefCell<VoleSet>) {
    unsafe {
        Rc::decrement_strong_count(set_ptr);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_map_basic_operations() {
        let map = VoleMap::new(i64_eq);
        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
    }

    #[test]
    fn test_map_set_get() {
        let mut map = VoleMap::new(i64_eq);

        // Use simple hash for test (key value as hash)
        map.set(1, 1, 100);
        map.set(2, 2, 200);

        assert_eq!(map.get(1, 1), Some(100));
        assert_eq!(map.get(2, 2), Some(200));
        assert_eq!(map.get(3, 3), None);
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn test_map_remove() {
        let mut map = VoleMap::new(i64_eq);
        map.set(1, 1, 100);

        assert_eq!(map.remove(1, 1), Some(100));
        assert_eq!(map.remove(1, 1), None);
        assert!(map.is_empty());
    }

    #[test]
    fn test_set_basic_operations() {
        let set = VoleSet::new(i64_eq);
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
    }

    #[test]
    fn test_set_add_contains() {
        let mut set = VoleSet::new(i64_eq);

        assert!(set.add(1, 1));
        assert!(!set.add(1, 1)); // Already present
        assert!(set.add(2, 2));

        assert!(set.contains(1, 1));
        assert!(set.contains(2, 2));
        assert!(!set.contains(3, 3));
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn test_set_operations() {
        let mut a = VoleSet::new(i64_eq);
        a.add(1, 1);
        a.add(2, 2);

        let mut b = VoleSet::new(i64_eq);
        b.add(2, 2);
        b.add(3, 3);

        let union = a.union(&b);
        assert_eq!(union.len(), 3);

        let intersection = a.intersection(&b);
        assert_eq!(intersection.len(), 1);
        assert!(intersection.contains(2, 2));

        let diff = a.difference(&b);
        assert_eq!(diff.len(), 1);
        assert!(diff.contains(1, 1));
    }

    // Test custom equality function injection
    // This simulates comparing "Point" structs where the i64 is a pointer
    // and equality compares the underlying field values

    /// Custom equality that compares only the lower 32 bits (simulating field comparison)
    extern "C" fn lower_bits_eq(a: i64, b: i64) -> bool {
        (a & 0xFFFFFFFF) == (b & 0xFFFFFFFF)
    }

    #[test]
    fn test_map_custom_equality() {
        let mut map = VoleMap::new(lower_bits_eq);

        // Two values with same lower 32 bits but different upper bits
        let val1: i64 = 0x0000_0001_0000_0005; // lower = 5
        let val2: i64 = 0x0000_0002_0000_0005; // lower = 5 (same as val1)
        let val3: i64 = 0x0000_0001_0000_0006; // lower = 6 (different)

        // Use lower bits as hash
        map.set(val1, 5, 100);
        assert_eq!(map.get(val1, 5), Some(100));

        // val2 should find the same entry (same lower bits = same key)
        assert_eq!(map.get(val2, 5), Some(100));

        // Updating with val2 should update the same entry
        map.set(val2, 5, 200);
        assert_eq!(map.get(val1, 5), Some(200));
        assert_eq!(map.len(), 1); // Still just one entry

        // val3 is a different key
        map.set(val3, 6, 300);
        assert_eq!(map.len(), 2);
        assert_eq!(map.get(val3, 6), Some(300));
    }

    #[test]
    fn test_set_custom_equality() {
        let mut set = VoleSet::new(lower_bits_eq);

        let val1: i64 = 0x0000_0001_0000_0005; // lower = 5
        let val2: i64 = 0x0000_0002_0000_0005; // lower = 5 (same as val1)
        let val3: i64 = 0x0000_0001_0000_0006; // lower = 6 (different)

        assert!(set.add(val1, 5)); // Added
        assert!(!set.add(val2, 5)); // Not added - considered equal to val1
        assert!(set.add(val3, 6)); // Added - different key

        assert_eq!(set.len(), 2);
        assert!(set.contains(val1, 5));
        assert!(set.contains(val2, 5)); // Found via custom equality
        assert!(set.contains(val3, 6));
    }
}
