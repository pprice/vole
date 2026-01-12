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
use std::hash::{BuildHasher, Hasher};
use std::rc::Rc;

use hashbrown::{HashMap, HashSet};

use crate::runtime::array::RcArray;
use crate::runtime::iterator::{ArraySource, IteratorKind, IteratorSource, UnifiedIterator};
use crate::runtime::value::TaggedValue;

// =============================================================================
// VoleMap - Hash map for Vole Map<K, V> type
// =============================================================================

/// A Vole map storing key-value pairs as i64 words.
/// Keys are stored with their pre-computed hash from Hashable.hash().
#[derive(Debug)]
pub struct VoleMap {
    inner: HashMap<HashedKey, i64, PassthroughBuildHasher>,
}

/// A key with its pre-computed hash value from Vole's Hashable interface.
#[derive(Debug, Clone, Copy)]
struct HashedKey {
    value: i64,
    hash: u64,
}

impl PartialEq for HashedKey {
    fn eq(&self, other: &Self) -> bool {
        // For Vole values, equality is based on the raw i64 value
        // This works for integers and reference types (pointer equality)
        self.value == other.value
    }
}

impl Eq for HashedKey {}

impl std::hash::Hash for HashedKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Use the pre-computed hash from Vole's Hashable interface
        state.write_u64(self.hash);
    }
}

/// A hasher that passes through already-hashed values.
#[derive(Default)]
struct PassthroughHasher(u64);

impl Hasher for PassthroughHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, _bytes: &[u8]) {
        // Not used - we only use write_u64
    }

    fn write_u64(&mut self, i: u64) {
        self.0 = i;
    }
}

#[derive(Default, Clone)]
struct PassthroughBuildHasher;

impl BuildHasher for PassthroughBuildHasher {
    type Hasher = PassthroughHasher;

    fn build_hasher(&self) -> Self::Hasher {
        PassthroughHasher::default()
    }
}

impl VoleMap {
    pub fn new() -> Self {
        Self {
            inner: HashMap::with_hasher(PassthroughBuildHasher),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: HashMap::with_capacity_and_hasher(capacity, PassthroughBuildHasher),
        }
    }

    pub fn get(&self, key: i64, key_hash: i64) -> Option<i64> {
        let hashed = HashedKey {
            value: key,
            hash: key_hash as u64,
        };
        self.inner.get(&hashed).copied()
    }

    pub fn set(&mut self, key: i64, key_hash: i64, value: i64) {
        let hashed = HashedKey {
            value: key,
            hash: key_hash as u64,
        };
        self.inner.insert(hashed, value);
    }

    pub fn remove(&mut self, key: i64, key_hash: i64) -> Option<i64> {
        let hashed = HashedKey {
            value: key,
            hash: key_hash as u64,
        };
        self.inner.remove(&hashed)
    }

    pub fn contains_key(&self, key: i64, key_hash: i64) -> bool {
        let hashed = HashedKey {
            value: key,
            hash: key_hash as u64,
        };
        self.inner.contains_key(&hashed)
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn clear(&mut self) {
        self.inner.clear();
    }

    pub fn keys(&self) -> Vec<i64> {
        self.inner.keys().map(|k| k.value).collect()
    }

    pub fn values(&self) -> Vec<i64> {
        self.inner.values().copied().collect()
    }

    pub fn entries(&self) -> Vec<(i64, i64)> {
        self.inner.iter().map(|(k, v)| (k.value, *v)).collect()
    }
}

impl Default for VoleMap {
    fn default() -> Self {
        Self::new()
    }
}

/// Reference-counted VoleMap for Vole runtime
pub type RcMap = Rc<RefCell<VoleMap>>;

// =============================================================================
// VoleSet - Hash set for Vole Set<T> type
// =============================================================================

/// A Vole set storing elements as i64 words with pre-computed hashes.
#[derive(Debug)]
pub struct VoleSet {
    inner: HashSet<HashedKey, PassthroughBuildHasher>,
}

impl VoleSet {
    pub fn new() -> Self {
        Self {
            inner: HashSet::with_hasher(PassthroughBuildHasher),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: HashSet::with_capacity_and_hasher(capacity, PassthroughBuildHasher),
        }
    }

    pub fn add(&mut self, value: i64, hash: i64) -> bool {
        let hashed = HashedKey {
            value,
            hash: hash as u64,
        };
        self.inner.insert(hashed)
    }

    pub fn remove(&mut self, value: i64, hash: i64) -> bool {
        let hashed = HashedKey {
            value,
            hash: hash as u64,
        };
        self.inner.remove(&hashed)
    }

    pub fn contains(&self, value: i64, hash: i64) -> bool {
        let hashed = HashedKey {
            value,
            hash: hash as u64,
        };
        self.inner.contains(&hashed)
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn clear(&mut self) {
        self.inner.clear();
    }

    pub fn values(&self) -> Vec<i64> {
        self.inner.iter().map(|k| k.value).collect()
    }

    // Set operations
    pub fn union(&self, other: &VoleSet) -> VoleSet {
        VoleSet {
            inner: self.inner.union(&other.inner).copied().collect(),
        }
    }

    pub fn intersection(&self, other: &VoleSet) -> VoleSet {
        VoleSet {
            inner: self.inner.intersection(&other.inner).copied().collect(),
        }
    }

    pub fn difference(&self, other: &VoleSet) -> VoleSet {
        VoleSet {
            inner: self.inner.difference(&other.inner).copied().collect(),
        }
    }

    pub fn symmetric_difference(&self, other: &VoleSet) -> VoleSet {
        VoleSet {
            inner: self
                .inner
                .symmetric_difference(&other.inner)
                .copied()
                .collect(),
        }
    }

    pub fn is_subset(&self, other: &VoleSet) -> bool {
        self.inner.is_subset(&other.inner)
    }

    pub fn is_superset(&self, other: &VoleSet) -> bool {
        self.inner.is_superset(&other.inner)
    }

    pub fn is_disjoint(&self, other: &VoleSet) -> bool {
        self.inner.is_disjoint(&other.inner)
    }
}

impl Default for VoleSet {
    fn default() -> Self {
        Self::new()
    }
}

/// Reference-counted VoleSet for Vole runtime
pub type RcSet = Rc<RefCell<VoleSet>>;

// =============================================================================
// FFI Functions for Map<K, V>
// =============================================================================

/// Create a new empty map
#[unsafe(no_mangle)]
pub extern "C" fn map_new() -> *const RefCell<VoleMap> {
    Rc::into_raw(Rc::new(RefCell::new(VoleMap::new())))
}

/// Create a new map with the given capacity
#[unsafe(no_mangle)]
pub extern "C" fn map_with_capacity(capacity: i64) -> *const RefCell<VoleMap> {
    Rc::into_raw(Rc::new(RefCell::new(VoleMap::with_capacity(
        capacity as usize,
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

/// Create a new empty set
#[unsafe(no_mangle)]
pub extern "C" fn set_new() -> *const RefCell<VoleSet> {
    Rc::into_raw(Rc::new(RefCell::new(VoleSet::new())))
}

/// Create a new set with the given capacity
#[unsafe(no_mangle)]
pub extern "C" fn set_with_capacity(capacity: i64) -> *const RefCell<VoleSet> {
    Rc::into_raw(Rc::new(RefCell::new(VoleSet::with_capacity(
        capacity as usize,
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
        let map = VoleMap::new();
        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
    }

    #[test]
    fn test_map_set_get() {
        let mut map = VoleMap::new();

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
        let mut map = VoleMap::new();
        map.set(1, 1, 100);

        assert_eq!(map.remove(1, 1), Some(100));
        assert_eq!(map.remove(1, 1), None);
        assert!(map.is_empty());
    }

    #[test]
    fn test_set_basic_operations() {
        let set = VoleSet::new();
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
    }

    #[test]
    fn test_set_add_contains() {
        let mut set = VoleSet::new();

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
        let mut a = VoleSet::new();
        a.add(1, 1);
        a.add(2, 2);

        let mut b = VoleSet::new();
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
}
