//! Iterator backend conformance harness.
//!
//! This harness runs the same scenario against multiple iterator backends and
//! compares semantic outputs. During early migration both backends may route to
//! legacy implementations; this still provides a stable test contract for future
//! backend switching.

use std::alloc::{Layout, dealloc};
use std::env;

use crate::array::RcArray;
use crate::closure::Closure;
use crate::iterator::{
    RcIterator, vole_array_iter, vole_iter_all, vole_iter_any, vole_iter_collect_tagged,
    vole_iter_find, vole_iter_first, vole_iter_last, vole_iter_nth, vole_iter_reduce,
};
use crate::iterator_abi::TaggedNextWord;
use crate::value::TaggedValue;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum IteratorBackend {
    Legacy,
    NewCore,
}

impl IteratorBackend {
    fn name(self) -> &'static str {
        match self {
            Self::Legacy => "legacy",
            Self::NewCore => "new_core",
        }
    }
}

/// Backend selector for tests.
///
/// `VOLE_ITERATOR_TEST_BACKEND`:
/// - `both` (default)
/// - `legacy`
/// - `new_core`
fn selected_backends() -> Vec<IteratorBackend> {
    match env::var("VOLE_ITERATOR_TEST_BACKEND").ok().as_deref() {
        Some("legacy") => vec![IteratorBackend::Legacy],
        Some("new_core") => vec![IteratorBackend::NewCore],
        _ => vec![IteratorBackend::Legacy, IteratorBackend::NewCore],
    }
}

fn run_conformance_case<T, F>(case_name: &str, run: F)
where
    T: PartialEq + std::fmt::Debug,
    F: Fn(IteratorBackend) -> T,
{
    let backends = selected_backends();
    let mut outputs: Vec<(IteratorBackend, T)> = backends
        .iter()
        .map(|&backend| (backend, run(backend)))
        .collect();

    if outputs.len() < 2 {
        return;
    }

    let (_, baseline) = outputs.remove(0);
    for (backend, output) in outputs {
        assert_eq!(
            output,
            baseline,
            "iterator parity mismatch in case '{case_name}' for backend '{}'",
            backend.name()
        );
    }
}

fn make_i64_array(values: &[i64]) -> *mut RcArray {
    let array = RcArray::new();
    unsafe {
        for &value in values {
            RcArray::push(array, TaggedValue::from_i64(value));
        }
    }
    array
}

fn collect_i64_values(array: *mut RcArray) -> Vec<i64> {
    let mut out = Vec::new();
    unsafe {
        let len = RcArray::len(array);
        for index in 0..len {
            out.push(RcArray::get(array, index).as_i64());
        }
        RcArray::dec_ref(array);
    }
    out
}

fn decode_optional_i64(ptr: *mut u8) -> Option<i64> {
    if ptr.is_null() {
        return None;
    }
    let result = unsafe {
        let tag = *ptr;
        let payload = *(ptr.add(TaggedNextWord::PAYLOAD_OFFSET) as *const i64);
        if tag == 0 { Some(payload) } else { None }
    };
    let layout = Layout::from_size_align(TaggedNextWord::SIZE, TaggedNextWord::ALIGN)
        .expect("valid optional layout");
    unsafe {
        dealloc(ptr, layout);
    }
    result
}

fn mk_array_iter(backend: IteratorBackend, values: &[i64]) -> *mut RcIterator {
    let array = make_i64_array(values);
    let iter = match backend {
        IteratorBackend::Legacy => vole_array_iter(array),
        // Placeholder routing until the new core backend exists.
        IteratorBackend::NewCore => vole_array_iter(array),
    };
    // Transfer ownership to iterator chain.
    unsafe {
        RcArray::dec_ref(array);
    }
    iter
}

extern "C" fn reducer_sum(_closure: *const Closure, acc: i64, value: i64) -> i64 {
    acc + value
}

extern "C" fn predicate_even(_closure: *const Closure, value: i64) -> i8 {
    (value % 2 == 0) as i8
}

extern "C" fn predicate_gt_ten(_closure: *const Closure, value: i64) -> i8 {
    (value > 10) as i8
}

fn alloc_closure_for_binary_i64(
    fn_ptr: extern "C" fn(*const Closure, i64, i64) -> i64,
) -> *mut Closure {
    unsafe { Closure::alloc(fn_ptr as *const u8, 0) }
}

fn alloc_closure_for_unary_i64_bool(
    fn_ptr: extern "C" fn(*const Closure, i64) -> i8,
) -> *mut Closure {
    unsafe { Closure::alloc(fn_ptr as *const u8, 0) }
}

#[test]
fn parity_collect_tagged() {
    run_conformance_case("collect_tagged", |backend| {
        let iter = mk_array_iter(backend, &[1, 2, 3, 4]);
        let collected = vole_iter_collect_tagged(iter, crate::value::TYPE_I64 as u64);
        collect_i64_values(collected)
    });
}

#[test]
fn parity_first_last_nth() {
    run_conformance_case("first_last_nth", |backend| {
        let first = decode_optional_i64(vole_iter_first(mk_array_iter(backend, &[3, 7, 11, 15])));
        let last = decode_optional_i64(vole_iter_last(mk_array_iter(backend, &[3, 7, 11, 15])));
        let nth = decode_optional_i64(vole_iter_nth(mk_array_iter(backend, &[3, 7, 11, 15]), 2));
        (first, last, nth)
    });
}

#[test]
fn parity_reduce() {
    run_conformance_case("reduce", |backend| {
        let iter = mk_array_iter(backend, &[1, 2, 3, 4, 5]);
        let reducer = alloc_closure_for_binary_i64(reducer_sum);
        vole_iter_reduce(iter, 0, reducer)
    });
}

#[test]
fn parity_find_any_all() {
    run_conformance_case("find_any_all", |backend| {
        let find_predicate = alloc_closure_for_unary_i64_bool(predicate_even);
        let found = decode_optional_i64(vole_iter_find(
            mk_array_iter(backend, &[1, 3, 6, 9]),
            find_predicate,
        ));
        unsafe { Closure::free(find_predicate) };

        let any_predicate = alloc_closure_for_unary_i64_bool(predicate_gt_ten);
        let any = vole_iter_any(mk_array_iter(backend, &[1, 3, 6, 9]), any_predicate);
        unsafe { Closure::free(any_predicate) };

        let all_predicate = alloc_closure_for_unary_i64_bool(predicate_even);
        let all = vole_iter_all(mk_array_iter(backend, &[2, 4, 6, 8]), all_predicate);
        unsafe { Closure::free(all_predicate) };

        (found, any, all)
    });
}
