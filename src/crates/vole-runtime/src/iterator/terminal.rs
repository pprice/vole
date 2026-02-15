//! Iterator terminal operations: count, sum, for_each, reduce, first, last, nth.

use crate::closure::Closure;
use crate::value::rc_dec;

use super::consumers::{
    iter_produces_owned_rc, try_new_core_first, try_new_core_last, try_new_core_nth,
};
use super::types::*;
use super::{iter_produces_owned, vole_array_iter_next};

// =============================================================================
// Consumer methods - eager evaluation that consumes the entire iterator
// =============================================================================

/// Count the number of elements in any iterator
/// Returns the count as i64
/// Frees the iterator after counting.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_count(iter: *mut RcIterator) -> i64 {
    if iter.is_null() {
        return 0;
    }

    let owned_rc = iter_produces_owned_rc(iter);
    let mut count: i64 = 0;
    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }
        // Free owned RC values that we're discarding (e.g., strings from string iteration)
        if owned_rc && value != 0 {
            rc_dec(value as *mut u8);
        }
        count += 1;
    }

    // Free the iterator chain
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }

    count
}

/// Sum all elements in any iterator.
/// Reads the iterator's stored `elem_tag` to determine whether to perform
/// integer or floating-point addition.
/// When `elem_tag` == RuntimeTypeId::F64, interprets raw bits as f64 and returns f64 bits as i64.
/// Otherwise performs integer (i64) addition.
/// Returns the sum as i64 (raw bits).
/// Frees the iterator after summing.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_sum(iter: *mut RcIterator) -> i64 {
    use crate::value::RuntimeTypeId;

    if iter.is_null() {
        return 0;
    }

    let elem_tag = unsafe { (*iter).elem_tag };

    if elem_tag == RuntimeTypeId::F64 as u64 {
        // Float summation: interpret raw bits as f64
        let mut sum: f64 = 0.0;
        loop {
            let mut value: i64 = 0;
            let has_value = vole_array_iter_next(iter, &mut value);

            if has_value == 0 {
                break;
            }
            sum += f64::from_bits(value as u64);
        }

        // Free the iterator chain
        // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
        unsafe {
            RcIterator::dec_ref(iter);
        }

        sum.to_bits() as i64
    } else {
        // Integer summation — use wrapping_add to match JIT arithmetic semantics
        // (Cranelift iadd wraps by default)
        let mut sum: i64 = 0;
        loop {
            let mut value: i64 = 0;
            let has_value = vole_array_iter_next(iter, &mut value);

            if has_value == 0 {
                break;
            }
            sum = sum.wrapping_add(value);
        }

        // Free the iterator chain
        // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
        unsafe {
            RcIterator::dec_ref(iter);
        }

        sum
    }
}

/// Call a function for each element in any iterator
/// The callback is a closure that takes one i64 argument and returns nothing
/// Frees the iterator after iteration.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_for_each(iter: *mut RcIterator, callback: *const Closure) {
    if iter.is_null() || callback.is_null() {
        return;
    }

    let owned_rc = iter_produces_owned_rc(iter);

    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }

        // Call the callback closure with the value
        // All lambdas now use closure calling convention (closure ptr as first arg)
        unsafe {
            let func_ptr = Closure::get_func(callback);
            let callback_fn: extern "C" fn(*const Closure, i64) = std::mem::transmute(func_ptr);
            callback_fn(callback, value);
        }

        // Free owned RC values after the callback has used them (callback borrows, doesn't own)
        if owned_rc && value != 0 {
            rc_dec(value as *mut u8);
        }
    }

    // Free the iterator chain
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }

    // Free the callback closure (ownership transferred from codegen)
    unsafe { Closure::free(callback as *mut Closure) };
}

/// Reduce all elements in any iterator using an accumulator function, with RC cleanup.
/// `acc_tag` is the runtime type tag for the accumulator type.
/// `elem_tag` is the runtime type tag for the element type.
/// When the accumulator or element is an RC type, old values are properly decremented.
/// Returns the final accumulated value.
/// Frees the iterator after reduction.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_reduce_tagged(
    iter: *mut RcIterator,
    init: i64,
    reducer: *const Closure,
    acc_tag: u64,
    elem_tag: u64,
) -> i64 {
    use crate::value::tag_needs_rc;

    if iter.is_null() || reducer.is_null() {
        return init;
    }

    let acc_is_rc = tag_needs_rc(acc_tag);
    // Use the passed elem_tag to determine if elements need RC cleanup.
    // This is more reliable than checking the iterator's stored elem_tag,
    // which may be unset for interface iterators (generators).
    let elem_is_owned_rc = tag_needs_rc(elem_tag) && iter_produces_owned(iter);

    let mut acc = init;
    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }

        // Call the reducer closure with (acc, value) -> new_acc
        // All lambdas now use closure calling convention (closure ptr as first arg)
        let old_acc = acc;
        unsafe {
            let func_ptr = Closure::get_func(reducer);
            let reducer_fn: extern "C" fn(*const Closure, i64, i64) -> i64 =
                std::mem::transmute(func_ptr);
            acc = reducer_fn(reducer, old_acc, value);
        }

        // Decrement old accumulator if it's an RC type and changed
        if acc_is_rc && old_acc != acc && old_acc != 0 {
            rc_dec(old_acc as *mut u8);
        }
        // Free owned RC element values after the reducer has used them
        if elem_is_owned_rc && value != 0 {
            rc_dec(value as *mut u8);
        }
    }

    // Free the iterator chain
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }

    // Free the reducer closure (ownership transferred from codegen)
    unsafe { Closure::free(reducer as *mut Closure) };

    acc
}

/// Reduce all elements in any iterator using an accumulator function
/// Takes initial value and a reducer closure (acc, value) -> new_acc
/// Returns the final accumulated value
/// Frees the iterator after reduction.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_reduce(
    iter: *mut RcIterator,
    init: i64,
    reducer: *const Closure,
) -> i64 {
    // Delegate to the tagged version using the iterator's stored elem_tag.
    // For reduce, the accumulator type equals the element type (T),
    // so both acc_tag and elem_tag use the same value.
    let tag = if iter.is_null() {
        0
    } else {
        unsafe { (*iter).elem_tag }
    };
    vole_iter_reduce_tagged(iter, init, reducer, tag, tag)
}

/// Get the first element from any iterator, returns T? (optional)
/// Layout: [tag:1][pad:7][payload:8] where tag 0 = value present (I64), tag 1 = nil
/// Note: For T?, variants are sorted by debug string. I64 < Nil alphabetically,
/// so tag 0 = I64 (value), tag 1 = Nil.
/// Frees the iterator after getting the first element.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_first(iter: *mut RcIterator) -> *mut u8 {
    try_new_core_first(iter).expect("first path should always produce a value")
}

/// Get the last element from any iterator, returns T? (optional)
/// Consumes the entire iterator to find the last element.
/// Layout: [tag:1][pad:7][payload:8] where tag 0 = value present (I64), tag 1 = nil
/// Frees the iterator after getting the last element.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_last(iter: *mut RcIterator) -> *mut u8 {
    try_new_core_last(iter).expect("last path should always produce a value")
}

/// Get the nth element from any iterator (0-indexed), returns T? (optional)
/// Layout: [tag:1][pad:7][payload:8] where tag 0 = value present (I64), tag 1 = nil
/// Frees the iterator after getting the nth element.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_nth(iter: *mut RcIterator, n: i64) -> *mut u8 {
    try_new_core_nth(iter, n).expect("nth path should always produce a value")
}
