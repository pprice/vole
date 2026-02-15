//! Iterator collect operations and shared consumer helpers.

use crate::array::RcArray;
use crate::iterator_abi::TaggedNextWord;
use crate::iterator_core::CoreIter;
use crate::value::{rc_dec, rc_inc, tag_needs_rc};
use std::alloc::{Layout, alloc};
use std::ptr;

use super::combine::vole_flatten_iter_collect;
use super::types::*;
use super::{iter_produces_owned, vole_array_iter_next};

pub(super) fn pack_optional_i64(value: Option<i64>) -> *mut u8 {
    let layout = Layout::from_size_align(TaggedNextWord::SIZE, TaggedNextWord::ALIGN)
        .expect("valid optional layout");
    let ptr = unsafe { alloc(layout) };
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    unsafe {
        match value {
            Some(v) => {
                ptr::write(ptr, 0u8);
                ptr::write(ptr.add(TaggedNextWord::PAYLOAD_OFFSET) as *mut i64, v);
            }
            None => {
                ptr::write(ptr, 1u8);
                ptr::write(ptr.add(TaggedNextWord::PAYLOAD_OFFSET) as *mut i64, 0);
            }
        }
    }
    ptr
}

pub(super) fn consume_values_via_next(iter: *mut RcIterator, limit: Option<usize>) -> Vec<i64> {
    let mut out = Vec::new();
    if iter.is_null() {
        return out;
    }
    loop {
        if let Some(max) = limit
            && out.len() >= max
        {
            break;
        }
        let mut value = 0i64;
        if vole_array_iter_next(iter, &mut value) == 0 {
            break;
        }
        out.push(value);
    }
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }
    out
}

pub(super) fn cleanup_owned_rc_except(words: &[i64], keep_index: Option<usize>, owned_rc: bool) {
    if !owned_rc {
        return;
    }
    for (idx, &value) in words.iter().enumerate() {
        if Some(idx) != keep_index && value != 0 {
            rc_dec(value as *mut u8);
        }
    }
}

pub(super) fn try_new_core_collect_tagged(
    iter: *mut RcIterator,
    elem_tag: u64,
) -> Option<*mut RcArray> {
    use crate::value::TaggedValue;

    if iter.is_null() {
        return Some(RcArray::new());
    }

    let values_owned = iter_produces_owned(iter);
    let needs_rc = tag_needs_rc(elem_tag);
    let words = consume_values_via_next(iter, None);
    let collected = CoreIter::from_i64_slice(&words).collect_i64().ok()?;
    let result = RcArray::new();

    for value in collected {
        let actual_tag = if needs_rc && !(value as usize).is_multiple_of(8) {
            0u64
        } else {
            elem_tag
        };
        let actual_needs_rc = tag_needs_rc(actual_tag);
        if actual_needs_rc && !values_owned && value != 0 {
            rc_inc(value as *mut u8);
        }
        unsafe {
            RcArray::push(
                result,
                TaggedValue {
                    tag: actual_tag,
                    value: value as u64,
                },
            );
        }
    }

    Some(result)
}

pub(super) fn try_new_core_first(iter: *mut RcIterator) -> Option<*mut u8> {
    let borrowed_rc = if iter.is_null() {
        false
    } else {
        iter_produces_borrowed_rc(iter)
    };
    let words = consume_values_via_next(iter, Some(1));
    let value = CoreIter::from_i64_slice(&words).first_i64().ok()?;
    if let Some(v) = value
        && borrowed_rc
        && v != 0
    {
        rc_inc(v as *mut u8);
    }
    Some(pack_optional_i64(value))
}

pub(super) fn try_new_core_last(iter: *mut RcIterator) -> Option<*mut u8> {
    let owned_rc = if iter.is_null() {
        false
    } else {
        iter_produces_owned_rc(iter)
    };
    let borrowed_rc = if iter.is_null() {
        false
    } else {
        iter_produces_borrowed_rc(iter)
    };
    let words = consume_values_via_next(iter, None);
    let value = CoreIter::from_i64_slice(&words).last_i64().ok()?;
    let keep_index = if value.is_some() && !words.is_empty() {
        Some(words.len() - 1)
    } else {
        None
    };
    cleanup_owned_rc_except(&words, keep_index, owned_rc);
    if let Some(v) = value
        && borrowed_rc
        && v != 0
    {
        rc_inc(v as *mut u8);
    }
    Some(pack_optional_i64(value))
}

pub(super) fn try_new_core_nth(iter: *mut RcIterator, n: i64) -> Option<*mut u8> {
    if n < 0 {
        if !iter.is_null() {
            // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
            unsafe {
                RcIterator::dec_ref(iter);
            }
        }
        return Some(pack_optional_i64(None));
    }
    let owned_rc = if iter.is_null() {
        false
    } else {
        iter_produces_owned_rc(iter)
    };
    let borrowed_rc = if iter.is_null() {
        false
    } else {
        iter_produces_borrowed_rc(iter)
    };
    let words = consume_values_via_next(iter, Some((n as usize).saturating_add(1)));
    let value = CoreIter::from_i64_slice(&words).nth_i64(n as usize).ok()?;
    let keep_index = if value.is_some() {
        Some(n as usize)
    } else {
        None
    };
    cleanup_owned_rc_except(&words, keep_index, owned_rc);
    if let Some(v) = value
        && borrowed_rc
        && v != 0
    {
        rc_inc(v as *mut u8);
    }
    Some(pack_optional_i64(value))
}

/// Collect all remaining iterator values into a new array with proper element type tags.
/// Reads `elem_tag` from the iterator's stored tag (set by codegen or
/// `interface_iter_tagged`). Used by vtable dispatch where the extra tag
/// parameter is not available in the interface signature.
/// Frees the iterator after collecting.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_iter_collect(iter: *mut RcIterator) -> *mut RcArray {
    if iter.is_null() {
        return vole_iter_collect_tagged(iter, 0);
    }

    let kind = unsafe { (*iter).iter.kind };
    let tag = unsafe { (*iter).elem_tag };

    // For Flatten iterators, use vole_flatten_iter_collect which reads
    // the correct inner element tag. The codegen-set elem_tag may incorrectly
    // be RuntimeTypeId::Array (the pre-flatten outer element type) rather than the
    // flattened inner element type (e.g. RuntimeTypeId::F64).
    if kind == IteratorKind::Flatten {
        return vole_flatten_iter_collect(iter);
    }

    vole_iter_collect_tagged(iter, tag)
}

/// Collect all remaining iterator values into a new array with proper element type tags.
/// `elem_tag` is the runtime type tag for the element type.
/// Frees the iterator after collecting.
#[unsafe(no_mangle)]
pub extern "C" fn vole_iter_collect_tagged(iter: *mut RcIterator, elem_tag: u64) -> *mut RcArray {
    try_new_core_collect_tagged(iter, elem_tag).expect("collect path should always produce a value")
}

/// Collect all remaining iterator values into a new array.
/// Frees the iterator after collecting.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_array_iter_collect(iter: *mut RcIterator) -> *mut RcArray {
    use crate::value::TaggedValue;

    let result = RcArray::new();

    if iter.is_null() {
        return result;
    }

    loop {
        let mut value: i64 = 0;
        let has_value = vole_array_iter_next(iter, &mut value);

        if has_value == 0 {
            break;
        }

        // Push to result array with value
        unsafe {
            RcArray::push(
                result,
                TaggedValue {
                    tag: 0, // i64 type
                    value: value as u64,
                },
            );
        }
    }

    // Free the iterator chain
    // SAFETY: ptr was obtained from a valid RcIterator allocation or is null
    unsafe {
        RcIterator::dec_ref(iter);
    }

    result
}

/// Check if an iterator produces owned RC values that need to be freed when discarded.
pub(super) fn iter_produces_owned_rc(iter: *mut RcIterator) -> bool {
    if iter.is_null() {
        return false;
    }
    let tag = unsafe { (*iter).elem_tag };
    tag_needs_rc(tag) && iter_produces_owned(iter)
}

/// Returns true if the iterator produces borrowed RC values.
pub(super) fn iter_produces_borrowed_rc(iter: *mut RcIterator) -> bool {
    if iter.is_null() {
        return false;
    }
    let tag = unsafe { (*iter).elem_tag };
    tag_needs_rc(tag) && !iter_produces_owned(iter)
}
