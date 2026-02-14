//! New iterator core (FFI-agnostic, safe-first).
//!
//! This module is intentionally independent from legacy `extern "C"` iterator entry
//! points. It provides a pull-based engine that can later be wired behind adapters.
#![allow(dead_code)]

use std::sync::Arc;

use crate::iterator_abi::{ElemTag, IteratorError, NextResult, OwnershipMode};

enum CoreNode {
    Array {
        data: Arc<[i64]>,
        index: usize,
    },
    MapI64 {
        source: Box<CoreIter>,
        map_fn: fn(i64) -> i64,
    },
}

/// Core iterator engine used by the rewrite path.
pub(crate) struct CoreIter {
    node: CoreNode,
    elem_tag: ElemTag,
    ownership: OwnershipMode,
}

impl CoreIter {
    /// Construct an iterator over i64 values.
    pub(crate) fn from_i64_slice(values: &[i64]) -> Self {
        Self {
            node: CoreNode::Array {
                data: Arc::<[i64]>::from(values),
                index: 0,
            },
            elem_tag: ElemTag(crate::value::TYPE_I64 as u64),
            ownership: OwnershipMode::Borrowed,
        }
    }

    /// Compose a map stage over i64 values.
    pub(crate) fn map_i64(self, map_fn: fn(i64) -> i64) -> Self {
        Self {
            node: CoreNode::MapI64 {
                source: Box::new(self),
                map_fn,
            },
            elem_tag: ElemTag(crate::value::TYPE_I64 as u64),
            ownership: OwnershipMode::Owned,
        }
    }

    /// Pull one value from the iterator.
    pub(crate) fn next(&mut self) -> Result<NextResult, IteratorError> {
        match &mut self.node {
            CoreNode::Array { data, index } => {
                if *index >= data.len() {
                    return Ok(NextResult::Done);
                }
                let value = data[*index];
                *index += 1;
                Ok(NextResult::Value {
                    value_word: value,
                    elem_tag: self.elem_tag,
                    ownership: self.ownership,
                })
            }
            CoreNode::MapI64 { source, map_fn } => match source.next()? {
                NextResult::Done => Ok(NextResult::Done),
                NextResult::Value {
                    value_word,
                    elem_tag,
                    ..
                } => Ok(NextResult::Value {
                    value_word: map_fn(value_word),
                    elem_tag,
                    ownership: self.ownership,
                }),
            },
        }
    }

    /// Collect all remaining values.
    pub(crate) fn collect_i64(mut self) -> Result<Vec<i64>, IteratorError> {
        let mut out = Vec::new();
        loop {
            match self.next()? {
                NextResult::Done => return Ok(out),
                NextResult::Value { value_word, .. } => out.push(value_word),
            }
        }
    }

    pub(crate) fn first_i64(mut self) -> Result<Option<i64>, IteratorError> {
        match self.next()? {
            NextResult::Done => Ok(None),
            NextResult::Value { value_word, .. } => Ok(Some(value_word)),
        }
    }

    pub(crate) fn last_i64(mut self) -> Result<Option<i64>, IteratorError> {
        let mut last = None;
        loop {
            match self.next()? {
                NextResult::Done => return Ok(last),
                NextResult::Value { value_word, .. } => last = Some(value_word),
            }
        }
    }

    pub(crate) fn nth_i64(mut self, n: usize) -> Result<Option<i64>, IteratorError> {
        let mut i = 0usize;
        loop {
            match self.next()? {
                NextResult::Done => return Ok(None),
                NextResult::Value { value_word, .. } => {
                    if i == n {
                        return Ok(Some(value_word));
                    }
                    i += 1;
                }
            }
        }
    }

    pub(crate) fn reduce_i64(
        mut self,
        init: i64,
        reducer: fn(i64, i64) -> i64,
    ) -> Result<i64, IteratorError> {
        let mut acc = init;
        loop {
            match self.next()? {
                NextResult::Done => return Ok(acc),
                NextResult::Value { value_word, .. } => {
                    acc = reducer(acc, value_word);
                }
            }
        }
    }

    pub(crate) fn find_i64(
        mut self,
        predicate: fn(i64) -> bool,
    ) -> Result<Option<i64>, IteratorError> {
        loop {
            match self.next()? {
                NextResult::Done => return Ok(None),
                NextResult::Value { value_word, .. } => {
                    if predicate(value_word) {
                        return Ok(Some(value_word));
                    }
                }
            }
        }
    }

    pub(crate) fn any_i64(mut self, predicate: fn(i64) -> bool) -> Result<bool, IteratorError> {
        loop {
            match self.next()? {
                NextResult::Done => return Ok(false),
                NextResult::Value { value_word, .. } => {
                    if predicate(value_word) {
                        return Ok(true);
                    }
                }
            }
        }
    }

    pub(crate) fn all_i64(mut self, predicate: fn(i64) -> bool) -> Result<bool, IteratorError> {
        loop {
            match self.next()? {
                NextResult::Done => return Ok(true),
                NextResult::Value { value_word, .. } => {
                    if !predicate(value_word) {
                        return Ok(false);
                    }
                }
            }
        }
    }

    /// Release resources associated with this iterator.
    ///
    /// For the safe core this is currently a no-op (RAII handles memory), but this
    /// explicit primitive mirrors adapter/backend lifecycle hooks.
    pub(crate) fn release(self) {
        drop(self);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn plus_one(v: i64) -> i64 {
        v + 1
    }

    fn sum(acc: i64, v: i64) -> i64 {
        acc + v
    }

    fn is_even(v: i64) -> bool {
        v % 2 == 0
    }

    #[test]
    fn core_pipeline_array_map_collect() {
        let values = CoreIter::from_i64_slice(&[1, 2, 3, 4])
            .map_i64(plus_one)
            .collect_i64()
            .expect("collect should succeed");
        assert_eq!(values, vec![2, 3, 4, 5]);
    }

    #[test]
    fn core_terminal_ops() {
        assert_eq!(
            CoreIter::from_i64_slice(&[3, 7, 11])
                .first_i64()
                .expect("first should succeed"),
            Some(3)
        );
        assert_eq!(
            CoreIter::from_i64_slice(&[3, 7, 11])
                .last_i64()
                .expect("last should succeed"),
            Some(11)
        );
        assert_eq!(
            CoreIter::from_i64_slice(&[3, 7, 11])
                .nth_i64(1)
                .expect("nth should succeed"),
            Some(7)
        );
        assert_eq!(
            CoreIter::from_i64_slice(&[1, 2, 3, 4])
                .reduce_i64(0, sum)
                .expect("reduce should succeed"),
            10
        );
        assert_eq!(
            CoreIter::from_i64_slice(&[1, 3, 6, 9])
                .find_i64(is_even)
                .expect("find should succeed"),
            Some(6)
        );
        assert!(
            CoreIter::from_i64_slice(&[1, 3, 6, 9])
                .any_i64(is_even)
                .expect("any should succeed")
        );
        assert!(
            CoreIter::from_i64_slice(&[2, 4, 6, 8])
                .all_i64(is_even)
                .expect("all should succeed")
        );
    }
}
