//! Internal iterator ABI contract for runtime migration.
//!
//! This module is the source of truth for the new iterator core/adapters rewrite.
//! It intentionally defines *internal* contracts only (`pub(crate)` at module boundary).
//!
//! # Ownership Contract
//! - `OwnershipMode::Borrowed`: produced value is borrowed from upstream storage.
//!   Consumers that retain the value must `rc_inc` when `ElemTag` requires RC.
//! - `OwnershipMode::Owned`: produced value is freshly owned by the producer.
//!   Consumers that *consume* the value must `rc_dec` when `ElemTag` requires RC.
//!
//! # Tagged Next Memory Contract
//! `vole_iter_next` and related paths use a tagged-word layout:
//! `[tag: u8][pad: 7 bytes][payload: i64]`.
//! - tag `0` => value present (`payload` contains value word)
//! - tag `1` => done (`payload` ignored, conventionally `0`)
//!
//! # Legacy FFI Mapping (old symbol -> internal operation)
//! - `vole_iter_next` -> `next` + `TaggedNextWord::encode_*`
//! - `vole_iter_collect`/`vole_iter_collect_tagged` -> `collect`
//! - `vole_iter_set_elem_tag` -> `set_elem_tag`
//! - `vole_iter_set_produces_owned` -> `set_ownership_hint`
//! - `vole_*_iter` constructors -> `construct(kind, source)`
#![allow(dead_code)]

use crate::iterator::RcIterator;

/// Opaque handle passed between adapters and iterator core.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IteratorHandle(*mut RcIterator);

impl IteratorHandle {
    /// Construct from raw runtime iterator pointer.
    pub fn from_raw(raw: *mut RcIterator) -> Self {
        Self(raw)
    }

    /// Return the underlying raw pointer for legacy adapter calls.
    pub fn as_raw(self) -> *mut RcIterator {
        self.0
    }

    /// Return true when handle is null.
    pub fn is_null(self) -> bool {
        self.0.is_null()
    }
}

/// Runtime element tag flowing through an iterator.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ElemTag(pub u64);

/// Value ownership mode for produced iterator items.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OwnershipMode {
    Borrowed,
    Owned,
}

impl OwnershipMode {
    pub fn from_produces_owned(produces_owned: bool) -> Self {
        if produces_owned {
            Self::Owned
        } else {
            Self::Borrowed
        }
    }
}

/// Iterator next() semantic result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NextResult {
    Value {
        value_word: i64,
        elem_tag: ElemTag,
        ownership: OwnershipMode,
    },
    Done,
}

/// Internal iterator ABI errors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IteratorError {
    NullIterator,
    InvalidTaggedWordTag(u8),
    InternalInvariant(&'static str),
}

/// Discriminants for tagged next-word results.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NextTag {
    Value = 0,
    Done = 1,
}

/// Fixed memory contract for `next` FFI payload transport.
/// Layout: `[tag: u8][pad: 7 bytes][payload: i64]`.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct TaggedNextWord {
    pub tag: u8,
    pub pad: [u8; 7],
    pub payload: i64,
}

impl TaggedNextWord {
    pub const SIZE: usize = 16;
    pub const ALIGN: usize = 8;
    pub const PAYLOAD_OFFSET: usize = 8;

    pub fn encode_value(value_word: i64) -> Self {
        Self {
            tag: NextTag::Value as u8,
            pad: [0; 7],
            payload: value_word,
        }
    }

    pub fn encode_done() -> Self {
        Self {
            tag: NextTag::Done as u8,
            pad: [0; 7],
            payload: 0,
        }
    }

    pub fn decode(self) -> Result<Option<i64>, IteratorError> {
        match self.tag {
            x if x == NextTag::Value as u8 => Ok(Some(self.payload)),
            x if x == NextTag::Done as u8 => Ok(None),
            x => Err(IteratorError::InvalidTaggedWordTag(x)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tagged_next_word_layout_is_stable() {
        assert_eq!(std::mem::size_of::<TaggedNextWord>(), TaggedNextWord::SIZE);
        assert_eq!(
            std::mem::align_of::<TaggedNextWord>(),
            TaggedNextWord::ALIGN
        );
        assert_eq!(TaggedNextWord::PAYLOAD_OFFSET, 8);
    }

    #[test]
    fn tagged_next_word_round_trip() {
        let value = TaggedNextWord::encode_value(42);
        assert_eq!(value.decode(), Ok(Some(42)));

        let done = TaggedNextWord::encode_done();
        assert_eq!(done.decode(), Ok(None));
    }
}
