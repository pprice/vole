// src/sema/well_known.rs
//
// Cached NameIds for well-known stdlib types.
// These are looked up once after prelude loading and cached for fast comparison.

use crate::identity::{NameId, NameTable};

/// Well-known type NameIds from the stdlib prelude.
/// These are populated after prelude loading for fast type identification.
#[derive(Debug, Clone, Default)]
pub struct WellKnownTypes {
    /// std:prelude/traits::Iterator
    pub iterator: Option<NameId>,
    /// std:prelude/traits::Iterable
    pub iterable: Option<NameId>,
    /// std:prelude/traits::Equatable
    pub equatable: Option<NameId>,
    /// std:prelude/traits::Comparable
    pub comparable: Option<NameId>,
    /// std:prelude/traits::Hashable
    pub hashable: Option<NameId>,
    /// std:prelude/traits::Stringable
    pub stringable: Option<NameId>,
}

impl WellKnownTypes {
    /// Create an empty WellKnownTypes (before prelude is loaded)
    pub fn new() -> Self {
        Self::default()
    }

    /// Populate well-known type NameIds after prelude has been loaded.
    /// Call this after `load_prelude()` completes.
    pub fn populate(&mut self, name_table: &mut NameTable) {
        let traits_module = name_table.module_id("std:prelude/traits");

        self.iterator = Some(name_table.intern_raw(traits_module, &["Iterator"]));
        self.iterable = Some(name_table.intern_raw(traits_module, &["Iterable"]));
        self.equatable = Some(name_table.intern_raw(traits_module, &["Equatable"]));
        self.comparable = Some(name_table.intern_raw(traits_module, &["Comparable"]));
        self.hashable = Some(name_table.intern_raw(traits_module, &["Hashable"]));
        self.stringable = Some(name_table.intern_raw(traits_module, &["Stringable"]));
    }

    /// Check if a NameId is the Iterator interface
    pub fn is_iterator(&self, name_id: NameId) -> bool {
        self.iterator == Some(name_id)
    }

    /// Check if a NameId is the Iterable interface
    pub fn is_iterable(&self, name_id: NameId) -> bool {
        self.iterable == Some(name_id)
    }
}
