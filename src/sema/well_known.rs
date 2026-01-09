// src/sema/well_known.rs
//
// Cached identifiers for well-known stdlib types.
// These are looked up once after prelude loading and cached for fast comparison.

use crate::identity::{MethodId, NameId, NameTable, TypeDefId};
use crate::sema::EntityRegistry;

/// Well-known type identifiers from the stdlib prelude.
/// These are populated after prelude loading for fast type identification.
///
/// Both NameId and TypeDefId are stored for parallel migration:
/// - NameId: Used by existing code that works with InterfaceType.name_id
/// - TypeDefId: Used by new code that works with EntityRegistry
#[derive(Debug, Clone, Default)]
pub struct WellKnownTypes {
    // NameId fields (for compatibility with existing code)
    /// std:prelude/traits::Iterator (NameId)
    pub iterator: Option<NameId>,
    /// std:prelude/traits::Iterable (NameId)
    pub iterable: Option<NameId>,
    /// std:prelude/traits::Equatable (NameId)
    pub equatable: Option<NameId>,
    /// std:prelude/traits::Comparable (NameId)
    pub comparable: Option<NameId>,
    /// std:prelude/traits::Hashable (NameId)
    pub hashable: Option<NameId>,
    /// std:prelude/traits::Stringable (NameId)
    pub stringable: Option<NameId>,

    // TypeDefId fields (for EntityRegistry integration)
    /// std:prelude/traits::Iterator (TypeDefId)
    pub iterator_type_def: Option<TypeDefId>,
    /// std:prelude/traits::Iterable (TypeDefId)
    pub iterable_type_def: Option<TypeDefId>,
    /// std:prelude/traits::Equatable (TypeDefId)
    pub equatable_type_def: Option<TypeDefId>,
    /// std:prelude/traits::Comparable (TypeDefId)
    pub comparable_type_def: Option<TypeDefId>,
    /// std:prelude/traits::Hashable (TypeDefId)
    pub hashable_type_def: Option<TypeDefId>,
    /// std:prelude/traits::Stringable (TypeDefId)
    pub stringable_type_def: Option<TypeDefId>,
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

    /// Populate TypeDefId fields from EntityRegistry after analysis.
    /// Call this after semantic analysis is complete and EntityRegistry is populated.
    pub fn populate_type_def_ids(&mut self, entity_registry: &EntityRegistry) {
        // Look up TypeDefIds from the NameIds we already have
        if let Some(name_id) = self.iterator {
            self.iterator_type_def = entity_registry.type_by_name(name_id);
        }
        if let Some(name_id) = self.iterable {
            self.iterable_type_def = entity_registry.type_by_name(name_id);
        }
        if let Some(name_id) = self.equatable {
            self.equatable_type_def = entity_registry.type_by_name(name_id);
        }
        if let Some(name_id) = self.comparable {
            self.comparable_type_def = entity_registry.type_by_name(name_id);
        }
        if let Some(name_id) = self.hashable {
            self.hashable_type_def = entity_registry.type_by_name(name_id);
        }
        if let Some(name_id) = self.stringable {
            self.stringable_type_def = entity_registry.type_by_name(name_id);
        }
    }

    /// Check if a NameId is the Iterator interface
    pub fn is_iterator(&self, name_id: NameId) -> bool {
        self.iterator == Some(name_id)
    }

    /// Check if a NameId is the Iterable interface
    pub fn is_iterable(&self, name_id: NameId) -> bool {
        self.iterable == Some(name_id)
    }

    /// Check if a TypeDefId is the Iterator interface
    pub fn is_iterator_type_def(&self, type_def_id: TypeDefId) -> bool {
        self.iterator_type_def == Some(type_def_id)
    }

    /// Check if a TypeDefId is the Iterable interface
    pub fn is_iterable_type_def(&self, type_def_id: TypeDefId) -> bool {
        self.iterable_type_def == Some(type_def_id)
    }
}

/// Well-known method MethodIds from the stdlib prelude.
/// These are populated after EntityRegistry integration for fast method identification.
#[derive(Debug, Clone, Default)]
pub struct WellKnownMethods {
    /// Iterator::next
    pub iterator_next: Option<MethodId>,
    /// Iterable::iter
    pub iterable_iter: Option<MethodId>,
    /// Stringable::to_string
    pub stringable_to_string: Option<MethodId>,
    /// Equatable::equals
    pub equatable_equals: Option<MethodId>,
    /// Comparable::compare
    pub comparable_compare: Option<MethodId>,
    /// Hashable::hash
    pub hashable_hash: Option<MethodId>,
}

impl WellKnownMethods {
    pub fn new() -> Self {
        Self::default()
    }
}
