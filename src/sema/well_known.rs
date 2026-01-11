// src/sema/well_known.rs
//
// Functions for populating well-known type identifiers from stdlib.
// The WellKnownTypes and WellKnownMethods structs live in identity.rs.

use crate::sema::EntityRegistry;

// Re-export from identity.rs for compatibility
pub use crate::identity::{WellKnownMethods, WellKnownTypes};

/// Populate TypeDefId fields from EntityRegistry after analysis.
/// Call this after semantic analysis is complete and EntityRegistry is populated.
pub fn populate_type_def_ids(well_known: &mut WellKnownTypes, entity_registry: &EntityRegistry) {
    // Look up TypeDefIds from the NameIds we already have
    if let Some(name_id) = well_known.iterator {
        well_known.iterator_type_def = entity_registry.type_by_name(name_id);
    }
    if let Some(name_id) = well_known.iterable {
        well_known.iterable_type_def = entity_registry.type_by_name(name_id);
    }
    if let Some(name_id) = well_known.equatable {
        well_known.equatable_type_def = entity_registry.type_by_name(name_id);
    }
    if let Some(name_id) = well_known.comparable {
        well_known.comparable_type_def = entity_registry.type_by_name(name_id);
    }
    if let Some(name_id) = well_known.hashable {
        well_known.hashable_type_def = entity_registry.type_by_name(name_id);
    }
    if let Some(name_id) = well_known.stringable {
        well_known.stringable_type_def = entity_registry.type_by_name(name_id);
    }
}
