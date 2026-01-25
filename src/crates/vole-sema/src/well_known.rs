// src/sema/well_known.rs
//
// Functions for populating well-known type identifiers from stdlib.
// The WellKnownTypes and WellKnownMethods structs live in identity.rs.

use crate::EntityRegistry;
use vole_identity::NameTable;

// Re-export from identity.rs for compatibility
pub use vole_identity::{WellKnownMethods, WellKnownTypes};

/// Populate TypeDefId fields from EntityRegistry after analysis.
/// Call this after semantic analysis is complete and EntityRegistry is populated.
pub fn populate_type_def_ids(name_table: &mut NameTable, entity_registry: &EntityRegistry) {
    // Look up TypeDefIds by interning NameIds and looking up in EntityRegistry
    let iterator_name_id = name_table.well_known_interface_name_id("Iterator");
    name_table.well_known.iterator_type_def = entity_registry.type_by_name(iterator_name_id);

    let iterable_name_id = name_table.well_known_interface_name_id("Iterable");
    name_table.well_known.iterable_type_def = entity_registry.type_by_name(iterable_name_id);

    let equatable_name_id = name_table.well_known_interface_name_id("Equatable");
    name_table.well_known.equatable_type_def = entity_registry.type_by_name(equatable_name_id);

    let comparable_name_id = name_table.well_known_interface_name_id("Comparable");
    name_table.well_known.comparable_type_def = entity_registry.type_by_name(comparable_name_id);

    let hashable_name_id = name_table.well_known_interface_name_id("Hashable");
    name_table.well_known.hashable_type_def = entity_registry.type_by_name(hashable_name_id);

    let stringable_name_id = name_table.well_known_interface_name_id("Stringable");
    name_table.well_known.stringable_type_def = entity_registry.type_by_name(stringable_name_id);
}
