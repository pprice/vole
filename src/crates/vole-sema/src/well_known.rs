// src/sema/well_known.rs
//
// Functions for populating well-known type identifiers from stdlib.
// The WellKnownTypes and WellKnownMethods structs live in identity.rs.

use crate::EntityRegistry;
use vole_identity::NameTable;

// Re-export from identity.rs for internal use
pub use vole_identity::WellKnownTypes;

/// Populate TypeDefId fields from EntityRegistry after analysis.
/// Call this after semantic analysis is complete and EntityRegistry is populated.
pub fn populate_type_def_ids(name_table: &mut NameTable, entity_registry: &EntityRegistry) {
    let well_known = WellKnownTypes::populated(|interface_name| {
        let name_id = name_table.well_known_interface_name_id(interface_name);
        entity_registry.type_by_name(name_id)
    });
    name_table.well_known = well_known;
}
