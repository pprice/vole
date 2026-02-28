// analyzed_lower_entity_metadata.rs
//
// Populates `VirEntityMetadata` from sema's `EntityRegistry` during VIR
// lowering.  This is the bridge that converts sema entity definitions
// (TypeDef, FieldDef, MethodDef) into VIR-native metadata.

use vole_identity::{Interner, NameTable};

use crate::LoweringEntityLookup;
use crate::TypeArena;
use crate::entity_defs::{self, TypeDefKind};
use crate::vir_lower::type_translate::translate_type_id;
use vole_vir::entity_metadata::{
    VirEntityMetadata, VirFieldDef, VirImplementation, VirMethodBinding, VirMethodDef, VirTypeDef,
    VirTypeDefKind,
};
use vole_vir::type_table::VirTypeTable;

/// Build VIR entity metadata from sema entities.
///
/// Iterates all type definitions, field definitions, and method definitions
/// in the `EntityRegistry` and translates them into VIR-native metadata.
/// Field types are translated from sema `TypeId` to `VirTypeId` using the
/// existing `translate_type_id` machinery.
///
/// `interner` and `name_table` are used to resolve field `NameId`s to
/// `Symbol`s, enabling the monomorph rederive pass to match field names
/// without needing the interner at rederive time.
pub fn build_entity_metadata(
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    type_table: &VirTypeTable,
    interner: &mut Interner,
    name_table: &NameTable,
) -> VirEntityMetadata {
    let registry = entities.as_entity_registry();
    let mut meta = VirEntityMetadata::new();

    // Use a mutable clone of the type table for translating field types.
    // translate_type_id may intern new compound types it encounters.
    let mut tt = type_table.clone();

    populate_type_defs(registry.all_type_defs(), &mut meta);
    populate_field_defs(
        registry.all_field_defs(),
        type_arena,
        &mut tt,
        &mut meta,
        interner,
        name_table,
    );
    populate_method_defs(registry.all_method_defs(), &mut meta);

    meta
}

/// Convert a sema `TypeDefKind` to a VIR `VirTypeDefKind`.
fn convert_type_def_kind(kind: TypeDefKind) -> VirTypeDefKind {
    match kind {
        TypeDefKind::Interface => VirTypeDefKind::Interface,
        TypeDefKind::Class => VirTypeDefKind::Class,
        TypeDefKind::Struct => VirTypeDefKind::Struct,
        TypeDefKind::ErrorType => VirTypeDefKind::ErrorType,
        TypeDefKind::Primitive => VirTypeDefKind::Primitive,
        TypeDefKind::Alias => VirTypeDefKind::Alias,
        TypeDefKind::Sentinel => VirTypeDefKind::Sentinel,
    }
}

/// Populate type definitions from sema into VIR entity metadata.
fn populate_type_defs(type_defs: &[entity_defs::TypeDef], meta: &mut VirEntityMetadata) {
    for td in type_defs {
        let implements = td
            .implements
            .iter()
            .map(|imp| VirImplementation {
                interface: imp.interface,
                method_bindings: imp
                    .method_bindings
                    .iter()
                    .map(|mb| VirMethodBinding {
                        method_name: mb.method_name,
                        is_builtin: mb.is_builtin,
                    })
                    .collect(),
            })
            .collect();

        meta.insert_type_def(VirTypeDef {
            id: td.id,
            name_id: td.name_id,
            kind: convert_type_def_kind(td.kind),
            fields: td.fields.clone(),
            methods: td.methods.clone(),
            static_methods: td.static_methods.clone(),
            extends: td.extends.clone(),
            type_params: td.type_params.clone(),
            implements,
            is_annotation: td.is_annotation,
        });
    }
}

/// Populate field definitions from sema into VIR entity metadata.
///
/// Translates each field's sema `TypeId` to a `VirTypeId` using the
/// standard type translation machinery.  Also resolves each field's
/// `NameId` to a `Symbol` via the name table + interner so that the
/// monomorph rederive pass can match field names without the interner.
fn populate_field_defs(
    field_defs: &[entity_defs::FieldDef],
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
    meta: &mut VirEntityMetadata,
    interner: &mut Interner,
    name_table: &NameTable,
) {
    for fd in field_defs {
        let vir_ty = translate_type_id(type_table, fd.ty, type_arena);
        let symbol = name_table
            .last_segment_str(fd.name_id)
            .map(|name| interner.intern(&name));
        meta.insert_field_def(VirFieldDef {
            id: fd.id,
            name_id: fd.name_id,
            full_name_id: fd.full_name_id,
            defining_type: fd.defining_type,
            vir_ty,
            slot: fd.slot,
            symbol,
        });
    }
}

/// Populate method definitions from sema into VIR entity metadata.
fn populate_method_defs(method_defs: &[entity_defs::MethodDef], meta: &mut VirEntityMetadata) {
    for md in method_defs {
        meta.insert_method_def(VirMethodDef {
            id: md.id,
            name_id: md.name_id,
            full_name_id: md.full_name_id,
            defining_type: md.defining_type,
            has_default: md.has_default,
            is_static: md.is_static,
            required_params: md.required_params,
            param_names: md.param_names.clone(),
        });
    }
}
