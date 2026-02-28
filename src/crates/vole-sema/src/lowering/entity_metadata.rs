// analyzed_lower_entity_metadata.rs
//
// Populates `VirEntityMetadata` from sema's `EntityRegistry` during VIR
// lowering.  This is the bridge that converts sema entity definitions
// (TypeDef, FieldDef, MethodDef, FunctionDef) into VIR-native metadata.

use vole_identity::{Interner, NameTable, VirTypeId};

use crate::LoweringEntityLookup;
use crate::TypeArena;
use crate::entity_defs::{self, TypeDefKind};
use crate::implement_registry::PrimitiveTypeId;
use crate::vir_lower::type_translate::translate_type_id;
use vole_vir::VirExternalMethodInfo;
use vole_vir::entity_metadata::{
    VirEntityMetadata, VirFieldDef, VirFunctionDef, VirGlobalDef, VirImplementation,
    VirMethodBinding, VirMethodDef, VirTypeDef, VirTypeDefKind,
};
use vole_vir::type_table::VirTypeTable;

/// Build VIR entity metadata from sema entities.
///
/// Iterates all type definitions, field definitions, method definitions,
/// and global variable definitions in the `EntityRegistry` and translates
/// them into VIR-native metadata.  Types are translated from sema `TypeId`
/// to `VirTypeId` using the existing `translate_type_id` machinery.
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

    populate_type_defs(registry.all_type_defs(), type_arena, &mut tt, &mut meta);
    populate_field_defs(
        registry.all_field_defs(),
        type_arena,
        &mut tt,
        &mut meta,
        interner,
        name_table,
    );
    populate_method_defs(registry.all_method_defs(), type_arena, &mut tt, &mut meta);
    populate_function_defs(registry.all_function_defs(), type_arena, &mut tt, &mut meta);
    populate_global_defs(registry.all_global_defs(), type_arena, &mut tt, &mut meta);

    // Populate the function_by_name reverse lookup from the registry.
    // (insert_function_def already inserts by name_id, but the registry's
    // function_by_name_map uses full_name_id keys, so we mirror it directly.)
    for (&name_id, &func_id) in registry.function_by_name_map() {
        // Only insert if not already present from insert_function_def.
        // The registry map may use full_name_id or name_id — we cover both.
        meta.insert_function_by_name(name_id, func_id);
    }

    // Populate the array type NameId for array implement dispatch.
    if let Some(array_name) = entities.array_name_id() {
        meta.set_array_name_id(array_name);
    }

    // Build the short-name (last segment) lookup map from all type defs.
    populate_short_name_map(registry.all_type_defs(), name_table, &mut meta);

    // Pre-compute implement-registry type names for primitives, Range, Handle.
    populate_impl_type_names(registry, type_arena, &mut meta);

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
///
/// Translates each implementation's sema `TypeId` type arguments to
/// `VirTypeId`s so codegen can read them without the sema type arena.
fn populate_type_defs(
    type_defs: &[entity_defs::TypeDef],
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
    meta: &mut VirEntityMetadata,
) {
    for td in type_defs {
        let implements = td
            .implements
            .iter()
            .map(|imp| VirImplementation {
                interface: imp.interface,
                type_args: imp
                    .type_args
                    .iter()
                    .map(|&ty| translate_type_id(type_table, ty, type_arena))
                    .collect(),
                sema_type_args: imp.type_args.clone(),
                method_bindings: imp
                    .method_bindings
                    .iter()
                    .map(|mb| VirMethodBinding {
                        method_name: mb.method_name,
                        is_builtin: mb.is_builtin,
                        return_type: translate_type_id(
                            type_table,
                            mb.func_type.return_type_id,
                            type_arena,
                        ),
                    })
                    .collect(),
            })
            .collect();

        let generic_field_types = td.generic_info.as_ref().map(|gi| {
            gi.field_types
                .iter()
                .map(|&ty| translate_type_id(type_table, ty, type_arena))
                .collect()
        });
        let sema_generic_field_types = td.generic_info.as_ref().map(|gi| gi.field_types.clone());
        let generic_field_names = td.generic_info.as_ref().map(|gi| gi.field_names.clone());

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
            base_type_id: td.base_type_id,
            module: td.module,
            is_generic: td.generic_info.is_some(),
            generic_field_types,
            sema_generic_field_types,
            generic_field_names,
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
            sema_type_id: fd.ty,
            vir_ty,
            slot: fd.slot,
            symbol,
        });
    }
}

/// Populate method definitions from sema into VIR entity metadata.
///
/// Unwraps each method's sema signature to extract parameter types and
/// return type, then translates them to `VirTypeId`s so codegen can
/// read method signatures without `arena.unwrap_function()`.
fn populate_method_defs(
    method_defs: &[entity_defs::MethodDef],
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
    meta: &mut VirEntityMetadata,
) {
    for md in method_defs {
        let (param_types, return_type) =
            translate_method_signature(md.signature_id, type_arena, type_table);
        meta.insert_method_def(VirMethodDef {
            id: md.id,
            name_id: md.name_id,
            full_name_id: md.full_name_id,
            defining_type: md.defining_type,
            signature_id: md.signature_id,
            has_default: md.has_default,
            is_static: md.is_static,
            external_binding: md.external_binding.map(|info| VirExternalMethodInfo {
                module_path: info.module_path,
                native_name: info.native_name,
            }),
            has_param_defaults: md.param_defaults.iter().map(|opt| opt.is_some()).collect(),
            method_type_params: md.method_type_params.iter().map(|tp| tp.name_id).collect(),
            required_params: md.required_params,
            param_names: md.param_names.clone(),
            param_types,
            return_type,
        });
    }
}

/// Translate a sema method signature into VIR param types and return type.
///
/// Unwraps the function type from the type arena and translates each
/// parameter and the return type from sema `TypeId` to `VirTypeId`.
/// Returns empty params and `VirTypeId::VOID` if the signature cannot
/// be unwrapped (e.g. for builtins with unresolved signatures).
fn translate_method_signature(
    signature_id: vole_identity::TypeId,
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
) -> (Vec<VirTypeId>, VirTypeId) {
    let Some((params, ret, _is_closure)) = type_arena.unwrap_function(signature_id) else {
        return (Vec::new(), VirTypeId::VOID);
    };
    let param_types = params
        .iter()
        .map(|&p| translate_type_id(type_table, p, type_arena))
        .collect();
    let return_type = translate_type_id(type_table, ret, type_arena);
    (param_types, return_type)
}

/// Populate function definitions from sema into VIR entity metadata.
///
/// Translates each function's signature parameter types and return type
/// from sema `TypeId` to `VirTypeId`.  Also extracts the `has_defaults`
/// boolean vector (codegen only checks `is_some()`, not the expressions
/// themselves) and the generator element type if present.
fn populate_function_defs(
    function_defs: &[entity_defs::FunctionDef],
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
    meta: &mut VirEntityMetadata,
) {
    for fd in function_defs {
        let param_types: Vec<VirTypeId> = fd
            .signature
            .params_id
            .iter()
            .map(|&p| translate_type_id(type_table, p, type_arena))
            .collect();
        let return_type = translate_type_id(type_table, fd.signature.return_type_id, type_arena);
        let generator_element_type = fd
            .generator_element_type
            .map(|ty| translate_type_id(type_table, ty, type_arena));

        meta.insert_function_def(VirFunctionDef {
            id: fd.id,
            name_id: fd.name_id,
            full_name_id: fd.full_name_id,
            module: fd.module,
            param_types,
            return_type,
            param_names: fd.param_names.clone(),
            required_params: fd.required_params,
            has_defaults: fd.param_defaults.iter().map(|d| d.is_some()).collect(),
            is_generic: fd.generic_info.is_some(),
            is_external: fd.is_external,
            generator_element_type,
        });
    }
}

/// Populate global variable definitions from sema into VIR entity metadata.
///
/// Translates each global's sema `TypeId` to a `VirTypeId` using the
/// standard type translation machinery.
fn populate_global_defs(
    global_defs: &[entity_defs::GlobalDef],
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
    meta: &mut VirEntityMetadata,
) {
    for gd in global_defs {
        let vir_ty = translate_type_id(type_table, gd.type_id, type_arena);
        meta.insert_global_def(VirGlobalDef {
            id: gd.id,
            name_id: gd.name_id,
            vir_ty,
            module_id: gd.module_id,
        });
    }
}

/// Populate the short-name (last-segment) lookup map from all type
/// definitions.
///
/// Mirrors `build_short_name_map` in `entity_view.rs`.  Uses the
/// `NameTable` to extract the last segment of each type's `NameId`
/// and registers it in `VirEntityMetadata::short_name_map`.
fn populate_short_name_map(
    type_defs: &[entity_defs::TypeDef],
    name_table: &NameTable,
    meta: &mut VirEntityMetadata,
) {
    for td in type_defs {
        if let Some(last_segment) = name_table.last_segment_str(td.name_id) {
            meta.insert_short_name(last_segment, td.id);
        }
    }
}

/// Pre-compute implement-registry type names for primitive, Range, and
/// Handle types.
///
/// Maps each `PrimitiveTypeId` from the entity registry to the corresponding
/// sema `TypeId` (via the type arena's pre-interned primitives) and stores
/// the `TypeId → NameId` mapping in `VirEntityMetadata`.  This allows codegen
/// to resolve primitive/Range/Handle implement-registry names without needing
/// the `EntityView` or `PrimitiveTypeId` enum at query time.
fn populate_impl_type_names(
    registry: &crate::EntityRegistry,
    type_arena: &TypeArena,
    meta: &mut VirEntityMetadata,
) {
    for (prim_id, name_id) in registry.primitive_name_entries() {
        let type_id = match prim_id {
            PrimitiveTypeId::I8 => type_arena.primitives.i8,
            PrimitiveTypeId::I16 => type_arena.primitives.i16,
            PrimitiveTypeId::I32 => type_arena.primitives.i32,
            PrimitiveTypeId::I64 => type_arena.primitives.i64,
            PrimitiveTypeId::I128 => type_arena.primitives.i128,
            PrimitiveTypeId::U8 => type_arena.primitives.u8,
            PrimitiveTypeId::U16 => type_arena.primitives.u16,
            PrimitiveTypeId::U32 => type_arena.primitives.u32,
            PrimitiveTypeId::U64 => type_arena.primitives.u64,
            PrimitiveTypeId::F32 => type_arena.primitives.f32,
            PrimitiveTypeId::F64 => type_arena.primitives.f64,
            PrimitiveTypeId::F128 => type_arena.primitives.f128,
            PrimitiveTypeId::Bool => type_arena.primitives.bool,
            PrimitiveTypeId::String => type_arena.primitives.string,
            PrimitiveTypeId::Range => type_arena.primitives.range,
            PrimitiveTypeId::Handle => type_arena.primitives.handle,
        };
        meta.insert_impl_type_name(type_id, name_id);
    }
}
