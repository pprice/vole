// remap.rs
//
// VirTypeId remapping for VirEntityMetadata.
//
// Clones a VirEntityMetadata and remaps all VirTypeId fields using a
// provided mapping.  Used during module VIR caching to translate type
// IDs from a cached module's type table into the current compilation's
// type table.

use rustc_hash::FxHashMap;
use vole_identity::VirTypeId;

use crate::entity_metadata::{
    VirEntityMetadata, VirFunctionDef, VirImplementation, VirMethodDef, VirTypeDef,
};

/// Look up a VirTypeId in the mapping, falling back to identity.
fn remap(mapping: &FxHashMap<VirTypeId, VirTypeId>, vir_ty: VirTypeId) -> VirTypeId {
    mapping.get(&vir_ty).copied().unwrap_or(vir_ty)
}

/// Clone a `VirEntityMetadata` with all `VirTypeId` fields remapped.
///
/// Walks every type definition, field definition, method definition,
/// global definition, function definition, and implementation block,
/// replacing each `VirTypeId` according to the provided mapping.
/// Unmapped IDs are left unchanged (identity fallback).
///
/// Non-`VirTypeId` fields (entity IDs, names, sema TypeIds, etc.) are
/// cloned verbatim.
pub fn remap_entity_metadata(
    meta: &VirEntityMetadata,
    mapping: &FxHashMap<VirTypeId, VirTypeId>,
) -> VirEntityMetadata {
    let mut result = meta.clone();
    result.remap_vir_type_ids(mapping);
    result
}

// ---------------------------------------------------------------------------
// Internal remapping on VirEntityMetadata
// ---------------------------------------------------------------------------

impl VirEntityMetadata {
    /// Remap all `VirTypeId` fields in-place using the provided mapping.
    ///
    /// `VirImplementBlockEntry` is not remapped because it contains no
    /// `VirTypeId` fields (only entity IDs and sema TypeIds).
    /// `VirImplementation` type_args are on `VirTypeDef.implements`,
    /// handled by `remap_type_defs`.
    fn remap_vir_type_ids(&mut self, mapping: &FxHashMap<VirTypeId, VirTypeId>) {
        self.remap_type_defs(mapping);
        self.remap_field_defs(mapping);
        self.remap_method_defs(mapping);
        self.remap_global_defs(mapping);
        self.remap_function_defs(mapping);
    }

    fn remap_type_defs(&mut self, mapping: &FxHashMap<VirTypeId, VirTypeId>) {
        for td in self.type_defs_mut().values_mut() {
            remap_type_def(td, mapping);
        }
    }

    fn remap_field_defs(&mut self, mapping: &FxHashMap<VirTypeId, VirTypeId>) {
        for fd in self.field_defs_mut().values_mut() {
            fd.vir_ty = remap(mapping, fd.vir_ty);
        }
    }

    fn remap_method_defs(&mut self, mapping: &FxHashMap<VirTypeId, VirTypeId>) {
        for md in self.method_defs_mut().values_mut() {
            remap_method_def(md, mapping);
        }
    }

    fn remap_global_defs(&mut self, mapping: &FxHashMap<VirTypeId, VirTypeId>) {
        for gd in self.global_defs_mut().values_mut() {
            gd.vir_ty = remap(mapping, gd.vir_ty);
        }
    }

    fn remap_function_defs(&mut self, mapping: &FxHashMap<VirTypeId, VirTypeId>) {
        for fd in self.function_defs_mut().values_mut() {
            remap_function_def(fd, mapping);
        }
    }
}

// ---------------------------------------------------------------------------
// Per-struct remapping helpers
// ---------------------------------------------------------------------------

fn remap_type_def(td: &mut VirTypeDef, mapping: &FxHashMap<VirTypeId, VirTypeId>) {
    for vir_ty in &mut td.field_types {
        *vir_ty = remap(mapping, *vir_ty);
    }
    if let Some(ref mut generic_field_types) = td.generic_field_types {
        for vir_ty in generic_field_types {
            *vir_ty = remap(mapping, *vir_ty);
        }
    }
    for impl_ in &mut td.implements {
        remap_implementation(impl_, mapping);
    }
}

fn remap_implementation(impl_: &mut VirImplementation, mapping: &FxHashMap<VirTypeId, VirTypeId>) {
    for vir_ty in &mut impl_.type_args {
        *vir_ty = remap(mapping, *vir_ty);
    }
    for binding in &mut impl_.method_bindings {
        binding.return_type = remap(mapping, binding.return_type);
    }
}

fn remap_method_def(md: &mut VirMethodDef, mapping: &FxHashMap<VirTypeId, VirTypeId>) {
    for vir_ty in &mut md.param_types {
        *vir_ty = remap(mapping, *vir_ty);
    }
    md.return_type = remap(mapping, md.return_type);
}

fn remap_function_def(fd: &mut VirFunctionDef, mapping: &FxHashMap<VirTypeId, VirTypeId>) {
    for vir_ty in &mut fd.param_types {
        *vir_ty = remap(mapping, *vir_ty);
    }
    fd.return_type = remap(mapping, fd.return_type);
    if let Some(ref mut gen_ty) = fd.generator_element_type {
        *gen_ty = remap(mapping, *gen_ty);
    }
}

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::entity_metadata::{
        VirFieldDef, VirFieldTypeTag, VirGlobalDef, VirImplementBlockEntry, VirMethodBinding,
        VirTypeDefKind,
    };
    use vole_identity::{
        FieldId, FunctionId, FunctionType, GlobalId, MethodId, ModuleId, NameId, TypeDefId, TypeId,
        TypeIdVec,
    };

    fn make_type_def_id(n: u32) -> TypeDefId {
        TypeDefId::new(n)
    }

    fn make_field_id(n: u32) -> FieldId {
        FieldId::new(n)
    }

    fn make_method_id(n: u32) -> MethodId {
        MethodId::new(n)
    }

    fn make_name_id(n: u32) -> NameId {
        NameId::new_for_test(n)
    }

    fn make_global_id(n: u32) -> GlobalId {
        GlobalId::new(n)
    }

    fn make_function_id(n: u32) -> FunctionId {
        FunctionId::new(n)
    }

    fn make_module_id(n: u32) -> ModuleId {
        ModuleId::new(n)
    }

    /// Build a mapping that swaps I64 <-> STRING and BOOL -> F64.
    fn test_mapping() -> FxHashMap<VirTypeId, VirTypeId> {
        let mut m = FxHashMap::default();
        m.insert(VirTypeId::I64, VirTypeId::STRING);
        m.insert(VirTypeId::STRING, VirTypeId::I64);
        m.insert(VirTypeId::BOOL, VirTypeId::F64);
        m
    }

    #[test]
    fn remap_type_def_field_types() {
        let mut meta = VirEntityMetadata::new();
        meta.insert_type_def(VirTypeDef {
            id: make_type_def_id(1),
            name_id: make_name_id(100),
            kind: VirTypeDefKind::Class,
            fields: vec![make_field_id(1), make_field_id(2)],
            field_types: vec![VirTypeId::I64, VirTypeId::BOOL],
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: make_module_id(0),
            is_generic: false,
            generic_field_types: None,
            generic_field_names: None,
        });

        let remapped = remap_entity_metadata(&meta, &test_mapping());
        let td = remapped.get_type_def(make_type_def_id(1)).unwrap();
        assert_eq!(td.field_types, vec![VirTypeId::STRING, VirTypeId::F64]);
    }

    #[test]
    fn remap_type_def_generic_field_types() {
        let mut meta = VirEntityMetadata::new();
        meta.insert_type_def(VirTypeDef {
            id: make_type_def_id(1),
            name_id: make_name_id(100),
            kind: VirTypeDefKind::Class,
            fields: vec![],
            field_types: vec![],
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![make_name_id(200)],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: make_module_id(0),
            is_generic: true,
            generic_field_types: Some(vec![VirTypeId::I64, VirTypeId::STRING]),
            generic_field_names: Some(vec![make_name_id(300), make_name_id(301)]),
        });

        let remapped = remap_entity_metadata(&meta, &test_mapping());
        let td = remapped.get_type_def(make_type_def_id(1)).unwrap();
        assert_eq!(
            td.generic_field_types.as_deref(),
            Some(&[VirTypeId::STRING, VirTypeId::I64][..])
        );
    }

    #[test]
    fn remap_implementation_type_args() {
        let mut meta = VirEntityMetadata::new();
        meta.insert_type_def(VirTypeDef {
            id: make_type_def_id(1),
            name_id: make_name_id(100),
            kind: VirTypeDefKind::Class,
            fields: vec![],
            field_types: vec![],
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![VirImplementation {
                interface: make_type_def_id(2),
                type_args: vec![VirTypeId::I64, VirTypeId::BOOL],
                sema_type_args: vec![TypeId::I64, TypeId::BOOL],
                method_bindings: vec![VirMethodBinding {
                    method_name: make_name_id(300),
                    is_builtin: false,
                    return_type: VirTypeId::STRING,
                    sema_func_type: FunctionType {
                        is_closure: false,
                        params_id: TypeIdVec::from_slice(&[TypeId::VOID]),
                        return_type_id: TypeId::STRING,
                    },
                    external_info: None,
                }],
            }],
            is_annotation: false,
            base_type_id: None,
            module: make_module_id(0),
            is_generic: false,
            generic_field_types: None,
            generic_field_names: None,
        });

        let remapped = remap_entity_metadata(&meta, &test_mapping());
        let td = remapped.get_type_def(make_type_def_id(1)).unwrap();
        let impl_ = &td.implements[0];
        // I64 -> STRING, BOOL -> F64
        assert_eq!(impl_.type_args, vec![VirTypeId::STRING, VirTypeId::F64]);
        // sema_type_args unchanged
        assert_eq!(impl_.sema_type_args, vec![TypeId::I64, TypeId::BOOL]);
        // method binding return_type: STRING -> I64
        assert_eq!(impl_.method_bindings[0].return_type, VirTypeId::I64);
    }

    #[test]
    fn remap_field_def_vir_ty() {
        let mut meta = VirEntityMetadata::new();
        meta.insert_field_def(VirFieldDef {
            id: make_field_id(1),
            name_id: make_name_id(50),
            full_name_id: make_name_id(51),
            defining_type: make_type_def_id(1),
            vir_ty: VirTypeId::BOOL,
            slot: 0,
            symbol: None,
            field_type_tag: VirFieldTypeTag::Value,
        });

        let remapped = remap_entity_metadata(&meta, &test_mapping());
        let fd = remapped.get_field_def(make_field_id(1)).unwrap();
        assert_eq!(fd.vir_ty, VirTypeId::F64);
        // Non-VirTypeId fields unchanged.
        assert_eq!(fd.name_id, make_name_id(50));
        assert_eq!(fd.slot, 0);
    }

    #[test]
    fn remap_method_def_param_and_return_types() {
        let mut meta = VirEntityMetadata::new();
        meta.insert_method_def(VirMethodDef {
            id: make_method_id(1),
            name_id: make_name_id(70),
            full_name_id: make_name_id(71),
            defining_type: make_type_def_id(1),
            signature_id: TypeId::I64,
            has_default: false,
            is_static: false,
            external_binding: None,
            has_param_defaults: vec![false],
            method_type_params: vec![],
            required_params: 1,
            param_names: vec!["x".into()],
            param_types: vec![VirTypeId::I64, VirTypeId::STRING],
            return_type: VirTypeId::BOOL,
        });

        let remapped = remap_entity_metadata(&meta, &test_mapping());
        let md = remapped.get_method_def(make_method_id(1)).unwrap();
        // I64 -> STRING, STRING -> I64
        assert_eq!(md.param_types, vec![VirTypeId::STRING, VirTypeId::I64]);
        // BOOL -> F64
        assert_eq!(md.return_type, VirTypeId::F64);
        // Non-VirTypeId fields unchanged.
        assert_eq!(md.name_id, make_name_id(70));
        assert_eq!(md.signature_id, TypeId::I64);
    }

    #[test]
    fn remap_global_def_vir_ty() {
        let mut meta = VirEntityMetadata::new();
        meta.insert_global_def(VirGlobalDef {
            id: make_global_id(1),
            name_id: make_name_id(300),
            vir_ty: VirTypeId::I64,
            module_id: make_module_id(0),
        });

        let remapped = remap_entity_metadata(&meta, &test_mapping());
        let gd = remapped.get_global_def(make_global_id(1)).unwrap();
        assert_eq!(gd.vir_ty, VirTypeId::STRING);
    }

    #[test]
    fn remap_function_def_types() {
        let mut meta = VirEntityMetadata::new();
        meta.insert_function_def(VirFunctionDef {
            id: make_function_id(1),
            name_id: make_name_id(500),
            full_name_id: make_name_id(501),
            module: make_module_id(0),
            param_types: vec![VirTypeId::I64, VirTypeId::BOOL],
            return_type: VirTypeId::STRING,
            param_names: vec!["a".into(), "b".into()],
            required_params: 2,
            has_defaults: vec![false, false],
            is_generic: false,
            is_external: false,
            generator_element_type: Some(VirTypeId::BOOL),
            sema_param_types: vec![TypeId::I64, TypeId::BOOL],
            sema_return_type: TypeId::STRING,
            sema_generator_element_type: Some(TypeId::BOOL),
        });

        let remapped = remap_entity_metadata(&meta, &test_mapping());
        let fd = remapped.get_function_def(make_function_id(1)).unwrap();
        // I64 -> STRING, BOOL -> F64
        assert_eq!(fd.param_types, vec![VirTypeId::STRING, VirTypeId::F64]);
        // STRING -> I64
        assert_eq!(fd.return_type, VirTypeId::I64);
        // BOOL -> F64
        assert_eq!(fd.generator_element_type, Some(VirTypeId::F64));
        // sema types unchanged
        assert_eq!(fd.sema_param_types, vec![TypeId::I64, TypeId::BOOL]);
        assert_eq!(fd.sema_return_type, TypeId::STRING);
        assert_eq!(fd.sema_generator_element_type, Some(TypeId::BOOL));
    }

    #[test]
    fn remap_identity_for_unmapped_ids() {
        let mut meta = VirEntityMetadata::new();
        meta.insert_field_def(VirFieldDef {
            id: make_field_id(1),
            name_id: make_name_id(50),
            full_name_id: make_name_id(51),
            defining_type: make_type_def_id(1),
            vir_ty: VirTypeId::F32, // Not in the mapping
            slot: 0,
            symbol: None,
            field_type_tag: VirFieldTypeTag::Value,
        });

        let remapped = remap_entity_metadata(&meta, &test_mapping());
        let fd = remapped.get_field_def(make_field_id(1)).unwrap();
        // F32 is not in the mapping, so it should stay F32.
        assert_eq!(fd.vir_ty, VirTypeId::F32);
    }

    #[test]
    fn remap_empty_mapping_is_identity() {
        let mut meta = VirEntityMetadata::new();
        meta.insert_field_def(VirFieldDef {
            id: make_field_id(1),
            name_id: make_name_id(50),
            full_name_id: make_name_id(51),
            defining_type: make_type_def_id(1),
            vir_ty: VirTypeId::I64,
            slot: 0,
            symbol: None,
            field_type_tag: VirFieldTypeTag::Value,
        });

        let empty: FxHashMap<VirTypeId, VirTypeId> = FxHashMap::default();
        let remapped = remap_entity_metadata(&meta, &empty);
        let fd = remapped.get_field_def(make_field_id(1)).unwrap();
        assert_eq!(fd.vir_ty, VirTypeId::I64);
    }

    #[test]
    fn remap_preserves_implement_block_entries() {
        let mut meta = VirEntityMetadata::new();
        meta.insert_implement_block(VirImplementBlockEntry {
            type_def_id: make_type_def_id(1),
            self_type_id: TypeId::I64,
            instance_methods: vec![make_method_id(10)],
            static_methods: vec![make_method_id(11)],
            module_id: make_module_id(0),
        });

        let remapped = remap_entity_metadata(&meta, &test_mapping());
        let blocks = remapped.implement_blocks();
        assert_eq!(blocks.len(), 1);
        assert_eq!(blocks[0].type_def_id, make_type_def_id(1));
        assert_eq!(blocks[0].instance_methods, vec![make_method_id(10)]);
    }

    #[test]
    fn remap_all_entity_kinds_together() {
        let mut meta = VirEntityMetadata::new();

        // Type def with field_types
        meta.insert_type_def(VirTypeDef {
            id: make_type_def_id(1),
            name_id: make_name_id(100),
            kind: VirTypeDefKind::Struct,
            fields: vec![make_field_id(1)],
            field_types: vec![VirTypeId::I64],
            methods: vec![make_method_id(1)],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: make_module_id(0),
            is_generic: false,
            generic_field_types: None,
            generic_field_names: None,
        });

        // Field def
        meta.insert_field_def(VirFieldDef {
            id: make_field_id(1),
            name_id: make_name_id(50),
            full_name_id: make_name_id(51),
            defining_type: make_type_def_id(1),
            vir_ty: VirTypeId::I64,
            slot: 0,
            symbol: None,
            field_type_tag: VirFieldTypeTag::Value,
        });

        // Method def
        meta.insert_method_def(VirMethodDef {
            id: make_method_id(1),
            name_id: make_name_id(70),
            full_name_id: make_name_id(71),
            defining_type: make_type_def_id(1),
            signature_id: TypeId::I64,
            has_default: false,
            is_static: false,
            external_binding: None,
            has_param_defaults: vec![],
            method_type_params: vec![],
            required_params: 0,
            param_names: vec![],
            param_types: vec![],
            return_type: VirTypeId::I64,
        });

        // Global def
        meta.insert_global_def(VirGlobalDef {
            id: make_global_id(1),
            name_id: make_name_id(300),
            vir_ty: VirTypeId::STRING,
            module_id: make_module_id(0),
        });

        // Function def
        meta.insert_function_def(VirFunctionDef {
            id: make_function_id(1),
            name_id: make_name_id(500),
            full_name_id: make_name_id(501),
            module: make_module_id(0),
            param_types: vec![VirTypeId::BOOL],
            return_type: VirTypeId::I64,
            param_names: vec!["x".into()],
            required_params: 1,
            has_defaults: vec![false],
            is_generic: false,
            is_external: false,
            generator_element_type: None,
            sema_param_types: vec![TypeId::BOOL],
            sema_return_type: TypeId::I64,
            sema_generator_element_type: None,
        });

        let remapped = remap_entity_metadata(&meta, &test_mapping());

        // Verify all VirTypeId fields were remapped.
        let td = remapped.get_type_def(make_type_def_id(1)).unwrap();
        assert_eq!(td.field_types, vec![VirTypeId::STRING]);

        let fd = remapped.get_field_def(make_field_id(1)).unwrap();
        assert_eq!(fd.vir_ty, VirTypeId::STRING);

        let md = remapped.get_method_def(make_method_id(1)).unwrap();
        assert_eq!(md.return_type, VirTypeId::STRING);

        let gd = remapped.get_global_def(make_global_id(1)).unwrap();
        assert_eq!(gd.vir_ty, VirTypeId::I64);

        let func = remapped.get_function_def(make_function_id(1)).unwrap();
        assert_eq!(func.param_types, vec![VirTypeId::F64]);
        assert_eq!(func.return_type, VirTypeId::STRING);
    }
}
