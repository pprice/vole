//! Field registration and lookup for EntityRegistry.

use crate::identity::{FieldId, NameId, TypeDefId};
use crate::sema::LegacyType;
use crate::sema::entity_defs::FieldDef;
use crate::sema::generic::substitute_type;
use crate::sema::type_arena::TypeId as ArenaTypeId;
use std::collections::HashMap;

use super::EntityRegistry;

impl EntityRegistry {
    /// Register a new field on a type
    pub fn register_field(
        &mut self,
        defining_type: TypeDefId,
        name_id: NameId,
        full_name_id: NameId,
        ty: ArenaTypeId,
        slot: usize,
    ) -> FieldId {
        let id = FieldId::new(self.field_defs.len() as u32);
        self.field_defs.push(FieldDef {
            id,
            name_id,
            full_name_id,
            defining_type,
            ty,
            slot,
        });
        self.field_by_full_name.insert(full_name_id, id);
        self.fields_by_type
            .get_mut(&defining_type)
            .expect("type must be registered before adding fields")
            .insert(name_id, id);
        self.type_defs[defining_type.index() as usize]
            .fields
            .push(id);
        id
    }

    /// Get a field definition by ID
    pub fn get_field(&self, id: FieldId) -> &FieldDef {
        &self.field_defs[id.index() as usize]
    }

    /// Get all fields defined directly on a type
    pub fn fields_on_type(&self, type_id: TypeDefId) -> impl Iterator<Item = FieldId> + '_ {
        self.type_defs[type_id.index() as usize]
            .fields
            .iter()
            .copied()
    }

    /// Find a field on a type by its short name
    pub fn find_field_on_type(&self, type_id: TypeDefId, name_id: NameId) -> Option<FieldId> {
        self.fields_by_type
            .get(&type_id)
            .and_then(|fields| fields.get(&name_id).copied())
    }

    // ===== Field and Substitution Helpers =====

    /// Get all field NameIds for a type (for iteration and lookups)
    pub fn field_name_ids(&self, type_def_id: TypeDefId) -> &[NameId] {
        self.get_type(type_def_id)
            .generic_info
            .as_ref()
            .map(|gi| gi.field_names.as_slice())
            .unwrap_or(&[])
    }

    /// Build substitution map for a generic type instantiation
    pub fn substitution_map(
        &self,
        type_def_id: TypeDefId,
        type_args: &[LegacyType],
    ) -> HashMap<NameId, LegacyType> {
        let type_def = self.get_type(type_def_id);
        type_def
            .type_params
            .iter()
            .zip(type_args.iter())
            .map(|(param, arg)| (*param, arg.clone()))
            .collect()
    }

    /// Apply substitution to a type based on type_def's type params
    pub fn substitute_type_with_args(
        &self,
        type_def_id: TypeDefId,
        type_args: &[LegacyType],
        ty: &LegacyType,
    ) -> LegacyType {
        if type_args.is_empty() {
            return ty.clone();
        }
        let subs = self.substitution_map(type_def_id, type_args);
        substitute_type(ty, &subs)
    }

    /// Get field type with type argument substitution applied
    /// Requires arena to convert stored TypeId to LegacyType for substitution
    pub fn field_type(
        &self,
        type_def_id: TypeDefId,
        type_args: &[LegacyType],
        field_name_id: NameId,
        arena: &crate::sema::type_arena::TypeArena,
    ) -> Option<LegacyType> {
        let type_def = self.get_type(type_def_id);
        let generic_info = type_def.generic_info.as_ref()?;
        let idx = generic_info
            .field_names
            .iter()
            .position(|n| *n == field_name_id)?;
        // Convert stored TypeId to LegacyType for substitution
        let field_type = arena.to_type(generic_info.field_types[idx]);

        if type_args.is_empty() {
            Some(field_type)
        } else {
            Some(self.substitute_type_with_args(type_def_id, type_args, &field_type))
        }
    }

    /// Get field index by NameId
    pub fn field_index(&self, type_def_id: TypeDefId, field_name_id: NameId) -> Option<usize> {
        let type_def = self.get_type(type_def_id);
        let generic_info = type_def.generic_info.as_ref()?;
        generic_info
            .field_names
            .iter()
            .position(|n| *n == field_name_id)
    }
}
