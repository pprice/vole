//! Field registration and lookup for EntityRegistry.

use crate::identity::{FieldId, NameId, TypeDefId};
use crate::sema::entity_defs::FieldDef;
use crate::sema::type_arena::TypeId as ArenaTypeId;

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

    /// Build substitution map using TypeId (for arena-based substitution)
    pub fn substitution_map_id(
        &self,
        type_def_id: TypeDefId,
        type_args_id: &[ArenaTypeId],
    ) -> hashbrown::HashMap<NameId, ArenaTypeId> {
        let type_def = self.get_type(type_def_id);
        type_def
            .type_params
            .iter()
            .zip(type_args_id.iter())
            .map(|(&param, &arg)| (param, arg))
            .collect()
    }

    /// Apply substitution to a TypeId using arena-based substitution
    pub fn substitute_type_id_with_args(
        &self,
        type_def_id: TypeDefId,
        type_args_id: &[ArenaTypeId],
        type_id: ArenaTypeId,
        arena: &mut crate::sema::type_arena::TypeArena,
    ) -> ArenaTypeId {
        if type_args_id.is_empty() {
            return type_id;
        }
        let subs = self.substitution_map_id(type_def_id, type_args_id);
        arena.substitute(type_id, &subs)
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
