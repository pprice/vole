//! Field registration and lookup for EntityRegistry.

use crate::entity_defs::FieldDef;
use crate::type_arena::{TypeId as ArenaTypeId, TypeIdVec};
use rustc_hash::FxHashMap;
use vole_identity::{FieldId, NameId, TypeDefId};

use super::EntityRegistry;

/// Cache key for field type substitutions.
///
/// When accessing a field on a generic type like `Box<T>`, the field's type needs
/// to be substituted with concrete type arguments. This key identifies a unique
/// (type definition, type arguments, field type) combination.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FieldSubstitutionKey {
    /// The type definition (e.g., Box)
    pub type_def_id: TypeDefId,
    /// The concrete type arguments (e.g., [i64] for Box<i64>)
    pub type_args: TypeIdVec,
    /// The unsubstituted field type (e.g., T for the `value` field)
    pub field_type_id: ArenaTypeId,
}

impl FieldSubstitutionKey {
    pub fn new(
        type_def_id: TypeDefId,
        type_args: impl Into<TypeIdVec>,
        field_type_id: ArenaTypeId,
    ) -> Self {
        Self {
            type_def_id,
            type_args: type_args.into(),
            field_type_id,
        }
    }
}

/// Cache for field type substitutions.
///
/// Stores the result of substituting type parameters in field types, avoiding
/// repeated substitution computations for the same generic instantiation.
#[derive(Debug, Clone, Default)]
pub struct FieldSubstitutionCache {
    cache: FxHashMap<FieldSubstitutionKey, ArenaTypeId>,
}

impl FieldSubstitutionCache {
    pub fn new() -> Self {
        Self {
            cache: FxHashMap::default(),
        }
    }

    /// Look up a cached substitution result.
    pub fn get(&self, key: &FieldSubstitutionKey) -> Option<ArenaTypeId> {
        self.cache.get(key).copied()
    }

    /// Store a substitution result in the cache.
    pub fn insert(&mut self, key: FieldSubstitutionKey, result: ArenaTypeId) {
        self.cache.insert(key, result);
    }

    /// Clear the cache.
    pub fn clear(&mut self) {
        self.cache.clear();
    }

    /// Get the number of cached entries (for debugging/testing).
    #[allow(dead_code)]
    pub fn len(&self) -> usize {
        self.cache.len()
    }

    /// Check if the cache is empty.
    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.cache.is_empty()
    }
}

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
    ) -> FxHashMap<NameId, ArenaTypeId> {
        let type_def = self.get_type(type_def_id);
        type_def
            .type_params
            .iter()
            .zip(type_args_id.iter())
            .map(|(&param, &arg)| (param, arg))
            .collect()
    }

    /// Apply substitution to a TypeId using arena-based substitution.
    ///
    /// Results are cached per (TypeDefId, type_args, field_type_id) to avoid
    /// recomputing substitutions for the same generic instantiation.
    pub fn substitute_type_id_with_args(
        &mut self,
        type_def_id: TypeDefId,
        type_args_id: &[ArenaTypeId],
        type_id: ArenaTypeId,
        arena: &mut crate::type_arena::TypeArena,
    ) -> ArenaTypeId {
        if type_args_id.is_empty() {
            return type_id;
        }

        // Check cache first
        let key = FieldSubstitutionKey::new(type_def_id, type_args_id.to_vec(), type_id);
        if let Some(cached) = self.field_substitution_cache.get(&key) {
            return cached;
        }

        // Compute substitution
        let subs = self.substitution_map_id(type_def_id, type_args_id);
        let result = arena.substitute(type_id, &subs);

        // Cache the result
        self.field_substitution_cache.insert(key, result);

        result
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
