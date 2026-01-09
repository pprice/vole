//! Central registry for all language entities.
//!
//! EntityRegistry stores type definitions, methods, fields, and functions,
//! providing type-safe lookups by ID and name.

use std::collections::HashMap;

use crate::identity::{FieldId, FunctionId, MethodId, NameId, TypeDefId};
use crate::sema::entity_defs::{FieldDef, FunctionDef, MethodDef, TypeDef};

/// Central registry for all language entities
#[derive(Debug, Clone)]
pub struct EntityRegistry {
    // Storage - IDs are indices into these vectors
    pub(crate) type_defs: Vec<TypeDef>,
    pub(crate) method_defs: Vec<MethodDef>,
    pub(crate) field_defs: Vec<FieldDef>,
    pub(crate) function_defs: Vec<FunctionDef>,

    // Primary lookups by NameId
    pub(crate) type_by_name: HashMap<NameId, TypeDefId>,
    pub(crate) method_by_full_name: HashMap<NameId, MethodId>,
    pub(crate) field_by_full_name: HashMap<NameId, FieldId>,
    pub(crate) function_by_name: HashMap<NameId, FunctionId>,

    // Scoped lookups: (type, method_name) -> MethodId
    pub(crate) methods_by_type: HashMap<TypeDefId, HashMap<NameId, MethodId>>,
    pub(crate) fields_by_type: HashMap<TypeDefId, HashMap<NameId, FieldId>>,
}

impl EntityRegistry {
    pub fn new() -> Self {
        Self {
            type_defs: Vec::new(),
            method_defs: Vec::new(),
            field_defs: Vec::new(),
            function_defs: Vec::new(),
            type_by_name: HashMap::new(),
            method_by_full_name: HashMap::new(),
            field_by_full_name: HashMap::new(),
            function_by_name: HashMap::new(),
            methods_by_type: HashMap::new(),
            fields_by_type: HashMap::new(),
        }
    }
}

impl Default for EntityRegistry {
    fn default() -> Self {
        Self::new()
    }
}
