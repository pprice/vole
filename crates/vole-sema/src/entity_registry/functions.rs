//! Free function registration and lookup for EntityRegistry.

use crate::FunctionType;
use crate::entity_defs::FunctionDef;
use vole_identity::{FunctionId, ModuleId, NameId};

use super::EntityRegistry;

impl EntityRegistry {
    /// Register a new free function
    pub fn register_function(
        &mut self,
        name_id: NameId,
        full_name_id: NameId,
        module: ModuleId,
        signature: FunctionType,
    ) -> FunctionId {
        let id = FunctionId::new(self.function_defs.len() as u32);
        self.function_defs.push(FunctionDef {
            id,
            name_id,
            full_name_id,
            module,
            signature,
            generic_info: None,
        });
        self.function_by_name.insert(full_name_id, id);
        id
    }

    /// Get a function definition by ID
    pub fn get_function(&self, id: FunctionId) -> &FunctionDef {
        &self.function_defs[id.index() as usize]
    }

    /// Look up a function by its full NameId
    pub fn function_by_name(&self, full_name_id: NameId) -> Option<FunctionId> {
        self.function_by_name.get(&full_name_id).copied()
    }

    /// Set generic function info (type params, param/return types) for a generic function
    pub fn set_function_generic_info(
        &mut self,
        func_id: FunctionId,
        info: crate::entity_defs::GenericFuncInfo,
    ) {
        self.function_defs[func_id.index() as usize].generic_info = Some(info);
    }

    /// Update the return type of a function (used for return type inference)
    pub fn update_function_return_type(
        &mut self,
        func_id: FunctionId,
        return_type: crate::type_arena::TypeId,
    ) {
        self.function_defs[func_id.index() as usize]
            .signature
            .return_type_id = return_type;
    }
}
