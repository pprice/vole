//! Free function registration and lookup for EntityRegistry.

use crate::FunctionType;
use crate::entity_defs::FunctionDef;
use vole_frontend::Expr;
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
        let total_params = signature.params_id.len();
        self.register_function_full(
            name_id,
            full_name_id,
            module,
            signature,
            total_params, // All params required
            vec![None; total_params],
        )
    }

    /// Register a new free function with specified number of required params
    pub fn register_function_with_defaults(
        &mut self,
        name_id: NameId,
        full_name_id: NameId,
        module: ModuleId,
        signature: FunctionType,
        required_params: usize,
    ) -> FunctionId {
        let total_params = signature.params_id.len();
        self.register_function_full(
            name_id,
            full_name_id,
            module,
            signature,
            required_params,
            vec![None; total_params],
        )
    }

    /// Register a new free function with default expressions
    pub fn register_function_full(
        &mut self,
        name_id: NameId,
        full_name_id: NameId,
        module: ModuleId,
        signature: FunctionType,
        required_params: usize,
        param_defaults: Vec<Option<Box<Expr>>>,
    ) -> FunctionId {
        let id = FunctionId::new(self.function_defs.len() as u32);
        self.function_defs.push(FunctionDef {
            id,
            name_id,
            full_name_id,
            module,
            signature,
            required_params,
            generic_info: None,
            param_defaults,
        });
        self.function_by_name.insert(full_name_id, id);
        // Also register under name_id if different (for renamed imports like `sqrt as squareRoot`)
        if name_id != full_name_id {
            self.function_by_name.insert(name_id, id);
        }
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

    /// Update the number of required parameters for a function
    pub fn set_function_required_params(&mut self, func_id: FunctionId, required_params: usize) {
        self.function_defs[func_id.index() as usize].required_params = required_params;
    }

    /// Iterate over all function definitions
    pub fn iter_functions(&self) -> impl Iterator<Item = &FunctionDef> {
        self.function_defs.iter()
    }
}
