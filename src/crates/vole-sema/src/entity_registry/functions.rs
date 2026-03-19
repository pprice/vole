//! Free function registration and lookup for EntityRegistry.

use crate::FunctionType;
use crate::entity_defs::FunctionDef;
use vole_frontend::Expr;
use vole_identity::{FunctionId, ModuleId, NameId};

use super::EntityRegistry;

impl EntityRegistry {
    /// Register a new free function (all params required, no names, not external)
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
            vec![String::new(); total_params],
            false,
        )
    }

    /// Register a new free function with default expressions and param names.
    ///
    /// If a function with the same `full_name_id` was already registered (e.g.,
    /// the same module was analyzed by multiple files sharing a `CompilationDb`),
    /// returns the existing `FunctionId` to keep VIR caches consistent.
    #[expect(clippy::too_many_arguments)]
    pub fn register_function_full(
        &mut self,
        name_id: NameId,
        full_name_id: NameId,
        module: ModuleId,
        signature: FunctionType,
        required_params: usize,
        param_defaults: Vec<Option<Box<Expr>>>,
        param_names: Vec<String>,
        is_external: bool,
    ) -> FunctionId {
        // If this function was already registered (shared CompilationDb across
        // multiple files), return the existing FunctionId so that VIR caches
        // keyed by FunctionId remain valid.
        //
        // Update `param_defaults` to the new parse's AST nodes so that VIR
        // lowering's `fill_default_args` can find their types in the current
        // NodeMap (each analysis produces a fresh NodeMap with new NodeIds).
        if let Some(&existing_id) = self.function_by_name.get(&full_name_id) {
            self.function_defs[existing_id.index() as usize].param_defaults = param_defaults;
            return existing_id;
        }

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
            param_names,
            is_external,
            generator_element_type: None,
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

    /// Mark a function as a generator and store its element type.
    pub fn set_generator_element_type(
        &mut self,
        func_id: FunctionId,
        element_type: crate::type_arena::TypeId,
    ) {
        self.function_defs[func_id.index() as usize].generator_element_type = Some(element_type);
    }

    /// Iterate over all function definitions
    pub fn iter_functions(&self) -> impl Iterator<Item = &FunctionDef> {
        self.function_defs.iter()
    }
}
