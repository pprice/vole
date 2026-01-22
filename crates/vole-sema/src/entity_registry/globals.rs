//! Global variable registration and lookup for EntityRegistry.

use crate::entity_defs::GlobalDef;
use crate::type_arena::TypeId;
use vole_frontend::NodeId;
use vole_identity::{GlobalId, ModuleId, NameId};

use super::EntityRegistry;

impl EntityRegistry {
    /// Register a new global variable
    pub fn register_global(
        &mut self,
        name_id: NameId,
        type_id: TypeId,
        module_id: ModuleId,
        is_mutable: bool,
        init_node_id: NodeId,
    ) -> GlobalId {
        let id = GlobalId::new(self.global_defs.len() as u32);
        self.global_defs.push(GlobalDef {
            id,
            name_id,
            type_id,
            module_id,
            is_mutable,
            init_node_id,
        });
        self.global_by_name.insert(name_id, id);
        id
    }

    /// Get a global definition by ID
    pub fn get_global(&self, id: GlobalId) -> &GlobalDef {
        &self.global_defs[id.index() as usize]
    }

    /// Look up a global by its NameId
    pub fn global_by_name(&self, name_id: NameId) -> Option<GlobalId> {
        self.global_by_name.get(&name_id).copied()
    }
}
