use std::rc::Rc;

use vole_identity::{FunctionId, MethodId, NameId, NameTable, TypeDefId};

use crate::EntityRegistry;

/// Bridge trait used by VIR lowering helpers so they can run against
/// `EntityRegistry` and `Rc<EntityRegistry>` uniformly.
pub trait LoweringEntityLookup {
    fn function_by_name(&self, name_id: NameId) -> Option<FunctionId>;
    fn type_by_name(&self, name_id: NameId) -> Option<TypeDefId>;
    fn type_by_short_name(&self, short_name: &str, names: &NameTable) -> Option<TypeDefId>;
    fn find_method_on_type(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId>;
    fn find_static_method_on_type(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId>;
    fn as_entity_registry(&self) -> &EntityRegistry;
    fn array_name_id(&self) -> Option<NameId>;
    fn get_type(&self, type_def_id: TypeDefId) -> &crate::entity_defs::TypeDef;
    fn get_function(&self, func_id: FunctionId) -> &crate::entity_defs::FunctionDef;
    fn get_method(&self, method_id: MethodId) -> &crate::entity_defs::MethodDef;
    fn get_implemented_interfaces(&self, type_def_id: TypeDefId) -> Vec<TypeDefId>;
    fn methods_on_type(&self, type_def_id: TypeDefId) -> Vec<MethodId>;
    fn monomorph_instances(&self) -> Vec<crate::generic::MonomorphInstance>;
    fn class_method_monomorph_instances(&self)
    -> Vec<crate::generic::ClassMethodMonomorphInstance>;
    fn static_method_monomorph_instances(
        &self,
    ) -> Vec<crate::generic::StaticMethodMonomorphInstance>;
}

impl LoweringEntityLookup for EntityRegistry {
    fn function_by_name(&self, name_id: NameId) -> Option<FunctionId> {
        EntityRegistry::function_by_name(self, name_id)
    }

    fn type_by_name(&self, name_id: NameId) -> Option<TypeDefId> {
        EntityRegistry::type_by_name(self, name_id)
    }

    fn type_by_short_name(&self, short_name: &str, names: &NameTable) -> Option<TypeDefId> {
        EntityRegistry::type_by_short_name(self, short_name, names)
    }

    fn find_method_on_type(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId> {
        EntityRegistry::find_method_on_type(self, type_def_id, method_name_id)
    }

    fn find_static_method_on_type(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId> {
        EntityRegistry::find_static_method_on_type(self, type_def_id, method_name_id)
    }

    fn as_entity_registry(&self) -> &EntityRegistry {
        self
    }

    fn array_name_id(&self) -> Option<NameId> {
        EntityRegistry::array_name_id(self)
    }

    fn get_type(&self, type_def_id: TypeDefId) -> &crate::entity_defs::TypeDef {
        EntityRegistry::get_type(self, type_def_id)
    }

    fn get_function(&self, func_id: FunctionId) -> &crate::entity_defs::FunctionDef {
        EntityRegistry::get_function(self, func_id)
    }

    fn get_method(&self, method_id: MethodId) -> &crate::entity_defs::MethodDef {
        EntityRegistry::get_method(self, method_id)
    }

    fn get_implemented_interfaces(&self, type_def_id: TypeDefId) -> Vec<TypeDefId> {
        EntityRegistry::get_implemented_interfaces(self, type_def_id)
    }

    fn methods_on_type(&self, type_def_id: TypeDefId) -> Vec<MethodId> {
        EntityRegistry::methods_on_type(self, type_def_id).collect()
    }

    fn monomorph_instances(&self) -> Vec<crate::generic::MonomorphInstance> {
        self.monomorph_cache.collect_instances()
    }

    fn class_method_monomorph_instances(
        &self,
    ) -> Vec<crate::generic::ClassMethodMonomorphInstance> {
        self.class_method_monomorph_cache.collect_instances()
    }

    fn static_method_monomorph_instances(
        &self,
    ) -> Vec<crate::generic::StaticMethodMonomorphInstance> {
        self.static_method_monomorph_cache.collect_instances()
    }
}

impl<T> LoweringEntityLookup for Rc<T>
where
    T: LoweringEntityLookup + ?Sized,
{
    fn function_by_name(&self, name_id: NameId) -> Option<FunctionId> {
        (**self).function_by_name(name_id)
    }

    fn type_by_name(&self, name_id: NameId) -> Option<TypeDefId> {
        (**self).type_by_name(name_id)
    }

    fn type_by_short_name(&self, short_name: &str, names: &NameTable) -> Option<TypeDefId> {
        (**self).type_by_short_name(short_name, names)
    }

    fn find_method_on_type(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId> {
        (**self).find_method_on_type(type_def_id, method_name_id)
    }

    fn find_static_method_on_type(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId> {
        (**self).find_static_method_on_type(type_def_id, method_name_id)
    }

    fn as_entity_registry(&self) -> &EntityRegistry {
        (**self).as_entity_registry()
    }

    fn array_name_id(&self) -> Option<NameId> {
        (**self).array_name_id()
    }

    fn get_type(&self, type_def_id: TypeDefId) -> &crate::entity_defs::TypeDef {
        (**self).get_type(type_def_id)
    }

    fn get_function(&self, func_id: FunctionId) -> &crate::entity_defs::FunctionDef {
        (**self).get_function(func_id)
    }

    fn get_method(&self, method_id: MethodId) -> &crate::entity_defs::MethodDef {
        (**self).get_method(method_id)
    }

    fn get_implemented_interfaces(&self, type_def_id: TypeDefId) -> Vec<TypeDefId> {
        (**self).get_implemented_interfaces(type_def_id)
    }

    fn methods_on_type(&self, type_def_id: TypeDefId) -> Vec<MethodId> {
        (**self).methods_on_type(type_def_id)
    }

    fn monomorph_instances(&self) -> Vec<crate::generic::MonomorphInstance> {
        (**self).monomorph_instances()
    }

    fn class_method_monomorph_instances(
        &self,
    ) -> Vec<crate::generic::ClassMethodMonomorphInstance> {
        (**self).class_method_monomorph_instances()
    }

    fn static_method_monomorph_instances(
        &self,
    ) -> Vec<crate::generic::StaticMethodMonomorphInstance> {
        (**self).static_method_monomorph_instances()
    }
}
