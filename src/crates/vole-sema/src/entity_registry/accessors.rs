//! Convenience accessor methods for EntityRegistry.
//!
//! These methods return owned data tuples to avoid borrow checker conflicts.
//! Instead of:
//!   let registry = self.entity_registry();
//!   let type_def = registry.get_type(id);
//!   let (kind, name) = (type_def.kind, type_def.name_id);
//!   drop(registry);
//!
//! You can use:
//!   let (kind, name) = self.entity_registry().type_kind_and_name(id);

use crate::entity_defs::{GenericTypeInfo, TypeDefKind};
use crate::generic::TypeParamInfo;
use crate::type_arena::TypeId as ArenaTypeId;
use vole_identity::{FieldId, MethodId, NameId, TypeDefId};

use super::EntityRegistry;

impl EntityRegistry {
    // ===== TypeDef Accessors =====

    /// Get kind and name_id for a type definition.
    ///
    /// Common pattern: checking type kind and getting its name for error messages.
    #[inline]
    pub fn type_kind_and_name(&self, id: TypeDefId) -> (TypeDefKind, NameId) {
        let td = self.get_type(id);
        (td.kind, td.name_id)
    }

    /// Get kind for a type definition.
    #[inline]
    pub fn type_kind(&self, id: TypeDefId) -> TypeDefKind {
        self.get_type(id).kind
    }

    /// Get aliased_type for a type alias.
    ///
    /// Returns None if type is not an alias or has no aliased_type set.
    #[inline]
    pub fn type_aliased(&self, id: TypeDefId) -> Option<ArenaTypeId> {
        self.get_type(id).aliased_type
    }

    /// Get type_params for a type definition.
    #[inline]
    pub fn type_params(&self, id: TypeDefId) -> Vec<NameId> {
        self.get_type(id).type_params.clone()
    }

    /// Get methods list for a type (cloned to release borrow).
    #[inline]
    pub fn type_methods(&self, id: TypeDefId) -> Vec<MethodId> {
        self.get_type(id).methods.clone()
    }

    /// Get fields list for a type (cloned to release borrow).
    #[inline]
    pub fn type_fields(&self, id: TypeDefId) -> Vec<FieldId> {
        self.get_type(id).fields.clone()
    }

    /// Get extends list for a type (cloned to release borrow).
    #[inline]
    pub fn type_extends_list(&self, id: TypeDefId) -> Vec<TypeDefId> {
        self.get_type(id).extends.clone()
    }

    /// Get generic_info for a type (cloned to release borrow).
    #[inline]
    pub fn type_generic_info(&self, id: TypeDefId) -> Option<GenericTypeInfo> {
        self.get_type(id).generic_info.clone()
    }

    /// Get interface info: is_interface, fields, methods, extends (all cloned).
    ///
    /// Common pattern: checking interface satisfaction.
    pub fn interface_info(
        &self,
        id: TypeDefId,
    ) -> (bool, Vec<FieldId>, Vec<MethodId>, Vec<TypeDefId>) {
        let td = self.get_type(id);
        (
            td.kind == TypeDefKind::Interface,
            td.fields.clone(),
            td.methods.clone(),
            td.extends.clone(),
        )
    }

    // ===== MethodDef Accessors =====

    /// Get name_id and signature_id for a method.
    ///
    /// Common pattern: method lookup and type checking.
    #[inline]
    pub fn method_name_and_sig(&self, id: MethodId) -> (NameId, ArenaTypeId) {
        let md = self.get_method(id);
        (md.name_id, md.signature_id)
    }

    /// Get signature_id for a method.
    #[inline]
    pub fn method_signature(&self, id: MethodId) -> ArenaTypeId {
        self.get_method(id).signature_id
    }

    /// Get has_default, name_id, and signature_id for a method.
    ///
    /// Common pattern: interface satisfaction checking.
    #[inline]
    pub fn method_default_name_sig(&self, id: MethodId) -> (bool, NameId, ArenaTypeId) {
        let md = self.get_method(id);
        (md.has_default, md.name_id, md.signature_id)
    }

    /// Get full method info needed for generic method calls.
    ///
    /// Returns: (is_static, method_type_params, signature_id, required_params, full_name_id)
    pub fn method_call_info(
        &self,
        id: MethodId,
    ) -> (bool, Vec<TypeParamInfo>, ArenaTypeId, usize, NameId) {
        let md = self.get_method(id);
        (
            md.is_static,
            md.method_type_params.clone(),
            md.signature_id,
            md.required_params,
            md.full_name_id,
        )
    }

    /// Get defining_type for a method.
    #[inline]
    pub fn method_defining_type(&self, id: MethodId) -> TypeDefId {
        self.get_method(id).defining_type
    }

    /// Get full_name_id for a method.
    #[inline]
    pub fn method_full_name(&self, id: MethodId) -> NameId {
        self.get_method(id).full_name_id
    }

    // ===== FieldDef Accessors =====

    /// Get name_id and type for a field.
    ///
    /// Common pattern: field lookup and type checking.
    #[inline]
    pub fn field_name_and_type(&self, id: FieldId) -> (NameId, ArenaTypeId) {
        let fd = self.get_field(id);
        (fd.name_id, fd.ty)
    }

    /// Get type for a field.
    #[inline]
    pub fn field_type(&self, id: FieldId) -> ArenaTypeId {
        self.get_field(id).ty
    }

    // ===== Default expression accessors =====

    /// Get the default expression for a function parameter by index.
    ///
    /// Returns `Some(&Expr)` if the parameter at `param_idx` has a default,
    /// or `None` if it is required or the index is out of range.
    #[inline]
    pub fn function_default_expr(
        &self,
        func_id: vole_identity::FunctionId,
        param_idx: usize,
    ) -> Option<&vole_frontend::Expr> {
        self.get_function(func_id)
            .param_defaults
            .get(param_idx)
            .and_then(|opt| opt.as_deref())
    }

    /// Get the default expression for a method parameter by index.
    ///
    /// Returns `Some(&Expr)` if the parameter at `param_idx` has a default,
    /// or `None` if it is required or the index is out of range.
    #[inline]
    pub fn method_default_expr(
        &self,
        method_id: MethodId,
        param_idx: usize,
    ) -> Option<&vole_frontend::Expr> {
        self.get_method(method_id)
            .param_defaults
            .get(param_idx)
            .and_then(|opt| opt.as_deref())
    }
}
