//! Builder for method registration to reduce argument boilerplate.

use crate::entity_defs::MethodDef;
use crate::generic::TypeParamInfo;
use crate::implement_registry::ExternalMethodInfo;
use crate::type_arena::TypeId;
use vole_frontend::Expr;
use vole_identity::{MethodId, ModuleId, NameId, TypeDefId};

use super::EntityRegistry;

/// Builder for registering methods on types.
///
/// Provides a fluent API for method registration with sensible defaults:
/// - `is_static`: false
/// - `has_default`: false
/// - `external_binding`: None
/// - `method_type_params`: empty
/// - `required_params`: 0
/// - `param_defaults`: empty
///
/// # Example
/// ```ignore
/// let method_id = MethodDefBuilder::new(type_id, name_id, full_name_id, signature_id)
///     .has_default(true)
///     .is_static(true)
///     .register(&mut registry);
/// ```
pub struct MethodDefBuilder {
    defining_type: TypeDefId,
    name_id: NameId,
    full_name_id: NameId,
    signature_id: TypeId,
    is_static: bool,
    has_default: bool,
    external_binding: Option<ExternalMethodInfo>,
    method_type_params: Vec<TypeParamInfo>,
    required_params: usize,
    param_defaults: Vec<Option<Box<Expr>>>,
    param_names: Vec<String>,
    defining_module: Option<ModuleId>,
}

impl MethodDefBuilder {
    /// Create a new method builder with required fields.
    ///
    /// All optional fields start with sensible defaults.
    pub fn new(
        defining_type: TypeDefId,
        name_id: NameId,
        full_name_id: NameId,
        signature_id: TypeId,
    ) -> Self {
        Self {
            defining_type,
            name_id,
            full_name_id,
            signature_id,
            is_static: false,
            has_default: false,
            external_binding: None,
            method_type_params: Vec::new(),
            required_params: 0,
            param_defaults: Vec::new(),
            param_names: Vec::new(),
            defining_module: None,
        }
    }

    /// Set whether this is a static method (called on type, not instance).
    pub fn is_static(mut self, is_static: bool) -> Self {
        self.is_static = is_static;
        self
    }

    /// Set whether this method has a default implementation.
    pub fn has_default(mut self, has_default: bool) -> Self {
        self.has_default = has_default;
        self
    }

    /// Set the external binding for this method.
    pub fn external_binding(mut self, binding: Option<ExternalMethodInfo>) -> Self {
        self.external_binding = binding;
        self
    }

    /// Set method-level type parameters.
    pub fn method_type_params(mut self, params: Vec<TypeParamInfo>) -> Self {
        self.method_type_params = params;
        self
    }

    /// Set the number of required parameters and default values.
    pub fn param_defaults(
        mut self,
        required_params: usize,
        defaults: Vec<Option<Box<Expr>>>,
    ) -> Self {
        self.required_params = required_params;
        self.param_defaults = defaults;
        self
    }

    /// Set parameter names for named argument resolution.
    pub fn param_names(mut self, names: Vec<String>) -> Self {
        self.param_names = names;
        self
    }

    /// Restrict this method to a specific module (file-scoped extension method).
    ///
    /// When set, this method is only visible to callers in the given module.
    /// Used for `extend Type { }` ad-hoc extension methods.
    pub fn defining_module(mut self, module: ModuleId) -> Self {
        self.defining_module = Some(module);
        self
    }

    /// Register the method on the EntityRegistry.
    ///
    /// Returns the newly created `MethodId`.
    pub fn register(self, registry: &mut EntityRegistry) -> MethodId {
        let id = MethodId::new(registry.method_defs.len() as u32);
        registry.method_defs.push(MethodDef {
            id,
            name_id: self.name_id,
            full_name_id: self.full_name_id,
            defining_type: self.defining_type,
            signature_id: self.signature_id,
            has_default: self.has_default,
            is_static: self.is_static,
            external_binding: self.external_binding,
            method_type_params: self.method_type_params,
            required_params: self.required_params,
            param_defaults: self.param_defaults,
            param_names: self.param_names,
            defining_module: self.defining_module,
        });
        registry.method_by_full_name.insert(self.full_name_id, id);

        if self.is_static {
            registry
                .static_methods_by_type
                .get_mut(&self.defining_type)
                .expect("type must be registered before adding static methods")
                .insert(self.name_id, id);
            registry.type_defs[self.defining_type.index() as usize]
                .static_methods
                .push(id);
        } else {
            registry
                .methods_by_type
                .get_mut(&self.defining_type)
                .expect("type must be registered before adding methods")
                .insert(self.name_id, id);
            registry.type_defs[self.defining_type.index() as usize]
                .methods
                .push(id);
        }

        id
    }
}
