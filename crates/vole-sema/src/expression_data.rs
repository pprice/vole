//! Node-level metadata for expressions.
//!
//! ExpressionData encapsulates all metadata that is keyed by NodeId,
//! including type information, method resolutions, and generic instantiations.

use rustc_hash::FxHashMap;
use std::collections::HashMap;

use crate::generic::{ClassMethodMonomorphKey, MonomorphKey, StaticMethodMonomorphKey};
use crate::resolution::ResolvedMethod;
use crate::type_arena::TypeId;
use vole_frontend::NodeId;

/// Encapsulates all NodeId-keyed metadata from semantic analysis.
/// This includes expression types, method resolutions, and generic instantiation info.
#[derive(Debug, Clone)]
pub struct ExpressionData {
    /// Type of each expression node (stored as interned TypeId handles)
    types: HashMap<NodeId, TypeId>,
    /// Resolved method information for method calls
    methods: HashMap<NodeId, ResolvedMethod>,
    /// Monomorphization key for generic function calls
    generics: HashMap<NodeId, MonomorphKey>,
    /// Monomorphization key for generic class method calls
    class_method_generics: HashMap<NodeId, ClassMethodMonomorphKey>,
    /// Monomorphization key for generic static method calls
    static_method_generics: HashMap<NodeId, StaticMethodMonomorphKey>,
    /// Per-module type mappings (for multi-module compilation)
    module_types: FxHashMap<String, HashMap<NodeId, TypeId>>,
    /// Per-module method resolutions (for multi-module compilation)
    module_methods: FxHashMap<String, HashMap<NodeId, ResolvedMethod>>,
    /// Substituted return types for generic method calls.
    /// When sema resolves a call like `list.head()` on `List<i32>`, the generic
    /// return type `T` is substituted to `i32`. This map stores the concrete type
    /// so codegen doesn't need to recompute the substitution.
    substituted_return_types: HashMap<NodeId, TypeId>,
}

impl Default for ExpressionData {
    fn default() -> Self {
        Self {
            types: HashMap::new(),
            methods: HashMap::new(),
            generics: HashMap::new(),
            class_method_generics: HashMap::new(),
            static_method_generics: HashMap::new(),
            module_types: FxHashMap::default(),
            module_methods: FxHashMap::default(),
            substituted_return_types: HashMap::new(),
        }
    }
}

impl ExpressionData {
    /// Create a new empty ExpressionData
    pub fn new() -> Self {
        Self::default()
    }

    /// Create ExpressionData from analysis results
    #[allow(clippy::too_many_arguments)]
    pub fn from_analysis(
        types: HashMap<NodeId, TypeId>,
        methods: HashMap<NodeId, ResolvedMethod>,
        generics: HashMap<NodeId, MonomorphKey>,
        class_method_generics: HashMap<NodeId, ClassMethodMonomorphKey>,
        static_method_generics: HashMap<NodeId, StaticMethodMonomorphKey>,
        module_types: FxHashMap<String, HashMap<NodeId, TypeId>>,
        module_methods: FxHashMap<String, HashMap<NodeId, ResolvedMethod>>,
        substituted_return_types: HashMap<NodeId, TypeId>,
    ) -> Self {
        Self {
            types,
            methods,
            generics,
            class_method_generics,
            static_method_generics,
            module_types,
            module_methods,
            substituted_return_types,
        }
    }

    /// Get the type of an expression by its NodeId (returns interned TypeId handle).
    pub fn get_type(&self, node: NodeId) -> Option<TypeId> {
        self.types.get(&node).copied()
    }

    /// Set the type of an expression using a TypeId handle directly
    pub fn set_type_handle(&mut self, node: NodeId, ty: TypeId) {
        self.types.insert(node, ty);
    }

    /// Get the resolved method for a method call
    pub fn get_method(&self, node: NodeId) -> Option<&ResolvedMethod> {
        self.methods.get(&node)
    }

    /// Get the resolved method for a method call, checking module-specific resolutions first
    pub fn get_method_in_module(
        &self,
        node: NodeId,
        current_module: Option<&str>,
    ) -> Option<&ResolvedMethod> {
        // First check module-specific resolutions
        if let Some(module) = current_module {
            tracing::trace!(module, ?node, "Looking up method in module");
            if let Some(module_methods) = self.module_methods.get(module) {
                let node_ids: Vec<_> = module_methods.keys().collect();
                tracing::trace!(
                    count = module_methods.len(),
                    ?node_ids,
                    "Found module methods"
                );
                if let Some(method) = module_methods.get(&node) {
                    tracing::trace!(?method, "Found method resolution in module");
                    return Some(method);
                }
                tracing::trace!(?node, "Method not found in module methods");
            } else {
                tracing::trace!("Module not found in module_methods");
            }
        }
        // Fall back to main program resolutions
        self.methods.get(&node)
    }

    /// Set the resolved method for a method call
    pub fn set_method(&mut self, node: NodeId, method: ResolvedMethod) {
        self.methods.insert(node, method);
    }

    /// Get the monomorphization key for a generic function call
    pub fn get_generic(&self, node: NodeId) -> Option<&MonomorphKey> {
        self.generics.get(&node)
    }

    /// Set the monomorphization key for a generic function call
    pub fn set_generic(&mut self, node: NodeId, key: MonomorphKey) {
        self.generics.insert(node, key);
    }

    /// Get all expression types (as TypeId handles)
    pub fn types(&self) -> &HashMap<NodeId, TypeId> {
        &self.types
    }

    /// Get mutable access to expression types
    pub fn types_mut(&mut self) -> &mut HashMap<NodeId, TypeId> {
        &mut self.types
    }

    /// Get all method resolutions
    pub fn methods(&self) -> &HashMap<NodeId, ResolvedMethod> {
        &self.methods
    }

    /// Get mutable access to method resolutions
    pub fn methods_mut(&mut self) -> &mut HashMap<NodeId, ResolvedMethod> {
        &mut self.methods
    }

    /// Get all monomorphization keys
    pub fn generics(&self) -> &HashMap<NodeId, MonomorphKey> {
        &self.generics
    }

    /// Get mutable access to monomorphization keys
    pub fn generics_mut(&mut self) -> &mut HashMap<NodeId, MonomorphKey> {
        &mut self.generics
    }

    /// Get the monomorphization key for a generic class method call
    pub fn get_class_method_generic(&self, node: NodeId) -> Option<&ClassMethodMonomorphKey> {
        self.class_method_generics.get(&node)
    }

    /// Set the monomorphization key for a generic class method call
    pub fn set_class_method_generic(&mut self, node: NodeId, key: ClassMethodMonomorphKey) {
        self.class_method_generics.insert(node, key);
    }

    /// Get all class method monomorphization keys
    pub fn class_method_generics(&self) -> &HashMap<NodeId, ClassMethodMonomorphKey> {
        &self.class_method_generics
    }

    /// Get mutable access to class method monomorphization keys
    pub fn class_method_generics_mut(&mut self) -> &mut HashMap<NodeId, ClassMethodMonomorphKey> {
        &mut self.class_method_generics
    }

    /// Get the monomorphization key for a generic static method call
    pub fn get_static_method_generic(&self, node: NodeId) -> Option<&StaticMethodMonomorphKey> {
        self.static_method_generics.get(&node)
    }

    /// Set the monomorphization key for a generic static method call
    pub fn set_static_method_generic(&mut self, node: NodeId, key: StaticMethodMonomorphKey) {
        self.static_method_generics.insert(node, key);
    }

    /// Get all static method monomorphization keys
    pub fn static_method_generics(&self) -> &HashMap<NodeId, StaticMethodMonomorphKey> {
        &self.static_method_generics
    }

    /// Get mutable access to static method monomorphization keys
    pub fn static_method_generics_mut(&mut self) -> &mut HashMap<NodeId, StaticMethodMonomorphKey> {
        &mut self.static_method_generics
    }

    /// Get types for a specific module (as TypeId handles)
    pub fn module_types(&self, module: &str) -> Option<&HashMap<NodeId, TypeId>> {
        self.module_types.get(module)
    }

    /// Set types for a specific module
    pub fn set_module_types(&mut self, module: String, types: HashMap<NodeId, TypeId>) {
        self.module_types.insert(module, types);
    }

    /// Get all module type mappings
    pub fn all_module_types(&self) -> &FxHashMap<String, HashMap<NodeId, TypeId>> {
        &self.module_types
    }

    /// Get methods for a specific module
    pub fn module_methods(&self, module: &str) -> Option<&HashMap<NodeId, ResolvedMethod>> {
        self.module_methods.get(module)
    }

    /// Set methods for a specific module
    pub fn set_module_methods(&mut self, module: String, methods: HashMap<NodeId, ResolvedMethod>) {
        self.module_methods.insert(module, methods);
    }

    /// Get all module method mappings
    pub fn all_module_methods(&self) -> &FxHashMap<String, HashMap<NodeId, ResolvedMethod>> {
        &self.module_methods
    }

    /// Get the substituted return type for a method call.
    /// This is the concrete return type after generic substitution (e.g., `i32` instead of `T`).
    pub fn get_substituted_return_type(&self, node: NodeId) -> Option<TypeId> {
        self.substituted_return_types.get(&node).copied()
    }

    /// Set the substituted return type for a method call.
    pub fn set_substituted_return_type(&mut self, node: NodeId, ty: TypeId) {
        self.substituted_return_types.insert(node, ty);
    }

    /// Get all substituted return types
    pub fn substituted_return_types(&self) -> &HashMap<NodeId, TypeId> {
        &self.substituted_return_types
    }

    /// Get mutable access to substituted return types
    pub fn substituted_return_types_mut(&mut self) -> &mut HashMap<NodeId, TypeId> {
        &mut self.substituted_return_types
    }
}
