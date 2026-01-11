//! Node-level metadata for expressions.
//!
//! ExpressionData encapsulates all metadata that is keyed by NodeId,
//! including type information, method resolutions, and generic instantiations.

use std::collections::HashMap;

use crate::frontend::NodeId;
use crate::sema::Type;
use crate::sema::generic::MonomorphKey;
use crate::sema::resolution::ResolvedMethod;

/// Encapsulates all NodeId-keyed metadata from semantic analysis.
/// This includes expression types, method resolutions, and generic instantiation info.
#[derive(Debug, Default, Clone)]
pub struct ExpressionData {
    /// Type of each expression node
    types: HashMap<NodeId, Type>,
    /// Resolved method information for method calls
    methods: HashMap<NodeId, ResolvedMethod>,
    /// Monomorphization key for generic function calls
    generics: HashMap<NodeId, MonomorphKey>,
    /// Per-module type mappings (for multi-module compilation)
    module_types: HashMap<String, HashMap<NodeId, Type>>,
}

impl ExpressionData {
    /// Create a new empty ExpressionData
    pub fn new() -> Self {
        Self::default()
    }

    /// Get the type of an expression by its NodeId
    pub fn get_type(&self, node: NodeId) -> Option<&Type> {
        self.types.get(&node)
    }

    /// Set the type of an expression
    pub fn set_type(&mut self, node: NodeId, ty: Type) {
        self.types.insert(node, ty);
    }

    /// Get the resolved method for a method call
    pub fn get_method(&self, node: NodeId) -> Option<&ResolvedMethod> {
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

    /// Get all expression types
    pub fn types(&self) -> &HashMap<NodeId, Type> {
        &self.types
    }

    /// Get mutable access to expression types
    pub fn types_mut(&mut self) -> &mut HashMap<NodeId, Type> {
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

    /// Get types for a specific module
    pub fn module_types(&self, module: &str) -> Option<&HashMap<NodeId, Type>> {
        self.module_types.get(module)
    }

    /// Set types for a specific module
    pub fn set_module_types(&mut self, module: String, types: HashMap<NodeId, Type>) {
        self.module_types.insert(module, types);
    }

    /// Get all module type mappings
    pub fn all_module_types(&self) -> &HashMap<String, HashMap<NodeId, Type>> {
        &self.module_types
    }
}
