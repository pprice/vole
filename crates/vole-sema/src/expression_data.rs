//! Node-level metadata for expressions.
//!
//! ExpressionData encapsulates all metadata that is keyed by NodeId,
//! including type information, method resolutions, and generic instantiations.

use rustc_hash::FxHashMap;
use std::collections::HashMap;

use crate::analysis_cache::IsCheckResult;
use crate::generic::{ClassMethodMonomorphKey, MonomorphKey, StaticMethodMonomorphKey};
use crate::resolution::ResolvedMethod;
use crate::type_arena::TypeId;
use vole_frontend::{NodeId, Span};

/// Information about a lambda's parameter defaults.
/// Used to support calling closures with default arguments.
#[derive(Debug, Clone)]
pub struct LambdaDefaults {
    /// Number of required parameters (those without defaults)
    pub required_params: usize,
    /// NodeId of the lambda expression (for accessing default expressions in AST)
    pub lambda_node_id: NodeId,
}

/// Encapsulates all NodeId-keyed metadata from semantic analysis.
/// This includes expression types, method resolutions, and generic instantiation info.
#[derive(Debug, Clone, Default)]
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
    /// Lambda defaults for closure calls.
    /// Maps a call site NodeId to the lambda's defaults info.
    lambda_defaults: HashMap<NodeId, LambdaDefaults>,
    /// Scoped function closure types.
    /// Maps function declaration span to its closure function type.
    /// Used for scoped functions in test blocks which are compiled as closures.
    scoped_function_types: HashMap<Span, TypeId>,
    /// Type check results for `is` expressions and type patterns.
    /// Maps NodeId → IsCheckResult to eliminate runtime type lookups in codegen.
    is_check_results: HashMap<NodeId, IsCheckResult>,
    /// Declared variable types for let statements with explicit type annotations.
    /// Maps init expression NodeId → declared TypeId, enabling codegen to handle
    /// union wrapping, numeric widening, and interface boxing without re-resolving types.
    declared_var_types: HashMap<NodeId, TypeId>,
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
        lambda_defaults: HashMap<NodeId, LambdaDefaults>,
        scoped_function_types: HashMap<Span, TypeId>,
        is_check_results: HashMap<NodeId, IsCheckResult>,
        declared_var_types: HashMap<NodeId, TypeId>,
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
            lambda_defaults,
            scoped_function_types,
            is_check_results,
            declared_var_types,
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

    /// Get lambda defaults for a call site
    pub fn get_lambda_defaults(&self, call_node: NodeId) -> Option<&LambdaDefaults> {
        self.lambda_defaults.get(&call_node)
    }

    /// Set lambda defaults for a call site
    pub fn set_lambda_defaults(&mut self, call_node: NodeId, defaults: LambdaDefaults) {
        self.lambda_defaults.insert(call_node, defaults);
    }

    /// Get all lambda defaults
    pub fn lambda_defaults(&self) -> &HashMap<NodeId, LambdaDefaults> {
        &self.lambda_defaults
    }

    /// Get mutable access to lambda defaults
    pub fn lambda_defaults_mut(&mut self) -> &mut HashMap<NodeId, LambdaDefaults> {
        &mut self.lambda_defaults
    }

    /// Get the closure function type for a scoped function by its declaration span
    pub fn get_scoped_function_type(&self, span: Span) -> Option<TypeId> {
        self.scoped_function_types.get(&span).copied()
    }

    /// Set the closure function type for a scoped function
    pub fn set_scoped_function_type(&mut self, span: Span, type_id: TypeId) {
        self.scoped_function_types.insert(span, type_id);
    }

    /// Get all scoped function types
    pub fn scoped_function_types(&self) -> &HashMap<Span, TypeId> {
        &self.scoped_function_types
    }

    /// Get the IsCheckResult for a type check node (is expression or type pattern)
    pub fn get_is_check_result(&self, node: NodeId) -> Option<IsCheckResult> {
        self.is_check_results.get(&node).copied()
    }

    /// Set the IsCheckResult for a type check node
    pub fn set_is_check_result(&mut self, node: NodeId, result: IsCheckResult) {
        self.is_check_results.insert(node, result);
    }

    /// Get all IsCheckResults
    pub fn is_check_results(&self) -> &HashMap<NodeId, IsCheckResult> {
        &self.is_check_results
    }

    /// Get mutable access to IsCheckResults
    pub fn is_check_results_mut(&mut self) -> &mut HashMap<NodeId, IsCheckResult> {
        &mut self.is_check_results
    }

    /// Get the declared type for a variable's init expression.
    /// Used for let statements with explicit type annotations (e.g., `let x: SomeType = ...`).
    pub fn get_declared_var_type(&self, init_node: NodeId) -> Option<TypeId> {
        self.declared_var_types.get(&init_node).copied()
    }

    /// Set the declared type for a variable's init expression.
    pub fn set_declared_var_type(&mut self, init_node: NodeId, type_id: TypeId) {
        self.declared_var_types.insert(init_node, type_id);
    }

    /// Get all declared variable types
    pub fn declared_var_types(&self) -> &HashMap<NodeId, TypeId> {
        &self.declared_var_types
    }
}
