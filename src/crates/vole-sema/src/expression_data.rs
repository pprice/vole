//! Node-level metadata for expressions.
//!
//! ExpressionData encapsulates all metadata that is keyed by NodeId,
//! including type information, method resolutions, and generic instantiations.

use rustc_hash::FxHashMap;

use crate::analysis_cache::IsCheckResult;
use crate::generic::{ClassMethodMonomorphKey, MonomorphKey, StaticMethodMonomorphKey};
use crate::resolution::ResolvedMethod;
use crate::type_arena::TypeId;
use vole_frontend::{NodeId, Span};
use vole_identity::ModuleId;

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
    types: FxHashMap<NodeId, TypeId>,
    /// Resolved method information for method calls
    methods: FxHashMap<NodeId, ResolvedMethod>,
    /// Monomorphization key for generic function calls
    generics: FxHashMap<NodeId, MonomorphKey>,
    /// Monomorphization key for generic class method calls
    class_method_generics: FxHashMap<NodeId, ClassMethodMonomorphKey>,
    /// Monomorphization key for generic static method calls
    static_method_generics: FxHashMap<NodeId, StaticMethodMonomorphKey>,
    /// Per-module type mappings (for multi-module compilation)
    module_types: FxHashMap<String, FxHashMap<NodeId, TypeId>>,
    /// Per-module method resolutions (for multi-module compilation)
    module_methods: FxHashMap<String, FxHashMap<NodeId, ResolvedMethod>>,
    /// Per-module is_check_results (for multi-module compilation)
    module_is_check_results: FxHashMap<String, FxHashMap<NodeId, IsCheckResult>>,
    /// Per-module generic function call keys (for multi-module compilation)
    module_generics: FxHashMap<String, FxHashMap<NodeId, MonomorphKey>>,
    /// Per-module class method generic keys (for multi-module compilation)
    module_class_method_generics: FxHashMap<String, FxHashMap<NodeId, ClassMethodMonomorphKey>>,
    /// Per-module static method generic keys (for multi-module compilation)
    module_static_method_generics: FxHashMap<String, FxHashMap<NodeId, StaticMethodMonomorphKey>>,
    /// Substituted return types for generic method calls.
    /// When sema resolves a call like `list.head()` on `List<i32>`, the generic
    /// return type `T` is substituted to `i32`. This map stores the concrete type
    /// so codegen doesn't need to recompute the substitution.
    substituted_return_types: FxHashMap<NodeId, TypeId>,
    /// Lambda defaults for closure calls.
    /// Maps a call site NodeId to the lambda's defaults info.
    lambda_defaults: FxHashMap<NodeId, LambdaDefaults>,
    /// Virtual module IDs for tests blocks. Maps tests block span to its virtual ModuleId.
    /// Used by codegen to compile scoped type declarations (records, classes) within tests blocks.
    tests_virtual_modules: FxHashMap<Span, ModuleId>,
    /// Type check results for `is` expressions and type patterns.
    /// Maps NodeId → IsCheckResult to eliminate runtime type lookups in codegen.
    is_check_results: FxHashMap<NodeId, IsCheckResult>,
    /// Declared variable types for let statements with explicit type annotations.
    /// Maps init expression NodeId → declared TypeId, enabling codegen to handle
    /// union wrapping, numeric widening, and interface boxing without re-resolving types.
    declared_var_types: FxHashMap<NodeId, TypeId>,
}

/// Builder for `ExpressionData` to reduce construction boilerplate.
///
/// Provides a fluent API for setting analysis results, with all fields
/// defaulting to empty collections.
///
/// # Example
/// ```ignore
/// let data = ExpressionDataBuilder::new()
///     .types(expr_types)
///     .methods(method_resolutions)
///     .generics(generic_calls)
///     .build();
/// ```
#[derive(Default)]
pub struct ExpressionDataBuilder {
    types: FxHashMap<NodeId, TypeId>,
    methods: FxHashMap<NodeId, ResolvedMethod>,
    generics: FxHashMap<NodeId, MonomorphKey>,
    class_method_generics: FxHashMap<NodeId, ClassMethodMonomorphKey>,
    static_method_generics: FxHashMap<NodeId, StaticMethodMonomorphKey>,
    module_types: FxHashMap<String, FxHashMap<NodeId, TypeId>>,
    module_methods: FxHashMap<String, FxHashMap<NodeId, ResolvedMethod>>,
    module_is_check_results: FxHashMap<String, FxHashMap<NodeId, IsCheckResult>>,
    module_generics: FxHashMap<String, FxHashMap<NodeId, MonomorphKey>>,
    module_class_method_generics: FxHashMap<String, FxHashMap<NodeId, ClassMethodMonomorphKey>>,
    module_static_method_generics: FxHashMap<String, FxHashMap<NodeId, StaticMethodMonomorphKey>>,
    substituted_return_types: FxHashMap<NodeId, TypeId>,
    lambda_defaults: FxHashMap<NodeId, LambdaDefaults>,
    tests_virtual_modules: FxHashMap<Span, ModuleId>,
    is_check_results: FxHashMap<NodeId, IsCheckResult>,
    declared_var_types: FxHashMap<NodeId, TypeId>,
}

impl ExpressionDataBuilder {
    /// Create a new builder with all fields set to empty defaults.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set expression types (NodeId -> TypeId mappings).
    pub fn types(mut self, types: FxHashMap<NodeId, TypeId>) -> Self {
        self.types = types;
        self
    }

    /// Set method resolutions for method calls.
    pub fn methods(mut self, methods: FxHashMap<NodeId, ResolvedMethod>) -> Self {
        self.methods = methods;
        self
    }

    /// Set monomorphization keys for generic function calls.
    pub fn generics(mut self, generics: FxHashMap<NodeId, MonomorphKey>) -> Self {
        self.generics = generics;
        self
    }

    /// Set monomorphization keys for generic class method calls.
    pub fn class_method_generics(
        mut self,
        class_method_generics: FxHashMap<NodeId, ClassMethodMonomorphKey>,
    ) -> Self {
        self.class_method_generics = class_method_generics;
        self
    }

    /// Set monomorphization keys for generic static method calls.
    pub fn static_method_generics(
        mut self,
        static_method_generics: FxHashMap<NodeId, StaticMethodMonomorphKey>,
    ) -> Self {
        self.static_method_generics = static_method_generics;
        self
    }

    /// Set per-module type mappings.
    pub fn module_types(
        mut self,
        module_types: FxHashMap<String, FxHashMap<NodeId, TypeId>>,
    ) -> Self {
        self.module_types = module_types;
        self
    }

    /// Set per-module method resolutions.
    pub fn module_methods(
        mut self,
        module_methods: FxHashMap<String, FxHashMap<NodeId, ResolvedMethod>>,
    ) -> Self {
        self.module_methods = module_methods;
        self
    }

    /// Set per-module is_check_results.
    pub fn module_is_check_results(
        mut self,
        module_is_check_results: FxHashMap<String, FxHashMap<NodeId, IsCheckResult>>,
    ) -> Self {
        self.module_is_check_results = module_is_check_results;
        self
    }

    /// Set per-module generic function monomorphization keys.
    pub fn module_generics(
        mut self,
        module_generics: FxHashMap<String, FxHashMap<NodeId, MonomorphKey>>,
    ) -> Self {
        self.module_generics = module_generics;
        self
    }

    /// Set per-module class method monomorphization keys.
    pub fn module_class_method_generics(
        mut self,
        module_class_method_generics: FxHashMap<String, FxHashMap<NodeId, ClassMethodMonomorphKey>>,
    ) -> Self {
        self.module_class_method_generics = module_class_method_generics;
        self
    }

    /// Set per-module static method monomorphization keys.
    pub fn module_static_method_generics(
        mut self,
        module_static_method_generics: FxHashMap<
            String,
            FxHashMap<NodeId, StaticMethodMonomorphKey>,
        >,
    ) -> Self {
        self.module_static_method_generics = module_static_method_generics;
        self
    }

    /// Set substituted return types for generic method calls.
    pub fn substituted_return_types(
        mut self,
        substituted_return_types: FxHashMap<NodeId, TypeId>,
    ) -> Self {
        self.substituted_return_types = substituted_return_types;
        self
    }

    /// Set lambda defaults for closure calls.
    pub fn lambda_defaults(mut self, lambda_defaults: FxHashMap<NodeId, LambdaDefaults>) -> Self {
        self.lambda_defaults = lambda_defaults;
        self
    }

    /// Set virtual module IDs for tests blocks.
    pub fn tests_virtual_modules(
        mut self,
        tests_virtual_modules: FxHashMap<Span, ModuleId>,
    ) -> Self {
        self.tests_virtual_modules = tests_virtual_modules;
        self
    }

    /// Set type check results for `is` expressions and type patterns.
    pub fn is_check_results(mut self, is_check_results: FxHashMap<NodeId, IsCheckResult>) -> Self {
        self.is_check_results = is_check_results;
        self
    }

    /// Set declared variable types for let statements with explicit type annotations.
    pub fn declared_var_types(mut self, declared_var_types: FxHashMap<NodeId, TypeId>) -> Self {
        self.declared_var_types = declared_var_types;
        self
    }

    /// Build the `ExpressionData` from this builder.
    pub fn build(self) -> ExpressionData {
        ExpressionData {
            types: self.types,
            methods: self.methods,
            generics: self.generics,
            class_method_generics: self.class_method_generics,
            static_method_generics: self.static_method_generics,
            module_types: self.module_types,
            module_methods: self.module_methods,
            module_is_check_results: self.module_is_check_results,
            module_generics: self.module_generics,
            module_class_method_generics: self.module_class_method_generics,
            module_static_method_generics: self.module_static_method_generics,
            substituted_return_types: self.substituted_return_types,
            lambda_defaults: self.lambda_defaults,
            tests_virtual_modules: self.tests_virtual_modules,
            is_check_results: self.is_check_results,
            declared_var_types: self.declared_var_types,
        }
    }
}

impl ExpressionData {
    /// Create a new empty ExpressionData
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns a builder for constructing `ExpressionData` with a fluent API.
    pub fn builder() -> ExpressionDataBuilder {
        ExpressionDataBuilder::new()
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

    /// Get the monomorphization key for a generic function call, using module-local
    /// NodeId space when `current_module` is provided.
    pub fn get_generic_in_module(
        &self,
        node: NodeId,
        current_module: Option<&str>,
    ) -> Option<&MonomorphKey> {
        if let Some(module) = current_module {
            // When compiling code from a specific module, ONLY look in that
            // module's NodeId space.  Falling back to the top-level map would
            // cause cross-file NodeId collisions (NodeIds restart at 0 per
            // parse unit, so a test file NodeId can alias a module NodeId).
            return self
                .module_generics
                .get(module)
                .and_then(|keys| keys.get(&node));
        }
        self.generics.get(&node)
    }

    /// Set the monomorphization key for a generic function call
    pub fn set_generic(&mut self, node: NodeId, key: MonomorphKey) {
        self.generics.insert(node, key);
    }

    /// Get all expression types (as TypeId handles)
    pub fn types(&self) -> &FxHashMap<NodeId, TypeId> {
        &self.types
    }

    /// Get mutable access to expression types
    pub fn types_mut(&mut self) -> &mut FxHashMap<NodeId, TypeId> {
        &mut self.types
    }

    /// Get all method resolutions
    pub fn methods(&self) -> &FxHashMap<NodeId, ResolvedMethod> {
        &self.methods
    }

    /// Get mutable access to method resolutions
    pub fn methods_mut(&mut self) -> &mut FxHashMap<NodeId, ResolvedMethod> {
        &mut self.methods
    }

    /// Get all monomorphization keys
    pub fn generics(&self) -> &FxHashMap<NodeId, MonomorphKey> {
        &self.generics
    }

    /// Get mutable access to monomorphization keys
    pub fn generics_mut(&mut self) -> &mut FxHashMap<NodeId, MonomorphKey> {
        &mut self.generics
    }

    /// Get the monomorphization key for a generic class method call
    pub fn get_class_method_generic(&self, node: NodeId) -> Option<&ClassMethodMonomorphKey> {
        self.class_method_generics.get(&node)
    }

    /// Get the monomorphization key for a generic class method call, using module-local
    /// NodeId space when `current_module` is provided.
    pub fn get_class_method_generic_in_module(
        &self,
        node: NodeId,
        current_module: Option<&str>,
    ) -> Option<&ClassMethodMonomorphKey> {
        if let Some(module) = current_module {
            // When compiling code from a specific module, ONLY look in that
            // module's NodeId space.  Falling back to the top-level map would
            // cause cross-file NodeId collisions (NodeIds restart at 0 per
            // parse unit, so a test file NodeId can alias a module NodeId).
            return self
                .module_class_method_generics
                .get(module)
                .and_then(|keys| keys.get(&node));
        }
        self.class_method_generics.get(&node)
    }

    /// Set the monomorphization key for a generic class method call
    pub fn set_class_method_generic(&mut self, node: NodeId, key: ClassMethodMonomorphKey) {
        self.class_method_generics.insert(node, key);
    }

    /// Get all class method monomorphization keys
    pub fn class_method_generics(&self) -> &FxHashMap<NodeId, ClassMethodMonomorphKey> {
        &self.class_method_generics
    }

    /// Get mutable access to class method monomorphization keys
    pub fn class_method_generics_mut(&mut self) -> &mut FxHashMap<NodeId, ClassMethodMonomorphKey> {
        &mut self.class_method_generics
    }

    /// Get the monomorphization key for a generic static method call
    pub fn get_static_method_generic(&self, node: NodeId) -> Option<&StaticMethodMonomorphKey> {
        self.static_method_generics.get(&node)
    }

    /// Get the monomorphization key for a generic static method call, using module-local
    /// NodeId space when `current_module` is provided.
    pub fn get_static_method_generic_in_module(
        &self,
        node: NodeId,
        current_module: Option<&str>,
    ) -> Option<&StaticMethodMonomorphKey> {
        if let Some(module) = current_module {
            // Same rationale as get_class_method_generic_in_module: avoid
            // cross-file NodeId collisions by never falling through to the
            // top-level map when we know which module we are compiling.
            return self
                .module_static_method_generics
                .get(module)
                .and_then(|keys| keys.get(&node));
        }
        self.static_method_generics.get(&node)
    }

    /// Set the monomorphization key for a generic static method call
    pub fn set_static_method_generic(&mut self, node: NodeId, key: StaticMethodMonomorphKey) {
        self.static_method_generics.insert(node, key);
    }

    /// Get all static method monomorphization keys
    pub fn static_method_generics(&self) -> &FxHashMap<NodeId, StaticMethodMonomorphKey> {
        &self.static_method_generics
    }

    /// Get mutable access to static method monomorphization keys
    pub fn static_method_generics_mut(
        &mut self,
    ) -> &mut FxHashMap<NodeId, StaticMethodMonomorphKey> {
        &mut self.static_method_generics
    }

    /// Get types for a specific module (as TypeId handles)
    pub fn module_types(&self, module: &str) -> Option<&FxHashMap<NodeId, TypeId>> {
        self.module_types.get(module)
    }

    /// Set types for a specific module
    pub fn set_module_types(&mut self, module: String, types: FxHashMap<NodeId, TypeId>) {
        self.module_types.insert(module, types);
    }

    /// Get all module type mappings
    pub fn all_module_types(&self) -> &FxHashMap<String, FxHashMap<NodeId, TypeId>> {
        &self.module_types
    }

    /// Get methods for a specific module
    pub fn module_methods(&self, module: &str) -> Option<&FxHashMap<NodeId, ResolvedMethod>> {
        self.module_methods.get(module)
    }

    /// Set methods for a specific module
    pub fn set_module_methods(
        &mut self,
        module: String,
        methods: FxHashMap<NodeId, ResolvedMethod>,
    ) {
        self.module_methods.insert(module, methods);
    }

    /// Get all module method mappings
    pub fn all_module_methods(&self) -> &FxHashMap<String, FxHashMap<NodeId, ResolvedMethod>> {
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
    pub fn substituted_return_types(&self) -> &FxHashMap<NodeId, TypeId> {
        &self.substituted_return_types
    }

    /// Get mutable access to substituted return types
    pub fn substituted_return_types_mut(&mut self) -> &mut FxHashMap<NodeId, TypeId> {
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
    pub fn lambda_defaults(&self) -> &FxHashMap<NodeId, LambdaDefaults> {
        &self.lambda_defaults
    }

    /// Get mutable access to lambda defaults
    pub fn lambda_defaults_mut(&mut self) -> &mut FxHashMap<NodeId, LambdaDefaults> {
        &mut self.lambda_defaults
    }

    /// Get the virtual module ID for a tests block by its span
    pub fn get_tests_virtual_module(&self, span: Span) -> Option<ModuleId> {
        self.tests_virtual_modules.get(&span).copied()
    }

    /// Set the virtual module ID for a tests block
    pub fn set_tests_virtual_module(&mut self, span: Span, module_id: ModuleId) {
        self.tests_virtual_modules.insert(span, module_id);
    }

    /// Get the IsCheckResult for a type check node (is expression or type pattern)
    pub fn get_is_check_result(&self, node: NodeId) -> Option<IsCheckResult> {
        self.is_check_results.get(&node).copied()
    }

    /// Get the IsCheckResult for a type check node, checking module-specific results first
    pub fn get_is_check_result_in_module(
        &self,
        node: NodeId,
        current_module: Option<&str>,
    ) -> Option<IsCheckResult> {
        if let Some(module) = current_module
            && let Some(module_results) = self.module_is_check_results.get(module)
            && let Some(result) = module_results.get(&node)
        {
            return Some(*result);
        }
        self.is_check_results.get(&node).copied()
    }

    /// Set the IsCheckResult for a type check node
    pub fn set_is_check_result(&mut self, node: NodeId, result: IsCheckResult) {
        self.is_check_results.insert(node, result);
    }

    /// Get all IsCheckResults
    pub fn is_check_results(&self) -> &FxHashMap<NodeId, IsCheckResult> {
        &self.is_check_results
    }

    /// Get mutable access to IsCheckResults
    pub fn is_check_results_mut(&mut self) -> &mut FxHashMap<NodeId, IsCheckResult> {
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
    pub fn declared_var_types(&self) -> &FxHashMap<NodeId, TypeId> {
        &self.declared_var_types
    }
}
