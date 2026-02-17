//! Node-level metadata for expressions.
//!
//! ExpressionData encapsulates all metadata that is keyed by NodeId,
//! including type information, method resolutions, and generic instantiations.

use rustc_hash::FxHashMap;

use crate::analysis_cache::IsCheckResult;
use crate::generic::{ClassMethodMonomorphKey, MonomorphKey, StaticMethodMonomorphKey};
use crate::resolution::ResolvedMethod;
use crate::type_arena::TypeId;
use vole_frontend::{Capture, LambdaPurity, NodeId, Span};
use vole_identity::ModuleId;

/// Analysis results for a lambda expression (captures and side effects).
/// Stored in ExpressionData keyed by the lambda expression's NodeId.
#[derive(Debug, Clone, Default)]
pub struct LambdaAnalysis {
    pub captures: Vec<Capture>,
    pub has_side_effects: bool,
}

impl LambdaAnalysis {
    /// Compute the purity level of this lambda based on its captures and side effects.
    ///
    /// Returns the most restrictive purity classification:
    /// - `HasSideEffects`: Calls print/println/assert or user functions
    /// - `MutatesCaptures`: Assigns to captured variables
    /// - `CapturesMutable`: Captures mutable variables (may observe external changes)
    /// - `CapturesImmutable`: Captures exist, but none are mutable
    /// - `Pure`: No captures, no side effects
    pub fn purity(&self) -> LambdaPurity {
        if self.has_side_effects {
            return LambdaPurity::HasSideEffects;
        }
        if self.captures.iter().any(|c| c.is_mutated) {
            return LambdaPurity::MutatesCaptures;
        }
        if self.captures.iter().any(|c| c.is_mutable) {
            return LambdaPurity::CapturesMutable;
        }
        if !self.captures.is_empty() {
            return LambdaPurity::CapturesImmutable;
        }
        LambdaPurity::Pure
    }
}

/// Information about a lambda's parameter defaults.
/// Used to support calling closures with default arguments.
#[derive(Debug, Clone)]
pub struct LambdaDefaults {
    /// Number of required parameters (those without defaults)
    pub required_params: usize,
    /// NodeId of the lambda expression (for accessing default expressions in AST)
    pub lambda_node_id: NodeId,
}

/// Per-module analysis data collected during multi-module compilation.
///
/// Each imported module gets its own set of NodeId-keyed maps because NodeIds
/// are file-local (they restart at 0 per parse unit). Grouping them into a
/// single struct replaces the 8 separate `FxHashMap<String, FxHashMap<NodeId, T>>`
/// fields that previously existed in both `AnalyzerContext` and `ExpressionData`.
#[derive(Debug, Clone, Default)]
pub struct ModuleAnalysisData {
    /// Expression types for this module's AST nodes.
    pub types: FxHashMap<NodeId, TypeId>,
    /// Resolved method information for method calls in this module.
    pub methods: FxHashMap<NodeId, ResolvedMethod>,
    /// Type check results for `is` expressions and type patterns.
    pub is_check_results: FxHashMap<NodeId, IsCheckResult>,
    /// Monomorphization keys for generic function calls.
    pub generic_calls: FxHashMap<NodeId, MonomorphKey>,
    /// Monomorphization keys for generic class method calls.
    pub class_method_calls: FxHashMap<NodeId, ClassMethodMonomorphKey>,
    /// Monomorphization keys for generic static method calls.
    pub static_method_calls: FxHashMap<NodeId, StaticMethodMonomorphKey>,
    /// Declared variable types for let statements with explicit type annotations.
    pub declared_var_types: FxHashMap<NodeId, TypeId>,
    /// Lambda analysis results (captures and side effects).
    pub lambda_analysis: FxHashMap<NodeId, LambdaAnalysis>,
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
    /// Per-module analysis data (for multi-module compilation).
    /// Each module's NodeIds are file-local, so they need separate maps.
    module_data: FxHashMap<String, ModuleAnalysisData>,
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
    /// Lambda analysis results (captures and side effects).
    /// Keyed by lambda expression NodeId.
    lambda_analysis: FxHashMap<NodeId, LambdaAnalysis>,
    /// Resolved intrinsic keys for compiler intrinsic calls.
    /// Maps call-site NodeId to the resolved intrinsic key (e.g., "f64_sqrt").
    /// Set by sema during generic external intrinsic resolution; consumed by
    /// the optimizer for constant folding of pure intrinsic calls.
    intrinsic_keys: FxHashMap<NodeId, String>,
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
    module_data: FxHashMap<String, ModuleAnalysisData>,
    substituted_return_types: FxHashMap<NodeId, TypeId>,
    lambda_defaults: FxHashMap<NodeId, LambdaDefaults>,
    tests_virtual_modules: FxHashMap<Span, ModuleId>,
    is_check_results: FxHashMap<NodeId, IsCheckResult>,
    declared_var_types: FxHashMap<NodeId, TypeId>,
    lambda_analysis: FxHashMap<NodeId, LambdaAnalysis>,
    intrinsic_keys: FxHashMap<NodeId, String>,
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

    /// Set per-module analysis data.
    pub fn module_data(mut self, module_data: FxHashMap<String, ModuleAnalysisData>) -> Self {
        self.module_data = module_data;
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

    /// Set lambda analysis results (captures and side effects).
    pub fn lambda_analysis(mut self, lambda_analysis: FxHashMap<NodeId, LambdaAnalysis>) -> Self {
        self.lambda_analysis = lambda_analysis;
        self
    }

    /// Set resolved intrinsic keys for compiler intrinsic calls.
    pub fn intrinsic_keys(mut self, intrinsic_keys: FxHashMap<NodeId, String>) -> Self {
        self.intrinsic_keys = intrinsic_keys;
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
            module_data: self.module_data,
            substituted_return_types: self.substituted_return_types,
            lambda_defaults: self.lambda_defaults,
            tests_virtual_modules: self.tests_virtual_modules,
            is_check_results: self.is_check_results,
            declared_var_types: self.declared_var_types,
            lambda_analysis: self.lambda_analysis,
            intrinsic_keys: self.intrinsic_keys,
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
            if let Some(data) = self.module_data.get(module) {
                let node_ids: Vec<_> = data.methods.keys().collect();
                tracing::trace!(
                    count = data.methods.len(),
                    ?node_ids,
                    "Found module methods"
                );
                if let Some(method) = data.methods.get(&node) {
                    tracing::trace!(?method, "Found method resolution in module");
                    return Some(method);
                }
                tracing::trace!(?node, "Method not found in module methods");
            } else {
                tracing::trace!("Module not found in module_data");
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
                .module_data
                .get(module)
                .and_then(|data| data.generic_calls.get(&node));
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
                .module_data
                .get(module)
                .and_then(|data| data.class_method_calls.get(&node));
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
                .module_data
                .get(module)
                .and_then(|data| data.static_method_calls.get(&node));
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
        self.module_data.get(module).map(|d| &d.types)
    }

    /// Get the per-module analysis data map.
    pub fn module_data(&self) -> &FxHashMap<String, ModuleAnalysisData> {
        &self.module_data
    }

    /// Get mutable per-module analysis data, inserting a default entry if absent.
    pub fn module_data_entry(&mut self, module: String) -> &mut ModuleAnalysisData {
        self.module_data.entry(module).or_default()
    }

    /// Get methods for a specific module
    pub fn module_methods(&self, module: &str) -> Option<&FxHashMap<NodeId, ResolvedMethod>> {
        self.module_data.get(module).map(|d| &d.methods)
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
            && let Some(data) = self.module_data.get(module)
            && let Some(result) = data.is_check_results.get(&node)
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

    /// Get the declared type for a variable's init expression from a specific module's data.
    /// Only checks the module-specific map (does NOT fall through to main program's map).
    pub fn get_module_declared_var_type(
        &self,
        module_path: &str,
        init_node: NodeId,
    ) -> Option<TypeId> {
        self.module_data
            .get(module_path)
            .and_then(|data| data.declared_var_types.get(&init_node).copied())
    }

    /// Set the declared type for a variable's init expression.
    pub fn set_declared_var_type(&mut self, init_node: NodeId, type_id: TypeId) {
        self.declared_var_types.insert(init_node, type_id);
    }

    /// Get all declared variable types
    pub fn declared_var_types(&self) -> &FxHashMap<NodeId, TypeId> {
        &self.declared_var_types
    }

    /// Get lambda analysis results for a lambda expression
    pub fn get_lambda_analysis(&self, node: NodeId) -> Option<&LambdaAnalysis> {
        self.lambda_analysis.get(&node)
    }

    /// Get lambda analysis results, checking module-specific results first
    pub fn get_lambda_analysis_in_module(
        &self,
        node: NodeId,
        current_module: Option<&str>,
    ) -> Option<&LambdaAnalysis> {
        if let Some(module) = current_module
            && let Some(data) = self.module_data.get(module)
            && let Some(result) = data.lambda_analysis.get(&node)
        {
            return Some(result);
        }
        self.lambda_analysis.get(&node)
    }

    /// Set lambda analysis results for a lambda expression
    pub fn set_lambda_analysis(&mut self, node: NodeId, analysis: LambdaAnalysis) {
        self.lambda_analysis.insert(node, analysis);
    }

    /// Get all lambda analysis results
    pub fn lambda_analysis(&self) -> &FxHashMap<NodeId, LambdaAnalysis> {
        &self.lambda_analysis
    }

    /// Look up the intrinsic key for a call-site expression.
    ///
    /// Returns the concrete intrinsic key (e.g., `"f64_sqrt"`) if this
    /// call site was resolved as a compiler intrinsic.
    pub fn get_intrinsic_key(&self, node: NodeId) -> Option<&str> {
        self.intrinsic_keys.get(&node).map(|s| s.as_str())
    }
}
