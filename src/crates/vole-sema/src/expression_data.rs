//! Node-level metadata for expressions.
//!
//! ExpressionData encapsulates all metadata that is keyed by NodeId,
//! including type information, method resolutions, and generic instantiations.
//!
//! Because NodeId is now globally unique (it embeds a ModuleId), all maps
//! are flat FxHashMap<NodeId, T> — no per-module namespacing is required.

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

/// Encapsulates all NodeId-keyed metadata from semantic analysis.
///
/// Because NodeId is globally unique (it embeds a ModuleId), all maps are
/// flat FxHashMap<NodeId, T>. No per-module namespacing is required.
#[derive(Debug, Clone, Default)]
pub struct ExpressionData {
    /// Type of each expression node (stored as interned TypeId handles)
    pub(crate) types: FxHashMap<NodeId, TypeId>,
    /// Resolved method information for method calls
    pub(crate) methods: FxHashMap<NodeId, ResolvedMethod>,
    /// Monomorphization key for generic function calls
    pub(crate) generics: FxHashMap<NodeId, MonomorphKey>,
    /// Monomorphization key for generic class method calls
    pub(crate) class_method_generics: FxHashMap<NodeId, ClassMethodMonomorphKey>,
    /// Monomorphization key for generic static method calls
    pub(crate) static_method_generics: FxHashMap<NodeId, StaticMethodMonomorphKey>,
    /// Substituted return types for generic method calls.
    pub(crate) substituted_return_types: FxHashMap<NodeId, TypeId>,
    /// Lambda defaults for closure calls.
    pub(crate) lambda_defaults: FxHashMap<NodeId, LambdaDefaults>,
    /// Virtual module IDs for tests blocks. Maps tests block span to its virtual ModuleId.
    pub(crate) tests_virtual_modules: FxHashMap<Span, ModuleId>,
    /// Type check results for `is` expressions and type patterns.
    pub(crate) is_check_results: FxHashMap<NodeId, IsCheckResult>,
    /// Declared variable types for let statements with explicit type annotations.
    pub(crate) declared_var_types: FxHashMap<NodeId, TypeId>,
    /// Lambda analysis results (captures and side effects).
    pub(crate) lambda_analysis: FxHashMap<NodeId, LambdaAnalysis>,
    /// Resolved intrinsic keys for compiler intrinsic calls.
    pub(crate) intrinsic_keys: FxHashMap<NodeId, String>,
}

impl ExpressionData {
    /// Create a new empty ExpressionData
    pub fn new() -> Self {
        Self::default()
    }

    /// Merge all entries from `other` into this ExpressionData.
    ///
    /// Used by `store_sub_analyzer_results` to fold module analysis results
    /// into the top-level flat maps. Because NodeIds are globally unique
    /// (they embed a ModuleId), there are no collisions.
    pub fn merge(&mut self, other: ExpressionData) {
        self.types.extend(other.types);
        self.methods.extend(other.methods);
        self.generics.extend(other.generics);
        self.class_method_generics
            .extend(other.class_method_generics);
        self.static_method_generics
            .extend(other.static_method_generics);
        self.substituted_return_types
            .extend(other.substituted_return_types);
        self.lambda_defaults.extend(other.lambda_defaults);
        self.tests_virtual_modules
            .extend(other.tests_virtual_modules);
        self.is_check_results.extend(other.is_check_results);
        self.declared_var_types.extend(other.declared_var_types);
        self.lambda_analysis.extend(other.lambda_analysis);
        self.intrinsic_keys.extend(other.intrinsic_keys);
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

    /// Get the substituted return type for a method call.
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

    /// Get lambda analysis results for a lambda expression
    pub fn get_lambda_analysis(&self, node: NodeId) -> Option<&LambdaAnalysis> {
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
    pub fn get_intrinsic_key(&self, node: NodeId) -> Option<&str> {
        self.intrinsic_keys.get(&node).map(|s| s.as_str())
    }
}
