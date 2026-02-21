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
use vole_frontend::{Capture, LambdaPurity, NodeId, Symbol};

/// Classification of a for-loop's iterable, annotated by sema.
///
/// Codegen uses this to dispatch to the correct loop compilation strategy
/// without re-detecting types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IterableKind {
    /// `0..10` or `0..=10` — range iteration (i64 loop var)
    Range,
    /// `[1, 2, 3]` — dynamic array iteration
    Array { elem_type: TypeId },
    /// `"hello"` — string character iteration (yields string)
    String,
    /// Direct `Iterator<T>` interface value (e.g. from a function returning Iterator<T>)
    IteratorInterface { elem_type: TypeId },
    /// Class/struct implementing `Iterator<T>` via extend
    CustomIterator { elem_type: TypeId },
    /// Class/struct implementing `Iterable<T>` — codegen calls `.iter()` first
    CustomIterable { elem_type: TypeId },
}

/// String conversion annotation for interpolation parts, annotated by sema.
///
/// Codegen reads this to apply the correct conversion without type inspection.
/// For union/optional types, per-variant conversion info is carried so codegen
/// can generate branching code without re-detecting types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StringConversion {
    /// Already a string — no conversion needed.
    Identity,
    /// i64 (or smaller integer widths that sext to i64) → string
    I64ToString,
    /// i128 → string
    I128ToString,
    /// f32 → string
    F32ToString,
    /// f64 → string
    F64ToString,
    /// f128 → string (passed as i128 bits)
    F128ToString,
    /// bool → string
    BoolToString,
    /// nil → string (always "nil")
    NilToString,
    /// Array → string
    ArrayToString,
    /// Optional (union with nil) → branches on tag, converts inner value.
    /// `nil_index` is the tag index for nil in the union variants.
    /// `variants` is the full variant type list for codegen layout.
    /// `inner_conversion` is the conversion for the non-nil variant.
    OptionalToString {
        nil_index: usize,
        variants: Vec<TypeId>,
        inner_conversion: Box<StringConversion>,
    },
    /// General union → branches on tag, converts each variant.
    /// Each entry is `(variant_type_id, conversion)`.
    UnionToString {
        variants: Vec<(TypeId, StringConversion)>,
    },
}

/// Interface coercion annotation, stored by sema at sites where a value
/// needs boxing or wrapping to satisfy an interface type.
///
/// Codegen reads this to apply the correct coercion without re-detecting types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CoercionKind {
    /// Method call receiver is a custom `Iterator<T>` implementor.
    /// Codegen should box to `Iterator<T>` interface, then wrap via
    /// `InterfaceIter` into a `RuntimeIterator` before dispatching the method.
    IteratorWrap { elem_type: TypeId },
}

/// What kind of optional chain this is (field access or method call).
#[derive(Debug, Clone)]
pub enum OptionalChainKind {
    /// `obj?.field` — field access on the unwrapped inner value.
    FieldAccess { field: Symbol },
    /// `obj?.method(args)` — method call on the unwrapped inner value.
    /// Method resolution and related metadata (coercion_kinds, class_method_generics,
    /// substituted_return_types) are stored on the OptionalMethodCallExpr's own NodeId.
    MethodCall,
}

/// Compact codegen-ready info for optional chain expressions (`?.`).
///
/// Replaces the previous approach of building a full synthetic MatchExpr AST
/// with 6+ fresh NodeIds. Instead, stores just the essential type info needed
/// for codegen to emit the nil-check branch directly.
#[derive(Debug, Clone)]
pub struct OptionalChainInfo {
    /// Type of the scrutinee expression (e.g. `T | nil`).
    pub object_type: TypeId,
    /// Non-nil inner type after unwrapping the optional (e.g. `T`).
    pub inner_type: TypeId,
    /// Type of the body expression (field access result or method return type),
    /// before wrapping as optional.
    pub result_type: TypeId,
    /// Whether this is a field access or method call.
    pub kind: OptionalChainKind,
}

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

/// Compact codegen-ready info for implicit `it` lambdas.
///
/// When sema synthesizes `it => expr` for a call argument matching a function-type
/// parameter, it analyzes the full synthetic lambda for type checking but stores
/// only this compact representation. Codegen reconstructs a lambda from the original
/// expression AST node with `it` bound as the single parameter.
#[derive(Debug, Clone, Copy)]
pub struct ItLambdaInfo {
    /// Type of the `it` parameter.
    pub param_type: TypeId,
    /// Return type of the lambda.
    pub return_type: TypeId,
    /// The original expression's NodeId (used as the lambda body).
    pub body_node: NodeId,
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
    /// Type check results for `is` expressions and type patterns.
    pub(crate) is_check_results: FxHashMap<NodeId, IsCheckResult>,
    /// Declared variable types for let statements with explicit type annotations.
    pub(crate) declared_var_types: FxHashMap<NodeId, TypeId>,
    /// Lambda analysis results (captures and side effects).
    pub(crate) lambda_analysis: FxHashMap<NodeId, LambdaAnalysis>,
    /// Resolved intrinsic keys for compiler intrinsic calls.
    pub(crate) intrinsic_keys: FxHashMap<NodeId, String>,
    /// Resolved call arg order for calls with named arguments.
    ///
    /// Maps call expression NodeId to a vec of length `total_params`.
    /// `resolved_call_args[i]` = Some(j) means call.args[j] fills param slot i.
    /// `resolved_call_args[i]` = None means the slot uses its default value.
    ///
    /// Only present when named arguments were used (or arg reordering was needed).
    /// Absent for purely positional calls (codegen uses call.args directly).
    pub(crate) resolved_call_args: FxHashMap<NodeId, Vec<Option<usize>>>,
    /// Compact info for implicit `it` lambdas synthesized by sema.
    ///
    /// When sema synthesizes an implicit `it => expr` lambda for a call argument
    /// that matches a function-type parameter, the compact `ItLambdaInfo` is stored
    /// here keyed by the original expression's NodeId. Codegen uses this to
    /// reconstruct and compile the lambda from the original expression AST.
    pub(crate) synthetic_it_lambdas: FxHashMap<NodeId, ItLambdaInfo>,
    /// Iterable classification for for-loops.
    ///
    /// Keyed by the iterable expression's NodeId. Tells codegen which loop
    /// compilation strategy to use without re-detecting the iterable type.
    pub(crate) iterable_kinds: FxHashMap<NodeId, IterableKind>,
    /// Interface coercion annotations for method call receivers.
    ///
    /// Keyed by the method call expression's NodeId. Tells codegen to apply
    /// a coercion (e.g., boxing a custom Iterator<T> as RuntimeIterator)
    /// before dispatching the method, without re-detecting types.
    pub(crate) coercion_kinds: FxHashMap<NodeId, CoercionKind>,
    /// Lowered optional chains: compact codegen-ready info for `?.` expressions.
    ///
    /// When sema encounters `obj?.field` or `obj?.method(args)`, it stores an
    /// `OptionalChainInfo` here with the essential type info. Codegen uses this
    /// to emit a nil-check branch directly, without a synthetic MatchExpr AST.
    pub(crate) lowered_optional_chains: FxHashMap<NodeId, OptionalChainInfo>,
    /// String conversion annotations for interpolation expression parts.
    ///
    /// Keyed by the interpolation expression's NodeId. Tells codegen which
    /// runtime conversion function to call without type-based dispatch.
    pub(crate) string_conversions: FxHashMap<NodeId, StringConversion>,
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
        self.types.reserve(other.types.len());
        self.types.extend(other.types);
        self.methods.reserve(other.methods.len());
        self.methods.extend(other.methods);
        self.generics.reserve(other.generics.len());
        self.generics.extend(other.generics);
        self.class_method_generics
            .reserve(other.class_method_generics.len());
        self.class_method_generics
            .extend(other.class_method_generics);
        self.static_method_generics
            .reserve(other.static_method_generics.len());
        self.static_method_generics
            .extend(other.static_method_generics);
        self.substituted_return_types
            .reserve(other.substituted_return_types.len());
        self.substituted_return_types
            .extend(other.substituted_return_types);
        self.lambda_defaults.reserve(other.lambda_defaults.len());
        self.lambda_defaults.extend(other.lambda_defaults);
        self.is_check_results.reserve(other.is_check_results.len());
        self.is_check_results.extend(other.is_check_results);
        self.declared_var_types
            .reserve(other.declared_var_types.len());
        self.declared_var_types.extend(other.declared_var_types);
        self.lambda_analysis.reserve(other.lambda_analysis.len());
        self.lambda_analysis.extend(other.lambda_analysis);
        self.intrinsic_keys.reserve(other.intrinsic_keys.len());
        self.intrinsic_keys.extend(other.intrinsic_keys);
        self.resolved_call_args
            .reserve(other.resolved_call_args.len());
        self.resolved_call_args.extend(other.resolved_call_args);
        self.synthetic_it_lambdas
            .reserve(other.synthetic_it_lambdas.len());
        self.synthetic_it_lambdas.extend(other.synthetic_it_lambdas);
        self.iterable_kinds.reserve(other.iterable_kinds.len());
        self.iterable_kinds.extend(other.iterable_kinds);
        self.coercion_kinds.reserve(other.coercion_kinds.len());
        self.coercion_kinds.extend(other.coercion_kinds);
        self.lowered_optional_chains
            .reserve(other.lowered_optional_chains.len());
        self.lowered_optional_chains
            .extend(other.lowered_optional_chains);
        self.string_conversions
            .reserve(other.string_conversions.len());
        self.string_conversions.extend(other.string_conversions);
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

    /// Get the resolved call arg mapping for a call with named arguments.
    ///
    /// Returns a slice where `slice[i]` = Some(j) means call.args[j] fills param slot i,
    /// and None means the slot uses its default value.
    pub fn get_resolved_call_args(&self, node: NodeId) -> Option<&Vec<Option<usize>>> {
        self.resolved_call_args.get(&node)
    }

    /// Set the resolved call arg mapping for a call with named arguments.
    pub fn set_resolved_call_args(&mut self, node: NodeId, mapping: Vec<Option<usize>>) {
        self.resolved_call_args.insert(node, mapping);
    }

    /// Get the compact info for an implicit `it`-expression, if one was synthesized.
    pub fn get_it_lambda_info(&self, node: NodeId) -> Option<&ItLambdaInfo> {
        self.synthetic_it_lambdas.get(&node)
    }

    /// Get the iterable kind for a for-loop's iterable expression.
    pub fn get_iterable_kind(&self, node: NodeId) -> Option<IterableKind> {
        self.iterable_kinds.get(&node).copied()
    }

    /// Set the iterable kind for a for-loop's iterable expression.
    pub fn set_iterable_kind(&mut self, node: NodeId, kind: IterableKind) {
        self.iterable_kinds.insert(node, kind);
    }

    /// Get the coercion kind for a method call expression's receiver.
    pub fn get_coercion_kind(&self, node: NodeId) -> Option<CoercionKind> {
        self.coercion_kinds.get(&node).copied()
    }

    /// Set the coercion kind for a method call expression's receiver.
    pub fn set_coercion_kind(&mut self, node: NodeId, kind: CoercionKind) {
        self.coercion_kinds.insert(node, kind);
    }

    /// Get the optional chain info for an optional chain expression.
    pub fn get_optional_chain(&self, node: NodeId) -> Option<&OptionalChainInfo> {
        self.lowered_optional_chains.get(&node)
    }

    /// Get the string conversion annotation for an interpolation expression part.
    pub fn get_string_conversion(&self, node: NodeId) -> Option<&StringConversion> {
        self.string_conversions.get(&node)
    }

    /// Set the string conversion annotation for an interpolation expression part.
    pub fn set_string_conversion(&mut self, node: NodeId, conv: StringConversion) {
        self.string_conversions.insert(node, conv);
    }
}
