//! Vec-backed per-node metadata store.
//!
//! `NodeMap` is the single source of truth for all per-node metadata produced
//! by semantic analysis. It maps `ModuleId -> Vec<NodeData>`, where each
//! `NodeId`'s embedded `ModuleId` selects the vec and its `local` field
//! indexes into it, giving O(1) lookup.
//!
//! Both sema writes and codegen reads go through `NodeMap`. Sub-analyzer
//! results are merged directly into the shared `NodeMap` on `AnalyzerContext`,
//! using `NodeMap::merge()` which moves each module's `Vec<NodeData>` in O(1).
//!
//! This module also defines the supporting enum/struct types that are stored
//! as fields of `NodeData`: `IterableKind`, `StringConversion`, `CoercionKind`,
//! `OptionalChainKind`, `OptionalChainInfo`, `LambdaAnalysis`, `LambdaDefaults`,
//! and `ItLambdaInfo`.

use rustc_hash::FxHashMap;

use crate::analysis_cache::IsCheckResult;
use crate::generic::{ClassMethodMonomorphKey, MonomorphKey, StaticMethodMonomorphKey};
use crate::resolution::ResolvedMethod;
use crate::type_arena::TypeId;
use vole_frontend::{Capture, LambdaPurity, NodeId, Symbol};
use vole_identity::{ModuleId, NameId, TypeDefId};

// ---------------------------------------------------------------------------
// Supporting types (previously in expression_data.rs)
// ---------------------------------------------------------------------------

/// Union storage strategy for array elements, annotated by sema.
///
/// When an array's element type is a union, codegen must choose between
/// inline storage (tag + payload in each TaggedValue slot) and heap-boxed
/// storage (pointer to a heap-allocated union buffer).
///
/// Inline is preferred when each variant maps to a unique runtime tag.
/// Heap is required when two variants would collide (e.g. `nil | i64`
/// both map to RuntimeTypeId::I64, making round-trip decode ambiguous).
///
/// Sema computes this once during type resolution; codegen reads it
/// to avoid re-detecting union storage decisions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnionStorageKind {
    /// Each variant has a unique runtime tag — store inline as (tag, payload).
    Inline,
    /// Tag collision — store as a heap-boxed union buffer pointer.
    Heap,
}

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

/// Method dispatch routing annotation, set by sema during method resolution.
///
/// Codegen reads this to route to the correct dispatch path without
/// re-detecting the receiver type via arena queries. This replaces
/// the module/builtin/array-push detection that previously used
/// arena queries in codegen.
///
/// Note: `RuntimeIterator` dispatch is NOT annotated here because the
/// Iterator<T> → RuntimeIterator<T> conversion happens in codegen only
/// (sema always sees Iterator<T> for builtin iterator return types).
/// Codegen detects RuntimeIterator dispatch from the compiled value's type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MethodDispatchKind {
    /// Module-scoped function call (e.g., `math.sqrt(16.0)`).
    /// The `ModuleId` identifies the module containing the function.
    Module(ModuleId),
    /// Built-in method on array/string/range (length, iter, to_upper, etc.)
    /// handled by `builtin_method()` in codegen.
    Builtin,
    /// `array.push(value)` — needs special codegen to compile the argument
    /// and call the array push runtime function.
    ArrayPush,
    /// Default: vtable dispatch, direct call, external call, or other
    /// standard method dispatch. Codegen proceeds through the normal
    /// resolution-driven paths. Codegen will still check for RuntimeIterator
    /// dispatch at the codegen level (since the Iterator<T> → RuntimeIterator<T>
    /// conversion is a codegen concern).
    Standard,
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
/// Stored in NodeMap keyed by the lambda expression's NodeId.
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

/// Classification of a `.@meta` access expression, annotated by sema.
///
/// Codegen reads this to determine whether the `TypeMeta` value can be
/// constructed at compile time (static — the underlying type is known) or
/// must be resolved at runtime via a vtable (dynamic — the value is typed
/// as an interface).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MetaAccessKind {
    /// The reflected type is statically known (e.g. `Point.@meta` or
    /// `val.@meta` where `val: Point`).
    Static { type_def_id: TypeDefId },
    /// The reflected type is only known at runtime (e.g. `val.@meta`
    /// where `val: SomeInterface`).
    Dynamic,
    /// The reflected type is a generic type parameter (e.g. `val.@meta`
    /// where `val: T` inside a generic class method). Set during initial
    /// sema analysis of generic class/struct method bodies.
    ///
    /// Codegen resolves this at monomorphization time by looking up the
    /// concrete type from `FunctionCtx.substitutions` and dispatching to
    /// `compile_static_meta` or `compile_dynamic_meta`.
    TypeParam { name_id: NameId },
}

// ---------------------------------------------------------------------------
// NodeData
// ---------------------------------------------------------------------------

/// Per-node metadata produced by semantic analysis.
///
/// Every field is `Option` so that `Default` yields an all-`None` value.
/// Large or rare types are boxed to keep the struct compact (target ~100-150 bytes).
#[derive(Debug, Clone, Default)]
pub struct NodeData {
    // -- Dense fields (populated for most expression nodes) -----------------
    /// Interned type of this expression.
    pub ty: Option<TypeId>,

    /// Resolved method information for method calls (large enum — boxed).
    pub method: Option<Box<ResolvedMethod>>,

    // -- Semi-dense (populated for generic calls) ---------------------------
    /// Monomorphization key for generic function calls (boxed — contains Vec).
    pub generic: Option<Box<MonomorphKey>>,

    /// Monomorphization key for generic class method calls (boxed — contains Vec).
    pub class_method_generic: Option<Box<ClassMethodMonomorphKey>>,

    /// Monomorphization key for generic static method calls (boxed — contains 2 Vecs).
    pub static_method_generic: Option<Box<StaticMethodMonomorphKey>>,

    /// Substituted return type for generic method calls.
    pub substituted_return_type: Option<TypeId>,

    // -- Sparse (specific constructs only) ----------------------------------
    /// Lambda parameter defaults for closure calls.
    pub lambda_defaults: Option<LambdaDefaults>,

    /// Compile-time type check result for `is` expressions and type patterns.
    pub is_check_result: Option<IsCheckResult>,

    /// Declared variable type for let statements with explicit annotations.
    pub declared_var_type: Option<TypeId>,

    /// Lambda analysis results (captures and side effects) (boxed — contains Vec).
    pub lambda_analysis: Option<Box<LambdaAnalysis>>,

    /// Resolved intrinsic key for compiler intrinsic calls (boxed — rare + heap String).
    pub intrinsic_key: Option<Box<String>>,

    /// Resolved call arg order for named-argument calls (boxed — rare + Vec).
    pub resolved_call_args: Option<Box<Vec<Option<usize>>>>,

    /// Iterable classification for for-loop iterables.
    pub iterable_kind: Option<IterableKind>,

    /// Interface coercion annotation for method call receivers.
    pub coercion_kind: Option<CoercionKind>,

    /// String conversion annotation for interpolation parts (boxed — can be large).
    pub string_conversion: Option<Box<StringConversion>>,

    // -- Compact lowered representations ------------------------------------
    /// Codegen-ready info for optional chain expressions (`?.`).
    pub optional_chain: Option<OptionalChainInfo>,

    /// Codegen-ready info for implicit `it` lambdas.
    pub it_lambda: Option<ItLambdaInfo>,

    /// Union storage kind for array elements (inline vs heap-boxed).
    pub union_storage_kind: Option<UnionStorageKind>,

    /// Method dispatch routing for method call expressions.
    pub method_dispatch_kind: Option<MethodDispatchKind>,

    /// Meta access classification for `.@meta` expressions.
    pub meta_access: Option<MetaAccessKind>,
}

// ---------------------------------------------------------------------------
// NodeMap
// ---------------------------------------------------------------------------

/// Vec-backed per-node metadata store, keyed by `NodeId`.
///
/// Internally maps `ModuleId -> Vec<NodeData>`. A `NodeId`'s `module` field
/// selects the vec, and its `local` field indexes into it.
#[derive(Debug, Clone, Default)]
pub struct NodeMap {
    modules: FxHashMap<ModuleId, Vec<NodeData>>,
}

impl NodeMap {
    /// Create a new empty `NodeMap`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Pre-size the vec for `module` to hold at least `capacity` entries.
    ///
    /// If the module already has a vec, it is extended (not shrunk).
    /// Called before analysis begins when the parser knows how many nodes
    /// a module will produce.
    pub fn ensure_module(&mut self, module: ModuleId, capacity: u32) {
        let vec = self.modules.entry(module).or_default();
        let cap = capacity as usize;
        if vec.len() < cap {
            vec.resize_with(cap, NodeData::default);
        }
    }

    /// Bulk-insert a pre-built `Vec<NodeData>` for a module.
    ///
    /// Used when merging sub-analyzer results into the top-level map.
    /// Panics (debug) if the module already has data — callers must not
    /// double-insert.
    pub fn insert_module(&mut self, module: ModuleId, data: Vec<NodeData>) {
        let prev = self.modules.insert(module, data);
        debug_assert!(
            prev.is_none(),
            "insert_module: module {module:?} already present"
        );
    }

    /// Remove and return the `Vec<NodeData>` for a module, or an empty Vec
    /// if the module is not present.
    ///
    /// Used to extract a single module's data from a sub-analyzer's NodeMap
    /// for O(1) insertion into the parent's merged NodeMap.
    pub fn take_module(&mut self, module: ModuleId) -> Vec<NodeData> {
        self.modules.remove(&module).unwrap_or_default()
    }

    /// Drain all `(ModuleId, Vec<NodeData>)` pairs, consuming the map.
    ///
    /// Used when merging a sub-analyzer that may contain data for multiple
    /// modules (e.g., a tests-block sub-analyzer that also imported modules).
    pub fn drain_modules(self) -> impl Iterator<Item = (ModuleId, Vec<NodeData>)> {
        self.modules.into_iter()
    }

    // -- low-level accessors -----------------------------------------------

    /// Get a shared reference to the `NodeData` for `id`, if present.
    pub fn get(&self, id: NodeId) -> Option<&NodeData> {
        self.modules
            .get(&id.module)
            .and_then(|v| v.get(id.local as usize))
    }

    /// Get a mutable reference to the `NodeData` for `id`, growing the
    /// module vec if necessary (inserts default entries up to `id.local`).
    pub fn get_mut_or_insert(&mut self, id: NodeId) -> &mut NodeData {
        let vec = self.modules.entry(id.module).or_default();
        let idx = id.local as usize;
        if idx >= vec.len() {
            vec.resize_with(idx + 1, NodeData::default);
        }
        &mut vec[idx]
    }

    // ======================================================================
    // Typed getters
    // ======================================================================

    // -- ty ----------------------------------------------------------------

    /// Get the type of an expression (returns interned `TypeId` handle).
    pub fn get_type(&self, node: NodeId) -> Option<TypeId> {
        self.get(node).and_then(|d| d.ty)
    }

    /// Set the type of an expression.
    pub fn set_type(&mut self, node: NodeId, ty: TypeId) {
        self.get_mut_or_insert(node).ty = Some(ty);
    }

    // -- method ------------------------------------------------------------

    /// Get the resolved method for a method call.
    pub fn get_method(&self, node: NodeId) -> Option<&ResolvedMethod> {
        self.get(node).and_then(|d| d.method.as_deref())
    }

    /// Set the resolved method for a method call.
    pub fn set_method(&mut self, node: NodeId, method: ResolvedMethod) {
        self.get_mut_or_insert(node).method = Some(Box::new(method));
    }

    // -- generic -----------------------------------------------------------

    /// Get the monomorphization key for a generic function call.
    pub fn get_generic(&self, node: NodeId) -> Option<&MonomorphKey> {
        self.get(node).and_then(|d| d.generic.as_deref())
    }

    /// Set the monomorphization key for a generic function call.
    pub fn set_generic(&mut self, node: NodeId, key: MonomorphKey) {
        self.get_mut_or_insert(node).generic = Some(Box::new(key));
    }

    // -- class_method_generic ----------------------------------------------

    /// Get the monomorphization key for a generic class method call.
    pub fn get_class_method_generic(&self, node: NodeId) -> Option<&ClassMethodMonomorphKey> {
        self.get(node)
            .and_then(|d| d.class_method_generic.as_deref())
    }

    /// Set the monomorphization key for a generic class method call.
    pub fn set_class_method_generic(&mut self, node: NodeId, key: ClassMethodMonomorphKey) {
        self.get_mut_or_insert(node).class_method_generic = Some(Box::new(key));
    }

    // -- static_method_generic ---------------------------------------------

    /// Get the monomorphization key for a generic static method call.
    pub fn get_static_method_generic(&self, node: NodeId) -> Option<&StaticMethodMonomorphKey> {
        self.get(node)
            .and_then(|d| d.static_method_generic.as_deref())
    }

    /// Set the monomorphization key for a generic static method call.
    pub fn set_static_method_generic(&mut self, node: NodeId, key: StaticMethodMonomorphKey) {
        self.get_mut_or_insert(node).static_method_generic = Some(Box::new(key));
    }

    // -- substituted_return_type -------------------------------------------

    /// Get the substituted return type for a generic method call.
    pub fn get_substituted_return_type(&self, node: NodeId) -> Option<TypeId> {
        self.get(node).and_then(|d| d.substituted_return_type)
    }

    /// Set the substituted return type for a generic method call.
    pub fn set_substituted_return_type(&mut self, node: NodeId, ty: TypeId) {
        self.get_mut_or_insert(node).substituted_return_type = Some(ty);
    }

    // -- lambda_defaults ---------------------------------------------------

    /// Get lambda defaults for a call site.
    pub fn get_lambda_defaults(&self, node: NodeId) -> Option<&LambdaDefaults> {
        self.get(node).and_then(|d| d.lambda_defaults.as_ref())
    }

    /// Set lambda defaults for a call site.
    pub fn set_lambda_defaults(&mut self, node: NodeId, defaults: LambdaDefaults) {
        self.get_mut_or_insert(node).lambda_defaults = Some(defaults);
    }

    // -- is_check_result ---------------------------------------------------

    /// Get the `IsCheckResult` for a type check node.
    pub fn get_is_check_result(&self, node: NodeId) -> Option<IsCheckResult> {
        self.get(node).and_then(|d| d.is_check_result)
    }

    /// Set the `IsCheckResult` for a type check node.
    pub fn set_is_check_result(&mut self, node: NodeId, result: IsCheckResult) {
        self.get_mut_or_insert(node).is_check_result = Some(result);
    }

    // -- declared_var_type -------------------------------------------------

    /// Get the declared type for a variable's init expression.
    pub fn get_declared_var_type(&self, node: NodeId) -> Option<TypeId> {
        self.get(node).and_then(|d| d.declared_var_type)
    }

    /// Set the declared type for a variable's init expression.
    pub fn set_declared_var_type(&mut self, node: NodeId, ty: TypeId) {
        self.get_mut_or_insert(node).declared_var_type = Some(ty);
    }

    // -- lambda_analysis ---------------------------------------------------

    /// Get lambda analysis results for a lambda expression.
    pub fn get_lambda_analysis(&self, node: NodeId) -> Option<&LambdaAnalysis> {
        self.get(node).and_then(|d| d.lambda_analysis.as_deref())
    }

    /// Set lambda analysis results for a lambda expression.
    pub fn set_lambda_analysis(&mut self, node: NodeId, analysis: LambdaAnalysis) {
        self.get_mut_or_insert(node).lambda_analysis = Some(Box::new(analysis));
    }

    // -- intrinsic_key -----------------------------------------------------

    /// Look up the intrinsic key for a call-site expression.
    pub fn get_intrinsic_key(&self, node: NodeId) -> Option<&str> {
        self.get(node)
            .and_then(|d| d.intrinsic_key.as_deref())
            .map(|s| s.as_str())
    }

    /// Set the intrinsic key for a call-site expression.
    pub fn set_intrinsic_key(&mut self, node: NodeId, key: String) {
        self.get_mut_or_insert(node).intrinsic_key = Some(Box::new(key));
    }

    // -- resolved_call_args ------------------------------------------------

    /// Get the resolved call arg mapping for a call with named arguments.
    pub fn get_resolved_call_args(&self, node: NodeId) -> Option<&[Option<usize>]> {
        self.get(node)
            .and_then(|d| d.resolved_call_args.as_deref())
            .map(|v| v.as_slice())
    }

    /// Set the resolved call arg mapping for a call with named arguments.
    pub fn set_resolved_call_args(&mut self, node: NodeId, mapping: Vec<Option<usize>>) {
        self.get_mut_or_insert(node).resolved_call_args = Some(Box::new(mapping));
    }

    // -- iterable_kind -----------------------------------------------------

    /// Get the iterable kind for a for-loop's iterable expression.
    pub fn get_iterable_kind(&self, node: NodeId) -> Option<IterableKind> {
        self.get(node).and_then(|d| d.iterable_kind)
    }

    /// Set the iterable kind for a for-loop's iterable expression.
    pub fn set_iterable_kind(&mut self, node: NodeId, kind: IterableKind) {
        self.get_mut_or_insert(node).iterable_kind = Some(kind);
    }

    // -- coercion_kind -----------------------------------------------------

    /// Get the coercion kind for a method call expression's receiver.
    pub fn get_coercion_kind(&self, node: NodeId) -> Option<CoercionKind> {
        self.get(node).and_then(|d| d.coercion_kind)
    }

    /// Set the coercion kind for a method call expression's receiver.
    pub fn set_coercion_kind(&mut self, node: NodeId, kind: CoercionKind) {
        self.get_mut_or_insert(node).coercion_kind = Some(kind);
    }

    // -- string_conversion -------------------------------------------------

    /// Get the string conversion annotation for an interpolation expression part.
    pub fn get_string_conversion(&self, node: NodeId) -> Option<&StringConversion> {
        self.get(node).and_then(|d| d.string_conversion.as_deref())
    }

    /// Set the string conversion annotation for an interpolation expression part.
    pub fn set_string_conversion(&mut self, node: NodeId, conv: StringConversion) {
        self.get_mut_or_insert(node).string_conversion = Some(Box::new(conv));
    }

    // -- optional_chain ----------------------------------------------------

    /// Get the optional chain info for an optional chain expression.
    pub fn get_optional_chain(&self, node: NodeId) -> Option<&OptionalChainInfo> {
        self.get(node).and_then(|d| d.optional_chain.as_ref())
    }

    /// Set the optional chain info for an optional chain expression.
    pub fn set_optional_chain(&mut self, node: NodeId, info: OptionalChainInfo) {
        self.get_mut_or_insert(node).optional_chain = Some(info);
    }

    // -- it_lambda ---------------------------------------------------------

    /// Get the compact info for an implicit `it`-expression lambda.
    pub fn get_it_lambda_info(&self, node: NodeId) -> Option<&ItLambdaInfo> {
        self.get(node).and_then(|d| d.it_lambda.as_ref())
    }

    /// Set the compact info for an implicit `it`-expression lambda.
    pub fn set_it_lambda_info(&mut self, node: NodeId, info: ItLambdaInfo) {
        self.get_mut_or_insert(node).it_lambda = Some(info);
    }

    // -- union_storage_kind ------------------------------------------------

    /// Get the union storage kind for an expression involving union array elements.
    pub fn get_union_storage_kind(&self, node: NodeId) -> Option<UnionStorageKind> {
        self.get(node).and_then(|d| d.union_storage_kind)
    }

    /// Set the union storage kind for an expression involving union array elements.
    pub fn set_union_storage_kind(&mut self, node: NodeId, kind: UnionStorageKind) {
        self.get_mut_or_insert(node).union_storage_kind = Some(kind);
    }

    // -- method_dispatch_kind ----------------------------------------------

    /// Get the method dispatch kind for a method call expression.
    pub fn get_method_dispatch_kind(&self, node: NodeId) -> Option<MethodDispatchKind> {
        self.get(node).and_then(|d| d.method_dispatch_kind)
    }

    /// Set the method dispatch kind for a method call expression.
    pub fn set_method_dispatch_kind(&mut self, node: NodeId, kind: MethodDispatchKind) {
        self.get_mut_or_insert(node).method_dispatch_kind = Some(kind);
    }

    // -- meta_access -------------------------------------------------------

    /// Get the meta access classification for a `.@meta` expression.
    pub fn get_meta_access(&self, node: NodeId) -> Option<MetaAccessKind> {
        self.get(node).and_then(|d| d.meta_access)
    }

    /// Set the meta access classification for a `.@meta` expression.
    pub fn set_meta_access(&mut self, node: NodeId, kind: MetaAccessKind) {
        self.get_mut_or_insert(node).meta_access = Some(kind);
    }

    // ======================================================================
    // Bulk operations
    // ======================================================================

    /// Merge all entries from `other` into `self`.
    ///
    /// For each module in `other`:
    /// - If `self` does not have that module, the vec is moved in directly.
    /// - If `self` already has the module, entries are merged element-wise
    ///   (non-None fields in `other` overwrite the corresponding fields in `self`).
    pub fn merge(&mut self, other: NodeMap) {
        for (module, other_vec) in other.modules {
            match self.modules.entry(module) {
                std::collections::hash_map::Entry::Vacant(e) => {
                    e.insert(other_vec);
                }
                std::collections::hash_map::Entry::Occupied(mut e) => {
                    let self_vec = e.get_mut();
                    if other_vec.len() > self_vec.len() {
                        self_vec.resize_with(other_vec.len(), NodeData::default);
                    }
                    for (i, other_data) in other_vec.into_iter().enumerate() {
                        merge_node_data(&mut self_vec[i], other_data);
                    }
                }
            }
        }
    }

    /// Merge cached module data directly into this `NodeMap`.
    ///
    /// Reads the per-node `FxHashMap` fields from a
    /// [`CachedModule`](crate::analysis_cache::CachedModule) and inserts them
    /// into the Vec-backed store.
    pub fn merge_cached(&mut self, cached: &crate::analysis_cache::CachedModule) {
        for (&node, &ty) in &cached.expr_types {
            self.set_type(node, ty);
        }
        for (&node, method) in &cached.method_resolutions {
            self.set_method(node, method.clone());
        }
        for (&node, key) in &cached.generic_calls {
            self.set_generic(node, key.clone());
        }
        for (&node, key) in &cached.class_method_generics {
            self.set_class_method_generic(node, key.clone());
        }
        for (&node, key) in &cached.static_method_generics {
            self.set_static_method_generic(node, key.clone());
        }
        for (&node, &result) in &cached.is_check_results {
            self.set_is_check_result(node, result);
        }
        for (&node, &ty) in &cached.declared_var_types {
            self.set_declared_var_type(node, ty);
        }
    }

    /// Extract the subset of per-node data needed by
    /// [`CachedModule`](crate::analysis_cache::CachedModule) as individual
    /// `FxHashMap`s.
    ///
    /// Returns `(types, methods, generics, class_method_generics,
    /// static_method_generics, is_check_results, declared_var_types)`.
    #[allow(clippy::type_complexity)]
    pub fn extract_cached_maps(
        &self,
    ) -> (
        FxHashMap<NodeId, TypeId>,
        FxHashMap<NodeId, ResolvedMethod>,
        FxHashMap<NodeId, MonomorphKey>,
        FxHashMap<NodeId, ClassMethodMonomorphKey>,
        FxHashMap<NodeId, StaticMethodMonomorphKey>,
        FxHashMap<NodeId, IsCheckResult>,
        FxHashMap<NodeId, TypeId>,
    ) {
        let mut types = FxHashMap::default();
        let mut methods = FxHashMap::default();
        let mut generics = FxHashMap::default();
        let mut class_method_generics = FxHashMap::default();
        let mut static_method_generics = FxHashMap::default();
        let mut is_check_results = FxHashMap::default();
        let mut declared_var_types = FxHashMap::default();

        for (&module, nodes) in &self.modules {
            for (local, data) in nodes.iter().enumerate() {
                let node = NodeId::new(module, local as u32);
                if let Some(ty) = data.ty {
                    types.insert(node, ty);
                }
                if let Some(ref method) = data.method {
                    methods.insert(node, (**method).clone());
                }
                if let Some(ref key) = data.generic {
                    generics.insert(node, (**key).clone());
                }
                if let Some(ref key) = data.class_method_generic {
                    class_method_generics.insert(node, (**key).clone());
                }
                if let Some(ref key) = data.static_method_generic {
                    static_method_generics.insert(node, (**key).clone());
                }
                if let Some(result) = data.is_check_result {
                    is_check_results.insert(node, result);
                }
                if let Some(ty) = data.declared_var_type {
                    declared_var_types.insert(node, ty);
                }
            }
        }

        (
            types,
            methods,
            generics,
            class_method_generics,
            static_method_generics,
            is_check_results,
            declared_var_types,
        )
    }
}

/// Merge non-None fields from `src` into `dst`.
fn merge_node_data(dst: &mut NodeData, src: NodeData) {
    if src.ty.is_some() {
        dst.ty = src.ty;
    }
    if src.method.is_some() {
        dst.method = src.method;
    }
    if src.generic.is_some() {
        dst.generic = src.generic;
    }
    if src.class_method_generic.is_some() {
        dst.class_method_generic = src.class_method_generic;
    }
    if src.static_method_generic.is_some() {
        dst.static_method_generic = src.static_method_generic;
    }
    if src.substituted_return_type.is_some() {
        dst.substituted_return_type = src.substituted_return_type;
    }
    if src.lambda_defaults.is_some() {
        dst.lambda_defaults = src.lambda_defaults;
    }
    if src.is_check_result.is_some() {
        dst.is_check_result = src.is_check_result;
    }
    if src.declared_var_type.is_some() {
        dst.declared_var_type = src.declared_var_type;
    }
    if src.lambda_analysis.is_some() {
        dst.lambda_analysis = src.lambda_analysis;
    }
    if src.intrinsic_key.is_some() {
        dst.intrinsic_key = src.intrinsic_key;
    }
    if src.resolved_call_args.is_some() {
        dst.resolved_call_args = src.resolved_call_args;
    }
    if src.iterable_kind.is_some() {
        dst.iterable_kind = src.iterable_kind;
    }
    if src.coercion_kind.is_some() {
        dst.coercion_kind = src.coercion_kind;
    }
    if src.string_conversion.is_some() {
        dst.string_conversion = src.string_conversion;
    }
    if src.optional_chain.is_some() {
        dst.optional_chain = src.optional_chain;
    }
    if src.it_lambda.is_some() {
        dst.it_lambda = src.it_lambda;
    }
    if src.union_storage_kind.is_some() {
        dst.union_storage_kind = src.union_storage_kind;
    }
    if src.method_dispatch_kind.is_some() {
        dst.method_dispatch_kind = src.method_dispatch_kind;
    }
    if src.meta_access.is_some() {
        dst.meta_access = src.meta_access;
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: create a `NodeId` with a given module index and local index.
    fn nid(module: u32, local: u32) -> NodeId {
        NodeId::new(ModuleId::new(module), local)
    }

    #[test]
    fn empty_map_returns_none() {
        let map = NodeMap::new();
        assert!(map.get(nid(0, 0)).is_none());
        assert!(map.get_type(nid(0, 0)).is_none());
    }

    #[test]
    fn set_and_get_type() {
        let mut map = NodeMap::new();
        let node = nid(1, 5);
        let ty = TypeId::I64;

        map.set_type(node, ty);
        assert_eq!(map.get_type(node), Some(ty));
    }

    #[test]
    fn ensure_module_pre_sizes() {
        let mut map = NodeMap::new();
        let module = ModuleId::new(2);
        map.ensure_module(module, 100);

        // All 100 slots should be accessible and default
        let node = nid(2, 99);
        assert!(map.get(node).is_some());
        assert!(map.get_type(node).is_none()); // default = None
    }

    #[test]
    fn get_mut_or_insert_grows_vec() {
        let mut map = NodeMap::new();
        let node = nid(3, 10);

        // Should auto-grow to fit local=10
        let data = map.get_mut_or_insert(node);
        assert!(data.ty.is_none());
        data.ty = Some(TypeId::BOOL);

        assert_eq!(map.get_type(node), Some(TypeId::BOOL));
    }

    #[test]
    fn insert_module_bulk() {
        let mut map = NodeMap::new();
        let module = ModuleId::new(4);
        let mut data = vec![NodeData::default(); 3];
        data[1].ty = Some(TypeId::STRING);

        map.insert_module(module, data);

        assert_eq!(map.get_type(nid(4, 1)), Some(TypeId::STRING));
        assert!(map.get_type(nid(4, 0)).is_none());
        assert!(map.get_type(nid(4, 2)).is_none());
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "already present")]
    fn insert_module_double_panics_in_debug() {
        let mut map = NodeMap::new();
        let module = ModuleId::new(5);
        map.insert_module(module, vec![NodeData::default()]);
        map.insert_module(module, vec![NodeData::default()]);
    }

    #[test]
    fn sparse_fields_round_trip() {
        let mut map = NodeMap::new();
        let node = nid(6, 0);

        // is_check_result
        map.set_is_check_result(node, IsCheckResult::AlwaysTrue);
        assert_eq!(
            map.get_is_check_result(node),
            Some(IsCheckResult::AlwaysTrue)
        );

        // iterable_kind
        map.set_iterable_kind(node, IterableKind::String);
        assert_eq!(map.get_iterable_kind(node), Some(IterableKind::String));

        // coercion_kind
        let ck = CoercionKind::IteratorWrap {
            elem_type: TypeId::I64,
        };
        map.set_coercion_kind(node, ck);
        assert_eq!(map.get_coercion_kind(node), Some(ck));

        // intrinsic_key
        map.set_intrinsic_key(node, "f64_sqrt".to_string());
        assert_eq!(map.get_intrinsic_key(node), Some("f64_sqrt"));

        // resolved_call_args
        map.set_resolved_call_args(node, vec![Some(0), None, Some(1)]);
        assert_eq!(
            map.get_resolved_call_args(node),
            Some([Some(0), None, Some(1)].as_slice())
        );
    }

    #[test]
    fn different_modules_are_independent() {
        let mut map = NodeMap::new();
        let a = nid(10, 0);
        let b = nid(11, 0);

        map.set_type(a, TypeId::I64);
        map.set_type(b, TypeId::BOOL);

        assert_eq!(map.get_type(a), Some(TypeId::I64));
        assert_eq!(map.get_type(b), Some(TypeId::BOOL));
    }

    #[test]
    fn take_module_returns_data_and_removes() {
        let mut map = NodeMap::new();
        let module = ModuleId::new(20);
        let mut data = vec![NodeData::default(); 2];
        data[0].ty = Some(TypeId::I64);
        map.insert_module(module, data);

        let taken = map.take_module(module);
        assert_eq!(taken.len(), 2);
        assert_eq!(taken[0].ty, Some(TypeId::I64));

        // Module is now gone
        assert!(map.get_type(nid(20, 0)).is_none());
    }

    #[test]
    fn take_module_missing_returns_empty() {
        let mut map = NodeMap::new();
        let taken = map.take_module(ModuleId::new(99));
        assert!(taken.is_empty());
    }

    #[test]
    fn drain_modules_yields_all() {
        let mut map = NodeMap::new();
        map.set_type(nid(30, 0), TypeId::I64);
        map.set_type(nid(31, 0), TypeId::BOOL);

        let drained: Vec<_> = map.drain_modules().collect();
        assert_eq!(drained.len(), 2);
    }

    #[test]
    fn node_data_size_is_reasonable() {
        let size = size_of::<NodeData>();
        // Target: ~100-200 bytes with strategic boxing. Currently 176 bytes.
        // If this assertion trips, audit the struct for un-boxed large fields.
        assert!(
            size <= 200,
            "NodeData is {size} bytes — consider boxing more fields"
        );
    }
}
