//! Vec-backed per-node metadata store.
//!
//! `NodeMap` replaces the 16 separate `FxHashMap<NodeId, T>` maps in
//! [`ExpressionData`](crate::expression_data::ExpressionData) with a single
//! `FxHashMap<ModuleId, Vec<NodeData>>`. Because `NodeId` embeds a `ModuleId`
//! and a sequential `local` counter, lookup is O(1): hash the module, index
//! the vec.
//!
//! **Migration status**: sema writes go through `NodeMap`; codegen still reads
//! from `ExpressionData` (built via [`NodeMap::into_expression_data`]).

use rustc_hash::FxHashMap;

use crate::analysis_cache::IsCheckResult;
use crate::expression_data::{
    CoercionKind, ItLambdaInfo, IterableKind, LambdaAnalysis, LambdaDefaults, OptionalChainInfo,
    StringConversion,
};
use crate::generic::{ClassMethodMonomorphKey, MonomorphKey, StaticMethodMonomorphKey};
use crate::resolution::ResolvedMethod;
use crate::type_arena::TypeId;
use vole_frontend::NodeId;
use vole_identity::ModuleId;

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
    // Typed getters — mirror ExpressionData's public API
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

    /// Convert this `NodeMap` into an [`ExpressionData`](crate::ExpressionData),
    /// consuming `self`.
    ///
    /// Used at the boundary between sema and codegen: sema writes to `NodeMap`,
    /// then this method materialises the flat `FxHashMap`-based layout that
    /// codegen currently expects.
    pub fn into_expression_data(self) -> crate::ExpressionData {
        use crate::ExpressionData;
        let mut ed = ExpressionData::new();
        for (module, nodes) in self.modules {
            for (local, data) in nodes.into_iter().enumerate() {
                let node = NodeId::new(module, local as u32);
                if let Some(ty) = data.ty {
                    ed.set_type_handle(node, ty);
                }
                if let Some(method) = data.method {
                    ed.set_method(node, *method);
                }
                if let Some(key) = data.generic {
                    ed.set_generic(node, *key);
                }
                if let Some(key) = data.class_method_generic {
                    ed.set_class_method_generic(node, *key);
                }
                if let Some(key) = data.static_method_generic {
                    ed.set_static_method_generic(node, *key);
                }
                if let Some(ty) = data.substituted_return_type {
                    ed.set_substituted_return_type(node, ty);
                }
                if let Some(defaults) = data.lambda_defaults {
                    ed.set_lambda_defaults(node, defaults);
                }
                if let Some(result) = data.is_check_result {
                    ed.set_is_check_result(node, result);
                }
                if let Some(ty) = data.declared_var_type {
                    ed.set_declared_var_type(node, ty);
                }
                if let Some(analysis) = data.lambda_analysis {
                    ed.set_lambda_analysis(node, *analysis);
                }
                if let Some(key) = data.intrinsic_key {
                    ed.intrinsic_keys.insert(node, *key);
                }
                if let Some(mapping) = data.resolved_call_args {
                    ed.set_resolved_call_args(node, *mapping);
                }
                if let Some(kind) = data.iterable_kind {
                    ed.set_iterable_kind(node, kind);
                }
                if let Some(kind) = data.coercion_kind {
                    ed.set_coercion_kind(node, kind);
                }
                if let Some(conv) = data.string_conversion {
                    ed.set_string_conversion(node, *conv);
                }
                if let Some(info) = data.optional_chain {
                    ed.lowered_optional_chains.insert(node, info);
                }
                if let Some(info) = data.it_lambda {
                    ed.synthetic_it_lambdas.insert(node, info);
                }
            }
        }
        ed
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
