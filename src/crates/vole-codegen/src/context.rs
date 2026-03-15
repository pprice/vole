// src/codegen/context.rs
//
// Unified codegen context - bundles all state needed during code generation.
// Methods are implemented across multiple files using split impl blocks.

use std::cell::RefCell;
use std::mem::size_of;

use cranelift::prelude::{
    Block, FunctionBuilder, Imm64, InstBuilder, MemFlags, Type, Value, Variable, types,
};
use cranelift_codegen::ir::{AbiParam, InstructionData, Opcode};
use cranelift_module::{FuncId, Linkage, Module};
use rustc_hash::FxHashMap;

use crate::callable_registry::CallableBackendPreference;
use crate::errors::{CodegenError, CodegenResult};
use crate::union_layout;
use crate::{FunctionKey, RuntimeKey};
use vole_identity::Symbol;
use vole_identity::{
    FieldId, FunctionId, MethodId, ModuleId, NameId, TypeId, UnionStorageKind, VirTypeId,
};

use super::lambda::CaptureBinding;
use super::rc_cleanup::RcScopeStack;
use super::rc_state::RcState;
use super::types::{
    CodegenCtx, CompileEnv, CompiledValue, MonomorphIndexEntry, PendingMonomorph, TypeMetadataMap,
};

/// Codegen-local external/native method binding payload.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ExternalMethodRef {
    pub module_path: NameId,
    pub native_name: NameId,
}

macro_rules! impl_from_external_ref {
    ($source:ty) => {
        impl From<$source> for ExternalMethodRef {
            fn from(value: $source) -> Self {
                Self {
                    module_path: value.module_path,
                    native_name: value.native_name,
                }
            }
        }
    };
}

impl_from_external_ref!(crate::analyzed::ExternalMethodInfoRef);
impl_from_external_ref!(vole_vir::expr::VirExternalMethodInfo);
impl_from_external_ref!(&vole_vir::expr::VirExternalMethodInfo);
impl_from_external_ref!(vole_vir::VirExternalFuncInfo);

/// Control flow context for loops (break/continue targets)
pub(crate) struct ControlFlow {
    /// Stack of loop exit blocks for break statements
    loop_exits: Vec<Block>,
    /// Stack of loop continue blocks for continue statements
    loop_continues: Vec<Block>,
    /// RC scope depth at loop entry, for break/continue cleanup
    loop_rc_depths: Vec<usize>,
}

impl ControlFlow {
    pub fn new() -> Self {
        Self {
            loop_exits: Vec::new(),
            loop_continues: Vec::new(),
            loop_rc_depths: Vec::new(),
        }
    }

    pub fn push_loop(&mut self, exit: Block, cont: Block, rc_scope_depth: usize) {
        self.loop_exits.push(exit);
        self.loop_continues.push(cont);
        self.loop_rc_depths.push(rc_scope_depth);
    }

    pub fn pop_loop(&mut self) {
        self.loop_exits.pop();
        self.loop_continues.pop();
        self.loop_rc_depths.pop();
    }

    pub fn loop_exit(&self) -> Option<Block> {
        self.loop_exits.last().copied()
    }

    pub fn loop_continue(&self) -> Option<Block> {
        self.loop_continues.last().copied()
    }

    /// Get the RC scope depth at the current loop entry (for break/continue cleanup).
    pub fn loop_rc_depth(&self) -> Option<usize> {
        self.loop_rc_depths.last().copied()
    }

    /// Returns true if currently inside a loop body.
    pub fn in_loop(&self) -> bool {
        !self.loop_exits.is_empty()
    }
}

impl Default for ControlFlow {
    fn default() -> Self {
        Self::new()
    }
}

/// Capture context for closures
pub(crate) struct Captures<'a> {
    pub bindings: &'a FxHashMap<Symbol, CaptureBinding>,
    pub closure_var: Variable,
}

// Re-export ModuleExportBinding from types module
pub use crate::types::ModuleExportBinding;

/// Unified codegen context - all state needed for code generation.
///
/// Lifetimes:
/// - 'a: lifetime of borrowed state (builder, codegen_ctx, env)
/// - 'b: lifetime of FunctionBuilder's internal data
/// - 'ctx: lifetime of context references (can outlive 'a for lambdas)
///
/// Methods are split across multiple files:
/// - expr.rs: expr()
/// - stmt.rs: stmt(), block()
/// - lambda.rs: lambda()
/// - calls.rs: call(), println(), assert()
/// - ops.rs: binary(), compound_assign()
/// - structs.rs: struct_literal(), field_access(), method_call()
/// - rc_ops.rs: RC lifecycle (inc/dec, scopes, cleanup, state queries)
/// - type_ops.rs: type resolution, substitution, Cranelift mapping, union storage policy
/// - intrinsic_compiler.rs: saturating/checked arithmetic, intrinsic dispatch, inline emission
/// - coercion_ops.rs: type coercion (union/interface/unknown boxing, call arg/return coercion)
/// - value_builders.rs: value constructors, control flow helpers, stack allocation, struct returns
pub(crate) struct Cg<'a, 'b, 'ctx> {
    pub builder: &'a mut FunctionBuilder<'b>,
    /// Variable bindings - owned, fresh per function
    pub vars: FxHashMap<Symbol, (Variable, VirTypeId)>,
    pub cf: ControlFlow,
    pub captures: Option<Captures<'a>>,
    /// For recursive lambdas: the binding name that captures itself
    pub self_capture: Option<Symbol>,
    /// Cache for field access: (instance_ptr, slot) -> field_value.
    ///
    /// Invalidated in two situations:
    /// 1. **SSA dominance** — `switch_to_block()` clears the cache because
    ///    `Value`s from a sibling block do not dominate the new block.
    /// 2. **Mutation** — call-emission helpers (`call_runtime`, `call_runtime_void`,
    ///    `emit_call`, `emit_call_indirect`) clear the cache because the callee
    ///    may mutate instance fields, making cached loads stale.
    pub field_cache: FxHashMap<(Value, u32), Value>,
    /// Return type of the current function
    pub return_type: Option<VirTypeId>,
    /// Pre-computed return ABI convention for the current function.
    ///
    /// Determined from `return_type` during context construction.  Read by
    /// return/raise codegen instead of re-querying type width/fallibility.
    pub return_abi: vole_vir::func::ReturnAbi,
    /// Module being compiled (None for main program)
    pub current_module: Option<ModuleId>,
    /// Type parameter substitutions for monomorphized generics (VirTypeId-native).
    pub substitutions: Option<&'a FxHashMap<NameId, VirTypeId>>,
    /// Backend selection policy for dual runtime/intrinsic callables.
    pub(crate) callable_backend_preference: CallableBackendPreference,
    /// Lazily-computed sema TypeId substitutions derived from VirTypeId substitutions.
    ///
    /// Populated on first access via [`sema_substitutions()`].  Callers that still
    /// work at the TypeId level (e.g. `try_substitute_type`, monomorph key rewriting)
    /// use this to avoid converting per-lookup.
    pub(crate) sema_substitutions: RefCell<Option<FxHashMap<NameId, TypeId>>>,
    /// Cache for substituted types (TypeId → TypeId)
    pub(crate) substitution_cache: RefCell<FxHashMap<TypeId, TypeId>>,
    /// Module export bindings registered within this function body (destructuring imports inside a function).
    /// Looked up first; falls back to `global_module_bindings` for top-level registrations.
    pub local_module_bindings: FxHashMap<Symbol, ModuleExportBinding>,
    /// Read-only reference to globally-registered module bindings from top-level destructuring imports.
    pub global_module_bindings: &'ctx FxHashMap<Symbol, ModuleExportBinding>,
    /// RC scope stack for drop flag tracking and cleanup emission
    pub rc_scopes: RcScopeStack,
    /// Yielder pointer variable for generator body functions.
    /// When set, `ExprKind::Yield` compiles to `vole_generator_yield(yielder, value)`.
    pub yielder_var: Option<Variable>,
    /// True when compiling an Iterable default method body.
    ///
    /// In these compiled bodies, closure parameters (like `f` in `fn map(f)`) are owned by
    /// the body — the outer caller transferred ownership without emitting rc_dec (due to
    /// `used_iterable_default_path`). This means:
    ///   - For pipeline methods (map/filter): do NOT emit rc_inc for borrowed closure params
    ///     (the iterator gets the single reference and frees it on drop)
    ///   - For terminal methods (any/all/find): DO emit rc_dec after the runtime call
    ///     (the runtime borrows the closure but doesn't free it; codegen must)
    ///
    /// When false (regular user code), closure params are borrowed — the CALLER retains
    /// ownership and will dec_ref them. Pipeline methods must rc_inc to get their own ref.
    pub in_iterable_default_body: bool,
    /// Concrete VirTypeId for `Self` in interface default method bodies.
    ///
    /// During VIR lowering, `Self` (Placeholder) maps to `VirTypeId::UNKNOWN`.
    /// When compiling a default method for a concrete implementor, this field
    /// tells `try_substitute_type_v` to replace UNKNOWN with the concrete type.
    pub self_vir_type: Option<VirTypeId>,
    /// Pre-resolved named-argument reordering mapping from VIR.
    ///
    /// Set by VIR call dispatch (ClosureVariable, CapturedClosure, GlobalClosure),
    /// consumed by `call_func_id_impl()` and `call_actual_closure()`.
    pub(crate) vir_resolved_call_args: Option<Vec<Option<usize>>>,
    /// Pre-resolved lambda parameter defaults from VIR.
    ///
    /// Set by VIR call dispatch (ClosureVariable, CapturedClosure, GlobalClosure),
    /// consumed by `call_actual_closure()`.
    pub(crate) vir_lambda_defaults: Option<vole_vir::LambdaDefaultsInfo>,
    /// Pre-resolved monomorph key from VIR.
    ///
    /// Set by VIR call dispatch (GlobalClosure), consumed by
    /// method dispatch for generic external intrinsics.
    pub(crate) vir_monomorph_key: Option<vole_identity::MonomorphKey>,
    /// Pre-resolved return type from VIR `Call` node.
    ///
    /// Set by VIR call dispatch (ClosureVariable, GlobalClosure), consumed by
    /// `get_call_return_type()`.
    pub(crate) vir_call_return_type: Option<TypeId>,
    /// Cached `iconst.i64 0` created in the entry block for void returns.
    /// Reused by every `void_value()` call to avoid emitting thousands of
    /// dead iconst instructions (previously ~18,951 per compilation).
    pub(crate) cached_void_val: Value,
    /// The entry block of the current function.
    ///
    /// Stored so that `iconst_cached()` can lazily insert constant
    /// instructions here on first use. Because the entry block dominates
    /// every other block in SSA form, entry-block values are usable
    /// everywhere without violating dominance.
    entry_block: Block,
    /// Function-wide iconst cache: `(Type, i64) -> Value`.
    ///
    /// All cached constants are placed in the entry block so they dominate
    /// every use. The cache is never cleared on block switches — every value
    /// created once and reused everywhere.
    iconst_cache: FxHashMap<(Type, i64), Value>,
    /// Lazily-populated cache for `rc_state_v()` results.
    ///
    /// RcState is a pure function of `(VirTypeId, VirTypeTable, AnalyzedProgram)`,
    /// all immutable during codegen. The cache eliminates repeated computation
    /// across the ~53 call sites.  Uses `RefCell` so `&self` methods can populate it.
    pub(crate) rc_state_cache: RefCell<FxHashMap<VirTypeId, RcState>>,
    /// Lazily-populated cache for optional type metadata (nil position + inner type).
    ///
    /// Pure function of `(VirTypeId, VirTypeTable)`, all immutable during codegen.
    /// Eliminates repeated `find_nil_variant_vir()` and `vir_query_unwrap_optional_v()`
    /// calls across optional comparison, coalescing, and chaining sites.
    pub(crate) optional_meta_cache: RefCell<FxHashMap<VirTypeId, super::type_ops::OptionalMeta>>,
    /// Lazily-populated cache for struct flat-slot layout (byte offset + Cranelift type per leaf).
    ///
    /// Pure function of `(VirTypeId, VirTypeTable, AnalyzedProgram)`, all immutable during codegen.
    /// Eliminates repeated recursive traversal of `vir_struct_flat_field_cranelift_types()`.
    pub(crate) struct_flat_slots_cache: RefCell<FxHashMap<VirTypeId, Vec<(i32, Type)>>>,

    // ========== Shared context fields ==========
    /// Mutable JIT infrastructure (module, func_registry)
    pub codegen_ctx: &'a mut CodegenCtx<'ctx>,
    /// Compilation environment (session/unit level)
    pub env: &'a CompileEnv<'ctx>,
}

impl<'a, 'b, 'ctx> Cg<'a, 'b, 'ctx> {
    /// Create a new codegen context.
    ///
    /// Creates fresh `vars` and `cf` internally. Use `with_*` methods for configuration:
    /// - `.with_return_type()` - set return type for the function
    /// - `.with_module()` - set current module
    /// - `.with_substitutions()` - set type parameter substitutions
    /// - `.with_captures()` - set closure captures
    pub fn new(
        builder: &'a mut FunctionBuilder<'b>,
        codegen_ctx: &'a mut CodegenCtx<'ctx>,
        env: &'a CompileEnv<'ctx>,
    ) -> Self {
        // Create the void constant eagerly — we're still in the entry block
        // so `ins().iconst()` places it there naturally.  This also ensures
        // the entry block is inserted into the layout (via ensure_inserted_block).
        let cached_void_val = builder.ins().iconst(types::I64, 0);
        let mut iconst_cache = FxHashMap::default();
        iconst_cache.insert((types::I64, 0i64), cached_void_val);

        // Now the entry block is in the layout; grab it for later lazy insertion.
        let entry_block = builder
            .func
            .layout
            .entry_block()
            .expect("entry block must exist after emitting void constant");

        Self {
            builder,
            vars: FxHashMap::default(),
            cf: ControlFlow::new(),
            captures: None,
            self_capture: None,
            field_cache: FxHashMap::default(),
            return_type: None,
            return_abi: vole_vir::func::ReturnAbi::Void,
            current_module: None,
            substitutions: None,
            callable_backend_preference: CallableBackendPreference::PreferInline,
            sema_substitutions: RefCell::new(None),
            substitution_cache: RefCell::new(FxHashMap::default()),
            // No clone: local_module_bindings starts empty for within-function inserts.
            // Global bindings are accessed via the read-only reference below.
            local_module_bindings: FxHashMap::default(),
            global_module_bindings: env.global_module_bindings,
            rc_scopes: RcScopeStack::new(),
            yielder_var: None,
            in_iterable_default_body: false,
            self_vir_type: None,
            vir_resolved_call_args: None,
            vir_lambda_defaults: None,
            vir_monomorph_key: None,
            vir_call_return_type: None,
            cached_void_val,
            entry_block,
            iconst_cache,
            rc_state_cache: RefCell::new(FxHashMap::default()),
            optional_meta_cache: RefCell::new(FxHashMap::default()),
            struct_flat_slots_cache: RefCell::new(FxHashMap::default()),
            codegen_ctx,
            env,
        }
    }

    /// Set closure captures (None = no captures).
    pub fn with_captures(mut self, captures: Option<Captures<'a>>) -> Self {
        self.captures = captures;
        self
    }

    /// Set the return type directly from a `VirTypeId`.
    ///
    /// Also recomputes `return_abi` from the new return type.
    pub fn with_return_type_v(mut self, return_type: Option<VirTypeId>) -> Self {
        self.return_type = return_type;
        self.return_abi = match return_type {
            Some(ret) => vole_vir::func::ReturnAbi::classify(ret, self.vir_type_table()),
            None => vole_vir::func::ReturnAbi::Void,
        };
        self
    }

    /// Set the current module.
    pub fn with_module(mut self, module_id: Option<ModuleId>) -> Self {
        self.current_module = module_id;
        self
    }

    /// Set type parameter substitutions for monomorphized generics (VirTypeId-native).
    pub fn with_substitutions(mut self, subs: Option<&'a FxHashMap<NameId, VirTypeId>>) -> Self {
        self.substitutions = subs;
        self
    }

    /// Get a lazily-computed sema `TypeId` substitution map derived from the
    /// VirTypeId-native `self.substitutions`.
    ///
    /// Returns `None` when no substitutions are active. The result is cached so
    /// the conversion (VirTypeId → TypeId via `vir_to_sema_type_id`) is performed
    /// at most once per `Cg` lifetime.
    pub fn sema_substitutions(&self) -> Option<std::cell::Ref<'_, FxHashMap<NameId, TypeId>>> {
        let subs = self.substitutions?;
        // Populate cache if empty.
        {
            let cache = self.sema_substitutions.borrow();
            if cache.is_some() {
                // Already populated — return a Ref that maps into the inner Option.
                return Some(std::cell::Ref::map(cache, |opt| opt.as_ref().unwrap()));
            }
        }
        // Build the TypeId map from VirTypeId substitutions via VirTypeTable.
        let table = self.vir_type_table();
        let sema_map: FxHashMap<NameId, TypeId> = subs
            .iter()
            .map(|(&name, &vir_ty)| {
                let type_id = table.vir_to_type_id(vir_ty);
                (name, type_id)
            })
            .collect();
        *self.sema_substitutions.borrow_mut() = Some(sema_map);
        Some(std::cell::Ref::map(
            self.sema_substitutions.borrow(),
            |opt| opt.as_ref().unwrap(),
        ))
    }

    /// Set the yielder variable for generator body compilation.
    pub fn with_yielder(mut self, yielder_var: Variable) -> Self {
        self.yielder_var = Some(yielder_var);
        self
    }

    /// Mark this as an Iterable default method body compilation.
    ///
    /// When true, closure parameters are treated as owned (caller transferred ownership).
    /// Pipeline methods skip rc_inc; terminal methods emit rc_dec after the runtime call.
    pub fn with_iterable_default_body(mut self) -> Self {
        self.in_iterable_default_body = true;
        self
    }

    /// Set the concrete Self type for interface default method compilation.
    pub fn with_self_vir_type(mut self, self_vir_ty: VirTypeId) -> Self {
        self.self_vir_type = Some(self_vir_ty);
        self
    }

    /// Set backend preference for dual runtime/intrinsic callables.
    pub fn with_callable_backend_preference(
        mut self,
        preference: CallableBackendPreference,
    ) -> Self {
        self.callable_backend_preference = preference;
        self
    }

    /// Set pre-populated variables (for cases where params are bound before Cg creation).
    pub fn with_vars(mut self, vars: FxHashMap<Symbol, (Variable, VirTypeId)>) -> Self {
        self.vars = vars;
        self
    }

    /// Check if we're in a closure context with captures
    pub fn has_captures(&self) -> bool {
        self.captures.is_some()
    }

    /// Bind a variable directly with a VirTypeId, skipping the sema TypeId round-trip.
    ///
    /// Used when the VirTypeId is known to be correct (e.g., from interface boxing
    /// in monomorphized contexts where `sema_type_id` returns UNKNOWN).
    pub fn bind_var_v(&mut self, name: Symbol, var: Variable, vir_type_id: VirTypeId) {
        self.vars.insert(name, (var, vir_type_id));
    }

    // ========== Context accessors ==========

    /// Get current module (as ModuleId)
    #[inline]
    pub fn current_module_id(&self) -> Option<ModuleId> {
        self.current_module
    }

    /// Get the name table.
    /// Returns `&'ctx NameTable` so references obtained from it outlive `self` borrows.
    #[inline]
    pub fn name_table(&self) -> &'ctx vole_identity::NameTable {
        self.env.analyzed.name_table()
    }

    /// Get the pointer type (Cranelift platform pointer)
    #[inline]
    pub fn ptr_type(&self) -> Type {
        self.codegen_ctx.ptr_type()
    }

    /// Get the VIR type table for `VirTypeId`-based queries.
    #[inline]
    pub fn vir_type_table(&self) -> &vole_vir::type_table::VirTypeTable {
        &self.env.analyzed.type_table
    }

    /// Best-effort translation from sema `TypeId` to `VirTypeId`.
    ///
    /// Reserved primitive/special IDs are aligned between `TypeId` and
    /// `VirTypeId`, so those can be mapped directly. Dynamic sema IDs are
    /// resolved by `vir_query_*` helpers via arena fallback paths.
    ///
    /// Temporary bridge after removing `VirTypeTable`'s sema cache (N279-B).
    /// Once N279-C migrates all VIR consumers to carry `VirTypeId` directly,
    /// this lookup path should be deleted.
    #[inline]
    pub fn vir_lookup(&self, type_id: TypeId) -> VirTypeId {
        let lookup = self.vir_type_table().lookup_type_id(type_id);
        // The post-lowering sweep (vol-wdt4) maps all concrete arena TypeIds
        // to VirTypeIds.  Only Module/Structural/Placeholder/Invalid types and
        // those containing type parameters remain unmapped — these should never
        // appear in codegen predicate queries.
        debug_assert!(
            lookup.is_some(),
            "TypeId({}) has no VirTypeId mapping — was it missed by the sweep?",
            type_id.raw(),
        );
        lookup.unwrap_or(VirTypeId::UNKNOWN)
    }

    /// Look up the VirTypeId for a sema TypeId.
    ///
    /// Returns the VirTypeId from VirTypeTable. For types that cannot be
    /// properly mapped (Placeholder, sema-internal), returns
    /// `VirTypeId::UNKNOWN`. Callers that need type substitution should use
    /// `try_substitute_type_v` which handles the UNKNOWN case by falling
    /// back to sema-level substitution.
    #[inline]
    pub fn vir_lookup_or_compat(&self, type_id: TypeId) -> VirTypeId {
        self.vir_lookup(type_id)
    }

    /// Convert a sema `TypeId` to a `VirTypeId` for interior codegen use.
    ///
    /// Boundary bridge: interior codegen should call this instead of
    /// `vir_lookup` or `vir_lookup_or_compat` directly. Returns
    /// `VirTypeId::UNKNOWN` for unmapped types (safe for all `_v` query
    /// methods). Callers that need compat-encoded round-tripping (variable
    /// registration, substitution) should use the dedicated bridges
    /// (`bind_var`, `register_rc_local_id`, `coerce_to_type_id`) instead.
    #[inline]
    pub fn to_vir_type(&self, type_id: TypeId) -> VirTypeId {
        self.vir_lookup(type_id)
    }

    /// Check if a `VirTypeId` is a struct type via VirTypeTable.
    ///
    /// Excludes sentinel types (Nil, Done, user-defined empties) — matching the
    /// arena's `is_struct()` semantics.
    #[inline]
    pub fn vir_query_is_struct_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_is_struct(vir_ty, self.vir_type_table())
    }

    /// Check if a sema `TypeId` is a struct type via VirTypeTable.
    ///
    /// Delegates to [`vir_query_is_struct_v`](Self::vir_query_is_struct_v)
    /// after translating `TypeId` → `VirTypeId`.
    #[inline]
    pub fn vir_query_is_struct(&self, type_id: TypeId) -> bool {
        self.vir_query_is_struct_v(self.vir_lookup(type_id))
    }

    /// Check if a `VirTypeId` is a union type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_union_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_is_union(vir_ty, self.vir_type_table())
    }

    /// Check if a sema `TypeId` is a union type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_union(&self, type_id: TypeId) -> bool {
        self.vir_query_is_union_v(self.vir_lookup(type_id))
    }

    /// Check if a `VirTypeId` is the unknown type.
    ///
    /// Uses identity check against the reserved `VirTypeId::UNKNOWN` constant
    /// rather than table lookup, since unmapped types (Placeholder, etc.) also
    /// map to `VirType::Unknown` but are not genuinely unknown.
    #[inline]
    pub fn vir_query_is_unknown_v(&self, vir_ty: VirTypeId) -> bool {
        vir_ty.is_unknown()
    }

    /// Check if a `VirTypeId` is a payload-carrying union via VirTypeTable.
    #[inline]
    pub fn vir_query_is_payload_union_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_is_payload_union(vir_ty, self.vir_type_table())
    }

    /// Check if a sema `TypeId` is a payload-carrying union via VirTypeTable.
    #[inline]
    pub fn vir_query_is_payload_union(&self, type_id: TypeId) -> bool {
        self.vir_query_is_payload_union_v(self.vir_lookup(type_id))
    }

    /// Check if a `VirTypeId` is void via VirTypeTable.
    #[inline]
    pub fn vir_query_is_void_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_is_void(vir_ty, self.vir_type_table())
    }

    /// Check if a sema `TypeId` is void via VirTypeTable.
    #[inline]
    pub fn vir_query_is_void(&self, type_id: TypeId) -> bool {
        self.vir_query_is_void_v(self.vir_lookup(type_id))
    }

    /// Check if a `VirTypeId` is a fallible type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_fallible_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_is_fallible(vir_ty, self.vir_type_table())
    }

    /// Check if a sema `TypeId` is a fallible type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_fallible(&self, type_id: TypeId) -> bool {
        self.vir_query_is_fallible_v(self.vir_lookup(type_id))
    }

    /// Classify a `VirTypeId` as a `WideType` (i128/f128) via VirTypeTable.
    ///
    /// Returns `None` for non-wide types.
    #[inline]
    pub fn vir_query_wide_type_v(
        &self,
        vir_ty: VirTypeId,
    ) -> Option<crate::types::wide_ops::WideType> {
        crate::types::wide_ops::WideType::from_vir_type_id(vir_ty)
    }

    /// Classify a sema `TypeId` as a `WideType` (i128/f128) via VirTypeTable.
    ///
    /// Returns `None` for non-wide types.
    #[inline]
    pub fn vir_query_wide_type(&self, type_id: TypeId) -> Option<crate::types::wide_ops::WideType> {
        self.vir_query_wide_type_v(self.vir_lookup(type_id))
    }

    /// Check if a `VirTypeId` is an interface type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_interface_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_is_interface(vir_ty, self.vir_type_table())
    }

    /// Check if a sema `TypeId` is an interface type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_interface(&self, type_id: TypeId) -> bool {
        self.vir_query_is_interface_v(self.vir_lookup(type_id))
    }

    /// Unwrap a nominal `VirTypeId` to its TypeDefId via VirTypeTable.
    #[inline]
    pub fn vir_query_unwrap_nominal_v(
        &self,
        vir_ty: VirTypeId,
    ) -> Option<vole_identity::TypeDefId> {
        crate::types::vir_conversions::vir_unwrap_nominal(vir_ty, self.vir_type_table())
    }

    /// Get a human-readable type display string for a `VirTypeId` via VirTypeTable.
    #[inline]
    pub fn vir_query_display_basic_v(&self, vir_ty: VirTypeId) -> String {
        crate::types::vir_conversions::vir_display_basic(vir_ty, self.vir_type_table())
    }

    /// Get a human-readable type display string via VirTypeTable.
    #[inline]
    pub fn vir_query_display_basic(&self, type_id: TypeId) -> String {
        self.vir_query_display_basic_v(self.vir_lookup(type_id))
    }

    /// Get the field byte size for a `VirTypeId` via VirTypeTable.
    #[inline]
    pub fn vir_query_field_byte_size_v(&self, vir_ty: VirTypeId) -> u32 {
        crate::types::vir_conversions::vir_field_byte_size(vir_ty, self.vir_type_table())
    }

    /// Get the runtime type tag for boxing a `VirTypeId` to unknown via VirTypeTable.
    #[inline]
    pub fn vir_query_unknown_type_tag_v(&self, vir_ty: VirTypeId) -> u64 {
        crate::types::vir_conversions::vir_unknown_type_tag(vir_ty, self.vir_type_table())
    }

    /// Get the runtime type tag for boxing a value to unknown via VirTypeTable.
    #[inline]
    pub fn vir_query_unknown_type_tag(&self, type_id: TypeId) -> u64 {
        self.vir_query_unknown_type_tag_v(self.vir_lookup(type_id))
    }

    /// Map a `VirTypeId` to its Cranelift type via VirTypeTable.
    #[inline]
    pub fn vir_query_type_to_cranelift_v(&self, vir_ty: VirTypeId) -> Type {
        // Sentinel types are always i8 (zero-field struct tag). VIR maps them
        // as Struct, which would incorrectly resolve to ptr_type.
        if crate::types::vir_conversions::vir_is_sentinel(vir_ty, self.vir_type_table()) {
            return types::I8;
        }
        let ptr = self.ptr_type();
        crate::types::vir_conversions::vir_type_to_cranelift(vir_ty, self.vir_type_table(), ptr)
    }

    /// Map a sema `TypeId` to its Cranelift type via VirTypeTable.
    #[inline]
    pub fn vir_query_type_to_cranelift(&self, type_id: TypeId) -> Type {
        self.vir_query_type_to_cranelift_v(self.vir_lookup(type_id))
    }

    /// Check if a `VirTypeId` is a sentinel type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_sentinel_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_is_sentinel(vir_ty, self.vir_type_table())
    }

    /// Check if a sema `TypeId` is a sentinel type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_sentinel(&self, type_id: TypeId) -> bool {
        self.vir_query_is_sentinel_v(self.vir_lookup(type_id))
    }

    /// Check if a `VirTypeId` is a function type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_function_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_is_function(vir_ty, self.vir_type_table())
    }

    /// Check if a sema `TypeId` is a function type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_function(&self, type_id: TypeId) -> bool {
        self.vir_query_is_function_v(self.vir_lookup(type_id))
    }

    /// Check if a `VirTypeId` is an unsigned integer type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_unsigned_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_is_unsigned(vir_ty, self.vir_type_table())
    }

    /// Check if a sema `TypeId` is an unsigned integer type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_unsigned(&self, type_id: TypeId) -> bool {
        self.vir_query_is_unsigned_v(self.vir_lookup(type_id))
    }

    /// Check if a `VirTypeId` is an integer type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_integer_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_is_integer(vir_ty, self.vir_type_table())
    }

    /// Check if a `VirTypeId` is a floating point type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_float_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_is_float(vir_ty, self.vir_type_table())
    }

    /// Check if a `VirTypeId` is the string type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_string_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_is_string(vir_ty, self.vir_type_table())
    }

    /// Check if a `VirTypeId` is an optional type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_optional_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_is_optional(vir_ty, self.vir_type_table())
    }

    /// Check if a `VirTypeId` is an array type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_array_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_is_array(vir_ty, self.vir_type_table())
    }

    /// Check if a `VirTypeId` is a runtime iterator type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_runtime_iterator_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_is_runtime_iterator(vir_ty, self.vir_type_table())
    }

    /// Unwrap a fallible `VirTypeId` to `(success, errors)` via VirTypeTable.
    #[inline]
    pub fn vir_query_unwrap_fallible_v(
        &self,
        vir_ty: VirTypeId,
    ) -> Option<(VirTypeId, Vec<VirTypeId>)> {
        crate::types::vir_conversions::vir_unwrap_fallible(vir_ty, self.vir_type_table())
            .map(|(success, errors)| (success, errors.to_vec()))
    }

    /// Unwrap a fallible sema `TypeId` to `(success, errors)` via VirTypeTable.
    #[inline]
    pub fn vir_query_unwrap_fallible(
        &self,
        type_id: TypeId,
    ) -> Option<(VirTypeId, Vec<VirTypeId>)> {
        self.vir_query_unwrap_fallible_v(self.vir_lookup(type_id))
    }

    /// Unwrap a union `VirTypeId` to its variant `VirTypeId`s via VirTypeTable.
    ///
    /// Also handles `VirType::Optional`, reading the pre-computed canonical
    /// variant order stored during VIR lowering.
    pub fn vir_query_unwrap_union_v(&self, vir_ty: VirTypeId) -> Option<Vec<VirTypeId>> {
        let table = self.vir_type_table();
        match table.get(vir_ty) {
            vole_vir::VirType::Union { variants } => Some(variants.to_vec()),
            vole_vir::VirType::Optional { variants, .. } => Some(variants.to_vec()),
            _ => None,
        }
    }

    /// Unwrap a union sema `TypeId` to its variant `VirTypeId`s via VirTypeTable.
    #[inline]
    pub fn vir_query_unwrap_union(&self, type_id: TypeId) -> Option<Vec<VirTypeId>> {
        self.vir_query_unwrap_union_v(self.vir_lookup(type_id))
    }

    /// Unwrap a tuple `VirTypeId` to its element `VirTypeId`s via VirTypeTable.
    #[inline]
    pub fn vir_query_unwrap_tuple_v(&self, vir_ty: VirTypeId) -> Option<Vec<VirTypeId>> {
        crate::types::vir_conversions::vir_unwrap_tuple(vir_ty, self.vir_type_table())
            .map(|v| v.to_vec())
    }

    /// Unwrap a fixed array `VirTypeId` to `(element, size)` via VirTypeTable.
    #[inline]
    pub fn vir_query_unwrap_fixed_array_v(&self, vir_ty: VirTypeId) -> Option<(VirTypeId, usize)> {
        crate::types::vir_conversions::vir_unwrap_fixed_array(vir_ty, self.vir_type_table())
            .map(|(elem, len)| (elem, len as usize))
    }

    /// Unwrap an array `VirTypeId` to its element `VirTypeId` via VirTypeTable.
    #[inline]
    pub fn vir_query_unwrap_array_v(&self, vir_ty: VirTypeId) -> Option<VirTypeId> {
        crate::types::vir_conversions::vir_unwrap_array(vir_ty, self.vir_type_table())
    }

    /// Unwrap a struct `VirTypeId` to `(TypeDefId, type_args)` via VirTypeTable.
    #[inline]
    pub fn vir_query_unwrap_struct_v(
        &self,
        vir_ty: VirTypeId,
    ) -> Option<(vole_identity::TypeDefId, Vec<VirTypeId>)> {
        crate::types::vir_conversions::vir_unwrap_struct(vir_ty, self.vir_type_table())
            .map(|(def, args)| (def, args.to_vec()))
    }

    /// Unwrap a function `VirTypeId` to `(params, return_type)` via VirTypeTable.
    ///
    /// VIR does not track the `is_closure` flag. Callers that need it must
    /// consult the arena directly.
    #[inline]
    pub fn vir_query_unwrap_function_v(
        &self,
        vir_ty: VirTypeId,
    ) -> Option<(Vec<VirTypeId>, VirTypeId)> {
        crate::types::vir_conversions::vir_unwrap_function(vir_ty, self.vir_type_table())
            .map(|(params, ret)| (params.to_vec(), ret))
    }

    /// Unwrap a function sema `TypeId` to `(params, return_type)` via VirTypeTable.
    #[inline]
    pub fn vir_query_unwrap_function(
        &self,
        type_id: TypeId,
    ) -> Option<(Vec<VirTypeId>, VirTypeId)> {
        self.vir_query_unwrap_function_v(self.vir_lookup(type_id))
    }

    /// Unwrap a type parameter `VirTypeId` to its `NameId` via VirTypeTable.
    #[inline]
    pub fn vir_query_unwrap_type_param_v(&self, vir_ty: VirTypeId) -> Option<NameId> {
        crate::types::vir_conversions::vir_unwrap_type_param(vir_ty, self.vir_type_table())
    }

    /// Unwrap a runtime iterator `VirTypeId` to its element `VirTypeId` via VirTypeTable.
    #[inline]
    pub fn vir_query_unwrap_runtime_iterator_v(&self, vir_ty: VirTypeId) -> Option<VirTypeId> {
        crate::types::vir_conversions::vir_unwrap_runtime_iterator(vir_ty, self.vir_type_table())
    }

    /// Unwrap an interface `VirTypeId` to `(TypeDefId, type_args)` via VirTypeTable.
    #[inline]
    pub fn vir_query_unwrap_interface_v(
        &self,
        vir_ty: VirTypeId,
    ) -> Option<(vole_identity::TypeDefId, Vec<VirTypeId>)> {
        crate::types::vir_conversions::vir_unwrap_interface(vir_ty, self.vir_type_table())
            .map(|(def, args)| (def, args.to_vec()))
    }

    /// Unwrap an error `VirTypeId` to its `TypeDefId` via VirTypeTable.
    #[inline]
    pub fn vir_query_unwrap_error_v(&self, vir_ty: VirTypeId) -> Option<vole_identity::TypeDefId> {
        crate::types::vir_conversions::vir_unwrap_error(vir_ty, self.vir_type_table())
    }

    /// Get the range `TypeId`.
    ///
    /// Constant — always `TypeId::RANGE`.
    #[inline]
    pub fn vir_query_range(&self) -> TypeId {
        TypeId::RANGE
    }

    /// Look up an existing array type by element `TypeId` via VirTypeTable.
    #[inline]
    pub fn vir_query_lookup_array(&self, elem: TypeId) -> Option<TypeId> {
        self.vir_type_table().lookup_array_sema(elem)
    }

    /// Look up an existing array type by element `VirTypeId` via VirTypeTable.
    #[inline]
    pub fn vir_query_lookup_array_v(&self, elem: VirTypeId) -> Option<VirTypeId> {
        self.vir_type_table().lookup_array_v(elem)
    }

    /// Look up the result of substituting type parameters in a type via VirTypeTable.
    ///
    /// Falls back to arena for compound types that were not lowered into the
    /// VIR type table (e.g., cross-module Self parameters in interface default
    /// methods).
    #[inline]
    pub fn vir_query_lookup_substitute(
        &self,
        ty: TypeId,
        subs: &FxHashMap<NameId, TypeId>,
    ) -> Option<TypeId> {
        self.vir_type_table()
            .lookup_substitute(ty, subs)
            .or_else(|| self.analyzed().substitute_fallback(ty, subs))
    }

    /// Look up an existing runtime iterator type by element `TypeId` via VirTypeTable.
    #[inline]
    pub fn vir_query_lookup_runtime_iterator(&self, elem: TypeId) -> Option<TypeId> {
        self.vir_type_table().lookup_runtime_iterator_sema(elem)
    }

    /// Look up an existing runtime iterator type by element `VirTypeId` via VirTypeTable.
    #[inline]
    pub fn vir_query_lookup_runtime_iterator_v(&self, elem: VirTypeId) -> Option<VirTypeId> {
        self.vir_type_table().lookup_runtime_iterator_v(elem)
    }

    /// Substitute type parameters in a type, panicking on failure.
    ///
    /// Tries VirTypeTable first, falls back to the injected substitution
    /// callback for compound types not yet interned in VIR.
    #[track_caller]
    #[inline]
    pub fn vir_query_expect_substitute(
        &self,
        ty: TypeId,
        subs: &FxHashMap<NameId, TypeId>,
        context: &str,
    ) -> TypeId {
        self.vir_type_table()
            .lookup_substitute(ty, subs)
            .or_else(|| self.analyzed().substitute_fallback(ty, subs))
            .unwrap_or_else(|| {
                panic!(
                    "vir_query_expect_substitute: type not found after substitution\n\
                     Context: {context}\n\
                     TypeId: {ty:?}\n\
                     Location: {}",
                    std::panic::Location::caller(),
                )
            })
    }

    /// Check if a `VirTypeId` contains any type parameter anywhere in its structure
    /// via VirTypeTable.
    #[inline]
    pub fn vir_query_contains_type_param_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_contains_type_param(vir_ty, self.vir_type_table())
    }

    /// Check if a `VirTypeId` is a numeric type (integer or float) via VirTypeTable.
    #[inline]
    pub fn vir_query_is_numeric_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_is_numeric(vir_ty, self.vir_type_table())
    }

    // vir_query_primitives() deleted — use TypeId constants directly
    // (e.g. TypeId::STRING, TypeId::I64)

    /// Check if a `VirTypeId` is a class type via VirTypeTable.
    pub fn vir_query_is_class_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_is_class(vir_ty, self.vir_type_table())
    }

    /// Unwrap a class `VirTypeId` to `(TypeDefId, type_args)` via VirTypeTable.
    #[inline]
    pub fn vir_query_unwrap_class_v(
        &self,
        vir_ty: VirTypeId,
    ) -> Option<(vole_identity::TypeDefId, Vec<VirTypeId>)> {
        crate::types::vir_conversions::vir_unwrap_class(vir_ty, self.vir_type_table())
            .map(|(def, args)| (def, args.to_vec()))
    }

    /// Unwrap a class sema `TypeId` to `(TypeDefId, type_args)` via VirTypeTable.
    #[inline]
    pub fn vir_query_unwrap_class(
        &self,
        type_id: TypeId,
    ) -> Option<(vole_identity::TypeDefId, Vec<VirTypeId>)> {
        self.vir_query_unwrap_class_v(self.vir_lookup(type_id))
    }

    /// Unwrap an optional `VirTypeId` to its inner `VirTypeId` via VirTypeTable.
    #[inline]
    pub fn vir_query_unwrap_optional_v(&self, vir_ty: VirTypeId) -> Option<VirTypeId> {
        crate::types::vir_conversions::vir_unwrap_optional(vir_ty, self.vir_type_table())
    }

    /// Check if a `VirTypeId` is the nil type via VirTypeTable.
    #[inline]
    pub fn vir_query_is_nil_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_is_nil(vir_ty, self.vir_type_table())
    }

    /// Unwrap an error or struct `VirTypeId` to its `TypeDefId` via VirTypeTable.
    #[inline]
    pub fn vir_query_unwrap_error_or_struct_def_v(
        &self,
        vir_ty: VirTypeId,
    ) -> Option<vole_identity::TypeDefId> {
        crate::types::vir_conversions::vir_unwrap_error_or_struct_def(vir_ty, self.vir_type_table())
    }

    /// Unwrap a function `VirTypeId` to `(params, return_type)` as sema `TypeId`s.
    ///
    /// Uses VirTypeTable to get the VIR params/ret, then converts each to
    /// sema TypeId via the reverse mapping.  SelfType placeholders are already
    /// resolved during VIR lowering.
    #[inline]
    pub fn vir_query_unwrap_function_sema_v(
        &self,
        vir_ty: VirTypeId,
    ) -> Option<(Vec<TypeId>, TypeId)> {
        let table = self.vir_type_table();
        let (vir_params, vir_ret) = table.unwrap_function(vir_ty)?;
        let params: Vec<TypeId> = vir_params
            .iter()
            .map(|&p| table.vir_to_type_id(p))
            .collect();
        let ret = table.vir_to_type_id(vir_ret);
        Some((params, ret))
    }

    /// Look up an existing fixed-array type by element `VirTypeId` and size
    /// via VirTypeTable.
    #[inline]
    pub fn vir_query_lookup_fixed_array_v(
        &self,
        element: VirTypeId,
        size: usize,
    ) -> Option<VirTypeId> {
        self.vir_type_table()
            .lookup_fixed_array_v(element, size as u32)
    }

    /// Look up module exports by `ModuleId`.
    ///
    /// Scans `VirProgram::module_exports` for a matching `ModuleId`.
    /// Used by module field access dispatch when the ModuleId is known
    /// from VIR lowering (FieldStorage::Module).
    #[inline]
    pub fn vir_query_module_exports_by_id(
        &self,
        module_id: ModuleId,
    ) -> Option<smallvec::SmallVec<[(NameId, TypeId); 8]>> {
        let vir = self.env.analyzed;
        vir.module_exports
            .values()
            .find(|(mid, _)| *mid == module_id)
            .map(|(_, exports)| exports.iter().copied().collect())
    }

    /// Look up a compile-time constant in a module's metadata.
    ///
    /// Uses VirProgram's pre-populated module_constants map.
    #[inline]
    pub fn vir_query_module_constant(
        &self,
        module_id: ModuleId,
        name_id: NameId,
    ) -> Option<vole_identity::ConstantValue> {
        self.env
            .analyzed
            .module_constants
            .get(&(module_id, name_id))
            .cloned()
    }

    /// Get the runtime tag for an array element `VirTypeId` via VirTypeTable.
    #[inline]
    pub fn vir_query_array_element_tag_id_v(&self, vir_ty: VirTypeId) -> i64 {
        crate::types::vir_conversions::vir_array_element_tag_id(vir_ty, self.vir_type_table())
    }

    /// Get the flat slot count for a VIR struct type.
    ///
    /// For compat-encoded VirTypeIds, resolves via VirTypeTable lookup.
    #[inline]
    pub fn vir_struct_flat_slot_count(&self, vir_ty: VirTypeId) -> Option<usize> {
        crate::types::vir_struct_helpers::vir_struct_flat_slot_count(
            vir_ty,
            self.vir_type_table(),
            self.analyzed(),
        )
    }

    /// Compute the byte offset of field `slot` within a VIR struct type.
    ///
    /// Panics if the type is not a struct or the slot is out of range.
    #[inline]
    pub fn vir_struct_field_byte_offset(&self, vir_ty: VirTypeId, slot: usize) -> i32 {
        crate::types::vir_struct_helpers::vir_struct_field_byte_offset(
            vir_ty,
            slot,
            self.vir_type_table(),
            self.analyzed(),
        )
        .expect("INTERNAL: struct field offset must be computable for valid struct type")
    }

    /// Get field slot and type for a field access using VirTypeId.
    ///
    /// Converts `VirTypeId` → `TypeId` internally and delegates to the
    /// `get_field_slot_and_type_id_cg` path, which uses
    /// `generic_field_types` (VirTypeIds) for substitution.
    #[inline]
    pub fn vir_field_slot_and_type(
        &self,
        vir_ty: VirTypeId,
        field_name: &str,
    ) -> CodegenResult<(usize, TypeId)> {
        let type_id = self.vir_type_table().vir_to_type_id(vir_ty);
        crate::structs::helpers::get_field_slot_and_type_id_cg(type_id, field_name, self)
    }

    /// Get the VIR-stashed return type for the current call expression.
    ///
    /// Set during VIR call dispatch (`compile_vir_unresolved_call` and friends).
    /// All call sites now flow through VIR, so the stashed value is always
    /// present when this method is reached from a live path.
    #[inline]
    pub fn get_call_return_type(&self) -> Option<TypeId> {
        self.vir_call_return_type
    }

    /// Check if a struct type is actually allocated as a heap instance (annotation type).
    ///
    /// Annotation struct types are normally stack-allocated, but when stored in
    /// FieldMeta.annotations they are heap-allocated via InstanceNew. Field access
    /// on these values must use InstanceGetField rather than struct offset loads.
    ///
    /// VirTypeId-native variant.
    pub fn is_heap_allocated_annotation_v(&self, vir_ty: VirTypeId) -> bool {
        if let Some((type_def_id, _)) = self.vir_query_unwrap_struct_v(vir_ty) {
            self.env
                .state
                .annotation_type_ids
                .borrow()
                .contains_key(&type_def_id)
        } else {
            false
        }
    }

    /// Get the runtime type_id for an annotation struct type, eagerly registering
    /// it if needed.
    pub fn get_annotation_runtime_type_id_v(&self, vir_ty: VirTypeId) -> Option<u32> {
        let (type_def_id, _) = self.vir_query_unwrap_struct_v(vir_ty)?;

        // Check sema's is_annotation flag (authoritative source)
        if !self.analyzed().type_is_annotation(type_def_id) {
            return None;
        }

        // Check the annotation_type_ids cache first
        if let Some(&cached_id) = self
            .env
            .state
            .annotation_type_ids
            .borrow()
            .get(&type_def_id)
        {
            return Some(cached_id);
        }

        // Check if this type already has a non-zero type_id in type_metadata
        // (it's a class rather than a struct)
        if let Some(meta) = self.type_metadata().get(&type_def_id)
            && meta.type_id != 0
        {
            return Some(meta.type_id);
        }

        // Eagerly register: allocate a new runtime type_id with field type tags
        let new_type_id = vole_runtime::type_registry::alloc_type_id();
        let field_type_tags: Vec<_> = self
            .analyzed()
            .fields_on_type(type_def_id)
            .map(|field_id| {
                crate::compiler::type_registry::to_runtime_field_tag(
                    self.analyzed().field_def(field_id).field_type_tag,
                )
            })
            .collect();
        vole_runtime::type_registry::register_instance_type(new_type_id, field_type_tags);

        self.env
            .state
            .annotation_type_ids
            .borrow_mut()
            .insert(type_def_id, new_type_id);

        Some(new_type_id)
    }

    /// Get type metadata map
    #[inline]
    pub fn type_metadata(&self) -> &'ctx TypeMetadataMap {
        &self.env.state.type_metadata
    }

    /// Check whether a global variable initializer exists for the given symbol.
    #[inline]
    pub fn has_global_init(&self, name: Symbol) -> bool {
        let module_id = self.current_module.unwrap_or(self.env.analyzed.module_id);
        self.name_table()
            .name_id(module_id, &[name], self.interner())
            .is_some_and(|name_id| self.analyzed().has_global(name_id))
    }

    /// Get VIR-lowered global variable initializer by name.
    ///
    /// Looks up in the main program's VIR global inits, or the current
    /// module's VIR global inits if compiling in a module context.
    pub fn global_vir_init(&self, name: Symbol) -> Option<&vole_vir::VirExpr> {
        let analyzed = self.analyzed();
        if let Some(module_id) = self.current_module() {
            let module_path = self.name_table().module_path(module_id);
            if let Some(module_map) = analyzed.module_global_inits.get(module_path) {
                return module_map.get(&name).map(|r| r.as_ref());
            }
            // Imported modules use their own interner; Symbol indices are not
            // comparable with main-program globals. Don't fall back to the
            // main global VIR map in that case.
            if !std::ptr::eq(self.interner(), analyzed.interner()) {
                return None;
            }
        }
        analyzed.global_inits.get(&name).map(|r| r.as_ref())
    }

    /// Get VIR-lowered default parameter expression by semantic `FunctionId`.
    pub fn function_default_vir_init(
        &self,
        func_id: FunctionId,
        slot: usize,
    ) -> Option<&vole_vir::VirExpr> {
        self.analyzed()
            .get_function_default(func_id, slot)
            .map(|r| r.as_ref())
    }

    /// Get VIR-lowered default parameter expression by semantic `MethodId`.
    pub fn method_default_vir_init(
        &self,
        method_id: MethodId,
        slot: usize,
    ) -> Option<&vole_vir::VirExpr> {
        self.analyzed()
            .get_method_default(method_id, slot)
            .map(|r| r.as_ref())
    }

    /// Get VIR-lowered default parameter expression by lambda `NodeId`.
    pub fn lambda_default_vir_init(
        &self,
        lambda_node_id: vole_identity::NodeId,
        slot: usize,
    ) -> Option<&vole_vir::VirExpr> {
        self.analyzed()
            .get_lambda_default(lambda_node_id, slot)
            .map(|r| r.as_ref())
    }

    /// Get VIR-lowered default field initializer by semantic `FieldId`.
    #[inline]
    pub fn field_default_vir_init(&self, field_id: FieldId) -> Option<&vole_vir::VirExpr> {
        self.analyzed()
            .get_field_default(field_id)
            .map(|r| r.as_ref())
    }

    /// Get source file pointer for error reporting
    #[inline]
    pub fn source_file(&self) -> (*const u8, usize) {
        self.env.source_file_ptr
    }

    /// Increment lambda counter and return new value
    #[inline]
    pub fn next_lambda_id(&self) -> usize {
        let id = self.env.state.lambda_counter.get();
        self.env.state.lambda_counter.set(id + 1);
        id
    }

    /// Get native function registry
    #[inline]
    pub fn native_registry(&self) -> &'ctx vole_runtime::NativeRegistry {
        &self.env.state.native_registry
    }

    /// Get compiler intrinsics registry
    #[inline]
    pub fn intrinsics_registry(&self) -> &'ctx crate::intrinsics::IntrinsicsRegistry {
        &self.env.state.intrinsics_registry
    }

    /// Get the interner for symbol resolution
    #[inline]
    pub fn interner(&self) -> &'ctx vole_identity::Interner {
        self.env.interner
    }

    /// Resolve a symbol, trying the current interner first and then falling
    /// back to the main program interner.
    ///
    /// This is needed because VIR default-parameter expressions are
    /// re-interned into the main interner during lowering, but codegen may
    /// compile them in a module context whose interner has different indices.
    #[inline]
    pub fn resolve_symbol(&self, sym: Symbol) -> &str {
        self.env
            .interner
            .try_resolve(sym)
            .unwrap_or_else(|| self.analyzed().interner().resolve(sym))
    }

    /// Get unified method function key map
    /// Keyed by (type_name_id, method_name_id) for stable lookup across analyzer instances
    #[inline]
    pub fn method_func_keys(&self) -> &'ctx FxHashMap<(NameId, NameId), FunctionKey> {
        &self.env.state.method_func_keys
    }

    /// Look up a free-function monomorph by `MonomorphKey` via VirProgram.
    ///
    /// Uses the `free_monomorphs_by_key` reverse index to find the mangled
    /// name, then looks up the `VirMonomorphInfo` from `free_monomorphs`.
    #[inline]
    pub fn free_monomorph(
        &self,
        key: &vole_identity::MonomorphKey,
    ) -> Option<&'ctx vole_vir::monomorph::instance::VirMonomorphInfo> {
        let vir = self.env.analyzed;
        let mangled = vir.free_monomorphs_by_key.get(key)?;
        vir.free_monomorphs.get(mangled)
    }

    /// Get current module as Option<ModuleId> - use current_module_id() for new code
    #[inline]
    pub fn current_module(&self) -> Option<ModuleId> {
        self.current_module
    }

    /// Get VIR program reference
    #[inline]
    pub fn analyzed(&self) -> &'ctx vole_vir::VirProgram {
        self.env.analyzed
    }

    /// Get mutable reference to JIT module
    #[inline]
    pub fn jit_module(&mut self) -> &mut cranelift_jit::JITModule {
        self.codegen_ctx.jit_module()
    }

    /// Get mutable reference to function registry
    #[inline]
    pub fn funcs(&mut self) -> &mut crate::FunctionRegistry {
        self.codegen_ctx.funcs()
    }

    /// Get immutable reference to function registry
    #[inline]
    pub fn funcs_ref(&self) -> &crate::FunctionRegistry {
        self.codegen_ctx.funcs_ref()
    }

    /// Try to import a native function by its pointer and return a FuncRef for direct calls.
    ///
    /// If the pointer is found in the `ptr_to_symbol` reverse map, the function is
    /// imported into the JIT module (or the existing import is reused) and a FuncRef
    /// suitable for `call` is returned. Returns `None` if the pointer is unknown.
    pub fn try_import_native_func(
        &mut self,
        native_ptr: *const u8,
        sig: &cranelift::prelude::Signature,
    ) -> Option<cranelift::codegen::ir::FuncRef> {
        let symbol_name = self.env.state.ptr_to_symbol.get(&(native_ptr as usize))?;
        let module = self.codegen_ctx.jit_module();
        let func_id = module
            .declare_function(symbol_name, Linkage::Import, sig)
            .ok()?;
        Some(module.declare_func_in_func(func_id, self.builder.func))
    }

    /// Compute a pointer to the `idx`-th `TaggedValue` slot in a dynamic array,
    /// without any bounds check.  The caller must guarantee `idx < len`.
    pub fn dynamic_array_elem_ptr_unchecked(&mut self, arr_ptr: Value, idx: Value) -> Value {
        let ptr_type = self.ptr_type();
        let data_offset = std::mem::offset_of!(vole_runtime::array::RcArray, data) as i32;
        let tagged_value_size = size_of::<vole_runtime::value::TaggedValue>() as i64;
        let data_ptr = self
            .builder
            .ins()
            .load(ptr_type, MemFlags::new(), arr_ptr, data_offset);
        let idx_ptr = if ptr_type == types::I64 {
            idx
        } else {
            self.builder.ins().ireduce(ptr_type, idx)
        };
        let stride = self.iconst_cached(ptr_type, tagged_value_size);
        let elem_offset = self.builder.ins().imul(idx_ptr, stride);
        self.builder.ins().iadd(data_ptr, elem_offset)
    }

    /// Convert a value to dynamic array storage representation for a known element type.
    ///
    /// Returns `(tag, payload_bits, stored_value_for_lifecycle)`.
    ///
    /// When `union_storage_hint` is provided (from sema annotation), the union
    /// storage decision is used directly. Otherwise falls back to runtime
    /// re-detection via `union_array_prefers_inline_storage`.
    pub fn prepare_dynamic_array_store(
        &mut self,
        value: CompiledValue,
        elem_type_id: TypeId,
    ) -> CodegenResult<(Value, Value, CompiledValue)> {
        self.prepare_dynamic_array_store_with_hint(value, elem_type_id, None)
    }

    /// Convert a value to dynamic array storage representation when element
    /// type information is unavailable.
    ///
    /// TEMP(N279-C): migration bridge for fallback paths where sema array
    /// element `TypeId` is currently unavailable.
    pub(crate) fn prepare_dynamic_array_store_untyped(
        &mut self,
        value: CompiledValue,
    ) -> CodegenResult<(Value, Value, CompiledValue)> {
        let value = if self.vir_query_is_struct_v(value.type_id) {
            self.copy_struct_to_heap(value)?
        } else {
            value
        };
        let tag = self.vir_query_array_element_tag_id_v(value.type_id);
        let tag_val = self.iconst_cached(types::I64, tag);
        if let Some(wide) = crate::types::wide_ops::WideType::from_cranelift_type(value.ty) {
            let i128_bits = wide.to_i128_bits(self.builder, value.value);
            let boxed = self.call_runtime(RuntimeKey::Wide128Box, &[i128_bits])?;
            return Ok((tag_val, boxed, value));
        }
        let payload_bits = crate::structs::convert_to_i64_for_storage(self.builder, &value);
        Ok((tag_val, payload_bits, value))
    }

    /// VirTypeId-native variant of
    /// [`prepare_dynamic_array_store_with_hint`](Self::prepare_dynamic_array_store_with_hint).
    ///
    /// Bridges to the TypeId variant via VirTypeTable reverse lookup.
    pub fn prepare_dynamic_array_store_with_hint_v(
        &mut self,
        value: CompiledValue,
        elem_vir: VirTypeId,
        union_storage_hint: Option<UnionStorageKind>,
    ) -> CodegenResult<(Value, Value, CompiledValue)> {
        let table = &self.env.analyzed.type_table;
        let elem_sema = table.vir_to_type_id(elem_vir);
        self.prepare_dynamic_array_store_with_hint(value, elem_sema, union_storage_hint)
    }

    /// Convert a value to dynamic array storage representation, with an
    /// optional sema-provided union storage hint.
    pub fn prepare_dynamic_array_store_with_hint(
        &mut self,
        value: CompiledValue,
        elem_type_id: TypeId,
        union_storage_hint: Option<UnionStorageKind>,
    ) -> CodegenResult<(Value, Value, CompiledValue)> {
        let mut value = if self.vir_query_is_struct_v(value.type_id) {
            self.copy_struct_to_heap(value)?
        } else {
            value
        };

        let resolved_elem_type = self.try_substitute_type(elem_type_id);
        let resolved_elem_vir = self.vir_lookup_or_compat(resolved_elem_type);
        // Fast path: sema told us whether this is a union element or not.
        // If no hint, fall back to arena check.
        let is_union_elem =
            union_storage_hint.is_some() || self.vir_query_is_union(resolved_elem_type);
        if !is_union_elem {
            // Track whether the value was already unknown before coercion.
            // If so, the value is a heap TaggedValue pointer potentially owned
            // by a scope-cleanup binding. We must clone it so the array gets
            // an independent copy (avoiding use-after-free when the binding's
            // scope cleanup frees the original).
            let was_already_unknown = value.type_id.is_unknown();

            value = self.coerce_to_type(value, resolved_elem_vir)?;

            if was_already_unknown && value.type_id.is_unknown() {
                let cloned = self.call_runtime(RuntimeKey::TaggedValueClone, &[value.value])?;
                value = CompiledValue::new(cloned, self.ptr_type(), value.type_id);
            }

            if let Some(wide) = crate::types::wide_ops::WideType::from_cranelift_type(value.ty) {
                let i128_bits = wide.to_i128_bits(self.builder, value.value);
                let boxed = self.call_runtime(RuntimeKey::Wide128Box, &[i128_bits])?;
                let tag = self.vir_query_array_element_tag_id_v(value.type_id);
                let tag_val = self.iconst_cached(types::I64, tag);
                return Ok((tag_val, boxed, value));
            }
            let tag = self.vir_query_array_element_tag_id_v(value.type_id);
            let tag_val = self.iconst_cached(types::I64, tag);
            let payload_bits = crate::structs::convert_to_i64_for_storage(self.builder, &value);
            return Ok((tag_val, payload_bits, value));
        }

        // Union array element type: use sema hint or compute storage strategy.
        let prefers_inline = match union_storage_hint {
            Some(UnionStorageKind::Inline) => true,
            Some(UnionStorageKind::Heap) => false,
            None => self.union_array_prefers_inline_storage(resolved_elem_type),
        };
        if prefers_inline {
            value = self.coerce_to_type(value, resolved_elem_vir)?;
            if !self.vir_query_is_union_v(value.type_id) {
                return Err(CodegenError::type_mismatch(
                    "array union inline coercion",
                    self.vir_query_display_basic(resolved_elem_type),
                    self.vir_query_display_basic_v(value.type_id),
                ));
            }
            let vir_variants: Vec<VirTypeId> = self
                .vir_query_unwrap_union(resolved_elem_type)
                .expect("INTERNAL: expected union element type");

            let variant_idx = self
                .builder
                .ins()
                .load(types::I8, MemFlags::new(), value.value, 0);
            let runtime_tag = self.union_variant_index_to_array_tag_v(variant_idx, &vir_variants);
            let payload_bits = if self.type_size(resolved_elem_type) > union_layout::TAG_ONLY_SIZE {
                self.builder.ins().load(
                    types::I64,
                    MemFlags::new(),
                    value.value,
                    union_layout::PAYLOAD_OFFSET,
                )
            } else {
                self.iconst_cached(types::I64, 0)
            };
            return Ok((runtime_tag, payload_bits, value));
        }

        // Boxed union storage for ambiguous runtime tags.
        if self.vir_query_is_union_v(value.type_id) {
            value = self.coerce_to_type(value, resolved_elem_vir)?;
            if !self.vir_query_is_union_v(value.type_id) {
                return Err(CodegenError::type_mismatch(
                    "array union boxed coercion",
                    self.vir_query_display_basic(resolved_elem_type),
                    self.vir_query_display_basic_v(value.type_id),
                ));
            }
            value = self.copy_union_to_heap(value)?;
        } else {
            if let Some(subs) = self.substitutions
                && let Some(subst) = self
                    .vir_type_table()
                    .substitute_vir_ids(value.type_id, subs)
            {
                value.type_id = subst;
            }
            value = self.construct_union_heap_id(value, resolved_elem_type)?;
        }

        let tag = self.vir_query_array_element_tag_id_v(value.type_id);
        let tag_val = self.iconst_cached(types::I64, tag);
        let payload_bits = crate::structs::convert_to_i64_for_storage(self.builder, &value);
        Ok((tag_val, payload_bits, value))
    }

    /// Decode a dynamic array union element from `(tag, payload)` storage.
    pub fn decode_dynamic_array_union_element(
        &mut self,
        raw_tag: Value,
        raw_value: Value,
        union_type_id: TypeId,
    ) -> CompiledValue {
        let resolved_union_id = self.try_substitute_type(union_type_id);
        let resolved_vir = self.vir_lookup(resolved_union_id);
        self.decode_dynamic_array_union_element_v(raw_tag, raw_value, resolved_vir)
    }

    /// VirTypeId-native variant of
    /// [`decode_dynamic_array_union_element`](Self::decode_dynamic_array_union_element).
    pub fn decode_dynamic_array_union_element_v(
        &mut self,
        raw_tag: Value,
        raw_value: Value,
        union_vir_ty: VirTypeId,
    ) -> CompiledValue {
        if !self.union_array_prefers_inline_storage_v(union_vir_ty) {
            return self.copy_union_heap_to_stack_v(raw_value, union_vir_ty);
        }

        let vir_variants: Vec<VirTypeId> = self
            .vir_query_unwrap_union_v(union_vir_ty)
            .expect("INTERNAL: expected union type for array decode");

        let union_size = self.type_size_v(union_vir_ty);
        let slot = self.alloc_stack(union_size);
        let variant_idx = self.array_tag_to_union_variant_index_v(raw_tag, &vir_variants);
        self.builder.ins().stack_store(variant_idx, slot, 0);
        if union_size > union_layout::TAG_ONLY_SIZE {
            self.builder
                .ins()
                .stack_store(raw_value, slot, union_layout::PAYLOAD_OFFSET);
        }
        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
        let mut cv = CompiledValue::new(ptr, ptr_type, union_vir_ty);
        cv.mark_borrowed();
        cv
    }

    /// Look up a module export binding by symbol.
    ///
    /// Checks within-function local bindings first, then falls back to the
    /// globally-registered bindings from top-level destructuring imports.
    pub fn lookup_module_binding(&self, sym: &Symbol) -> Option<&ModuleExportBinding> {
        self.local_module_bindings
            .get(sym)
            .or_else(|| self.global_module_bindings.get(sym))
    }

    /// Get capture binding for a symbol, if any
    pub fn get_capture(&self, sym: &Symbol) -> Option<&CaptureBinding> {
        self.captures.as_ref()?.bindings.get(sym)
    }

    /// Get the closure variable, if in a closure context
    pub fn closure_var(&self) -> Option<Variable> {
        self.captures.as_ref().map(|c| c.closure_var)
    }

    // ========== Runtime function helpers ==========

    /// Get a function ID by key, with demand-driven monomorph declaration fallback.
    ///
    /// If the key has no FuncId yet, checks the entity_registry monomorph caches
    /// for a matching instance. If found, declares the function on the spot and
    /// queues it for later compilation via `pending_monomorphs`.
    pub fn func_id(&mut self, key: FunctionKey) -> CodegenResult<FuncId> {
        // Fast path: already declared
        if let Some(id) = self.funcs_ref().func_id(key) {
            return Ok(id);
        }
        // Demand-driven fallback: try to declare from monomorph caches
        if let Some(id) = self.try_demand_declare_monomorph(key) {
            return Ok(id);
        }
        let display = self.funcs_ref().display(key);
        Err(CodegenError::not_found(
            "function id",
            format!("{key:?} ({display})"),
        ))
    }

    /// Get a function reference for calling
    pub fn func_ref(&mut self, key: FunctionKey) -> CodegenResult<cranelift::codegen::ir::FuncRef> {
        let func_id = self.func_id(key)?;
        // Use codegen_ctx directly to avoid borrowing self twice
        let module = self.codegen_ctx.jit_module();
        Ok(module.declare_func_in_func(func_id, self.builder.func))
    }

    /// Get a FuncRef for a runtime function (RuntimeKey -> FuncRef in one call)
    pub fn runtime_func_ref(
        &mut self,
        runtime: RuntimeKey,
    ) -> CodegenResult<cranelift::codegen::ir::FuncRef> {
        let key = self
            .funcs()
            .runtime_key(runtime)
            .ok_or_else(|| CodegenError::not_found("runtime function", runtime.name()))?;
        self.func_ref(key)
    }

    /// Call a runtime function and return the first result (or error if no results).
    ///
    /// Automatically clears `field_cache` after the call — any runtime call may
    /// mutate heap objects, invalidating cached field loads.
    pub fn call_runtime(&mut self, runtime: RuntimeKey, args: &[Value]) -> CodegenResult<Value> {
        let func_ref = self.runtime_func_ref(runtime)?;
        let coerced = self.coerce_call_args(func_ref, args);
        let call = self.builder.ins().call(func_ref, &coerced);
        self.field_cache.clear();
        let results = self.builder.inst_results(call);
        if results.is_empty() {
            Err(CodegenError::internal_with_context(
                "runtime function returned no value",
                runtime.name(),
            ))
        } else {
            Ok(results[0])
        }
    }

    /// Get cached field value or call runtime and cache result
    pub fn get_field_cached(&mut self, instance: Value, slot: u32) -> CodegenResult<Value> {
        let key = (instance, slot);
        if let Some(&cached) = self.field_cache.get(&key) {
            return Ok(cached);
        }
        let slot_val = self.iconst_cached(types::I32, slot as i64);
        let result = self.call_runtime(RuntimeKey::InstanceGetField, &[instance, slot_val])?;
        self.field_cache.insert(key, result);
        Ok(result)
    }

    /// Load an instance field by slot index, handling wide (i128) fields.
    ///
    /// Wide fields occupy 2 consecutive slots and are loaded via `load_wide_field`.
    /// Normal fields use a single `InstanceGetField` runtime call + type conversion.
    /// This is the uncached version for use in destructuring and compound assignment.
    pub fn get_instance_field(
        &mut self,
        instance: Value,
        slot: usize,
        field_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        if let Some(wide) = crate::types::wide_ops::WideType::from_type_id(field_type_id) {
            let get_func_ref = self.runtime_func_ref(RuntimeKey::InstanceGetField)?;
            let wide_i128 =
                crate::structs::helpers::load_wide_field(self, get_func_ref, instance, slot);
            Ok(wide.compiled_value_from_i128(self.builder, wide_i128, field_type_id))
        } else {
            let slot_val = self.iconst_cached(types::I32, slot as i64);
            let result_raw =
                self.call_runtime(RuntimeKey::InstanceGetField, &[instance, slot_val])?;
            Ok(self.convert_field_value(result_raw, field_type_id))
        }
    }

    /// VirTypeId-native variant of `get_instance_field`.
    pub fn get_instance_field_v(
        &mut self,
        instance: Value,
        slot: usize,
        field_vir_ty: VirTypeId,
    ) -> CodegenResult<CompiledValue> {
        if let Some(wide) = self.vir_query_wide_type_v(field_vir_ty) {
            let get_func_ref = self.runtime_func_ref(RuntimeKey::InstanceGetField)?;
            let wide_i128 =
                crate::structs::helpers::load_wide_field(self, get_func_ref, instance, slot);
            Ok(wide.compiled_value_from_i128(self.builder, wide_i128, TypeId::UNKNOWN))
        } else {
            let slot_val = self.iconst_cached(types::I32, slot as i64);
            let result_raw =
                self.call_runtime(RuntimeKey::InstanceGetField, &[instance, slot_val])?;
            Ok(self.convert_field_value_v(result_raw, field_vir_ty))
        }
    }

    /// Return a cached `iconst` value, creating it in the entry block on first use.
    ///
    /// On a hit, returns the previously created `Value`. On a miss, inserts a
    /// new `iconst` instruction into the **entry block** (before its
    /// terminator) via the low-level DFG/layout API, then caches the result.
    ///
    /// Because the entry block dominates every other block, the returned
    /// `Value` is valid at any program point.
    #[inline]
    pub fn iconst_cached(&mut self, ty: Type, val: i64) -> Value {
        if let Some(&v) = self.iconst_cache.get(&(ty, val)) {
            return v;
        }
        let v = self.insert_iconst_in_entry(ty, val);
        self.iconst_cache.insert((ty, val), v);
        v
    }

    /// Insert an `iconst` instruction into the entry block using the
    /// low-level DFG + layout API (bypasses `FunctionBuilder` cursor).
    fn insert_iconst_in_entry(&mut self, ty: Type, val: i64) -> Value {
        // Mask the immediate to the type's bit width, matching the
        // normalization that `InstBuilder::iconst` performs internally
        // via `InstructionData::mask_immediates` (which is pub(crate)).
        let masked = mask_imm_to_type(val, ty);

        let func = &mut self.builder.func;
        let inst = func.dfg.make_inst(InstructionData::UnaryImm {
            opcode: Opcode::Iconst,
            imm: Imm64::new(masked),
        });
        func.dfg.make_inst_results(inst, ty);

        // Place before the entry block's terminator if one exists,
        // otherwise append (we're still building the entry block).
        let entry = self.entry_block;
        if let Some(last) = func.layout.last_inst(entry) {
            if func.dfg.insts[last].opcode().is_branch() {
                func.layout.insert_inst(inst, last);
            } else {
                func.layout.append_inst(inst, entry);
            }
        } else {
            func.layout.append_inst(inst, entry);
        }

        func.dfg.first_result(inst)
    }

    /// Switch the builder to a new basic block, resetting per-block caches.
    ///
    /// All `self.builder.switch_to_block(block)` calls inside `Cg` methods
    /// should go through this wrapper so that per-block caches are
    /// automatically invalidated.
    ///
    /// This is the **SSA dominance** invalidation path for `field_cache`:
    /// cached `Value`s from a sibling block do not dominate the new block
    /// and would cause a Cranelift verifier error ("uses value from
    /// non-dominating inst"). The **mutation** invalidation path lives in
    /// the call-emission helpers (`call_runtime`, `emit_call`, etc.).
    ///
    /// `iconst_cache` is **not** cleared — all cached constants live in the
    /// entry block and dominate every other block.
    pub fn switch_to_block(&mut self, block: Block) {
        self.builder.switch_to_block(block);
        self.field_cache.clear();
    }

    /// Call a runtime function that returns void.
    ///
    /// Automatically clears `field_cache` after the call — any runtime call may
    /// mutate heap objects, invalidating cached field loads.
    pub fn call_runtime_void(&mut self, runtime: RuntimeKey, args: &[Value]) -> CodegenResult<()> {
        let func_ref = self.runtime_func_ref(runtime)?;
        let coerced = self.coerce_call_args(func_ref, args);
        self.builder.ins().call(func_ref, &coerced);
        self.field_cache.clear();
        Ok(())
    }

    /// Emit a direct `call` instruction with arg coercion, returning the `Inst`.
    ///
    /// Use this for user-defined function calls, method calls, and any call to
    /// a `FuncRef` that is not a known-pure runtime helper. The `field_cache`
    /// is cleared automatically — the callee may mutate instance fields.
    pub fn emit_call(
        &mut self,
        func_ref: cranelift::codegen::ir::FuncRef,
        args: &[Value],
    ) -> cranelift::codegen::ir::Inst {
        let coerced = self.coerce_call_args(func_ref, args);
        let inst = self.builder.ins().call(func_ref, &coerced);
        self.field_cache.clear();
        inst
    }

    /// Emit an indirect `call_indirect` instruction, returning the `Inst`.
    ///
    /// Use this for closure calls, interface dispatch, native FFI, or any
    /// indirect call through a function pointer. The `field_cache` is cleared
    /// automatically — the callee may mutate instance fields.
    pub fn emit_call_indirect(
        &mut self,
        sig_ref: cranelift::codegen::ir::SigRef,
        func_ptr: Value,
        args: &[Value],
    ) -> cranelift::codegen::ir::Inst {
        let inst = self.builder.ins().call_indirect(sig_ref, func_ptr, args);
        self.field_cache.clear();
        inst
    }

    // ========== Demand-driven monomorph declaration ==========

    /// Attempt to declare a monomorphized function on demand when its FuncId is missing.
    ///
    /// Uses the pre-built monomorph name index (`state.monomorph_index`) for O(1) lookup
    /// by NameId. If found, builds a Cranelift signature from the instance's codegen-ready
    /// data, declares the function in the JIT module, and queues it in `pending_monomorphs`
    /// for later compilation.
    ///
    /// Returns `Some(FuncId)` if the monomorph was found and declared, `None` otherwise.
    fn try_demand_declare_monomorph(&mut self, key: FunctionKey) -> Option<FuncId> {
        // Only qualified (NameId-based) keys can be monomorphs
        let name_id = self.codegen_ctx.func_registry.name_id(key)?;

        let entry = self.env.state.monomorph_index.get(&name_id)?.clone();
        self.declare_monomorph_from_index(key, &entry)
    }

    /// Declare a monomorph from an index entry: build signature, declare in JIT, queue.
    fn declare_monomorph_from_index(
        &mut self,
        key: FunctionKey,
        entry: &MonomorphIndexEntry,
    ) -> Option<FuncId> {
        let table = self.vir_type_table();
        let ptr_type = self.ptr_type();

        let (func_type, has_self, mangled_name_id, pending, label) = match entry {
            MonomorphIndexEntry::Function(inst) => (
                &inst.func_type,
                false,
                inst.mangled_name,
                PendingMonomorph::Function(inst.clone()),
                "free-function",
            ),
            MonomorphIndexEntry::ClassMethod(inst) => (
                &inst.func_type,
                true,
                inst.mangled_name,
                PendingMonomorph::ClassMethod(inst.clone()),
                "class method",
            ),
            MonomorphIndexEntry::StaticMethod(inst) => (
                &inst.func_type,
                false,
                inst.mangled_name,
                PendingMonomorph::StaticMethod(inst.clone()),
                "static method",
            ),
        };
        let return_type_id = func_type.return_type_id;
        let mangled_name = self.analyzed().display_name(mangled_name_id);

        let sig = build_monomorph_signature(
            func_type,
            has_self,
            table,
            self.analyzed(),
            ptr_type,
            self.codegen_ctx.module,
        );
        let func_id = self
            .codegen_ctx
            .module
            .declare_function(&mangled_name, Linkage::Export, &sig)
            .unwrap_or_else(|e| {
                panic!(
                    "demand-declare {} monomorph '{}': {:?}",
                    label, mangled_name, e
                )
            });
        self.codegen_ctx.func_registry.set_func_id(key, func_id);
        self.codegen_ctx
            .func_registry
            .set_return_type(key, return_type_id);
        self.codegen_ctx.pending_monomorphs.push(pending);
        tracing::debug!(
            name = %mangled_name,
            "demand-declared {label} monomorph"
        );
        Some(func_id)
    }
}

impl<'a, 'b, 'ctx> crate::interfaces::VtableCtx for Cg<'a, 'b, 'ctx> {
    fn analyzed(&self) -> &vole_vir::VirProgram {
        self.env.analyzed
    }

    fn interner(&self) -> &vole_identity::Interner {
        self.env.interner
    }

    fn ptr_type(&self) -> Type {
        self.codegen_ctx.ptr_type()
    }

    fn jit_module(&mut self) -> &mut cranelift_jit::JITModule {
        self.codegen_ctx.jit_module()
    }

    fn funcs(&mut self) -> &mut crate::FunctionRegistry {
        self.codegen_ctx.funcs()
    }

    fn native_registry(&self) -> &vole_runtime::NativeRegistry {
        &self.env.state.native_registry
    }

    fn type_metadata(&self) -> &TypeMetadataMap {
        &self.env.state.type_metadata
    }

    fn method_func_keys(&self) -> &FxHashMap<(NameId, NameId), FunctionKey> {
        &self.env.state.method_func_keys
    }

    fn ptr_to_symbol(&self) -> &FxHashMap<usize, String> {
        &self.env.state.ptr_to_symbol
    }

    fn jit_module_and_funcs(
        &mut self,
    ) -> (&mut cranelift_jit::JITModule, &mut crate::FunctionRegistry) {
        (self.codegen_ctx.module, self.codegen_ctx.func_registry)
    }
}

/// Mask an `i64` immediate to the bit width of a Cranelift integer type.
///
/// Reproduces the normalization that `InstructionData::mask_immediates`
/// (pub(crate) in cranelift-codegen) performs so that the verifier sees a
/// zero-extended bit pattern when the type is narrower than 64 bits.
fn mask_imm_to_type(val: i64, ty: Type) -> i64 {
    let bits = ty.bits();
    if bits >= 64 {
        return val;
    }
    let mask = (1i64 << bits) - 1;
    val & mask
}

/// Resolve the module path and native function name strings from an external method reference.
pub(crate) fn resolve_external_names(
    name_table: &vole_identity::NameTable,
    external_info: &ExternalMethodRef,
) -> CodegenResult<(String, String)> {
    let module_path = name_table
        .last_segment_str(external_info.module_path)
        .ok_or_else(|| CodegenError::internal("module_path NameId has no segment"))?;
    let native_name = name_table
        .last_segment_str(external_info.native_name)
        .ok_or_else(|| CodegenError::internal("native_name NameId has no segment"))?;
    Ok((module_path, native_name))
}

/// Build a Cranelift signature for a monomorph instance using its codegen-ready data.
///
/// Replicates the logic of `Compiler::build_signature_from_type_ids` but operates
/// on raw references to the arena, registry, and JIT module — no `Compiler` needed.
///
/// Handles:
/// - Self pointer for class methods (`has_self_param`)
/// - Fallible return types (multi-value: tag + payload, or 3-register for wide i128)
/// - Struct return types (multi-value for small structs, sret pointer for large structs)
fn build_monomorph_signature(
    func_type: &vole_identity::FunctionType,
    has_self_param: bool,
    table: &vole_vir::type_table::VirTypeTable,
    analyzed: &vole_vir::VirProgram,
    ptr_type: Type,
    module: &cranelift_jit::JITModule,
) -> cranelift::prelude::Signature {
    use crate::types::vir_conversions::vir_type_to_cranelift;

    let vir_lookup = |tid: TypeId| -> VirTypeId {
        table.lookup_type_id(tid).unwrap_or_else(|| {
            debug_assert!(
                false,
                "TypeId({}) not in VirTypeTable for signature",
                tid.raw()
            );
            VirTypeId::UNKNOWN
        })
    };

    let mut sig = module.make_signature();

    // Self pointer for class methods
    if has_self_param {
        sig.params.push(AbiParam::new(ptr_type));
    }

    // Parameter types
    for &param_type_id in &func_type.params_id {
        let vir_ty = vir_lookup(param_type_id);
        let cranelift_type = vir_type_to_cranelift(vir_ty, table, ptr_type);
        sig.params.push(AbiParam::new(cranelift_type));
    }

    let return_type_id = func_type.return_type_id;
    let ret_vir = vir_lookup(return_type_id);

    // Fallible return type -> multi-value returns (dispatched via ReturnAbi)
    let abi = vole_vir::func::ReturnAbi::classify(ret_vir, table);
    if matches!(
        abi,
        vole_vir::func::ReturnAbi::Fallible | vole_vir::func::ReturnAbi::WideFallible
    ) {
        if abi == vole_vir::func::ReturnAbi::WideFallible {
            // Wide fallible (i128 success): (tag: i64, low: i64, high: i64)
            sig.returns.push(AbiParam::new(types::I64));
            sig.returns.push(AbiParam::new(types::I64));
            sig.returns.push(AbiParam::new(types::I64));
        } else {
            // Fallible returns: (tag: i64, payload: i64)
            sig.returns.push(AbiParam::new(types::I64));
            sig.returns.push(AbiParam::new(types::I64));
        }
        return sig;
    }

    // Struct return type -> multi-value or sret
    if let Some(field_count) =
        crate::types::vir_struct_helpers::vir_struct_flat_slot_count(ret_vir, table, analyzed)
    {
        if field_count <= crate::MAX_SMALL_STRUCT_FIELDS {
            // Small struct: return in registers, padded to MAX_SMALL_STRUCT_FIELDS
            for _ in 0..crate::MAX_SMALL_STRUCT_FIELDS {
                sig.returns.push(AbiParam::new(types::I64));
            }
        } else {
            // Large struct: sret convention — hidden first param for return buffer
            // Insert the sret pointer before all other params
            sig.params.insert(0, AbiParam::new(ptr_type));
            sig.returns.push(AbiParam::new(ptr_type));
        }
        return sig;
    }

    // Normal return type
    if !return_type_id.is_void() {
        let ret_cranelift = vir_type_to_cranelift(ret_vir, table, ptr_type);
        sig.returns.push(AbiParam::new(ret_cranelift));
    }

    sig
}
