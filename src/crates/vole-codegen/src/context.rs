// src/codegen/context.rs
//
// Unified codegen context - bundles all state needed during code generation.
// Methods are implemented across multiple files using split impl blocks.

use std::cell::RefCell;
use std::mem::size_of;
use std::rc::Rc;

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
use vole_frontend::{Expr, Symbol};
use vole_identity::{ModuleId, NameId};
use vole_sema::implement_registry::ExternalMethodInfo;
use vole_sema::type_arena::TypeId;

use super::lambda::CaptureBinding;
use super::rc_cleanup::RcScopeStack;
use super::rc_state::RcState;
use super::types::{
    CodegenCtx, CompileEnv, CompiledValue, MonomorphIndexEntry, PendingMonomorph, TypeMetadataMap,
};

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
    pub vars: FxHashMap<Symbol, (Variable, TypeId)>,
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
    pub return_type: Option<TypeId>,
    /// Module being compiled (None for main program)
    pub current_module: Option<ModuleId>,
    /// Type parameter substitutions for monomorphized generics
    pub substitutions: Option<&'a FxHashMap<NameId, TypeId>>,
    /// Backend selection policy for dual runtime/intrinsic callables.
    pub(crate) callable_backend_preference: CallableBackendPreference,
    /// Cache for substituted types
    pub(crate) substitution_cache: RefCell<FxHashMap<TypeId, TypeId>>,
    /// Cache for RC state computations
    pub(crate) rc_state_cache: RefCell<FxHashMap<TypeId, RcState>>,
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
    /// True when compiling an Iterable default method body (e.g. `__array_iterable_4_map`).
    ///
    /// In these compiled bodies, closure parameters (like `f` in `fn map(f)`) are owned by
    /// the body — the outer caller transferred ownership without emitting rc_dec (due to
    /// `used_array_iterable_path`). This means:
    ///   - For pipeline methods (map/filter): do NOT emit rc_inc for borrowed closure params
    ///     (the iterator gets the single reference and frees it on drop)
    ///   - For terminal methods (any/all/find): DO emit rc_dec after the runtime call
    ///     (the runtime borrows the closure but doesn't free it; codegen must)
    ///
    /// When false (regular user code), closure params are borrowed — the CALLER retains
    /// ownership and will dec_ref them. Pipeline methods must rc_inc to get their own ref.
    pub in_iterable_default_body: bool,
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
            current_module: None,
            substitutions: None,
            callable_backend_preference: CallableBackendPreference::PreferInline,
            substitution_cache: RefCell::new(FxHashMap::default()),
            rc_state_cache: RefCell::new(FxHashMap::default()),
            // No clone: local_module_bindings starts empty for within-function inserts.
            // Global bindings are accessed via the read-only reference below.
            local_module_bindings: FxHashMap::default(),
            global_module_bindings: env.global_module_bindings,
            rc_scopes: RcScopeStack::new(),
            yielder_var: None,
            in_iterable_default_body: false,
            cached_void_val,
            entry_block,
            iconst_cache,
            codegen_ctx,
            env,
        }
    }

    /// Set closure captures (None = no captures).
    pub fn with_captures(mut self, captures: Option<Captures<'a>>) -> Self {
        self.captures = captures;
        self
    }

    /// Set the return type.
    pub fn with_return_type(mut self, return_type: Option<TypeId>) -> Self {
        self.return_type = return_type;
        self
    }

    /// Set the current module.
    pub fn with_module(mut self, module_id: Option<ModuleId>) -> Self {
        self.current_module = module_id;
        self
    }

    /// Set type parameter substitutions for monomorphized generics.
    pub fn with_substitutions(mut self, subs: Option<&'a FxHashMap<NameId, TypeId>>) -> Self {
        self.substitutions = subs;
        self
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

    /// Set backend preference for dual runtime/intrinsic callables.
    pub fn with_callable_backend_preference(
        mut self,
        preference: CallableBackendPreference,
    ) -> Self {
        self.callable_backend_preference = preference;
        self
    }

    /// Set pre-populated variables (for cases where params are bound before Cg creation).
    pub fn with_vars(mut self, vars: FxHashMap<Symbol, (Variable, TypeId)>) -> Self {
        self.vars = vars;
        self
    }

    /// Check if we're in a closure context with captures
    pub fn has_captures(&self) -> bool {
        self.captures.is_some()
    }

    // ========== Context accessors ==========

    /// Get current module (as ModuleId)
    #[inline]
    pub fn current_module_id(&self) -> Option<ModuleId> {
        self.current_module
    }

    /// Get entity registry reference
    #[inline]
    pub fn registry(&self) -> &'ctx vole_sema::entity_registry::EntityRegistry {
        self.env.analyzed.entity_registry()
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

    /// Get the query interface for the analyzed program.
    /// Returns ProgramQuery<'ctx> so that references obtained from it
    /// have the full `'ctx` lifetime, enabling them to outlive `self` borrows.
    #[inline]
    pub fn query(&self) -> vole_sema::ProgramQuery<'ctx> {
        self.env.analyzed.query()
    }

    /// Get the type arena.
    /// Returns `&'ctx TypeArena` so that references obtained from it
    /// have the full `'ctx` lifetime, enabling them to outlive `self` borrows.
    #[inline]
    pub fn arena(&self) -> &'ctx vole_sema::type_arena::TypeArena {
        self.env.analyzed.type_arena()
    }

    /// Get expression type by NodeId.
    ///
    /// NodeIds are globally unique (they embed a ModuleId), so a single flat
    /// lookup covers both main-program and module nodes.
    #[inline]
    pub fn get_expr_type(&self, node_id: &vole_frontend::NodeId) -> Option<TypeId> {
        self.env.analyzed.node_map.get_type(*node_id)
    }

    /// Get expression type by NodeId, applying type param substitution for module code.
    ///
    /// This is used when the expression type needs to be concrete (e.g., for return types,
    /// call results). Module code stores generic types (e.g., `V`) which must be substituted
    /// to concrete types (e.g., `i64`) in monomorphized contexts.
    #[inline]
    pub fn get_expr_type_substituted(&self, node_id: &vole_frontend::NodeId) -> Option<TypeId> {
        let ty = self.get_expr_type(node_id)?;
        if self.current_module.is_some() && self.substitutions.is_some() {
            Some(self.try_substitute_type(ty))
        } else {
            Some(ty)
        }
    }

    /// Get IsCheckResult for an is-expression or type pattern.
    #[inline]
    pub fn get_is_check_result(
        &self,
        node_id: vole_frontend::NodeId,
    ) -> Option<vole_sema::IsCheckResult> {
        self.env.analyzed.node_map.get_is_check_result(node_id)
    }

    /// Get lambda analysis results (captures and side effects) for a lambda expression
    #[inline]
    pub fn get_lambda_analysis(
        &self,
        node_id: vole_frontend::NodeId,
    ) -> Option<&vole_sema::LambdaAnalysis> {
        self.env.analyzed.node_map.get_lambda_analysis(node_id)
    }

    /// Get the compact info for an implicit `it`-expression, if one was synthesized.
    #[inline]
    pub fn get_it_lambda_info(
        &self,
        node_id: vole_frontend::NodeId,
    ) -> Option<&vole_sema::ItLambdaInfo> {
        self.env.analyzed.node_map.get_it_lambda_info(node_id)
    }

    /// Get the optional chain info for an optional chain expression.
    #[inline]
    pub fn get_optional_chain(
        &self,
        node_id: vole_frontend::NodeId,
    ) -> Option<&vole_sema::OptionalChainInfo> {
        self.env.analyzed.node_map.get_optional_chain(node_id)
    }

    /// Get substituted return type for generic method calls.
    #[inline]
    pub fn get_substituted_return_type(&self, node_id: &vole_frontend::NodeId) -> Option<TypeId> {
        self.env
            .analyzed
            .node_map
            .get_substituted_return_type(*node_id)
            .map(|ty| self.try_substitute_type(ty))
    }

    /// Get declared variable type for let statements with explicit type annotations.
    /// Used for union wrapping, numeric widening, and interface boxing.
    #[inline]
    pub fn get_declared_var_type(&self, init_node_id: &vole_frontend::NodeId) -> Option<TypeId> {
        self.env
            .analyzed
            .node_map
            .get_declared_var_type(*init_node_id)
    }

    /// Get the iterable kind annotation for a for-loop's iterable expression.
    #[inline]
    pub fn get_iterable_kind(
        &self,
        iterable_node_id: vole_frontend::NodeId,
    ) -> Option<vole_sema::IterableKind> {
        self.env
            .analyzed
            .node_map
            .get_iterable_kind(iterable_node_id)
    }

    /// Get the coercion kind annotation for a method call expression.
    #[inline]
    pub fn get_coercion_kind(
        &self,
        expr_node_id: vole_frontend::NodeId,
    ) -> Option<vole_sema::CoercionKind> {
        self.env.analyzed.node_map.get_coercion_kind(expr_node_id)
    }

    /// Get the string conversion annotation for an interpolation expression part.
    #[inline]
    pub fn get_string_conversion(
        &self,
        expr_node_id: vole_frontend::NodeId,
    ) -> Option<&vole_sema::StringConversion> {
        self.env
            .analyzed
            .node_map
            .get_string_conversion(expr_node_id)
    }

    /// Get type metadata map
    #[inline]
    pub fn type_metadata(&self) -> &'ctx TypeMetadataMap {
        &self.env.state.type_metadata
    }

    /// Get global variable initializer by name
    #[inline]
    pub fn global_init(&self, name: Symbol) -> Option<&Rc<Expr>> {
        self.env.global_inits.get(&name)
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
    pub fn interner(&self) -> &'ctx vole_frontend::Interner {
        self.env.interner
    }

    /// Get unified method function key map
    /// Keyed by (type_name_id, method_name_id) for stable lookup across analyzer instances
    #[inline]
    pub fn method_func_keys(&self) -> &'ctx FxHashMap<(NameId, NameId), FunctionKey> {
        &self.env.state.method_func_keys
    }

    /// Get array Iterable default method key map.
    /// Keyed by (method_name_id, elem_type_id) for per-element-type lookup.
    #[inline]
    pub fn array_iterable_func_keys(&self) -> &'ctx FxHashMap<(NameId, TypeId), FunctionKey> {
        &self.env.state.array_iterable_func_keys
    }

    /// Get monomorph cache from entity registry
    #[inline]
    pub fn monomorph_cache(&self) -> &'ctx vole_sema::generic::MonomorphCache {
        &self.env.analyzed.entity_registry().monomorph_cache
    }

    /// Get current module as Option<ModuleId> - use current_module_id() for new code
    #[inline]
    pub fn current_module(&self) -> Option<ModuleId> {
        self.current_module
    }

    /// Get analyzed program reference
    #[inline]
    pub fn analyzed(&self) -> &'ctx crate::AnalyzedProgram {
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
    pub fn prepare_dynamic_array_store(
        &mut self,
        value: CompiledValue,
        elem_type_id: TypeId,
    ) -> CodegenResult<(Value, Value, CompiledValue)> {
        let mut value = if self.arena().is_struct(value.type_id) {
            self.copy_struct_to_heap(value)?
        } else {
            value
        };

        let resolved_elem_type = self.try_substitute_type(elem_type_id);
        if !self.arena().is_union(resolved_elem_type) {
            value = self.coerce_to_type(value, resolved_elem_type)?;
            if let Some(wide) = crate::types::wide_ops::WideType::from_cranelift_type(value.ty) {
                let i128_bits = wide.to_i128_bits(self.builder, value.value);
                let boxed = self.call_runtime(RuntimeKey::Wide128Box, &[i128_bits])?;
                let tag = {
                    let arena = self.arena();
                    crate::types::array_element_tag_id(value.type_id, arena)
                };
                let tag_val = self.iconst_cached(types::I64, tag);
                return Ok((tag_val, boxed, value));
            }
            let tag = {
                let arena = self.arena();
                crate::types::array_element_tag_id(value.type_id, arena)
            };
            let tag_val = self.iconst_cached(types::I64, tag);
            let payload_bits = crate::structs::convert_to_i64_for_storage(self.builder, &value);
            return Ok((tag_val, payload_bits, value));
        }

        // Union array element type: choose storage strategy by tag uniqueness.
        if self.union_array_prefers_inline_storage(resolved_elem_type) {
            value = self.coerce_to_type(value, resolved_elem_type)?;
            if !self.arena().is_union(value.type_id) {
                return Err(CodegenError::type_mismatch(
                    "array union inline coercion",
                    self.arena().display_basic(resolved_elem_type),
                    self.arena().display_basic(value.type_id),
                ));
            }
            let variants = self
                .arena()
                .unwrap_union(resolved_elem_type)
                .expect("INTERNAL: expected union element type")
                .clone();

            let variant_idx = self
                .builder
                .ins()
                .load(types::I8, MemFlags::new(), value.value, 0);
            let runtime_tag = self.union_variant_index_to_array_tag(variant_idx, &variants);
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
        if self.arena().is_union(value.type_id) {
            value = self.coerce_to_type(value, resolved_elem_type)?;
            if !self.arena().is_union(value.type_id) {
                return Err(CodegenError::type_mismatch(
                    "array union boxed coercion",
                    self.arena().display_basic(resolved_elem_type),
                    self.arena().display_basic(value.type_id),
                ));
            }
            value = self.copy_union_to_heap(value)?;
        } else {
            value.type_id = self.try_substitute_type(value.type_id);
            value = self.construct_union_heap_id(value, resolved_elem_type)?;
        }

        let tag = {
            let arena = self.arena();
            crate::types::array_element_tag_id(value.type_id, arena)
        };
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
        if !self.union_array_prefers_inline_storage(resolved_union_id) {
            return self.copy_union_heap_to_stack(raw_value, resolved_union_id);
        }

        let variants = self
            .arena()
            .unwrap_union(resolved_union_id)
            .expect("INTERNAL: expected union type for array decode")
            .clone();

        let union_size = self.type_size(resolved_union_id);
        let slot = self.alloc_stack(union_size);
        let variant_idx = self.array_tag_to_union_variant_index(raw_tag, &variants);
        self.builder.ins().stack_store(variant_idx, slot, 0);
        if union_size > union_layout::TAG_ONLY_SIZE {
            self.builder
                .ins()
                .stack_store(raw_value, slot, union_layout::PAYLOAD_OFFSET);
        }
        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
        let mut cv = CompiledValue::new(ptr, ptr_type, resolved_union_id);
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
        if let Some(wide) =
            crate::types::wide_ops::WideType::from_type_id(field_type_id, self.arena())
        {
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
        let registry = self.registry();
        let arena = self.arena();
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
        let mangled_name = self.query().display_name(mangled_name_id);

        let sig = build_monomorph_signature(
            func_type,
            has_self,
            arena,
            registry,
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
    fn analyzed(&self) -> &crate::AnalyzedProgram {
        self.env.analyzed
    }

    fn arena(&self) -> &vole_sema::type_arena::TypeArena {
        self.env.analyzed.type_arena()
    }

    fn registry(&self) -> &vole_sema::EntityRegistry {
        self.env.analyzed.entity_registry()
    }

    fn interner(&self) -> &vole_frontend::Interner {
        self.env.interner
    }

    fn query(&self) -> vole_sema::ProgramQuery<'_> {
        self.env.analyzed.query()
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

/// Resolve the module path and native function name strings from an ExternalMethodInfo.
pub(crate) fn resolve_external_names(
    name_table: &vole_identity::NameTable,
    external_info: &ExternalMethodInfo,
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
    func_type: &vole_sema::types::FunctionType,
    has_self_param: bool,
    arena: &vole_sema::type_arena::TypeArena,
    registry: &vole_sema::EntityRegistry,
    ptr_type: Type,
    module: &cranelift_jit::JITModule,
) -> cranelift::prelude::Signature {
    use crate::types::{is_wide_fallible, type_id_to_cranelift};

    let mut sig = module.make_signature();

    // Self pointer for class methods
    if has_self_param {
        sig.params.push(AbiParam::new(ptr_type));
    }

    // Parameter types
    for &param_type_id in &func_type.params_id {
        let cranelift_type = type_id_to_cranelift(param_type_id, arena, ptr_type);
        sig.params.push(AbiParam::new(cranelift_type));
    }

    let return_type_id = func_type.return_type_id;

    // Fallible return type -> multi-value returns
    if arena.unwrap_fallible(return_type_id).is_some() {
        if is_wide_fallible(return_type_id, arena) {
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
        crate::structs::struct_flat_slot_count(return_type_id, arena, registry)
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
        let ret_cranelift = type_id_to_cranelift(return_type_id, arena, ptr_type);
        sig.returns.push(AbiParam::new(ret_cranelift));
    }

    sig
}
