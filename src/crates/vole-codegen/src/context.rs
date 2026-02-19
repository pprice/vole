// src/codegen/context.rs
//
// Unified codegen context - bundles all state needed during code generation.
// Methods are implemented across multiple files using split impl blocks.

use std::cell::RefCell;
use std::mem::size_of;
use std::rc::Rc;

use cranelift::prelude::{
    Block, FunctionBuilder, InstBuilder, MemFlags, Type, Value, Variable, types,
};
use cranelift_module::{FuncId, Module};
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
use super::types::{CodegenCtx, CompileEnv, CompiledValue, TypeMetadataMap};

/// Dereference a raw `*const Expr` pointer from the AST.
///
/// All such pointers originate from `EntityRegistry` or `Program` AST nodes,
/// both owned by `AnalyzedProgram`. Because `AnalyzedProgram` outlives the
/// entire compilation session and its data is never moved or modified, the
/// pointer remains valid for the duration of compilation.
///
/// This is a free function (rather than a method on `Cg`) so the returned
/// reference does not borrow `self`, which would conflict with the `&mut self`
/// needed by expression-compilation methods.
#[inline]
pub(crate) fn deref_expr_ptr(ptr: *const Expr) -> &'static Expr {
    // SAFETY: All callers obtain these pointers from AnalyzedProgram's
    // EntityRegistry or Program AST, which outlive the Cg instance and
    // persist for the entire compilation session. The data is never
    // moved or modified.
    unsafe { &*ptr }
}

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

    pub fn push_loop(
        &mut self,
        exit: Block,
        cont: Block,
        rc_scope_depth: usize,
    ) {
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
    /// Cache for field access: (instance_ptr, slot) -> field_value
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
    /// Module export bindings from destructuring imports: local_name -> (module_id, export_name, type_id)
    pub module_bindings: FxHashMap<Symbol, ModuleExportBinding>,
    /// RC scope stack for drop flag tracking and cleanup emission
    pub rc_scopes: RcScopeStack,
    /// Yielder pointer variable for generator body functions.
    /// When set, `ExprKind::Yield` compiles to `vole_generator_yield(yielder, value)`.
    pub yielder_var: Option<Variable>,
    /// Cached `iconst.i64 0` created in the entry block for void returns.
    /// Reused by every `void_value()` call to avoid emitting thousands of
    /// dead iconst instructions (previously ~18,951 per compilation).
    pub(crate) cached_void_val: Value,
    /// Per-block iconst cache: `(Type, i64) -> Value`.
    ///
    /// Avoids emitting duplicate `iconst` instructions within the same basic
    /// block.  Cleared on every block switch (`switch_to_block`) because SSA
    /// values defined in one block may not dominate a sibling block.
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
        // Emit a single `iconst.i64 0` in the entry block (where the cursor is
        // at construction time). Because the entry block dominates every other
        // block, this value can be reused by all subsequent `void_value()` calls
        // without violating SSA dominance.
        let cached_void_val = builder.ins().iconst(types::I64, 0);
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
            // Initialize with global module bindings from top-level destructuring imports
            module_bindings: env.global_module_bindings.clone(),
            rc_scopes: RcScopeStack::new(),
            yielder_var: None,
            cached_void_val,
            iconst_cache: FxHashMap::default(),
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

    /// Get the name table
    #[inline]
    pub fn name_table(&self) -> &vole_identity::NameTable {
        self.env.analyzed.name_table()
    }

    /// Get the pointer type (Cranelift platform pointer)
    #[inline]
    pub fn ptr_type(&self) -> Type {
        self.codegen_ctx.ptr_type()
    }

    /// Get the query interface for the analyzed program
    #[inline]
    pub fn query(&self) -> vole_sema::ProgramQuery<'_> {
        self.env.analyzed.query()
    }

    /// Get the type arena
    #[inline]
    pub fn arena(&self) -> &vole_sema::type_arena::TypeArena {
        self.env.analyzed.type_arena()
    }

    /// Get expression type by NodeId (checks module-specific types if in module context)
    #[inline]
    pub fn get_expr_type(&self, node_id: &vole_frontend::NodeId) -> Option<TypeId> {
        // For module code, check module-specific expr_types first
        if let Some(module_id) = self.current_module {
            let name_table = self.name_table();
            let module_path = name_table.module_path(module_id);
            if let Some(module_types) = self
                .env
                .analyzed
                .query()
                .expr_data()
                .module_types(module_path)
            {
                // Module has its own type map — use it exclusively.
                // NodeIds are per-program, so falling through to the main program's
                // types would return wrong types for coincidentally matching NodeIds.
                return module_types.get(node_id).copied();
            }
        }
        // Fall back to main program expr_types
        self.env.analyzed.query().expr_data().get_type(*node_id)
    }

    /// Get expression type by NodeId, applying type param substitution for module code.
    ///
    /// This is used when the expression type needs to be concrete (e.g., for return types,
    /// call results). Module code stores generic types (e.g., `V`) which must be substituted
    /// to concrete types (e.g., `i64`) in monomorphized contexts.
    ///
    /// Falls back to `lookup_substitute` which returns None if the substituted type
    /// doesn't exist in the arena. In that case, returns the original type.
    #[inline]
    pub fn get_expr_type_substituted(&self, node_id: &vole_frontend::NodeId) -> Option<TypeId> {
        let ty = self.get_expr_type(node_id)?;
        if self.current_module.is_some() && self.substitutions.is_some() {
            Some(self.try_substitute_type(ty))
        } else {
            Some(ty)
        }
    }

    /// Get IsCheckResult for an is-expression or type pattern, checking module-specific results first
    #[inline]
    pub fn get_is_check_result(
        &self,
        node_id: vole_frontend::NodeId,
    ) -> Option<vole_sema::IsCheckResult> {
        let module_path = self.current_module.map(|mid| {
            let name_table = self.name_table();
            name_table.module_path(mid).to_string()
        });
        self.env
            .analyzed
            .query()
            .expr_data()
            .get_is_check_result_in_module(node_id, module_path.as_deref())
    }

    /// Get lambda analysis results (captures and side effects) for a lambda expression
    #[inline]
    pub fn get_lambda_analysis(
        &self,
        node_id: vole_frontend::NodeId,
    ) -> Option<&vole_sema::LambdaAnalysis> {
        let module_path = self.current_module.map(|mid| {
            let name_table = self.name_table();
            name_table.module_path(mid).to_string()
        });
        self.env
            .analyzed
            .query()
            .expr_data()
            .get_lambda_analysis_in_module(node_id, module_path.as_deref())
    }

    /// Get substituted return type for generic method calls
    #[inline]
    pub fn get_substituted_return_type(&self, node_id: &vole_frontend::NodeId) -> Option<TypeId> {
        // Module NodeIds are file-local. The sema substituted_return_types map is currently
        // global, so looking it up directly in module context can collide with unrelated
        // main-program NodeIds and produce wrong return types. For module code, use the
        // module-local expression type map (with substitution) instead.
        if self.current_module.is_some() {
            return self.get_expr_type_substituted(node_id);
        }

        self.env
            .analyzed
            .query()
            .expr_data()
            .get_substituted_return_type(*node_id)
            .map(|ty| self.try_substitute_type(ty))
    }

    /// Get declared variable type for let statements with explicit type annotations.
    /// Used for union wrapping, numeric widening, and interface boxing.
    /// For module code, checks module-specific declared_var_types only.
    #[inline]
    pub fn get_declared_var_type(&self, init_node_id: &vole_frontend::NodeId) -> Option<TypeId> {
        if let Some(module_id) = self.current_module {
            let name_table = self.name_table();
            let module_path = name_table.module_path(module_id);
            // Only check module-specific map — NodeIds collide across modules,
            // so falling through to main program's map would return wrong types.
            return self
                .env
                .analyzed
                .query()
                .expr_data()
                .get_module_declared_var_type(module_path, *init_node_id);
        }
        self.env
            .analyzed
            .query()
            .expr_data()
            .get_declared_var_type(*init_node_id)
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
            if value.ty == types::I128 || value.ty == types::F128 {
                let wide_bits = if value.ty == types::F128 {
                    self.builder
                        .ins()
                        .bitcast(types::I128, MemFlags::new(), value.value)
                } else {
                    value.value
                };
                let boxed = self.call_runtime(RuntimeKey::Wide128Box, &[wide_bits])?;
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

    /// Get capture binding for a symbol, if any
    pub fn get_capture(&self, sym: &Symbol) -> Option<&CaptureBinding> {
        self.captures.as_ref()?.bindings.get(sym)
    }

    /// Get the closure variable, if in a closure context
    pub fn closure_var(&self) -> Option<Variable> {
        self.captures.as_ref().map(|c| c.closure_var)
    }

    // ========== Runtime function helpers ==========

    /// Get a function ID by key
    pub fn func_id(&self, key: FunctionKey) -> CodegenResult<FuncId> {
        let display = self.funcs_ref().display(key);
        self.funcs_ref()
            .func_id(key)
            .ok_or_else(|| CodegenError::not_found("function id", format!("{key:?} ({display})")))
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

    /// Call a runtime function and return the first result (or error if no results)
    pub fn call_runtime(&mut self, runtime: RuntimeKey, args: &[Value]) -> CodegenResult<Value> {
        let func_ref = self.runtime_func_ref(runtime)?;
        let coerced = self.coerce_call_args(func_ref, args);
        let call = self.builder.ins().call(func_ref, &coerced);
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
        if crate::types::is_wide_type(field_type_id, self.arena()) {
            let get_func_ref = self.runtime_func_ref(RuntimeKey::InstanceGetField)?;
            let wide_i128 = crate::structs::helpers::load_wide_field(
                self.builder,
                get_func_ref,
                instance,
                slot,
            );
            let arena = self.arena();
            if field_type_id == arena.f128() {
                let value = self
                    .builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), wide_i128);
                Ok(CompiledValue::new(value, types::F128, field_type_id))
            } else {
                Ok(CompiledValue::new(wide_i128, types::I128, field_type_id))
            }
        } else {
            let slot_val = self.iconst_cached(types::I32, slot as i64);
            let result_raw =
                self.call_runtime(RuntimeKey::InstanceGetField, &[instance, slot_val])?;
            Ok(self.convert_field_value(result_raw, field_type_id))
        }
    }

    /// Emit or reuse a cached `iconst` instruction in the current basic block.
    ///
    /// Looks up `(ty, val)` in the per-block cache. On a miss, emits
    /// `builder.ins().iconst(ty, val)` and stores the result. On a hit,
    /// returns the previously emitted `Value`, eliminating a redundant
    /// instruction.
    #[inline]
    pub fn iconst_cached(&mut self, ty: Type, val: i64) -> Value {
        if let Some(&v) = self.iconst_cache.get(&(ty, val)) {
            return v;
        }
        let v = self.builder.ins().iconst(ty, val);
        self.iconst_cache.insert((ty, val), v);
        v
    }

    /// Switch the builder to a new basic block, clearing per-block caches.
    ///
    /// All `self.builder.switch_to_block(block)` calls inside `Cg` methods
    /// should go through this wrapper so that the iconst cache (and any future
    /// per-block caches) are automatically invalidated.
    pub fn switch_to_block(&mut self, block: Block) {
        self.builder.switch_to_block(block);
        self.iconst_cache.clear();
    }

    /// Invalidate value caches when entering a control flow branch.
    ///
    /// The `field_cache` and `iconst_cache` store Cranelift SSA `Value`s that
    /// are defined in a particular basic block.  When the builder switches to a
    /// sibling block (e.g., the next arm of a `when`/`match`/`if` expression),
    /// values cached from a previous arm do **not** dominate the new block,
    /// so reusing them would produce a Cranelift verifier error
    /// ("uses value from non-dominating inst").
    ///
    /// Call this at the start of each arm body in any branching construct.
    pub fn invalidate_value_caches(&mut self) {
        self.field_cache.clear();
        self.iconst_cache.clear();
    }

    /// Call a runtime function that returns void
    pub fn call_runtime_void(&mut self, runtime: RuntimeKey, args: &[Value]) -> CodegenResult<()> {
        let func_ref = self.runtime_func_ref(runtime)?;
        let coerced = self.coerce_call_args(func_ref, args);
        self.builder.ins().call(func_ref, &coerced);
        Ok(())
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
