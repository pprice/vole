// src/codegen/context.rs
//
// Unified codegen context - bundles all state needed during code generation.
// Methods are implemented across multiple files using split impl blocks.

use std::cell::RefCell;
use std::mem::size_of;
use std::rc::Rc;

use cranelift::prelude::{
    FunctionBuilder, InstBuilder, IntCC, MemFlags, StackSlotData, StackSlotKind, Type, Value,
    Variable, types,
};
use cranelift_codegen::ir::StackSlot;
use cranelift_module::{FuncId, Module};
use rustc_hash::FxHashMap;

use crate::callable_registry::CallableBackendPreference;
use crate::errors::{CodegenError, CodegenResult};
use crate::union_layout;
use crate::{FunctionKey, RuntimeKey};
use smallvec::SmallVec;
use vole_frontend::{Expr, Symbol};
use vole_identity::{ModuleId, NameId};
use vole_sema::PrimitiveType;
use vole_sema::implement_registry::ExternalMethodInfo;
use vole_sema::type_arena::{SemaType as ArenaType, TypeId};

use super::lambda::CaptureBinding;
use super::rc_cleanup::RcScopeStack;
use super::rc_state::RcState;
use super::types::{CodegenCtx, CompileEnv, CompiledValue, TypeMetadataMap};

/// Control flow context for loops (break/continue targets)
pub(crate) struct ControlFlow {
    /// Stack of loop exit blocks for break statements
    loop_exits: Vec<cranelift::prelude::Block>,
    /// Stack of loop continue blocks for continue statements
    loop_continues: Vec<cranelift::prelude::Block>,
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
        exit: cranelift::prelude::Block,
        cont: cranelift::prelude::Block,
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

    pub fn loop_exit(&self) -> Option<cranelift::prelude::Block> {
        self.loop_exits.last().copied()
    }

    pub fn loop_continue(&self) -> Option<cranelift::prelude::Block> {
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

/// Key for caching pure runtime function calls
pub type CallCacheKey = (RuntimeKey, SmallVec<[Value; 4]>);

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
pub(crate) struct Cg<'a, 'b, 'ctx> {
    pub builder: &'a mut FunctionBuilder<'b>,
    /// Variable bindings - owned, fresh per function
    pub vars: FxHashMap<Symbol, (Variable, TypeId)>,
    pub cf: ControlFlow,
    pub captures: Option<Captures<'a>>,
    /// For recursive lambdas: the binding name that captures itself
    pub self_capture: Option<Symbol>,
    /// Cache for pure runtime function calls: (func, args) -> result
    pub call_cache: FxHashMap<CallCacheKey, Value>,
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
        Self {
            builder,
            vars: FxHashMap::default(),
            cf: ControlFlow::new(),
            captures: None,
            self_capture: None,
            call_cache: FxHashMap::default(),
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
        let stride = self.builder.ins().iconst(ptr_type, tagged_value_size);
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
            let tag = {
                let arena = self.arena();
                crate::types::array_element_tag_id(value.type_id, arena)
            };
            let tag_val = self.builder.ins().iconst(types::I64, tag);
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
                self.builder.ins().iconst(types::I64, 0)
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
        let tag_val = self.builder.ins().iconst(types::I64, tag);
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
        self.funcs_ref()
            .func_id(key)
            .ok_or_else(|| CodegenError::not_found("function id", ""))
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

    /// Call a pure runtime function with caching (CSE)
    #[allow(dead_code)]
    pub fn call_runtime_cached(
        &mut self,
        func: RuntimeKey,
        args: &[Value],
    ) -> CodegenResult<Value> {
        let key = (func, SmallVec::from_slice(args));
        if let Some(&cached) = self.call_cache.get(&key) {
            return Ok(cached);
        }
        let result = self.call_runtime(func, args)?;
        self.call_cache.insert(key, result);
        Ok(result)
    }

    /// Get cached field value or call runtime and cache result
    pub fn get_field_cached(&mut self, instance: Value, slot: u32) -> CodegenResult<Value> {
        let key = (instance, slot);
        if let Some(&cached) = self.field_cache.get(&key) {
            return Ok(cached);
        }
        let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
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
            let value = crate::structs::helpers::load_wide_field(
                self.builder,
                get_func_ref,
                instance,
                slot,
            );
            Ok(CompiledValue::new(value, types::I128, field_type_id))
        } else {
            let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
            let result_raw =
                self.call_runtime(RuntimeKey::InstanceGetField, &[instance, slot_val])?;
            Ok(self.convert_field_value(result_raw, field_type_id))
        }
    }

    /// Invalidate value caches when entering a control flow branch.
    ///
    /// The `field_cache` and `call_cache` store Cranelift SSA `Value`s that are
    /// defined in a particular basic block.  When the builder switches to a
    /// sibling block (e.g., the next arm of a `when`/`match`/`if` expression),
    /// values cached from a previous arm do **not** dominate the new block,
    /// so reusing them would produce a Cranelift verifier error
    /// ("uses value from non-dominating inst").
    ///
    /// Call this at the start of each arm body in any branching construct.
    pub fn invalidate_value_caches(&mut self) {
        self.field_cache.clear();
        self.call_cache.clear();
    }

    /// Call a runtime function that returns void
    pub fn call_runtime_void(&mut self, runtime: RuntimeKey, args: &[Value]) -> CodegenResult<()> {
        let func_ref = self.runtime_func_ref(runtime)?;
        let coerced = self.coerce_call_args(func_ref, args);
        self.builder.ins().call(func_ref, &coerced);
        Ok(())
    }

    /// Create a void return value
    pub fn void_value(&mut self) -> CompiledValue {
        let zero = self.builder.ins().iconst(types::I64, 0);
        CompiledValue::new(zero, types::I64, TypeId::VOID)
    }

    /// Create a zero/default value of the given Cranelift type.
    ///
    /// Used for empty match arms and other cases where a typed default is needed.
    pub fn typed_zero(&mut self, ty: Type) -> Value {
        if ty == types::F64 {
            self.builder.ins().f64const(0.0)
        } else if ty == types::F32 {
            self.builder.ins().f32const(0.0)
        } else {
            self.builder.ins().iconst(ty, 0)
        }
    }

    /// Get the result of a call instruction as a CompiledValue.
    ///
    /// If the call has no results, returns void_value().
    /// For fallible returns with 2 results (tag, payload), packs them into a stack slot.
    /// Otherwise, wraps the first result with the given return_type_id.
    pub fn call_result(
        &mut self,
        call: cranelift_codegen::ir::Inst,
        return_type_id: TypeId,
    ) -> CompiledValue {
        let results = self.builder.inst_results(call);
        if results.is_empty() {
            return self.void_value();
        }

        // Check for wide fallible multi-value return (3 results: tag, low, high)
        // i128 success values are split across two i64 registers
        if results.len() == 3 && crate::types::is_wide_fallible(return_type_id, self.arena()) {
            let tag = results[0];
            let low = results[1];
            let high = results[2];

            // Allocate stack slot: 8 (tag) + 16 (i128 payload) = 24 bytes
            let slot_size = 24u32;
            let slot = self.alloc_stack(slot_size);

            // Store tag at offset 0
            self.builder.ins().stack_store(tag, slot, 0);
            // Reconstruct i128 from low/high and store at offset 8
            let i128_val = super::structs::reconstruct_i128(self.builder, low, high);
            super::structs::helpers::store_i128_to_stack(
                self.builder,
                i128_val,
                slot,
                union_layout::PAYLOAD_OFFSET,
            );

            let ptr_type = self.ptr_type();
            let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

            return CompiledValue::new(ptr, ptr_type, return_type_id);
        }

        // Check for fallible multi-value return (2 results: tag, payload)
        if results.len() == 2 && self.arena().unwrap_fallible(return_type_id).is_some() {
            let tag = results[0];
            let payload = results[1];

            // Allocate stack slot to store (tag, payload) for callers that expect a pointer
            let slot_size = union_layout::STANDARD_SIZE;
            let slot = self.alloc_stack(slot_size);

            // Store tag at offset 0
            self.builder.ins().stack_store(tag, slot, 0);
            // Store payload at offset 8
            self.builder
                .ins()
                .stack_store(payload, slot, union_layout::PAYLOAD_OFFSET);

            // Get pointer to stack slot
            let ptr_type = self.ptr_type();
            let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

            return CompiledValue::new(ptr, ptr_type, return_type_id);
        }

        // Check for small struct multi-value return (2 results: field0, field1)
        if results.len() == 2 && self.is_small_struct_return(return_type_id) {
            let results_vec: Vec<Value> = results.to_vec();
            return self.reconstruct_struct_from_regs(&results_vec, return_type_id);
        }

        // Large struct sret return: the result is already a pointer to the buffer
        // (handled by the caller passing the sret arg, result[0] is the sret pointer)
        // No special handling needed here since result[0] is already the pointer.

        // If the return type is a union, the returned value is a pointer to the callee's stack.
        // We must copy the union data to our own stack immediately, before any subsequent
        // calls (e.g. rc_dec for temporary args) can clobber the callee's stack frame.
        if self.arena().is_union(return_type_id) {
            let src_ptr = results[0];
            return self.copy_union_ptr_to_local(src_ptr, return_type_id);
        }

        self.compiled(results[0], return_type_id)
    }

    /// Copy a union value from a pointer (typically callee's stack) to a local stack slot.
    ///
    /// This prevents the returned union from being clobbered when the callee's
    /// stack frame is reused (e.g., by RC cleanup calls after a function return).
    pub fn copy_union_ptr_to_local(
        &mut self,
        src_ptr: Value,
        union_type_id: TypeId,
    ) -> CompiledValue {
        let union_size = self.type_size(union_type_id);
        let slot = self.alloc_stack(union_size);

        let tag = self
            .builder
            .ins()
            .load(types::I8, MemFlags::new(), src_ptr, 0);
        self.builder.ins().stack_store(tag, slot, 0);

        if union_size > union_layout::TAG_ONLY_SIZE {
            let payload = self.builder.ins().load(
                types::I64,
                MemFlags::new(),
                src_ptr,
                union_layout::PAYLOAD_OFFSET,
            );
            self.builder
                .ins()
                .stack_store(payload, slot, union_layout::PAYLOAD_OFFSET);
        }

        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
        self.compiled(ptr, union_type_id)
    }

    /// Load the payload from a union pointer, returning zero if the union is tag-only.
    ///
    /// Sentinel-only unions have `union_size == TAG_ONLY_SIZE` (8 bytes, tag only)
    /// and carry no payload data, so this returns an `iconst 0` for those.
    pub fn load_union_payload(
        &mut self,
        union_ptr: Value,
        union_type_id: TypeId,
        payload_type: Type,
    ) -> Value {
        let union_size = self.type_size(union_type_id);
        if union_size > union_layout::TAG_ONLY_SIZE {
            self.builder.ins().load(
                payload_type,
                MemFlags::new(),
                union_ptr,
                union_layout::PAYLOAD_OFFSET,
            )
        } else {
            self.builder.ins().iconst(payload_type, 0)
        }
    }

    // ========== CompiledValue constructors ==========

    /// Wrap a Cranelift value as a Bool CompiledValue
    pub fn bool_value(&self, value: Value) -> CompiledValue {
        CompiledValue::new(value, types::I8, TypeId::BOOL)
    }

    /// Create a boolean constant (true or false)
    pub fn bool_const(&mut self, b: bool) -> CompiledValue {
        let value = self.builder.ins().iconst(types::I8, if b { 1 } else { 0 });
        self.bool_value(value)
    }

    /// Wrap a Cranelift value as an I64 CompiledValue
    pub fn i64_value(&self, value: Value) -> CompiledValue {
        CompiledValue::new(value, types::I64, TypeId::I64)
    }

    /// Create an integer constant with a specific Vole type
    pub fn int_const(&mut self, n: i64, type_id: TypeId) -> CompiledValue {
        let ty = self.cranelift_type(type_id);
        let arena = self.arena();
        // If bidirectional inference produced a float type for an integer literal
        // (can happen in generic contexts where the type parameter resolves to f64
        // during sema but codegen uses i64 for the type param), fall back to i64.
        // Float conversion for `let x: f64 = 5` is handled by sema recording the
        // literal as a FloatLiteral, not through int_const.
        //
        // Likewise, if sema contextual typing labels an int literal as a union
        // element, keep the literal concrete here and let explicit union boxing
        // happen at coercion/assignment boundaries.
        let (ty, type_id) = if ty == types::F64 || ty == types::F32 || arena.is_union(type_id) {
            (types::I64, TypeId::I64)
        } else {
            (ty, type_id)
        };
        // Cranelift's iconst doesn't support I128 directly - we need to create
        // an i64 constant and sign-extend it to i128
        let value = if ty == types::I128 {
            let i64_val = self.builder.ins().iconst(types::I64, n);
            self.builder.ins().sextend(types::I128, i64_val)
        } else {
            self.builder.ins().iconst(ty, n)
        };
        CompiledValue::new(value, ty, type_id)
    }

    /// Create a float constant with explicit type (for bidirectional inference)
    pub fn float_const(&mut self, n: f64, type_id: TypeId) -> CompiledValue {
        let arena = self.arena();
        if arena.is_union(type_id) {
            let v = self.builder.ins().f64const(n);
            return CompiledValue::new(v, types::F64, TypeId::F64);
        }
        let (ty, value) = match arena.get(type_id) {
            ArenaType::Primitive(PrimitiveType::F32) => {
                let v = self.builder.ins().f32const(n as f32);
                (types::F32, v)
            }
            _ => {
                // Default to F64
                let v = self.builder.ins().f64const(n);
                (types::F64, v)
            }
        };
        CompiledValue::new(value, ty, type_id)
    }

    /// Create a nil value
    pub fn nil_value(&mut self) -> CompiledValue {
        let value = self.builder.ins().iconst(types::I8, 0);
        CompiledValue::new(value, types::I8, TypeId::NIL)
    }

    /// Load a tag byte from a union/optional pointer and compare to expected value.
    /// Returns an i8 value (1 if equal, 0 if not).
    pub fn tag_eq(&mut self, ptr: Value, expected_tag: i64) -> Value {
        let tag = self.builder.ins().load(types::I8, MemFlags::new(), ptr, 0);
        let expected = self.builder.ins().iconst(types::I8, expected_tag);
        self.builder.ins().icmp(IntCC::Equal, tag, expected)
    }

    /// Load a tag byte from a union/optional pointer and compare for inequality.
    /// Returns an i8 value (1 if not equal, 0 if equal).
    pub fn tag_ne(&mut self, ptr: Value, expected_tag: i64) -> Value {
        let tag = self.builder.ins().load(types::I8, MemFlags::new(), ptr, 0);
        let expected = self.builder.ins().iconst(types::I8, expected_tag);
        self.builder.ins().icmp(IntCC::NotEqual, tag, expected)
    }

    /// Wrap a Cranelift value as a String CompiledValue marked as an RC temp
    pub fn string_temp(&self, value: Value) -> CompiledValue {
        CompiledValue::owned(value, self.ptr_type(), TypeId::STRING)
    }

    /// Create a CompiledValue from a value and TypeId, automatically computing the cranelift type
    pub fn compiled(&self, value: Value, type_id: TypeId) -> CompiledValue {
        CompiledValue::new(value, self.cranelift_type(type_id), type_id)
    }

    /// Convert a raw i64 field value to a CompiledValue with the proper type.
    /// Handles type narrowing for primitives (f64 bitcast, bool/int reduction).
    pub fn convert_field_value(&mut self, raw_value: Value, type_id: TypeId) -> CompiledValue {
        // Use env.analyzed.type_arena() to avoid borrow conflict with builder
        let arena = self.env.analyzed.type_arena();
        let (value, ty) =
            super::structs::convert_field_value_id(self.builder, raw_value, type_id, arena);
        CompiledValue::new(value, ty, type_id)
    }

    /// Extract a value from a TaggedValue (unknown type) after type narrowing.
    /// The raw_value is the value field from the TaggedValue (already loaded from offset 8).
    /// This converts it to the appropriate Cranelift type based on the narrowed type.
    pub fn extract_unknown_value(&mut self, raw_value: Value, type_id: TypeId) -> CompiledValue {
        self.convert_field_value(raw_value, type_id)
    }

    /// Compile a list of expression arguments into Cranelift values.
    /// This is the common pattern for function/method calls.
    pub fn compile_call_args(&mut self, args: &[Expr]) -> CodegenResult<Vec<Value>> {
        let (values, _) = self.compile_call_args_tracking_rc(args)?;
        Ok(values)
    }

    /// Compile call arguments, returning both Cranelift values for the call
    /// and owned `CompiledValue`s that need rc_dec after the call completes.
    pub fn compile_call_args_tracking_rc(
        &mut self,
        args: &[Expr],
    ) -> CodegenResult<(Vec<Value>, Vec<CompiledValue>)> {
        let mut values = Vec::with_capacity(args.len());
        let mut rc_temps = Vec::new();
        for arg in args {
            let compiled = self.expr(arg)?;
            if compiled.is_owned() {
                rc_temps.push(compiled);
            }
            values.push(compiled.value);
        }
        Ok((values, rc_temps))
    }

    // ========== Control flow helpers ==========

    /// Switch to a block and seal it (common pattern for sequential control flow)
    pub fn switch_and_seal(&mut self, block: cranelift::prelude::Block) {
        self.builder.switch_to_block(block);
        self.builder.seal_block(block);
    }

    /// Extend a boolean condition to I32 for use with brif
    pub fn cond_to_i32(&mut self, cond: Value) -> Value {
        self.builder.ins().uextend(types::I32, cond)
    }

    /// Compile a loop body with proper loop context setup.
    ///
    /// - Registers the loop with exit_block and continue_block
    /// - Compiles the body block
    /// - If not terminated, jumps to continue_block
    ///
    /// Returns true if the body terminated (return/break).
    pub fn compile_loop_body(
        &mut self,
        body: &vole_frontend::Block,
        exit_block: cranelift::prelude::Block,
        continue_block: cranelift::prelude::Block,
    ) -> CodegenResult<bool> {
        let rc_depth = self.rc_scope_depth();
        self.cf.push_loop(exit_block, continue_block, rc_depth);
        // Push a per-iteration RC scope so temps created in the loop body
        // get cleaned up at the end of each iteration, not just once at loop exit.
        self.push_rc_scope();
        let terminated = self.block(body)?;
        self.cf.pop_loop();
        if !terminated {
            // Emit per-iteration cleanup before jumping back to continue/header
            self.pop_rc_scope_with_cleanup(None)?;
            self.builder.ins().jump(continue_block, &[]);
        } else {
            // Body terminated (break/return) — scope already cleaned by those paths.
            // Still pop the scope to keep the stack balanced.
            self.rc_scopes.pop_scope();
        }
        Ok(terminated)
    }

    /// Finalize a for-loop by switching to exit_block and sealing internal blocks.
    ///
    /// Standard for-loop structure has 4 blocks: header, body, continue, exit.
    /// This must be called after compile_loop_body and any continue-block logic.
    ///
    /// Seals header, body, and continue blocks since their predecessors are now known.
    /// The exit block is NOT sealed - code following the loop may use variables
    /// defined before the loop (potentially in another loop), and sealing the exit
    /// block prematurely prevents Cranelift's SSA construction from properly
    /// threading those values through block parameters. The exit block will be
    /// sealed by seal_all_blocks() at function finalization.
    pub fn finalize_for_loop(
        &mut self,
        header: cranelift::prelude::Block,
        body_block: cranelift::prelude::Block,
        continue_block: cranelift::prelude::Block,
        exit_block: cranelift::prelude::Block,
    ) {
        self.builder.switch_to_block(exit_block);
        self.builder.seal_block(header);
        self.builder.seal_block(body_block);
        self.builder.seal_block(continue_block);
        // exit_block left unsealed - see note above
    }

    // ========== Stack allocation ==========

    /// Allocate a stack slot of the given size in bytes
    pub fn alloc_stack(&mut self, size: u32) -> StackSlot {
        self.builder.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            size,
            0,
        ))
    }

    /// Copy a union heap buffer (16 bytes: [tag:i8, is_rc:i8, pad(6), payload:i64])
    /// to a stack-allocated union slot (16 bytes: [tag:i8, pad(7), payload:i64]).
    /// This prevents use-after-free when reading union elements from dynamic arrays,
    /// since the array slot may be overwritten (e.g. by rehash) while the value is
    /// still in use.
    pub fn copy_union_heap_to_stack(
        &mut self,
        heap_ptr: Value,
        union_type_id: TypeId,
    ) -> CompiledValue {
        let union_size = self.type_size(union_type_id);
        let slot = self.alloc_stack(union_size);
        let tag = self
            .builder
            .ins()
            .load(types::I8, MemFlags::new(), heap_ptr, 0);
        self.builder.ins().stack_store(tag, slot, 0);
        let payload = self.builder.ins().load(
            types::I64,
            MemFlags::new(),
            heap_ptr,
            union_layout::PAYLOAD_OFFSET,
        );
        self.builder
            .ins()
            .stack_store(payload, slot, union_layout::PAYLOAD_OFFSET);
        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
        let mut cv = CompiledValue::new(ptr, ptr_type, union_type_id);
        cv.mark_borrowed();
        cv
    }

    /// Get the flat slot count for a struct (recursively counts leaf fields).
    /// This is the number of 8-byte slots needed to store the struct inline,
    /// accounting for nested struct fields.
    pub fn struct_flat_slot_count(&self, type_id: TypeId) -> Option<usize> {
        let arena = self.arena();
        let entities = self.registry();
        super::structs::struct_flat_slot_count(type_id, arena, entities)
    }

    /// Check if a struct type uses small return convention (1-2 flat slots).
    pub fn is_small_struct_return(&self, type_id: TypeId) -> bool {
        self.struct_flat_slot_count(type_id)
            .is_some_and(|count| count <= crate::MAX_SMALL_STRUCT_FIELDS)
    }

    /// Check if a struct type uses sret convention (3+ flat slots).
    pub fn is_sret_struct_return(&self, type_id: TypeId) -> bool {
        self.struct_flat_slot_count(type_id)
            .is_some_and(|count| count > crate::MAX_SMALL_STRUCT_FIELDS)
    }

    /// If the return type uses sret convention (large struct), allocate a stack
    /// buffer for the return value and return a pointer to it. The caller should
    /// prepend this pointer to the call arguments.
    pub fn alloc_sret_ptr(&mut self, return_type_id: TypeId) -> Option<Value> {
        if !self.is_sret_struct_return(return_type_id) {
            return None;
        }
        let ptr_type = self.ptr_type();
        let flat_count = self
            .struct_flat_slot_count(return_type_id)
            .expect("INTERNAL: sret call: missing flat slot count");
        let total_size = (flat_count as u32) * 8;
        let slot = self.alloc_stack(total_size);
        Some(self.builder.ins().stack_addr(ptr_type, slot, 0))
    }

    /// Emit a return for a small struct (1-2 flat slots) via register passing.
    /// Loads flat slots into registers, pads to 2, and emits the return instruction.
    pub fn emit_small_struct_return(&mut self, struct_ptr: Value, ret_type_id: TypeId) {
        let flat_count = self
            .struct_flat_slot_count(ret_type_id)
            .expect("INTERNAL: struct return: missing flat slot count");
        let mut return_vals = Vec::with_capacity(crate::MAX_SMALL_STRUCT_FIELDS);
        for i in 0..flat_count {
            let offset = (i as i32) * 8;
            let val = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), struct_ptr, offset);
            return_vals.push(val);
        }
        while return_vals.len() < crate::MAX_SMALL_STRUCT_FIELDS {
            return_vals.push(self.builder.ins().iconst(types::I64, 0));
        }
        self.builder.ins().return_(&return_vals);
    }

    /// Emit a return for a large struct (3+ flat slots) via sret convention.
    /// Copies flat slots into the sret buffer (first parameter) and returns the pointer.
    pub fn emit_sret_struct_return(&mut self, struct_ptr: Value, ret_type_id: TypeId) {
        let entry_block = self
            .builder
            .func
            .layout
            .entry_block()
            .expect("INTERNAL: sret return: function has no entry block");
        let sret_ptr = self.builder.block_params(entry_block)[0];
        let flat_count = self
            .struct_flat_slot_count(ret_type_id)
            .expect("INTERNAL: sret return: missing flat slot count");
        for i in 0..flat_count {
            let offset = (i as i32) * 8;
            let val = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), struct_ptr, offset);
            self.builder
                .ins()
                .store(MemFlags::new(), val, sret_ptr, offset);
        }
        self.builder.ins().return_(&[sret_ptr]);
    }

    /// Reconstruct a struct from a multi-value return (two i64 registers).
    /// Allocates a stack slot and stores the register values as fields.
    pub fn reconstruct_struct_from_regs(
        &mut self,
        values: &[Value],
        type_id: TypeId,
    ) -> CompiledValue {
        let flat_count = self
            .struct_flat_slot_count(type_id)
            .expect("INTERNAL: reconstruct_struct_from_regs: expected struct type");
        let total_size = (flat_count as u32) * 8;
        let slot = self.alloc_stack(total_size);

        for (i, &val) in values.iter().enumerate().take(flat_count) {
            let offset = (i as i32) * 8;
            self.builder.ins().stack_store(val, slot, offset);
        }

        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

        CompiledValue::new(ptr, ptr_type, type_id)
    }

    /// Copy a struct value to a new stack slot (value semantics).
    /// Copies all flat slots (8 bytes each), accounting for nested structs.
    pub fn copy_struct_value(&mut self, src: CompiledValue) -> CodegenResult<CompiledValue> {
        let flat_count = self.struct_flat_slot_count(src.type_id).ok_or_else(|| {
            CodegenError::type_mismatch("copy_struct_value", "struct type", "non-struct")
        })?;

        let total_size = (flat_count as u32) * 8;
        let dst_slot = self.alloc_stack(total_size);

        // Copy all flat slots (8 bytes each)
        for i in 0..flat_count {
            let offset = (i as i32) * 8;
            let val = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), src.value, offset);
            self.builder.ins().stack_store(val, dst_slot, offset);
        }

        let ptr_type = self.ptr_type();
        let dst_ptr = self.builder.ins().stack_addr(ptr_type, dst_slot, 0);

        Ok(CompiledValue::new(dst_ptr, ptr_type, src.type_id))
    }

    /// Copy a struct value to a heap allocation.
    /// Used when storing structs into arrays so the data survives the current stack frame.
    pub fn copy_struct_to_heap(&mut self, src: CompiledValue) -> CodegenResult<CompiledValue> {
        let flat_count = self.struct_flat_slot_count(src.type_id).ok_or_else(|| {
            CodegenError::type_mismatch("copy_struct_to_heap", "struct type", "non-struct")
        })?;

        let total_size = (flat_count as u32) * 8;
        let ptr_type = self.ptr_type();

        // Heap-allocate storage
        let heap_alloc_ref = self.runtime_func_ref(RuntimeKey::HeapAlloc)?;
        let size_val = self.builder.ins().iconst(ptr_type, total_size as i64);
        let alloc_call = self.builder.ins().call(heap_alloc_ref, &[size_val]);
        let heap_ptr = self.builder.inst_results(alloc_call)[0];

        // Copy all flat slots (8 bytes each) from stack to heap
        for i in 0..flat_count {
            let offset = (i as i32) * 8;
            let val = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), src.value, offset);
            self.builder
                .ins()
                .store(MemFlags::new(), val, heap_ptr, offset);
        }

        Ok(CompiledValue::new(heap_ptr, ptr_type, src.type_id))
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
