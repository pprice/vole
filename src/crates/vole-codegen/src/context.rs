// src/codegen/context.rs
//
// Unified codegen context - bundles all state needed during code generation.
// Methods are implemented across multiple files using split impl blocks.

use std::cell::RefCell;

use cranelift::prelude::{
    AbiParam, FunctionBuilder, InstBuilder, IntCC, MemFlags, StackSlotData, StackSlotKind, Type,
    Value, Variable, types,
};
use cranelift_codegen::ir::StackSlot;
use cranelift_module::{FuncId, Module};
use rustc_hash::FxHashMap;

use crate::errors::CodegenError;
use crate::{FunctionKey, RuntimeFn};
use smallvec::SmallVec;
use vole_frontend::{Expr, Symbol};
use vole_identity::{ModuleId, NameId};
use vole_runtime::native_registry::NativeType;
use vole_sema::PrimitiveType;
use vole_sema::implement_registry::ExternalMethodInfo;
use vole_sema::type_arena::{SemaType as ArenaType, TypeId};

use super::lambda::CaptureBinding;
use super::types::{
    CodegenCtx, CompileEnv, CompiledValue, TypeMetadataMap, native_type_to_cranelift, type_id_size,
    type_id_to_cranelift,
};

/// Control flow context for loops (break/continue targets)
pub(crate) struct ControlFlow {
    /// Stack of loop exit blocks for break statements
    loop_exits: Vec<cranelift::prelude::Block>,
    /// Stack of loop continue blocks for continue statements
    loop_continues: Vec<cranelift::prelude::Block>,
}

impl ControlFlow {
    pub fn new() -> Self {
        Self {
            loop_exits: Vec::new(),
            loop_continues: Vec::new(),
        }
    }

    pub fn push_loop(&mut self, exit: cranelift::prelude::Block, cont: cranelift::prelude::Block) {
        self.loop_exits.push(exit);
        self.loop_continues.push(cont);
    }

    pub fn pop_loop(&mut self) {
        self.loop_exits.pop();
        self.loop_continues.pop();
    }

    pub fn loop_exit(&self) -> Option<cranelift::prelude::Block> {
        self.loop_exits.last().copied()
    }

    pub fn loop_continue(&self) -> Option<cranelift::prelude::Block> {
        self.loop_continues.last().copied()
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
pub type CallCacheKey = (RuntimeFn, SmallVec<[Value; 4]>);

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
    /// Cache for substituted types
    substitution_cache: RefCell<FxHashMap<TypeId, TypeId>>,
    /// Module export bindings from destructuring imports: local_name -> (module_id, export_name, type_id)
    pub module_bindings: FxHashMap<Symbol, ModuleExportBinding>,

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
            substitution_cache: RefCell::new(FxHashMap::default()),
            // Initialize with global module bindings from top-level destructuring imports
            module_bindings: env.global_module_bindings.clone(),
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

    /// Set pre-populated variables (for cases where params are bound before Cg creation).
    pub fn with_vars(mut self, vars: FxHashMap<Symbol, (Variable, TypeId)>) -> Self {
        self.vars = vars;
        self
    }

    /// Get mutable reference to variables map (for binding params after creation).
    #[allow(dead_code)]
    pub fn vars_mut(&mut self) -> &mut FxHashMap<Symbol, (Variable, TypeId)> {
        &mut self.vars
    }

    /// Check if we're in a closure context with captures
    pub fn has_captures(&self) -> bool {
        self.captures.is_some()
    }

    // ========== Context accessors ==========

    /// Get a TypeCtx view
    #[inline]
    pub fn type_ctx(&self) -> super::types::TypeCtx<'_> {
        super::types::TypeCtx::new(self.env.analyzed.query(), self.codegen_ctx.ptr_type())
    }

    /// Substitute type parameters using current substitutions
    ///
    /// Uses expect_substitute for read-only lookup since sema pre-computes all
    /// substituted types when creating MonomorphInstance.
    #[inline]
    pub fn substitute_type(&self, ty: TypeId) -> TypeId {
        if let Some(substitutions) = self.substitutions {
            // Check cache first
            if let Some(&cached) = self.substitution_cache.borrow().get(&ty) {
                return cached;
            }
            // Convert std HashMap to FxHashMap for arena compatibility
            let subs: FxHashMap<NameId, TypeId> =
                substitutions.iter().map(|(&k, &v)| (k, v)).collect();
            let arena = self.env.analyzed.type_arena();
            let result = arena.expect_substitute(ty, &subs, "Cg::substitute_type");
            // Cache the result
            self.substitution_cache.borrow_mut().insert(ty, result);
            result
        } else {
            ty
        }
    }

    /// Get current module (as ModuleId)
    #[inline]
    #[allow(dead_code)]
    pub fn current_module_id(&self) -> Option<ModuleId> {
        self.current_module
    }

    /// Get type substitutions
    #[inline]
    #[allow(dead_code)]
    pub fn type_substitutions(&self) -> Option<&FxHashMap<NameId, TypeId>> {
        self.substitutions
    }

    /// Alias for type_substitutions (backward compat)
    #[inline]
    #[allow(dead_code)]
    pub fn get_substitutions(&self) -> Option<&FxHashMap<NameId, TypeId>> {
        self.substitutions
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
                && let Some(ty) = module_types.get(node_id)
            {
                return Some(*ty);
            }
        }
        // Fall back to main program expr_types
        self.env.analyzed.query().expr_data().get_type(*node_id)
    }

    /// Get substituted return type for generic method calls
    #[inline]
    pub fn get_substituted_return_type(&self, node_id: &vole_frontend::NodeId) -> Option<TypeId> {
        self.env
            .analyzed
            .query()
            .expr_data()
            .get_substituted_return_type(*node_id)
    }

    /// Get declared variable type for let statements with explicit type annotations.
    /// Used for union wrapping, numeric widening, and interface boxing.
    /// Only available for main program code (not module code) since declared_var_types
    /// are stored with main program NodeIds only.
    #[inline]
    pub fn get_declared_var_type(&self, init_node_id: &vole_frontend::NodeId) -> Option<TypeId> {
        // Don't use declared_var_types for module code - NodeIds would collide
        if self.current_module.is_some() {
            return None;
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
    pub fn global_init(&self, name: Symbol) -> Option<&Expr> {
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

    /// Alias for native_registry (backward compat)
    #[inline]
    pub fn native_funcs(&self) -> &'ctx vole_runtime::NativeRegistry {
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

    /// Alias for type_metadata (backward compat)
    #[inline]
    pub fn type_meta(&self) -> &'ctx TypeMetadataMap {
        &self.env.state.type_metadata
    }

    /// Get unified method function key map
    #[inline]
    pub fn method_func_keys(
        &self,
    ) -> &'ctx FxHashMap<(vole_identity::TypeDefId, NameId), FunctionKey> {
        &self.env.state.method_func_keys
    }

    /// Get interface vtable registry
    #[inline]
    #[allow(dead_code)]
    pub fn interface_vtables(
        &self,
    ) -> &'ctx RefCell<crate::interface_vtable::InterfaceVtableRegistry> {
        &self.env.state.interface_vtables
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

    // ========== Arena helpers ==========

    /// Find the nil variant index in a union (for optional handling)
    pub fn find_nil_variant(&self, ty: TypeId) -> Option<usize> {
        let arena = self.arena();
        if let Some(variants) = arena.unwrap_union(ty) {
            variants.iter().position(|&id| id.is_nil())
        } else {
            None
        }
    }

    /// Convert a TypeId to a Cranelift type
    pub fn cranelift_type(&self, ty: TypeId) -> Type {
        type_id_to_cranelift(ty, self.arena(), self.ptr_type())
    }

    /// Convert a slice of TypeIds to Cranelift types
    pub fn cranelift_types(&self, type_ids: &[TypeId]) -> Vec<Type> {
        let arena = self.arena();
        type_ids
            .iter()
            .map(|&ty| type_id_to_cranelift(ty, arena, self.ptr_type()))
            .collect()
    }

    /// Get the size (in bits) of a TypeId
    pub fn type_size(&self, ty: TypeId) -> u32 {
        type_id_size(ty, self.ptr_type(), self.query().registry(), self.arena())
    }

    /// Unwrap an interface type, returning the TypeDefId if it is one
    pub fn interface_type_def_id(&self, ty: TypeId) -> Option<vole_identity::TypeDefId> {
        self.arena().unwrap_interface(ty).map(|(id, _)| id)
    }

    /// Resolve a type name Symbol to its TypeDefId using the full resolution chain.
    ///
    /// This uses the same resolution path as sema: primitives, current module,
    /// imports, builtin module, and interface/class fallback.
    /// Note: We convert the Symbol to string first because the current interner
    /// may be module-specific while the query uses the main program's interner.
    pub fn resolve_type(&self, sym: Symbol) -> Option<vole_identity::TypeDefId> {
        let name = self.interner().resolve(sym);
        let query = self.query();
        let module_id = self
            .current_module_id()
            .unwrap_or_else(|| query.main_module());
        query.resolve_type_def_by_str(module_id, name)
    }

    /// Resolve a type name string to its TypeDefId using the full resolution chain.
    ///
    /// This uses the same resolution path as sema: primitives, current module,
    /// imports, builtin module, and interface/class fallback.
    pub fn resolve_type_str_or_interface(&self, name: &str) -> Option<vole_identity::TypeDefId> {
        let query = self.query();
        let module_id = self
            .current_module_id()
            .unwrap_or_else(|| query.main_module());
        query.resolve_type_def_by_str(module_id, name)
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
    pub fn func_id(&self, key: FunctionKey) -> Result<FuncId, String> {
        self.funcs_ref()
            .func_id(key)
            .ok_or_else(|| "function id not found".to_string())
    }

    /// Get a function reference for calling
    pub fn func_ref(
        &mut self,
        key: FunctionKey,
    ) -> Result<cranelift::codegen::ir::FuncRef, String> {
        let func_id = self.func_id(key)?;
        // Use codegen_ctx directly to avoid borrowing self twice
        let module = self.codegen_ctx.jit_module();
        Ok(module.declare_func_in_func(func_id, self.builder.func))
    }

    /// Get a FuncRef for a runtime function (RuntimeFn -> FuncRef in one call)
    pub fn runtime_func_ref(
        &mut self,
        runtime: RuntimeFn,
    ) -> Result<cranelift::codegen::ir::FuncRef, String> {
        let key = self.funcs().runtime_key(runtime).ok_or_else(|| {
            CodegenError::not_found("runtime function", runtime.name()).to_string()
        })?;
        self.func_ref(key)
    }

    /// Call a runtime function and return the first result (or error if no results)
    pub fn call_runtime(&mut self, runtime: RuntimeFn, args: &[Value]) -> Result<Value, String> {
        let func_ref = self.runtime_func_ref(runtime)?;
        let call = self.builder.ins().call(func_ref, args);
        let results = self.builder.inst_results(call);
        if results.is_empty() {
            Err(CodegenError::internal_with_context(
                "runtime function returned no value",
                runtime.name(),
            )
            .into())
        } else {
            Ok(results[0])
        }
    }

    /// Call a pure runtime function with caching (CSE)
    pub fn call_runtime_cached(
        &mut self,
        func: RuntimeFn,
        args: &[Value],
    ) -> Result<Value, String> {
        let key = (func, SmallVec::from_slice(args));
        if let Some(&cached) = self.call_cache.get(&key) {
            return Ok(cached);
        }
        let result = self.call_runtime(func, args)?;
        self.call_cache.insert(key, result);
        Ok(result)
    }

    /// Get cached field value or call runtime and cache result
    pub fn get_field_cached(&mut self, instance: Value, slot: u32) -> Result<Value, String> {
        let key = (instance, slot);
        if let Some(&cached) = self.field_cache.get(&key) {
            return Ok(cached);
        }
        let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
        let result = self.call_runtime(RuntimeFn::InstanceGetField, &[instance, slot_val])?;
        self.field_cache.insert(key, result);
        Ok(result)
    }

    /// Call a runtime function that returns void
    pub fn call_runtime_void(&mut self, runtime: RuntimeFn, args: &[Value]) -> Result<(), String> {
        let func_ref = self.runtime_func_ref(runtime)?;
        self.builder.ins().call(func_ref, args);
        Ok(())
    }

    /// Create a void return value
    pub fn void_value(&mut self) -> CompiledValue {
        let zero = self.builder.ins().iconst(types::I64, 0);
        CompiledValue {
            value: zero,
            ty: types::I64,
            type_id: TypeId::VOID,
        }
    }

    /// Get the result of a call instruction as a CompiledValue.
    ///
    /// If the call has no results, returns void_value().
    /// Otherwise, wraps the first result with the given return_type_id.
    pub fn call_result(
        &mut self,
        call: cranelift_codegen::ir::Inst,
        return_type_id: TypeId,
    ) -> CompiledValue {
        let results = self.builder.inst_results(call);
        if results.is_empty() {
            self.void_value()
        } else {
            self.compiled(results[0], return_type_id)
        }
    }

    // ========== CompiledValue constructors ==========

    /// Wrap a Cranelift value as a Bool CompiledValue
    pub fn bool_value(&self, value: Value) -> CompiledValue {
        CompiledValue {
            value,
            ty: types::I8,
            type_id: TypeId::BOOL,
        }
    }

    /// Create a boolean constant (true or false)
    pub fn bool_const(&mut self, b: bool) -> CompiledValue {
        let value = self.builder.ins().iconst(types::I8, if b { 1 } else { 0 });
        self.bool_value(value)
    }

    /// Wrap a Cranelift value as an I64 CompiledValue
    pub fn i64_value(&self, value: Value) -> CompiledValue {
        CompiledValue {
            value,
            ty: types::I64,
            type_id: TypeId::I64,
        }
    }

    /// Create an integer constant with a specific Vole type
    pub fn int_const(&mut self, n: i64, type_id: TypeId) -> CompiledValue {
        let ty = self.cranelift_type(type_id);
        // Cranelift's iconst doesn't support I128 directly - we need to create
        // an i64 constant and sign-extend it to i128
        let value = if ty == types::I128 {
            let i64_val = self.builder.ins().iconst(types::I64, n);
            self.builder.ins().sextend(types::I128, i64_val)
        } else {
            self.builder.ins().iconst(ty, n)
        };
        CompiledValue { value, ty, type_id }
    }

    /// Create a float constant with explicit type (for bidirectional inference)
    pub fn float_const(&mut self, n: f64, type_id: TypeId) -> CompiledValue {
        let arena = self.arena();
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
        CompiledValue { value, ty, type_id }
    }

    /// Create a nil value
    pub fn nil_value(&mut self) -> CompiledValue {
        let value = self.builder.ins().iconst(types::I8, 0);
        CompiledValue {
            value,
            ty: types::I8,
            type_id: TypeId::NIL,
        }
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

    /// Create a Done value (iterator termination sentinel)
    pub fn done_value(&mut self) -> CompiledValue {
        let value = self.builder.ins().iconst(types::I8, 0);
        CompiledValue {
            value,
            ty: types::I8,
            type_id: TypeId::DONE,
        }
    }

    /// Wrap a Cranelift value as a String CompiledValue
    pub fn string_value(&self, value: Value) -> CompiledValue {
        CompiledValue {
            value,
            ty: self.ptr_type(),
            type_id: TypeId::STRING,
        }
    }

    /// Create a CompiledValue from a value and TypeId, automatically computing the cranelift type
    pub fn compiled(&self, value: Value, type_id: TypeId) -> CompiledValue {
        CompiledValue {
            value,
            ty: self.cranelift_type(type_id),
            type_id,
        }
    }

    /// Convert a raw i64 field value to a CompiledValue with the proper type.
    /// Handles type narrowing for primitives (f64 bitcast, bool/int reduction).
    pub fn convert_field_value(&mut self, raw_value: Value, type_id: TypeId) -> CompiledValue {
        // Use env.analyzed.type_arena() to avoid borrow conflict with builder
        let arena = self.env.analyzed.type_arena();
        let (value, ty) =
            super::structs::convert_field_value_id(self.builder, raw_value, type_id, arena);
        CompiledValue { value, ty, type_id }
    }

    /// Compile a list of expression arguments into Cranelift values.
    /// This is the common pattern for function/method calls.
    pub fn compile_call_args(&mut self, args: &[Expr]) -> Result<Vec<Value>, String> {
        let mut values = Vec::with_capacity(args.len());
        for arg in args {
            let compiled = self.expr(arg)?;
            values.push(compiled.value);
        }
        Ok(values)
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
    ) -> Result<bool, String> {
        self.cf.push_loop(exit_block, continue_block);
        let terminated = self.block(body)?;
        self.cf.pop_loop();
        if !terminated {
            self.builder.ins().jump(continue_block, &[]);
        }
        Ok(terminated)
    }

    /// Finalize a for-loop by switching to exit_block and sealing all loop blocks.
    ///
    /// Standard for-loop structure has 4 blocks: header, body, continue, exit.
    /// This must be called after compile_loop_body and any continue-block logic.
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
        self.builder.seal_block(exit_block);
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

    // ========== External native function calls ==========

    /// The module path for compiler intrinsics (e.g., f64.nan(), f32.infinity())
    pub const COMPILER_INTRINSIC_MODULE: &'static str = "vole:compiler_intrinsic";

    /// Call an external native function using TypeId for return type.
    /// If the module path is "vole:compiler_intrinsic", the call is handled as a
    /// compiler intrinsic (e.g., f64_nan emits a constant instead of an FFI call).
    pub fn call_external_id(
        &mut self,
        external_info: &ExternalMethodInfo,
        args: &[Value],
        return_type_id: TypeId,
    ) -> Result<CompiledValue, String> {
        // Get string names from NameId
        let (module_path, native_name) = {
            let name_table = self.name_table();
            let mp = name_table
                .last_segment_str(external_info.module_path)
                .ok_or_else(|| "module_path NameId has no segment".to_string())?;
            let nn = name_table
                .last_segment_str(external_info.native_name)
                .ok_or_else(|| "native_name NameId has no segment".to_string())?;
            (mp, nn)
        };

        // Check if this is a compiler intrinsic
        if module_path == Self::COMPILER_INTRINSIC_MODULE {
            return self.call_compiler_intrinsic(&native_name, args, return_type_id);
        }

        // Look up native function for FFI call
        let native_func = self
            .native_registry()
            .lookup(&module_path, &native_name)
            .ok_or_else(|| {
                format!(
                    "Native function {}::{} not found in registry",
                    module_path, native_name
                )
            })?;

        // Build the Cranelift signature from NativeSignature
        let ptr_type = self.ptr_type();
        let mut sig = self.jit_module().make_signature();
        for param_type in &native_func.signature.params {
            sig.params.push(AbiParam::new(native_type_to_cranelift(
                param_type, ptr_type,
            )));
        }
        if native_func.signature.return_type != NativeType::Nil {
            sig.returns.push(AbiParam::new(native_type_to_cranelift(
                &native_func.signature.return_type,
                ptr_type,
            )));
        }

        // Import the signature and emit an indirect call
        let sig_ref = self.builder.import_signature(sig);
        let func_ptr = native_func.ptr;

        // Load the function pointer as a constant
        let func_ptr_val = self.builder.ins().iconst(ptr_type, func_ptr as i64);

        // Emit the indirect call
        let call_inst = self
            .builder
            .ins()
            .call_indirect(sig_ref, func_ptr_val, args);
        let results = self.builder.inst_results(call_inst);

        if results.is_empty() {
            Ok(self.void_value())
        } else {
            let arena = self.arena();
            let cranelift_ty = type_id_to_cranelift(return_type_id, arena, ptr_type);
            Ok(CompiledValue {
                value: results[0],
                ty: cranelift_ty,
                type_id: return_type_id,
            })
        }
    }

    /// Call a compiler intrinsic by key (e.g., "f64_nan", "f32_infinity").
    ///
    /// Compiler intrinsics are declared with `external("vole:compiler_intrinsic")` and
    /// emit inline IR instead of FFI calls. The intrinsic key format is `{type}_{method}`.
    pub fn call_compiler_intrinsic(
        &mut self,
        intrinsic_key: &str,
        args: &[Value],
        _return_type_id: TypeId,
    ) -> Result<CompiledValue, String> {
        use crate::intrinsics::{FloatConstant, IntrinsicHandler, IntrinsicKey, UnaryFloatOp};

        let key = IntrinsicKey::from(intrinsic_key);
        let handler = self
            .intrinsics_registry()
            .lookup(&key)
            .ok_or_else(|| {
                format!(
                    "intrinsic \"{}\" declared but no handler registered\n  note: add handler in codegen/intrinsics.rs",
                    intrinsic_key
                )
            })?;

        match handler {
            IntrinsicHandler::FloatConstant(fc) => {
                let (value, ty, type_id) = match fc {
                    FloatConstant::F32Nan => {
                        let v = self.builder.ins().f32const(f32::NAN);
                        (v, types::F32, TypeId::F32)
                    }
                    FloatConstant::F64Nan => {
                        let v = self.builder.ins().f64const(f64::NAN);
                        (v, types::F64, TypeId::F64)
                    }
                    FloatConstant::F32Infinity => {
                        let v = self.builder.ins().f32const(f32::INFINITY);
                        (v, types::F32, TypeId::F32)
                    }
                    FloatConstant::F64Infinity => {
                        let v = self.builder.ins().f64const(f64::INFINITY);
                        (v, types::F64, TypeId::F64)
                    }
                    FloatConstant::F32NegInfinity => {
                        let v = self.builder.ins().f32const(f32::NEG_INFINITY);
                        (v, types::F32, TypeId::F32)
                    }
                    FloatConstant::F64NegInfinity => {
                        let v = self.builder.ins().f64const(f64::NEG_INFINITY);
                        (v, types::F64, TypeId::F64)
                    }
                    FloatConstant::F32Epsilon => {
                        let v = self.builder.ins().f32const(f32::EPSILON);
                        (v, types::F32, TypeId::F32)
                    }
                    FloatConstant::F64Epsilon => {
                        let v = self.builder.ins().f64const(f64::EPSILON);
                        (v, types::F64, TypeId::F64)
                    }
                };
                Ok(CompiledValue { value, ty, type_id })
            }
            IntrinsicHandler::UnaryFloatOp(op) => {
                if args.is_empty() {
                    return Err(format!(
                        "unary float intrinsic \"{}\" requires 1 argument",
                        intrinsic_key
                    ));
                }
                let arg = args[0];
                let (value, ty, type_id) = match op {
                    UnaryFloatOp::F32Sqrt => {
                        let v = self.builder.ins().sqrt(arg);
                        (v, types::F32, TypeId::F32)
                    }
                    UnaryFloatOp::F64Sqrt => {
                        let v = self.builder.ins().sqrt(arg);
                        (v, types::F64, TypeId::F64)
                    }
                    UnaryFloatOp::F32Abs => {
                        let v = self.builder.ins().fabs(arg);
                        (v, types::F32, TypeId::F32)
                    }
                    UnaryFloatOp::F64Abs => {
                        let v = self.builder.ins().fabs(arg);
                        (v, types::F64, TypeId::F64)
                    }
                    UnaryFloatOp::F32Ceil => {
                        let v = self.builder.ins().ceil(arg);
                        (v, types::F32, TypeId::F32)
                    }
                    UnaryFloatOp::F64Ceil => {
                        let v = self.builder.ins().ceil(arg);
                        (v, types::F64, TypeId::F64)
                    }
                    UnaryFloatOp::F32Floor => {
                        let v = self.builder.ins().floor(arg);
                        (v, types::F32, TypeId::F32)
                    }
                    UnaryFloatOp::F64Floor => {
                        let v = self.builder.ins().floor(arg);
                        (v, types::F64, TypeId::F64)
                    }
                    UnaryFloatOp::F32Trunc => {
                        let v = self.builder.ins().trunc(arg);
                        (v, types::F32, TypeId::F32)
                    }
                    UnaryFloatOp::F64Trunc => {
                        let v = self.builder.ins().trunc(arg);
                        (v, types::F64, TypeId::F64)
                    }
                    UnaryFloatOp::F32Round => {
                        let v = self.builder.ins().nearest(arg);
                        (v, types::F32, TypeId::F32)
                    }
                    UnaryFloatOp::F64Round => {
                        let v = self.builder.ins().nearest(arg);
                        (v, types::F64, TypeId::F64)
                    }
                };
                Ok(CompiledValue { value, ty, type_id })
            }
            IntrinsicHandler::BinaryFloatOp(op) => {
                use crate::intrinsics::BinaryFloatOp;
                if args.len() < 2 {
                    return Err(format!(
                        "binary float intrinsic \"{}\" requires 2 arguments",
                        intrinsic_key
                    ));
                }
                let arg1 = args[0];
                let arg2 = args[1];
                let (value, ty, type_id) = match op {
                    BinaryFloatOp::F32Min => {
                        let v = self.builder.ins().fmin(arg1, arg2);
                        (v, types::F32, TypeId::F32)
                    }
                    BinaryFloatOp::F64Min => {
                        let v = self.builder.ins().fmin(arg1, arg2);
                        (v, types::F64, TypeId::F64)
                    }
                    BinaryFloatOp::F32Max => {
                        let v = self.builder.ins().fmax(arg1, arg2);
                        (v, types::F32, TypeId::F32)
                    }
                    BinaryFloatOp::F64Max => {
                        let v = self.builder.ins().fmax(arg1, arg2);
                        (v, types::F64, TypeId::F64)
                    }
                };
                Ok(CompiledValue { value, ty, type_id })
            }
            IntrinsicHandler::UnaryIntOp(op) => {
                use crate::intrinsics::UnaryIntOp;
                if args.is_empty() {
                    return Err(format!(
                        "unary int intrinsic \"{}\" requires 1 argument",
                        intrinsic_key
                    ));
                }
                let arg = args[0];
                let (value, ty, type_id) = match op {
                    // abs (signed only)
                    UnaryIntOp::I8Abs => {
                        let v = self.builder.ins().iabs(arg);
                        (v, types::I8, TypeId::I8)
                    }
                    UnaryIntOp::I16Abs => {
                        let v = self.builder.ins().iabs(arg);
                        (v, types::I16, TypeId::I16)
                    }
                    UnaryIntOp::I32Abs => {
                        let v = self.builder.ins().iabs(arg);
                        (v, types::I32, TypeId::I32)
                    }
                    UnaryIntOp::I64Abs => {
                        let v = self.builder.ins().iabs(arg);
                        (v, types::I64, TypeId::I64)
                    }
                    // clz
                    UnaryIntOp::I8Clz | UnaryIntOp::U8Clz => {
                        let v = self.builder.ins().clz(arg);
                        (v, types::I8, TypeId::I8)
                    }
                    UnaryIntOp::I16Clz | UnaryIntOp::U16Clz => {
                        let v = self.builder.ins().clz(arg);
                        (v, types::I16, TypeId::I16)
                    }
                    UnaryIntOp::I32Clz | UnaryIntOp::U32Clz => {
                        let v = self.builder.ins().clz(arg);
                        (v, types::I32, TypeId::I32)
                    }
                    UnaryIntOp::I64Clz | UnaryIntOp::U64Clz => {
                        let v = self.builder.ins().clz(arg);
                        (v, types::I64, TypeId::I64)
                    }
                    // ctz
                    UnaryIntOp::I8Ctz | UnaryIntOp::U8Ctz => {
                        let v = self.builder.ins().ctz(arg);
                        (v, types::I8, TypeId::I8)
                    }
                    UnaryIntOp::I16Ctz | UnaryIntOp::U16Ctz => {
                        let v = self.builder.ins().ctz(arg);
                        (v, types::I16, TypeId::I16)
                    }
                    UnaryIntOp::I32Ctz | UnaryIntOp::U32Ctz => {
                        let v = self.builder.ins().ctz(arg);
                        (v, types::I32, TypeId::I32)
                    }
                    UnaryIntOp::I64Ctz | UnaryIntOp::U64Ctz => {
                        let v = self.builder.ins().ctz(arg);
                        (v, types::I64, TypeId::I64)
                    }
                    // popcnt
                    UnaryIntOp::I8Popcnt | UnaryIntOp::U8Popcnt => {
                        let v = self.builder.ins().popcnt(arg);
                        (v, types::I8, TypeId::I8)
                    }
                    UnaryIntOp::I16Popcnt | UnaryIntOp::U16Popcnt => {
                        let v = self.builder.ins().popcnt(arg);
                        (v, types::I16, TypeId::I16)
                    }
                    UnaryIntOp::I32Popcnt | UnaryIntOp::U32Popcnt => {
                        let v = self.builder.ins().popcnt(arg);
                        (v, types::I32, TypeId::I32)
                    }
                    UnaryIntOp::I64Popcnt | UnaryIntOp::U64Popcnt => {
                        let v = self.builder.ins().popcnt(arg);
                        (v, types::I64, TypeId::I64)
                    }
                    // bitrev
                    UnaryIntOp::I8Bitrev | UnaryIntOp::U8Bitrev => {
                        let v = self.builder.ins().bitrev(arg);
                        (v, types::I8, TypeId::I8)
                    }
                    UnaryIntOp::I16Bitrev | UnaryIntOp::U16Bitrev => {
                        let v = self.builder.ins().bitrev(arg);
                        (v, types::I16, TypeId::I16)
                    }
                    UnaryIntOp::I32Bitrev | UnaryIntOp::U32Bitrev => {
                        let v = self.builder.ins().bitrev(arg);
                        (v, types::I32, TypeId::I32)
                    }
                    UnaryIntOp::I64Bitrev | UnaryIntOp::U64Bitrev => {
                        let v = self.builder.ins().bitrev(arg);
                        (v, types::I64, TypeId::I64)
                    }
                };
                Ok(CompiledValue { value, ty, type_id })
            }
            IntrinsicHandler::BinaryIntOp(op) => {
                use crate::intrinsics::BinaryIntOp;
                if args.len() < 2 {
                    return Err(format!(
                        "binary int intrinsic \"{}\" requires 2 arguments",
                        intrinsic_key
                    ));
                }
                let arg1 = args[0];
                let arg2 = args[1];
                let (value, ty, type_id) = match op {
                    // min signed
                    BinaryIntOp::I8Min => {
                        let v = self.builder.ins().smin(arg1, arg2);
                        (v, types::I8, TypeId::I8)
                    }
                    BinaryIntOp::I16Min => {
                        let v = self.builder.ins().smin(arg1, arg2);
                        (v, types::I16, TypeId::I16)
                    }
                    BinaryIntOp::I32Min => {
                        let v = self.builder.ins().smin(arg1, arg2);
                        (v, types::I32, TypeId::I32)
                    }
                    BinaryIntOp::I64Min => {
                        let v = self.builder.ins().smin(arg1, arg2);
                        (v, types::I64, TypeId::I64)
                    }
                    // min unsigned
                    BinaryIntOp::U8Min => {
                        let v = self.builder.ins().umin(arg1, arg2);
                        (v, types::I8, TypeId::U8)
                    }
                    BinaryIntOp::U16Min => {
                        let v = self.builder.ins().umin(arg1, arg2);
                        (v, types::I16, TypeId::U16)
                    }
                    BinaryIntOp::U32Min => {
                        let v = self.builder.ins().umin(arg1, arg2);
                        (v, types::I32, TypeId::U32)
                    }
                    BinaryIntOp::U64Min => {
                        let v = self.builder.ins().umin(arg1, arg2);
                        (v, types::I64, TypeId::U64)
                    }
                    // max signed
                    BinaryIntOp::I8Max => {
                        let v = self.builder.ins().smax(arg1, arg2);
                        (v, types::I8, TypeId::I8)
                    }
                    BinaryIntOp::I16Max => {
                        let v = self.builder.ins().smax(arg1, arg2);
                        (v, types::I16, TypeId::I16)
                    }
                    BinaryIntOp::I32Max => {
                        let v = self.builder.ins().smax(arg1, arg2);
                        (v, types::I32, TypeId::I32)
                    }
                    BinaryIntOp::I64Max => {
                        let v = self.builder.ins().smax(arg1, arg2);
                        (v, types::I64, TypeId::I64)
                    }
                    // max unsigned
                    BinaryIntOp::U8Max => {
                        let v = self.builder.ins().umax(arg1, arg2);
                        (v, types::I8, TypeId::U8)
                    }
                    BinaryIntOp::U16Max => {
                        let v = self.builder.ins().umax(arg1, arg2);
                        (v, types::I16, TypeId::U16)
                    }
                    BinaryIntOp::U32Max => {
                        let v = self.builder.ins().umax(arg1, arg2);
                        (v, types::I32, TypeId::U32)
                    }
                    BinaryIntOp::U64Max => {
                        let v = self.builder.ins().umax(arg1, arg2);
                        (v, types::I64, TypeId::U64)
                    }
                    // rotl (arg2 is u8, needs extension to target type)
                    BinaryIntOp::I8Rotl | BinaryIntOp::U8Rotl => {
                        let v = self.builder.ins().rotl(arg1, arg2);
                        (v, types::I8, TypeId::I8)
                    }
                    BinaryIntOp::I16Rotl | BinaryIntOp::U16Rotl => {
                        let amt = self.builder.ins().uextend(types::I16, arg2);
                        let v = self.builder.ins().rotl(arg1, amt);
                        (v, types::I16, TypeId::I16)
                    }
                    BinaryIntOp::I32Rotl | BinaryIntOp::U32Rotl => {
                        let amt = self.builder.ins().uextend(types::I32, arg2);
                        let v = self.builder.ins().rotl(arg1, amt);
                        (v, types::I32, TypeId::I32)
                    }
                    BinaryIntOp::I64Rotl | BinaryIntOp::U64Rotl => {
                        let amt = self.builder.ins().uextend(types::I64, arg2);
                        let v = self.builder.ins().rotl(arg1, amt);
                        (v, types::I64, TypeId::I64)
                    }
                    // rotr (arg2 is u8, needs extension to target type)
                    BinaryIntOp::I8Rotr | BinaryIntOp::U8Rotr => {
                        let v = self.builder.ins().rotr(arg1, arg2);
                        (v, types::I8, TypeId::I8)
                    }
                    BinaryIntOp::I16Rotr | BinaryIntOp::U16Rotr => {
                        let amt = self.builder.ins().uextend(types::I16, arg2);
                        let v = self.builder.ins().rotr(arg1, amt);
                        (v, types::I16, TypeId::I16)
                    }
                    BinaryIntOp::I32Rotr | BinaryIntOp::U32Rotr => {
                        let amt = self.builder.ins().uextend(types::I32, arg2);
                        let v = self.builder.ins().rotr(arg1, amt);
                        (v, types::I32, TypeId::I32)
                    }
                    BinaryIntOp::I64Rotr | BinaryIntOp::U64Rotr => {
                        let amt = self.builder.ins().uextend(types::I64, arg2);
                        let v = self.builder.ins().rotr(arg1, amt);
                        (v, types::I64, TypeId::I64)
                    }
                };
                Ok(CompiledValue { value, ty, type_id })
            }
        }
    }

    /// Box a value as an interface type.
    /// Coerce a value to match a target type if needed.
    ///
    /// Handles two cases:
    /// - If target is an interface and value is not, boxes the value
    /// - If target is a union and value is not, wraps the value in a union
    ///
    /// Returns the value unchanged if no coercion is needed.
    pub fn coerce_to_type(
        &mut self,
        value: CompiledValue,
        target_type_id: TypeId,
    ) -> Result<CompiledValue, String> {
        let (is_target_interface, is_value_interface, is_target_union, is_value_union) = {
            let arena = self.arena();
            (
                arena.is_interface(target_type_id),
                arena.is_interface(value.type_id),
                arena.is_union(target_type_id),
                arena.is_union(value.type_id),
            )
        };
        if is_target_interface && !is_value_interface {
            self.box_interface_value(value, target_type_id)
        } else if is_target_union && !is_value_union {
            self.construct_union_id(value, target_type_id)
        } else {
            Ok(value)
        }
    }

    /// Box a value as an interface type.
    ///
    /// This method avoids borrow issues by having exclusive access to self.
    /// If the value is already an interface or the type is not an interface,
    /// returns the value unchanged.
    pub fn box_interface_value(
        &mut self,
        value: CompiledValue,
        interface_type_id: TypeId,
    ) -> Result<CompiledValue, String> {
        crate::interface_vtable::box_interface_value_id(
            self.builder,
            self.codegen_ctx,
            self.env,
            value,
            interface_type_id,
        )
    }

    /// Compile default expressions for omitted parameters.
    ///
    /// This is a unified helper used by function calls, method calls, and static method calls.
    /// It takes pre-extracted raw pointers to default expressions to avoid borrow checker issues.
    ///
    /// # Arguments
    /// - `default_ptrs`: Raw pointers to default expressions (indexed by parameter position)
    /// - `start_index`: Index of the first omitted parameter
    /// - `expected_type_ids`: Expected TypeIds for the omitted parameters (slice starting at start_index)
    /// - `is_generic_class`: Whether this is a generic class call (needs value_to_word conversion)
    ///
    /// # Safety
    /// The raw pointers must point to data in EntityRegistry which outlives compilation.
    /// Compile default expressions for omitted parameters.
    ///
    /// This is a unified helper used by function calls, method calls, and static method calls.
    /// It takes pre-extracted raw pointers to default expressions to avoid borrow checker issues.
    ///
    /// # Arguments
    /// - `default_ptrs`: Raw pointers to default expressions (indexed by parameter position)
    /// - `start_index`: Index of the first omitted parameter
    /// - `expected_type_ids`: Expected TypeIds for the omitted parameters (slice starting at start_index)
    /// - `is_generic_class`: Whether this is a generic class call (needs value_to_word conversion)
    ///
    /// # Safety
    /// The raw pointers must point to data in EntityRegistry which outlives compilation.
    pub fn compile_defaults_from_ptrs(
        &mut self,
        default_ptrs: &[Option<*const Expr>],
        start_index: usize,
        expected_type_ids: &[TypeId],
        is_generic_class: bool,
    ) -> Result<Vec<Value>, String> {
        use crate::types::value_to_word;

        let mut args = Vec::new();
        for (i, &param_type_id) in expected_type_ids.iter().enumerate() {
            let param_idx = start_index + i;
            if let Some(Some(default_ptr)) = default_ptrs.get(param_idx) {
                // SAFETY: The pointer points to data in EntityRegistry which is owned by
                // AnalyzedProgram. AnalyzedProgram outlives this entire compilation session.
                // The data is not moved or modified, so the pointer remains valid.
                let default_expr: &Expr = unsafe { &**default_ptr };
                let compiled = self.expr(default_expr)?;

                // Coerce to the expected param type (handles interface boxing, union construction)
                let compiled = self.coerce_to_type(compiled, param_type_id)?;

                // Handle integer narrowing/widening if needed
                let expected_ty = self.cranelift_type(param_type_id);
                let compiled = if compiled.ty.is_int()
                    && expected_ty.is_int()
                    && expected_ty.bits() != compiled.ty.bits()
                {
                    let new_value = if expected_ty.bits() < compiled.ty.bits() {
                        self.builder.ins().ireduce(expected_ty, compiled.value)
                    } else {
                        self.builder.ins().sextend(expected_ty, compiled.value)
                    };
                    CompiledValue {
                        value: new_value,
                        ty: expected_ty,
                        type_id: param_type_id,
                    }
                } else {
                    compiled
                };

                // Generic class methods expect i64 for TypeParam, convert if needed
                let arg_value = if is_generic_class && compiled.ty != types::I64 {
                    let ptr_type = self.ptr_type();
                    let arena = self.env.analyzed.type_arena();
                    let registry = self.env.analyzed.entity_registry();
                    value_to_word(
                        self.builder,
                        &compiled,
                        ptr_type,
                        None, // No heap alloc needed for primitive conversions
                        arena,
                        registry,
                    )?
                } else {
                    compiled.value
                };
                args.push(arg_value);
            }
        }

        Ok(args)
    }
}

impl<'a, 'b, 'ctx> crate::vtable_ctx::VtableCtx for Cg<'a, 'b, 'ctx> {
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

    fn resolve_type_str_or_interface(&self, name: &str) -> Option<vole_identity::TypeDefId> {
        let query = self.query();
        let module_id = self
            .current_module_id()
            .unwrap_or_else(|| query.main_module());
        query.resolve_type_def_by_str(module_id, name)
    }

    fn native_registry(&self) -> &vole_runtime::NativeRegistry {
        &self.env.state.native_registry
    }

    fn interface_vtables(&self) -> &RefCell<crate::interface_vtable::InterfaceVtableRegistry> {
        &self.env.state.interface_vtables
    }

    fn type_metadata(&self) -> &TypeMetadataMap {
        &self.env.state.type_metadata
    }

    fn method_func_keys(&self) -> &FxHashMap<(vole_identity::TypeDefId, NameId), FunctionKey> {
        &self.env.state.method_func_keys
    }
}
