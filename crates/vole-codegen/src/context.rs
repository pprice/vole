// src/codegen/context.rs
//
// Unified codegen context - bundles all state needed during code generation.
// Methods are implemented across multiple files using split impl blocks.

use std::collections::HashMap;

use cranelift::prelude::{AbiParam, FunctionBuilder, InstBuilder, Type, Value, Variable, types};
use cranelift_module::{FuncId, Module};

use crate::errors::CodegenError;
use crate::{FunctionKey, RuntimeFn};
use smallvec::SmallVec;
use vole_frontend::Symbol;
use vole_runtime::native_registry::NativeType;
use vole_sema::PrimitiveType;
use vole_sema::implement_registry::ExternalMethodInfo;
use vole_sema::type_arena::{SemaType as ArenaType, TypeId};

use super::lambda::CaptureBinding;
use super::types::{
    CodegenCtx, CompileCtx, CompiledValue, ExplicitParams, FunctionCtx, native_type_to_cranelift,
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
    pub bindings: &'a HashMap<Symbol, CaptureBinding>,
    pub closure_var: Variable,
}

/// Key for caching pure runtime function calls
pub type CallCacheKey = (RuntimeFn, SmallVec<[Value; 4]>);

/// Helper macro to prefer split codegen_ctx over fallback ctx (same method name)
macro_rules! split_cg {
    ($self:expr, $method:ident()) => {
        if let Some(cg_ctx) = &$self.codegen_ctx {
            cg_ctx.$method()
        } else {
            $self.ctx.$method()
        }
    };
}

/// Helper macro to prefer split explicit_params field over fallback ctx method
macro_rules! split_ep {
    ($self:expr, $field:ident, $ctx_method:ident()) => {
        if let Some(ep) = &$self.explicit_params {
            ep.$field
        } else {
            $self.ctx.$ctx_method()
        }
    };
}

/// Unified codegen context - all state needed for code generation.
///
/// Lifetimes:
/// - 'a: lifetime of local state (builder, vars, cf, captures)
/// - 'b: lifetime of FunctionBuilder's internal data
/// - 'ctx: lifetime of CompileCtx's inner references (can outlive 'a for lambdas)
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
    pub vars: &'a mut HashMap<Symbol, (Variable, TypeId)>,
    pub ctx: &'a mut CompileCtx<'ctx>,
    pub cf: &'a mut ControlFlow,
    pub captures: Option<Captures<'a>>,
    /// For recursive lambdas: the binding name that captures itself
    pub self_capture: Option<Symbol>,
    /// Cache for pure runtime function calls: (func, args) -> result
    pub call_cache: HashMap<CallCacheKey, Value>,
    /// Cache for field access: (instance_ptr, slot) -> field_value
    pub field_cache: HashMap<(Value, u32), Value>,
    /// Return type of the current function (moved from CompileCtx for cleaner separation)
    pub return_type: Option<TypeId>,

    // ========== Split context fields (for incremental migration) ==========
    // These are Optional to support both legacy (CompileCtx) and new (split) modes.
    // When set, accessor methods prefer these over ctx fields.
    /// Split mutable JIT infrastructure (module, func_registry)
    #[allow(dead_code)]
    codegen_ctx: Option<&'a mut CodegenCtx<'ctx>>,
    /// Split per-function state (return type, substitutions)
    #[allow(dead_code)]
    function_ctx: Option<&'a FunctionCtx<'ctx>>,
    /// Split read-only lookup tables
    #[allow(dead_code)]
    explicit_params: Option<&'a ExplicitParams<'ctx>>,
}

impl<'a, 'b, 'ctx> Cg<'a, 'b, 'ctx> {
    /// Create a new codegen context using split context types.
    ///
    /// This is the preferred constructor for new code. It takes the split contexts
    /// (CodegenCtx, FunctionCtx, ExplicitParams) alongside the legacy CompileCtx.
    /// During migration, both ctx and the split contexts are available - accessor
    /// methods will prefer the split contexts when set.
    ///
    /// # Arguments
    /// * `builder` - Cranelift FunctionBuilder for IR emission
    /// * `vars` - Variable bindings for the current function
    /// * `ctx` - Legacy CompileCtx (still required during migration)
    /// * `cf` - Control flow context for loops
    /// * `codegen_ctx` - Split mutable JIT infrastructure
    /// * `function_ctx` - Split per-function state
    /// * `explicit_params` - Split read-only lookup tables
    /// * `captures` - Optional closure captures
    /// * `return_type` - Function return type
    #[allow(dead_code)] // Part of incremental migration
    #[allow(clippy::too_many_arguments)]
    pub fn new_split(
        builder: &'a mut FunctionBuilder<'b>,
        vars: &'a mut HashMap<Symbol, (Variable, TypeId)>,
        ctx: &'a mut CompileCtx<'ctx>,
        cf: &'a mut ControlFlow,
        codegen_ctx: &'a mut CodegenCtx<'ctx>,
        function_ctx: &'a FunctionCtx<'ctx>,
        explicit_params: &'a ExplicitParams<'ctx>,
        captures: Option<Captures<'a>>,
        return_type: Option<TypeId>,
    ) -> Self {
        Self {
            builder,
            vars,
            ctx,
            cf,
            captures,
            self_capture: None,
            call_cache: HashMap::new(),
            field_cache: HashMap::new(),
            return_type,
            codegen_ctx: Some(codegen_ctx),
            function_ctx: Some(function_ctx),
            explicit_params: Some(explicit_params),
        }
    }

    /// Create a codegen context with explicit params during CompileCtx migration.
    ///
    /// This constructor is for the transition period where we need CompileCtx for
    /// mutable JIT infrastructure (module, func_registry) but want to use the new
    /// split context types for read-only data.
    ///
    /// CodegenCtx is NOT taken because it would conflict with CompileCtx's mutable
    /// references to the same data. The accessors will use explicit_params for
    /// read-only data and fall back to ctx for mutable operations.
    ///
    /// # Arguments
    /// * `builder` - Cranelift FunctionBuilder for IR emission
    /// * `vars` - Variable bindings for the current function
    /// * `ctx` - CompileCtx (provides mutable JIT infrastructure)
    /// * `cf` - Control flow context for loops
    /// * `function_ctx` - Split per-function state
    /// * `explicit_params` - Split read-only lookup tables
    /// * `captures` - Optional closure captures
    /// * `return_type` - Function return type
    #[allow(dead_code)] // Part of incremental migration
    #[allow(clippy::too_many_arguments)]
    pub fn new_with_params(
        builder: &'a mut FunctionBuilder<'b>,
        vars: &'a mut HashMap<Symbol, (Variable, TypeId)>,
        ctx: &'a mut CompileCtx<'ctx>,
        cf: &'a mut ControlFlow,
        function_ctx: &'a FunctionCtx<'ctx>,
        explicit_params: &'a ExplicitParams<'ctx>,
        captures: Option<Captures<'a>>,
        return_type: Option<TypeId>,
    ) -> Self {
        Self {
            builder,
            vars,
            ctx,
            cf,
            captures,
            self_capture: None,
            call_cache: HashMap::new(),
            field_cache: HashMap::new(),
            return_type,
            // CodegenCtx not used - would conflict with ctx's mutable refs
            codegen_ctx: None,
            function_ctx: Some(function_ctx),
            explicit_params: Some(explicit_params),
        }
    }

    /// Check if we're in a closure context with captures
    pub fn has_captures(&self) -> bool {
        self.captures.is_some()
    }

    // ========== Context accessors for migration ==========

    /// Get a TypeCtx view for functions that need the new API.
    /// This enables incremental migration from CompileCtx to TypeCtx + FunctionCtx.
    #[inline]
    pub fn type_ctx(&self) -> super::types::TypeCtx<'_> {
        super::types::TypeCtx::new(self.ctx.query(), self.ctx.ptr_type())
    }

    /// Get arena Rc for FunctionCtx operations (for future migration steps)
    #[inline]
    #[allow(dead_code)]
    pub fn arena_rc(&self) -> &std::rc::Rc<std::cell::RefCell<vole_sema::type_arena::TypeArena>> {
        self.ctx.arena_rc()
    }

    /// Substitute type parameters (delegates to CompileCtx for now)
    #[inline]
    pub fn substitute_type(&self, ty: TypeId) -> TypeId {
        self.ctx.substitute_type_id(ty)
    }

    /// Get current module path (will move to FunctionCtx as ModuleId)
    #[inline]
    pub fn current_module(&self) -> Option<&'ctx str> {
        self.ctx.module_path()
    }

    /// Get type substitutions (will move to FunctionCtx)
    #[inline]
    #[allow(dead_code)]
    pub fn type_substitutions(&self) -> Option<&'ctx HashMap<vole_identity::NameId, TypeId>> {
        self.ctx.substitutions()
    }

    /// Get entity registry reference
    #[inline]
    pub fn registry(&self) -> &'ctx vole_sema::entity_registry::EntityRegistry {
        self.ctx.registry()
    }

    /// Borrow the name table (shorter than query().name_table_rc().borrow())
    #[inline]
    pub fn name_table(&self) -> std::cell::Ref<'_, vole_identity::NameTable> {
        self.ctx.query().name_table_rc().borrow()
    }

    // ========== Convenience accessors for migration ==========
    // These wrap ctx.* calls to enable later migration to split contexts.
    // Allowed dead_code during incremental migration.

    /// Get the pointer type (Cranelift platform pointer)
    #[inline]
    pub fn ptr_type(&self) -> Type {
        split_cg!(self, ptr_type())
    }

    /// Get the query interface for the analyzed program
    #[inline]
    pub fn query(&self) -> vole_sema::ProgramQuery<'_> {
        // Always use ctx.query() for now - CodegenCtx stores &ProgramQuery
        // but we need to return an owned ProgramQuery
        self.ctx.query()
    }

    /// Borrow the type arena
    #[inline]
    pub fn arena(&self) -> std::cell::Ref<'_, vole_sema::type_arena::TypeArena> {
        split_cg!(self, arena())
    }

    /// Get expression type by NodeId
    #[allow(dead_code)]
    #[inline]
    pub fn get_expr_type(&self, node_id: &vole_frontend::NodeId) -> Option<TypeId> {
        self.ctx.get_expr_type(node_id)
    }

    /// Get substituted return type for generic method calls
    #[allow(dead_code)]
    #[inline]
    pub fn get_substituted_return_type(&self, node_id: &vole_frontend::NodeId) -> Option<TypeId> {
        self.ctx.get_substituted_return_type(node_id)
    }

    /// Get type metadata map
    #[inline]
    pub fn type_metadata(&self) -> &'ctx HashMap<Symbol, super::types::TypeMetadata> {
        split_ep!(self, type_metadata, type_meta())
    }

    /// Get impl method infos map
    #[allow(dead_code)] // Part of incremental migration
    #[inline]
    pub fn impl_method_infos(
        &self,
    ) -> &'ctx HashMap<
        (
            vole_sema::implement_registry::ImplTypeId,
            vole_identity::NameId,
        ),
        super::types::MethodInfo,
    > {
        split_ep!(self, impl_method_infos, impl_methods())
    }

    /// Get global variable initializer by name
    #[allow(dead_code)] // Part of incremental migration
    #[inline]
    pub fn global_init(&self, name: Symbol) -> Option<&vole_frontend::Expr> {
        if let Some(ep) = &self.explicit_params {
            ep.global_inits.get(&name)
        } else {
            self.ctx.global_init(name)
        }
    }

    /// Get source file pointer for error reporting
    #[allow(dead_code)] // Part of incremental migration
    #[inline]
    pub fn source_file(&self) -> (*const u8, usize) {
        if let Some(ep) = &self.explicit_params {
            ep.source_file_ptr
        } else {
            self.ctx.source_file()
        }
    }

    /// Increment lambda counter and return new value
    #[allow(dead_code)] // Part of incremental migration
    #[inline]
    pub fn next_lambda_id(&self) -> usize {
        if let Some(ep) = &self.explicit_params {
            let id = ep.lambda_counter.get();
            ep.lambda_counter.set(id + 1);
            id
        } else {
            self.ctx.next_lambda_id()
        }
    }

    /// Get native function registry
    #[allow(dead_code)] // Part of incremental migration
    #[inline]
    pub fn native_registry(&self) -> &'ctx vole_runtime::NativeRegistry {
        split_ep!(self, native_registry, native_funcs())
    }

    /// Get FunctionCtx for split context operations
    #[allow(dead_code)]
    #[inline]
    pub fn function_ctx(&self) -> FunctionCtx<'ctx> {
        self.ctx.function_ctx()
    }

    /// Get the interner for symbol resolution
    #[inline]
    pub fn interner(&self) -> &'ctx vole_frontend::Interner {
        split_ep!(self, interner, interner())
    }

    // ========== Arena helpers ==========

    /// Get an update interface for arena mutations.
    /// Centralizes all borrow_mut() calls for cleaner code.
    #[inline]
    pub fn update(&self) -> vole_sema::ProgramUpdate<'_> {
        self.ctx.update()
    }

    /// Find the nil variant index in a union (for optional handling)
    pub fn find_nil_variant(&self, ty: TypeId) -> Option<usize> {
        let arena = self.ctx.arena();
        if let Some(variants) = arena.unwrap_union(ty) {
            variants.iter().position(|&id| id.is_nil())
        } else {
            None
        }
    }

    /// Convert a TypeId to a Cranelift type
    pub fn cranelift_type(&self, ty: TypeId) -> Type {
        // Use type_ctx() for split context migration (same underlying values as ctx)
        let type_ctx = self.type_ctx();
        type_id_to_cranelift(ty, &type_ctx.arena(), type_ctx.pointer_type)
    }

    /// Unwrap an interface type, returning the TypeDefId if it is one
    pub fn interface_type_def_id(&self, ty: TypeId) -> Option<vole_identity::TypeDefId> {
        self.ctx.arena().unwrap_interface(ty).map(|(id, _)| id)
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
        self.ctx
            .funcs_ref()
            .func_id(key)
            .ok_or_else(|| "function id not found".to_string())
    }

    /// Get a function reference for calling
    pub fn func_ref(
        &mut self,
        key: FunctionKey,
    ) -> Result<cranelift::codegen::ir::FuncRef, String> {
        let func_id = self.func_id(key)?;
        Ok(self
            .ctx
            .jit_module()
            .declare_func_in_func(func_id, self.builder.func))
    }

    /// Call a runtime function and return the first result (or error if no results)
    pub fn call_runtime(&mut self, runtime: RuntimeFn, args: &[Value]) -> Result<Value, String> {
        let key = self.ctx.funcs().runtime_key(runtime).ok_or_else(|| {
            CodegenError::not_found("runtime function", runtime.name()).to_string()
        })?;
        let func_ref = self.func_ref(key)?;
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
        let key = self
            .ctx
            .funcs()
            .runtime_key(runtime)
            .ok_or_else(|| format!("{} not registered", runtime.name()))?;
        let func_ref = self.func_ref(key)?;
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
        let value = self.builder.ins().iconst(ty, n);
        CompiledValue { value, ty, type_id }
    }

    /// Create a float constant with explicit type (for bidirectional inference)
    pub fn float_const(&mut self, n: f64, type_id: TypeId) -> CompiledValue {
        let arena = self.ctx.arena();
        let (ty, value) = match arena.get(type_id) {
            ArenaType::Primitive(PrimitiveType::F32) => {
                drop(arena);
                let v = self.builder.ins().f32const(n as f32);
                (types::F32, v)
            }
            _ => {
                drop(arena);
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
            ty: self.ctx.ptr_type(),
            type_id: TypeId::STRING,
        }
    }

    /// Create a CompiledValue from a value and TypeId
    pub fn typed_value_interned(&self, value: Value, type_id: TypeId) -> CompiledValue {
        let arena = self.ctx.arena();
        CompiledValue {
            value,
            ty: type_id_to_cranelift(type_id, &arena, self.ctx.ptr_type()),
            type_id,
        }
    }

    // ========== Control flow helpers ==========

    /// Extend a boolean condition to I32 for use with brif
    pub fn cond_to_i32(&mut self, cond: Value) -> Value {
        self.builder.ins().uextend(types::I32, cond)
    }

    // ========== External native function calls ==========

    /// Call an external native function using TypeId for return type.
    pub fn call_external_id(
        &mut self,
        external_info: &ExternalMethodInfo,
        args: &[Value],
        return_type_id: TypeId,
    ) -> Result<CompiledValue, String> {
        // Get string names from NameId and look up native function
        let native_func = {
            let name_table = self.name_table();
            let module_path = name_table
                .last_segment_str(external_info.module_path)
                .ok_or_else(|| "module_path NameId has no segment".to_string())?;
            let native_name = name_table
                .last_segment_str(external_info.native_name)
                .ok_or_else(|| "native_name NameId has no segment".to_string())?;
            self.ctx
                .native_funcs()
                .lookup(&module_path, &native_name)
                .ok_or_else(|| {
                    format!(
                        "Native function {}::{} not found in registry",
                        module_path, native_name
                    )
                })?
        };

        // Build the Cranelift signature from NativeSignature
        let mut sig = self.ctx.jit_module().make_signature();
        for param_type in &native_func.signature.params {
            sig.params.push(AbiParam::new(native_type_to_cranelift(
                param_type,
                self.ctx.ptr_type(),
            )));
        }
        if native_func.signature.return_type != NativeType::Nil {
            sig.returns.push(AbiParam::new(native_type_to_cranelift(
                &native_func.signature.return_type,
                self.ctx.ptr_type(),
            )));
        }

        // Import the signature and emit an indirect call
        let sig_ref = self.builder.import_signature(sig);
        let func_ptr = native_func.ptr;

        // Load the function pointer as a constant
        let func_ptr_val = self
            .builder
            .ins()
            .iconst(self.ctx.ptr_type(), func_ptr as i64);

        // Emit the indirect call
        let call_inst = self
            .builder
            .ins()
            .call_indirect(sig_ref, func_ptr_val, args);
        let results = self.builder.inst_results(call_inst);

        if results.is_empty() {
            Ok(self.void_value())
        } else {
            let arena = self.ctx.arena();
            let cranelift_ty = type_id_to_cranelift(return_type_id, &arena, self.ctx.ptr_type());
            drop(arena);
            Ok(CompiledValue {
                value: results[0],
                ty: cranelift_ty,
                type_id: return_type_id,
            })
        }
    }
}
