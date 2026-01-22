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
    CodegenCtx, CompiledValue, ExplicitParams, FunctionCtx, native_type_to_cranelift,
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

/// Unified codegen context - all state needed for code generation.
///
/// Lifetimes:
/// - 'a: lifetime of local state (builder, vars, cf, captures)
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
    pub vars: &'a mut HashMap<Symbol, (Variable, TypeId)>,
    pub cf: &'a mut ControlFlow,
    pub captures: Option<Captures<'a>>,
    /// For recursive lambdas: the binding name that captures itself
    pub self_capture: Option<Symbol>,
    /// Cache for pure runtime function calls: (func, args) -> result
    pub call_cache: HashMap<CallCacheKey, Value>,
    /// Cache for field access: (instance_ptr, slot) -> field_value
    pub field_cache: HashMap<(Value, u32), Value>,
    /// Return type of the current function
    pub return_type: Option<TypeId>,

    // ========== Split context fields ==========
    /// Mutable JIT infrastructure (module, func_registry) - REQUIRED
    pub codegen_ctx: &'a mut CodegenCtx<'ctx>,
    /// Per-function state (return type, substitutions) - REQUIRED
    pub function_ctx: &'a FunctionCtx<'ctx>,
    /// Read-only lookup tables - REQUIRED
    pub explicit_params: &'a ExplicitParams<'ctx>,
}

impl<'a, 'b, 'ctx> Cg<'a, 'b, 'ctx> {
    /// Create a new codegen context with split contexts.
    ///
    /// # Arguments
    /// * `builder` - Cranelift FunctionBuilder for IR emission
    /// * `vars` - Variable bindings for the current function
    /// * `cf` - Control flow context for loops
    /// * `codegen_ctx` - Mutable JIT infrastructure (module, func_registry)
    /// * `function_ctx` - Per-function state (return type, substitutions)
    /// * `explicit_params` - Read-only lookup tables
    /// * `captures` - Optional closure captures
    /// * `return_type` - Function return type
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        builder: &'a mut FunctionBuilder<'b>,
        vars: &'a mut HashMap<Symbol, (Variable, TypeId)>,
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
            cf,
            captures,
            self_capture: None,
            call_cache: HashMap::new(),
            field_cache: HashMap::new(),
            return_type,
            codegen_ctx,
            function_ctx,
            explicit_params,
        }
    }

    /// Check if we're in a closure context with captures
    pub fn has_captures(&self) -> bool {
        self.captures.is_some()
    }

    // ========== Context accessors ==========

    /// Get a TypeCtx view
    #[inline]
    pub fn type_ctx(&self) -> super::types::TypeCtx<'_> {
        super::types::TypeCtx::new(
            self.explicit_params.analyzed.query(),
            self.codegen_ctx.ptr_type(),
        )
    }

    /// Get arena Rc
    #[inline]
    pub fn arena_rc(&self) -> &std::rc::Rc<std::cell::RefCell<vole_sema::type_arena::TypeArena>> {
        self.explicit_params.analyzed.type_arena_ref()
    }

    /// Substitute type parameters using function_ctx substitutions
    #[inline]
    pub fn substitute_type(&self, ty: TypeId) -> TypeId {
        self.function_ctx
            .substitute_type_id(ty, self.explicit_params.analyzed.type_arena_ref())
    }

    /// Get current module (as ModuleId)
    #[inline]
    #[allow(dead_code)]
    pub fn current_module_id(&self) -> Option<vole_identity::ModuleId> {
        self.function_ctx.current_module
    }

    /// Get type substitutions
    #[inline]
    #[allow(dead_code)]
    pub fn type_substitutions(&self) -> Option<&'ctx HashMap<vole_identity::NameId, TypeId>> {
        self.function_ctx.substitutions
    }

    /// Alias for type_substitutions (backward compat)
    #[inline]
    pub fn substitutions(&self) -> Option<&'ctx HashMap<vole_identity::NameId, TypeId>> {
        self.function_ctx.substitutions
    }

    /// Get entity registry reference
    #[inline]
    pub fn registry(&self) -> &'ctx vole_sema::entity_registry::EntityRegistry {
        self.explicit_params.analyzed.entity_registry()
    }

    /// Borrow the name table
    #[inline]
    pub fn name_table(&self) -> std::cell::Ref<'_, vole_identity::NameTable> {
        self.explicit_params.analyzed.name_table()
    }

    /// Get the pointer type (Cranelift platform pointer)
    #[inline]
    pub fn ptr_type(&self) -> Type {
        self.codegen_ctx.ptr_type()
    }

    /// Get the query interface for the analyzed program
    #[inline]
    pub fn query(&self) -> vole_sema::ProgramQuery<'_> {
        self.explicit_params.analyzed.query()
    }

    /// Borrow the type arena
    #[inline]
    pub fn arena(&self) -> std::cell::Ref<'_, vole_sema::type_arena::TypeArena> {
        self.explicit_params.analyzed.type_arena()
    }

    /// Get expression type by NodeId (checks module-specific types if in module context)
    #[inline]
    pub fn get_expr_type(&self, node_id: &vole_frontend::NodeId) -> Option<TypeId> {
        // For module code, check module-specific expr_types first
        if let Some(module_id) = self.function_ctx.current_module {
            let name_table = self.name_table();
            let module_path = name_table.module_path(module_id);
            if let Some(module_types) = self
                .explicit_params
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
        self.explicit_params
            .analyzed
            .query()
            .expr_data()
            .get_type(*node_id)
    }

    /// Get substituted return type for generic method calls
    #[inline]
    pub fn get_substituted_return_type(&self, node_id: &vole_frontend::NodeId) -> Option<TypeId> {
        self.explicit_params
            .analyzed
            .query()
            .expr_data()
            .get_substituted_return_type(*node_id)
    }

    /// Get type metadata map
    #[inline]
    pub fn type_metadata(&self) -> &'ctx HashMap<Symbol, super::types::TypeMetadata> {
        self.explicit_params.type_metadata
    }

    /// Get impl method infos map
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
        self.explicit_params.impl_method_infos
    }

    /// Get global variable initializer by name
    #[inline]
    pub fn global_init(&self, name: Symbol) -> Option<&vole_frontend::Expr> {
        self.explicit_params.global_inits.get(&name)
    }

    /// Get source file pointer for error reporting
    #[inline]
    pub fn source_file(&self) -> (*const u8, usize) {
        self.explicit_params.source_file_ptr
    }

    /// Increment lambda counter and return new value
    #[inline]
    pub fn next_lambda_id(&self) -> usize {
        let id = self.explicit_params.lambda_counter.get();
        self.explicit_params.lambda_counter.set(id + 1);
        id
    }

    /// Get native function registry
    #[inline]
    pub fn native_registry(&self) -> &'ctx vole_runtime::NativeRegistry {
        self.explicit_params.native_registry
    }

    /// Alias for native_registry (backward compat)
    #[inline]
    pub fn native_funcs(&self) -> &'ctx vole_runtime::NativeRegistry {
        self.explicit_params.native_registry
    }

    /// Get the interner for symbol resolution
    #[inline]
    pub fn interner(&self) -> &'ctx vole_frontend::Interner {
        self.explicit_params.interner
    }

    /// Alias for type_metadata (backward compat)
    #[inline]
    pub fn type_meta(&self) -> &'ctx HashMap<Symbol, super::types::TypeMetadata> {
        self.explicit_params.type_metadata
    }

    /// Alias for impl_method_infos (backward compat)
    #[inline]
    pub fn impl_methods(
        &self,
    ) -> &'ctx HashMap<
        (
            vole_sema::implement_registry::ImplTypeId,
            vole_identity::NameId,
        ),
        super::types::MethodInfo,
    > {
        self.explicit_params.impl_method_infos
    }

    /// Get static method infos map
    #[inline]
    pub fn static_method_infos(
        &self,
    ) -> &'ctx HashMap<(vole_identity::TypeDefId, vole_identity::NameId), super::types::MethodInfo>
    {
        self.explicit_params.static_method_infos
    }

    /// Get interface vtable registry
    #[inline]
    #[allow(dead_code)]
    pub fn interface_vtables(
        &self,
    ) -> &'ctx std::cell::RefCell<crate::interface_vtable::InterfaceVtableRegistry> {
        self.explicit_params.interface_vtables
    }

    /// Get monomorph cache from entity registry
    #[inline]
    pub fn monomorph_cache(&self) -> &'ctx vole_sema::generic::MonomorphCache {
        &self
            .explicit_params
            .analyzed
            .entity_registry()
            .monomorph_cache
    }

    /// Get current module as Option<ModuleId> - use current_module_id() for new code
    #[inline]
    pub fn current_module(&self) -> Option<vole_identity::ModuleId> {
        self.function_ctx.current_module
    }

    /// Get analyzed program reference
    #[inline]
    pub fn analyzed(&self) -> &'ctx crate::AnalyzedProgram {
        self.explicit_params.analyzed
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

    /// Get an update interface for arena mutations.
    #[inline]
    pub fn update(&self) -> vole_sema::ProgramUpdate<'_> {
        self.codegen_ctx.update()
    }

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
        type_id_to_cranelift(ty, &self.arena(), self.ptr_type())
    }

    /// Unwrap an interface type, returning the TypeDefId if it is one
    pub fn interface_type_def_id(&self, ty: TypeId) -> Option<vole_identity::TypeDefId> {
        self.arena().unwrap_interface(ty).map(|(id, _)| id)
    }

    /// Resolve a type name Symbol to its TypeDefId (for error types, etc.)
    ///
    /// This looks up type names by short name, searching through all registered types.
    /// Callers should check the TypeDefKind if they need a specific kind.
    pub fn resolve_type(&self, sym: Symbol) -> Option<vole_identity::TypeDefId> {
        let name = self.interner().resolve(sym);
        let name_table = self.name_table();
        self.registry().type_by_short_name(name, &name_table)
    }

    /// Resolve a type name string to its TypeDefId, with fallback to interface/class search.
    ///
    /// This tries direct resolution first, then falls back to searching by short name
    /// through interfaces and classes.
    pub fn resolve_type_str_or_interface(&self, name: &str) -> Option<vole_identity::TypeDefId> {
        let name_table = self.name_table();
        // Try interface first, then class, then any type by short name
        self.registry()
            .interface_by_short_name(name, &name_table)
            .or_else(|| self.registry().class_by_short_name(name, &name_table))
            .or_else(|| self.registry().type_by_short_name(name, &name_table))
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

    /// Call a runtime function and return the first result (or error if no results)
    pub fn call_runtime(&mut self, runtime: RuntimeFn, args: &[Value]) -> Result<Value, String> {
        let key = self.funcs().runtime_key(runtime).ok_or_else(|| {
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
        let arena = self.arena();
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
            ty: self.ptr_type(),
            type_id: TypeId::STRING,
        }
    }

    /// Create a CompiledValue from a value and TypeId
    pub fn typed_value_interned(&self, value: Value, type_id: TypeId) -> CompiledValue {
        let arena = self.arena();
        CompiledValue {
            value,
            ty: type_id_to_cranelift(type_id, &arena, self.ptr_type()),
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
            self.native_registry()
                .lookup(&module_path, &native_name)
                .ok_or_else(|| {
                    format!(
                        "Native function {}::{} not found in registry",
                        module_path, native_name
                    )
                })?
        };

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
            let cranelift_ty = type_id_to_cranelift(return_type_id, &arena, ptr_type);
            drop(arena);
            Ok(CompiledValue {
                value: results[0],
                ty: cranelift_ty,
                type_id: return_type_id,
            })
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
            self.explicit_params,
            value,
            interface_type_id,
        )
    }
}

impl<'a, 'b, 'ctx> crate::vtable_ctx::VtableCtx for Cg<'a, 'b, 'ctx> {
    fn analyzed(&self) -> &crate::AnalyzedProgram {
        self.explicit_params.analyzed
    }

    fn arena(&self) -> std::cell::Ref<'_, vole_sema::type_arena::TypeArena> {
        self.explicit_params.analyzed.type_arena()
    }

    fn arena_rc(&self) -> &std::rc::Rc<std::cell::RefCell<vole_sema::type_arena::TypeArena>> {
        self.explicit_params.analyzed.type_arena_ref()
    }

    fn registry(&self) -> &vole_sema::EntityRegistry {
        self.explicit_params.analyzed.entity_registry()
    }

    fn interner(&self) -> &vole_frontend::Interner {
        self.explicit_params.interner
    }

    fn query(&self) -> vole_sema::ProgramQuery<'_> {
        self.explicit_params.analyzed.query()
    }

    fn update(&self) -> vole_sema::ProgramUpdate<'_> {
        vole_sema::ProgramUpdate::new(self.explicit_params.analyzed.type_arena_ref())
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
        let name_table = self.name_table();
        // Try interface first, then class, then any type by short name
        self.registry()
            .interface_by_short_name(name, &name_table)
            .or_else(|| self.registry().class_by_short_name(name, &name_table))
            .or_else(|| self.registry().type_by_short_name(name, &name_table))
    }

    fn native_registry(&self) -> &vole_runtime::NativeRegistry {
        self.explicit_params.native_registry
    }

    fn interface_vtables(
        &self,
    ) -> &std::cell::RefCell<crate::interface_vtable::InterfaceVtableRegistry> {
        self.explicit_params.interface_vtables
    }

    fn type_metadata(&self) -> &HashMap<Symbol, super::types::TypeMetadata> {
        self.explicit_params.type_metadata
    }

    fn impl_method_infos(
        &self,
    ) -> &HashMap<
        (
            vole_sema::implement_registry::ImplTypeId,
            vole_identity::NameId,
        ),
        super::types::MethodInfo,
    > {
        self.explicit_params.impl_method_infos
    }
}
