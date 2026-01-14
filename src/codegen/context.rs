// src/codegen/context.rs
//
// Unified codegen context - bundles all state needed during code generation.
// Methods are implemented across multiple files using split impl blocks.

use std::collections::HashMap;

use cranelift::prelude::{AbiParam, FunctionBuilder, InstBuilder, Value, Variable, types};
use cranelift_module::{FuncId, Module};

use crate::codegen::{FunctionKey, RuntimeFn};
use smallvec::SmallVec;
use crate::errors::CodegenError;
use crate::frontend::Symbol;
use crate::runtime::native_registry::NativeType;
use crate::sema::implement_registry::ExternalMethodInfo;
use crate::sema::{PrimitiveType, Type};

use super::lambda::CaptureBinding;
use super::types::{CompileCtx, CompiledValue, native_type_to_cranelift, type_to_cranelift};

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
/// Key for caching pure runtime function calls
pub type CallCacheKey = (RuntimeFn, SmallVec<[Value; 4]>);

pub(crate) struct Cg<'a, 'b, 'ctx> {
    pub builder: &'a mut FunctionBuilder<'b>,
    pub vars: &'a mut HashMap<Symbol, (Variable, Type)>,
    pub ctx: &'a mut CompileCtx<'ctx>,
    pub cf: &'a mut ControlFlow,
    pub captures: Option<Captures<'a>>,
    /// Cache for pure runtime function calls: (func, args) -> result
    pub call_cache: HashMap<CallCacheKey, Value>,
    /// Cache for field access: (instance_ptr, slot) -> field_value
    pub field_cache: HashMap<(Value, u32), Value>,
}

impl<'a, 'b, 'ctx> Cg<'a, 'b, 'ctx> {
    /// Create a new codegen context
    pub fn new(
        builder: &'a mut FunctionBuilder<'b>,
        vars: &'a mut HashMap<Symbol, (Variable, Type)>,
        ctx: &'a mut CompileCtx<'ctx>,
        cf: &'a mut ControlFlow,
    ) -> Self {
        Self {
            builder,
            vars,
            ctx,
            cf,
            captures: None,
            call_cache: HashMap::new(),
            field_cache: HashMap::new(),
        }
    }

    /// Create a codegen context with capture information for closures
    pub fn with_captures(
        builder: &'a mut FunctionBuilder<'b>,
        vars: &'a mut HashMap<Symbol, (Variable, Type)>,
        ctx: &'a mut CompileCtx<'ctx>,
        cf: &'a mut ControlFlow,
        captures: Captures<'a>,
    ) -> Self {
        Self {
            builder,
            vars,
            ctx,
            cf,
            captures: Some(captures),
            call_cache: HashMap::new(),
            field_cache: HashMap::new(),
        }
    }

    /// Check if we're in a closure context with captures
    pub fn has_captures(&self) -> bool {
        self.captures.is_some()
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
            .func_registry
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
            .module
            .declare_func_in_func(func_id, self.builder.func))
    }

    /// Call a runtime function and return the first result (or error if no results)
    pub fn call_runtime(&mut self, runtime: RuntimeFn, args: &[Value]) -> Result<Value, String> {
        let key = self.ctx.func_registry.runtime_key(runtime).ok_or_else(|| {
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
    pub fn call_runtime_cached(&mut self, func: RuntimeFn, args: &[Value]) -> Result<Value, String> {
        let key = (func, SmallVec::from_slice(args));
        if let Some(&cached) = self.call_cache.get(&key) {
            return Ok(cached);
        }
        let result = self.call_runtime(func, args)?;
        self.call_cache.insert(key, result);
        Ok(result)
    }

    /// Invalidate call cache (call before mutations)
    #[allow(dead_code)]
    pub fn invalidate_call_cache(&mut self) {
        self.call_cache.clear();
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
            .func_registry
            .runtime_key(runtime)
            .ok_or_else(|| format!("{} not registered", runtime.name()))?;
        let func_ref = self.func_ref(key)?;
        self.builder.ins().call(func_ref, args);
        Ok(())
    }

    /// Create a void return value
    pub fn void_value(&mut self) -> CompiledValue {
        CompiledValue::void(self.builder)
    }

    // ========== CompiledValue constructors ==========

    /// Wrap a Cranelift value as a Bool CompiledValue
    pub fn bool_value(&self, value: Value) -> CompiledValue {
        CompiledValue {
            value,
            ty: types::I8,
            vole_type: Type::Primitive(PrimitiveType::Bool),
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
            vole_type: Type::Primitive(PrimitiveType::I64),
        }
    }

    /// Create an I64 constant
    #[allow(dead_code)]
    pub fn i64_const(&mut self, n: i64) -> CompiledValue {
        let value = self.builder.ins().iconst(types::I64, n);
        self.i64_value(value)
    }

    /// Create an integer constant with a specific Vole type
    pub fn int_const(&mut self, n: i64, vole_type: Type) -> CompiledValue {
        let ty = type_to_cranelift(&vole_type, self.ctx.pointer_type);
        let value = self.builder.ins().iconst(ty, n);
        CompiledValue {
            value,
            ty,
            vole_type,
        }
    }

    /// Create a float constant with explicit type (for bidirectional inference)
    pub fn float_const(&mut self, n: f64, vole_type: Type) -> CompiledValue {
        let (ty, value) = match vole_type {
            Type::Primitive(PrimitiveType::F32) => {
                let v = self.builder.ins().f32const(n as f32);
                (types::F32, v)
            }
            _ => {
                // Default to F64
                let v = self.builder.ins().f64const(n);
                (types::F64, v)
            }
        };
        CompiledValue {
            value,
            ty,
            vole_type,
        }
    }

    /// Create a nil value
    pub fn nil_value(&mut self) -> CompiledValue {
        let value = self.builder.ins().iconst(types::I8, 0);
        CompiledValue {
            value,
            ty: types::I8,
            vole_type: Type::Nil,
        }
    }

    /// Create a Done value (iterator termination sentinel)
    pub fn done_value(&mut self) -> CompiledValue {
        let value = self.builder.ins().iconst(types::I8, 0);
        CompiledValue {
            value,
            ty: types::I8,
            vole_type: Type::Done,
        }
    }

    /// Wrap a Cranelift value as a String CompiledValue
    pub fn string_value(&self, value: Value) -> CompiledValue {
        CompiledValue {
            value,
            ty: self.ctx.pointer_type,
            vole_type: Type::Primitive(PrimitiveType::String),
        }
    }

    /// Create a CompiledValue with a dynamic Vole type
    pub fn typed_value(&self, value: Value, vole_type: Type) -> CompiledValue {
        CompiledValue {
            value,
            ty: type_to_cranelift(&vole_type, self.ctx.pointer_type),
            vole_type,
        }
    }

    // ========== Control flow helpers ==========

    /// Extend a boolean condition to I32 for use with brif
    pub fn cond_to_i32(&mut self, cond: Value) -> Value {
        self.builder.ins().uextend(types::I32, cond)
    }

    // ========== External native function calls ==========

    /// Call an external native function from the NativeRegistry.
    /// Returns CompiledValue with the result, or error if function not found.
    pub fn call_external(
        &mut self,
        external_info: &ExternalMethodInfo,
        args: &[Value],
        return_type: &Type,
    ) -> Result<CompiledValue, String> {
        // Look up the native function in the registry
        let native_func = self
            .ctx
            .native_registry
            .lookup(&external_info.module_path, &external_info.native_name)
            .ok_or_else(|| {
                format!(
                    "Native function {}::{} not found in registry",
                    external_info.module_path, external_info.native_name
                )
            })?;

        // Build the Cranelift signature from NativeSignature
        let mut sig = self.ctx.module.make_signature();
        for param_type in &native_func.signature.params {
            sig.params.push(AbiParam::new(native_type_to_cranelift(
                param_type,
                self.ctx.pointer_type,
            )));
        }
        if native_func.signature.return_type != NativeType::Nil {
            sig.returns.push(AbiParam::new(native_type_to_cranelift(
                &native_func.signature.return_type,
                self.ctx.pointer_type,
            )));
        }

        // Import the signature and emit an indirect call
        let sig_ref = self.builder.import_signature(sig);
        let func_ptr = native_func.ptr;

        // Load the function pointer as a constant
        let func_ptr_val = self
            .builder
            .ins()
            .iconst(self.ctx.pointer_type, func_ptr as i64);

        // Emit the indirect call
        let call_inst = self
            .builder
            .ins()
            .call_indirect(sig_ref, func_ptr_val, args);
        let results = self.builder.inst_results(call_inst);

        if results.is_empty() {
            Ok(self.void_value())
        } else {
            Ok(CompiledValue {
                value: results[0],
                ty: type_to_cranelift(return_type, self.ctx.pointer_type),
                vole_type: return_type.clone(),
            })
        }
    }
}
