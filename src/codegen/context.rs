// src/codegen/context.rs
//
// Unified codegen context - bundles all state needed during code generation.
// Methods are implemented across multiple files using split impl blocks.

use std::collections::HashMap;

use cranelift::prelude::{FunctionBuilder, InstBuilder, Value, Variable, types};
use cranelift_module::{FuncId, Module};

use crate::frontend::Symbol;
use crate::sema::Type;

use super::lambda::CaptureBinding;
use super::types::{CompileCtx, CompiledValue, type_to_cranelift};

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
pub(crate) struct Cg<'a, 'b, 'ctx> {
    pub builder: &'a mut FunctionBuilder<'b>,
    pub vars: &'a mut HashMap<Symbol, (Variable, Type)>,
    pub ctx: &'a mut CompileCtx<'ctx>,
    pub cf: &'a mut ControlFlow,
    pub captures: Option<Captures<'a>>,
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

    /// Get a runtime function ID by name
    pub fn func_id(&self, name: &str) -> Result<FuncId, String> {
        self.ctx
            .func_ids
            .get(name)
            .copied()
            .ok_or_else(|| format!("{} not found", name))
    }

    /// Get a runtime function reference for calling
    pub fn func_ref(&mut self, name: &str) -> Result<cranelift::codegen::ir::FuncRef, String> {
        let func_id = self.func_id(name)?;
        Ok(self
            .ctx
            .module
            .declare_func_in_func(func_id, self.builder.func))
    }

    /// Call a runtime function and return the first result (or error if no results)
    pub fn call_runtime(&mut self, name: &str, args: &[Value]) -> Result<Value, String> {
        let func_ref = self.func_ref(name)?;
        let call = self.builder.ins().call(func_ref, args);
        let results = self.builder.inst_results(call);
        if results.is_empty() {
            Err(format!("{} returned no value", name))
        } else {
            Ok(results[0])
        }
    }

    /// Call a runtime function that returns void
    pub fn call_runtime_void(&mut self, name: &str, args: &[Value]) -> Result<(), String> {
        let func_ref = self.func_ref(name)?;
        self.builder.ins().call(func_ref, args);
        Ok(())
    }

    /// Create a void return value
    pub fn void_value(&mut self) -> CompiledValue {
        let zero = self.builder.ins().iconst(types::I64, 0);
        CompiledValue {
            value: zero,
            ty: types::I64,
            vole_type: Type::Void,
        }
    }

    // ========== CompiledValue constructors ==========

    /// Wrap a Cranelift value as a Bool CompiledValue
    pub fn bool_value(&self, value: Value) -> CompiledValue {
        CompiledValue {
            value,
            ty: types::I8,
            vole_type: Type::Bool,
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
            vole_type: Type::I64,
        }
    }

    /// Create an I64 constant
    pub fn i64_const(&mut self, n: i64) -> CompiledValue {
        let value = self.builder.ins().iconst(types::I64, n);
        self.i64_value(value)
    }

    /// Wrap a Cranelift value as an F64 CompiledValue
    pub fn f64_value(&self, value: Value) -> CompiledValue {
        CompiledValue {
            value,
            ty: types::F64,
            vole_type: Type::F64,
        }
    }

    /// Create an F64 constant
    pub fn f64_const(&mut self, n: f64) -> CompiledValue {
        let value = self.builder.ins().f64const(n);
        self.f64_value(value)
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

    /// Wrap a Cranelift value as a String CompiledValue
    pub fn string_value(&self, value: Value) -> CompiledValue {
        CompiledValue {
            value,
            ty: self.ctx.pointer_type,
            vole_type: Type::String,
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
}
