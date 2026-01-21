// src/codegen/compiler/common.rs
//
// Shared function compilation infrastructure.
// This module provides a unified helper for the common pattern across all
// function compilation paths (top-level funcs, methods, lambdas).

use std::collections::HashMap;

use cranelift::prelude::{types, FunctionBuilder, InstBuilder, Type};
use vole_frontend::{FuncBody, Symbol};
use vole_sema::type_arena::TypeId;

use crate::context::Captures;
use crate::lambda::CaptureBinding;
use crate::stmt::compile_func_body;
use crate::types::CompileCtx;

use super::ControlFlowCtx;

/// What to return from a non-terminated block
#[derive(Clone, Copy)]
pub enum DefaultReturn {
    /// Return nothing (for void functions): `return_(&[])`
    Empty,
    /// Return a zero i64 (for lambdas): `return_(&[iconst(i64, 0)])`
    ZeroI64,
}

/// Configuration for compiling a function body.
///
/// This struct captures the common parameters needed by all function compilation
/// paths, allowing them to share the core compilation logic.
pub struct FunctionCompileConfig<'a> {
    /// Function body to compile
    pub body: &'a FuncBody,
    /// Parameters: (name, vole_type_id, cranelift_type)
    pub params: Vec<(Symbol, TypeId, Type)>,
    /// Self binding for methods: (name, vole_type_id, cranelift_type)
    pub self_binding: Option<(Symbol, TypeId, Type)>,
    /// Capture bindings for closures. If Some, the first block param is the closure pointer.
    pub capture_bindings: Option<&'a HashMap<Symbol, CaptureBinding>>,
    /// Cranelift type for the closure pointer (needed when capture_bindings is Some)
    pub closure_ptr_type: Option<Type>,
    /// Return type (for nested return type context)
    pub return_type_id: Option<TypeId>,
    /// Number of block params to skip before binding user params.
    /// Used for lambdas where the first param is the closure pointer.
    pub skip_block_params: usize,
    /// What to return when the block doesn't terminate explicitly
    pub default_return: DefaultReturn,
}

impl<'a> FunctionCompileConfig<'a> {
    /// Create a config for a top-level function (no self, no captures)
    pub fn top_level(
        body: &'a FuncBody,
        params: Vec<(Symbol, TypeId, Type)>,
        return_type_id: Option<TypeId>,
    ) -> Self {
        Self {
            body,
            params,
            self_binding: None,
            capture_bindings: None,
            closure_ptr_type: None,
            return_type_id,
            skip_block_params: 0,
            default_return: DefaultReturn::Empty,
        }
    }

    /// Create a config for a method (has self, no captures)
    pub fn method(
        body: &'a FuncBody,
        params: Vec<(Symbol, TypeId, Type)>,
        self_binding: (Symbol, TypeId, Type),
        return_type_id: Option<TypeId>,
    ) -> Self {
        Self {
            body,
            params,
            self_binding: Some(self_binding),
            capture_bindings: None,
            closure_ptr_type: None,
            return_type_id,
            skip_block_params: 0,
            default_return: DefaultReturn::Empty,
        }
    }

    /// Create a config for a pure lambda (no captures, skips closure ptr param)
    pub fn pure_lambda(
        body: &'a FuncBody,
        params: Vec<(Symbol, TypeId, Type)>,
        return_type_id: TypeId,
    ) -> Self {
        Self {
            body,
            params,
            self_binding: None,
            capture_bindings: None,
            closure_ptr_type: None,
            return_type_id: Some(return_type_id),
            skip_block_params: 1, // Skip the closure pointer
            default_return: DefaultReturn::ZeroI64,
        }
    }

    /// Create a config for a capturing lambda (has captures, skips closure ptr param)
    pub fn capturing_lambda(
        body: &'a FuncBody,
        params: Vec<(Symbol, TypeId, Type)>,
        capture_bindings: &'a HashMap<Symbol, CaptureBinding>,
        closure_ptr_type: Type,
        return_type_id: TypeId,
    ) -> Self {
        Self {
            body,
            params,
            self_binding: None,
            capture_bindings: Some(capture_bindings),
            closure_ptr_type: Some(closure_ptr_type),
            return_type_id: Some(return_type_id),
            skip_block_params: 1, // Skip the closure pointer
            default_return: DefaultReturn::ZeroI64,
        }
    }
}

/// Compile the inner logic of a function: entry block, param binding, body, return handling.
///
/// This is the core compilation logic shared by all function compilation paths.
/// The caller is responsible for:
/// - Creating the FunctionBuilder with the correct context
/// - Setting up the function signature
/// - Calling define_function and clear after this returns
///
/// This function takes ownership of the builder because `finalize()` consumes it.
///
/// # Arguments
/// * `builder` - The FunctionBuilder for this function (consumed by finalize)
/// * `ctx` - The CompileCtx with all necessary context
/// * `config` - Configuration specifying the function to compile
///
/// # Returns
/// Ok(()) on success, Err with message on failure
pub fn compile_function_inner(
    mut builder: FunctionBuilder,
    ctx: &mut CompileCtx,
    config: FunctionCompileConfig,
) -> Result<(), String> {
    // Create entry block and switch to it
    let entry_block = builder.create_block();
    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);

    // Get block params
    let block_params = builder.block_params(entry_block).to_vec();
    let mut param_offset = config.skip_block_params;

    // Build variables map
    let mut variables: HashMap<Symbol, (cranelift::prelude::Variable, TypeId)> = HashMap::new();

    // Set up closure variable if this is a capturing lambda
    // The closure pointer is at block_params[0] when skip_block_params > 0 and we have captures
    let captures = if let (Some(bindings), Some(closure_ptr_type)) =
        (config.capture_bindings, config.closure_ptr_type)
    {
        let closure_var = builder.declare_var(closure_ptr_type);
        builder.def_var(closure_var, block_params[0]);
        Some(Captures {
            bindings,
            closure_var,
        })
    } else {
        None
    };

    // Bind self if this is a method
    if let Some((self_sym, self_type_id, self_cranelift_type)) = config.self_binding {
        let self_var = builder.declare_var(self_cranelift_type);
        builder.def_var(self_var, block_params[param_offset]);
        variables.insert(self_sym, (self_var, self_type_id));
        param_offset += 1;
    }

    // Bind regular parameters
    for (i, (name, type_id, cranelift_type)) in config.params.iter().enumerate() {
        let var = builder.declare_var(*cranelift_type);
        builder.def_var(var, block_params[param_offset + i]);
        variables.insert(*name, (var, *type_id));
    }

    // Compile function body
    let mut cf_ctx = ControlFlowCtx::default();
    let (terminated, expr_value) = compile_func_body(
        &mut builder,
        config.body,
        &mut variables,
        &mut cf_ctx,
        ctx,
        captures,
        config.return_type_id,
    )?;

    // Add implicit return if no explicit return
    if let Some(value) = expr_value {
        builder.ins().return_(&[value.value]);
    } else if !terminated {
        match config.default_return {
            DefaultReturn::Empty => {
                builder.ins().return_(&[]);
            }
            DefaultReturn::ZeroI64 => {
                let zero = builder.ins().iconst(types::I64, 0);
                builder.ins().return_(&[zero]);
            }
        }
    }

    builder.seal_all_blocks();
    builder.finalize();

    Ok(())
}
