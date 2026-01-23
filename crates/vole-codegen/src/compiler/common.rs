// src/codegen/compiler/common.rs
//
// Shared function compilation infrastructure.
// This module provides a unified helper for the common pattern across all
// function compilation paths (top-level funcs, methods, lambdas).

use std::collections::HashMap;

use cranelift::prelude::{Block, FunctionBuilder, InstBuilder, Type, Variable, types};
use vole_frontend::{FuncBody, Symbol};
use vole_sema::type_arena::TypeId;

use crate::context::{Captures, Cg};
use crate::lambda::CaptureBinding;
use crate::types::{CodegenCtx, CompileEnv};

/// What to return from a non-terminated block
#[derive(Clone, Copy)]
pub enum DefaultReturn {
    /// Return nothing (for void functions): `return_(&[])`
    Empty,
    /// Return a zero i64 (for lambdas): `return_(&[iconst(i64, 0)])`
    ZeroI64,
}

/// Create entry block, add function params, and switch to it.
///
/// This helper extracts the common 3-line entry block setup pattern:
/// - Create a new block
/// - Add block params matching the function signature
/// - Switch builder to the new block
///
/// Returns the entry block for parameter access via `builder.block_params()`.
pub fn create_entry_block(builder: &mut FunctionBuilder) -> Block {
    let entry_block = builder.create_block();
    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);
    entry_block
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

/// Set up function entry: create entry block, bind parameters and captures.
///
/// Returns (variables, captures) ready for Cg creation.
///
/// # Arguments
/// * `builder` - The FunctionBuilder (mutably borrowed for setup)
/// * `config` - Configuration specifying params, self binding, captures
pub(crate) fn setup_function_entry<'a>(
    builder: &mut FunctionBuilder,
    config: &FunctionCompileConfig<'a>,
) -> (HashMap<Symbol, (Variable, TypeId)>, Option<Captures<'a>>) {
    // Create entry block and switch to it
    let entry_block = builder.create_block();
    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);

    // Get block params
    let block_params = builder.block_params(entry_block).to_vec();
    let mut param_offset = config.skip_block_params;

    // Build variables map
    let mut variables: HashMap<Symbol, (Variable, TypeId)> = HashMap::new();

    // Set up closure variable if this is a capturing lambda
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

    (variables, captures)
}

/// Bind function parameters to variables.
///
/// This helper extracts the common pattern of zipping param names, Cranelift types,
/// Vole TypeIds, and block param Values together to create variable bindings.
///
/// # Arguments
/// * `builder` - The FunctionBuilder to declare variables in
/// * `variables` - The variables map to populate
/// * `param_names` - Slice of parameter name Symbols
/// * `param_cranelift_types` - Slice of Cranelift Types for each parameter
/// * `param_type_ids` - Slice of Vole TypeIds for each parameter
/// * `block_params` - Slice of Cranelift Values from the entry block
pub fn bind_params(
    builder: &mut FunctionBuilder,
    variables: &mut HashMap<Symbol, (Variable, TypeId)>,
    param_names: &[Symbol],
    param_cranelift_types: &[Type],
    param_type_ids: &[TypeId],
    block_params: &[cranelift::prelude::Value],
) {
    for (((name, ty), type_id), val) in param_names
        .iter()
        .zip(param_cranelift_types.iter())
        .zip(param_type_ids.iter())
        .zip(block_params.iter())
    {
        let var = builder.declare_var(*ty);
        builder.def_var(var, *val);
        variables.insert(*name, (var, *type_id));
    }
}

/// Compile function body using Cg context.
///
/// This is the new Cg-based compilation path. The caller is responsible for:
/// - Setting up the function entry (call `setup_function_entry`)
/// - Creating the Cg context
/// - Calling seal_all_blocks and finalize after this returns
///
/// # Arguments
/// * `cg` - The Cg context with builder, variables, captures, etc.
/// * `body` - The function body to compile
/// * `default_return` - What to return if body doesn't terminate explicitly
///
/// # Returns
/// Ok(()) on success, Err with message on failure
#[allow(dead_code)]
pub fn compile_function_body_with_cg(
    cg: &mut Cg,
    body: &FuncBody,
    default_return: DefaultReturn,
) -> Result<(), String> {
    // Compile function body
    let (terminated, expr_value) = match body {
        FuncBody::Block(block) => {
            let terminated = cg.block(block)?;
            (terminated, None)
        }
        FuncBody::Expr(expr) => {
            let value = cg.expr(expr)?;
            (true, Some(value))
        }
    };

    // Add implicit return if no explicit return
    if let Some(value) = expr_value {
        cg.builder.ins().return_(&[value.value]);
    } else if !terminated {
        match default_return {
            DefaultReturn::Empty => {
                cg.builder.ins().return_(&[]);
            }
            DefaultReturn::ZeroI64 => {
                let zero = cg.builder.ins().iconst(types::I64, 0);
                cg.builder.ins().return_(&[zero]);
            }
        }
    }

    Ok(())
}

/// Compile the inner logic of a function using split contexts.
///
/// This uses the new split context architecture:
/// - CodegenCtx for mutable JIT infrastructure (module, func_registry)
/// - CompileEnv for session/unit level context (analyzed program, type metadata, etc.)
/// - module_id and substitutions for per-function context
///
/// # Arguments
/// * `builder` - The FunctionBuilder for this function (consumed by finalize)
/// * `codegen_ctx` - Mutable JIT infrastructure (module, func_registry)
/// * `env` - Compilation environment (session/unit level)
/// * `config` - Configuration specifying the function to compile
/// * `module_id` - Current module (None for main program)
/// * `substitutions` - Type parameter substitutions for monomorphized generics
///
/// # Returns
/// Ok(()) on success, Err with message on failure
pub fn compile_function_inner_with_params<'ctx>(
    mut builder: FunctionBuilder,
    codegen_ctx: &mut CodegenCtx<'ctx>,
    env: &CompileEnv<'ctx>,
    config: FunctionCompileConfig,
    module_id: Option<vole_identity::ModuleId>,
    substitutions: Option<&HashMap<vole_identity::NameId, TypeId>>,
) -> Result<(), String> {
    // Set up entry block and bind parameters
    let (variables, captures) = setup_function_entry(&mut builder, &config);

    // Create Cg with split contexts
    let mut cg = Cg::new(&mut builder, codegen_ctx, env)
        .with_vars(variables)
        .with_return_type(config.return_type_id)
        .with_captures(captures)
        .with_module(module_id)
        .with_substitutions(substitutions);

    compile_function_body_with_cg(&mut cg, config.body, config.default_return)?;

    // Cg borrow ends here, builder is accessible again
    drop(cg);

    builder.seal_all_blocks();
    builder.finalize();

    Ok(())
}

/// Finalize a function body by adding implicit return and sealing blocks.
///
/// NOTE: This helper takes ownership of the builder because `finalize()` consumes it.
/// Call sites need to be restructured to pass ownership at the end of their scope.
#[allow(dead_code)]
///
/// This helper handles the common pattern at the end of function compilation:
/// - Return the expression value if present
/// - Add implicit empty return if not terminated
/// - Seal all blocks and finalize the builder
///
/// # Arguments
/// * `builder` - The FunctionBuilder to finalize (consumed)
/// * `expr_value` - Optional compiled expression value to return
/// * `terminated` - Whether the function body already terminated (return/break)
pub fn finalize_function_body(
    mut builder: FunctionBuilder,
    expr_value: Option<&crate::types::CompiledValue>,
    terminated: bool,
) {
    if let Some(value) = expr_value {
        builder.ins().return_(&[value.value]);
    } else if !terminated {
        builder.ins().return_(&[]);
    }
    builder.seal_all_blocks();
    builder.finalize();
}
