// src/codegen/compiler/common.rs
//
// Shared function compilation infrastructure.
// This module provides a unified helper for the common pattern across all
// function compilation paths (top-level funcs, methods, lambdas).

use rustc_hash::FxHashMap;

use cranelift::prelude::{FunctionBuilder, InstBuilder, MemFlags, Type, Variable, types};
use vole_frontend::{ExprKind, FuncBody, Symbol};
use vole_sema::type_arena::TypeId;

use crate::context::{Captures, Cg};
use crate::union_layout;
use crate::errors::CodegenResult;
use crate::lambda::CaptureBinding;
use crate::types::{CodegenCtx, CompileEnv};

/// What to return from a non-terminated block
#[derive(Clone, Copy)]
pub enum DefaultReturn {
    /// Return nothing (for void functions): `return_(&[])`
    Empty,
    /// Return a zero value matching the function signature's return type.
    /// Used for lambdas with block bodies that may not terminate explicitly.
    Zero,
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
    pub capture_bindings: Option<&'a FxHashMap<Symbol, CaptureBinding>>,
    /// Cranelift type for the closure pointer (needed when capture_bindings is Some)
    pub closure_ptr_type: Option<Type>,
    /// Return type (for nested return type context)
    pub return_type_id: Option<TypeId>,
    /// Number of block params to skip before binding user params.
    /// Used for lambdas where the first param is the closure pointer,
    /// or for sret functions where the first param is the return buffer pointer.
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

    /// Set skip_block_params to 1 (for sret hidden parameter).
    pub fn with_sret(mut self) -> Self {
        self.skip_block_params = 1;
        self
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
            default_return: DefaultReturn::Zero,
        }
    }

    /// Create a config for a capturing lambda (has captures, skips closure ptr param)
    pub fn capturing_lambda(
        body: &'a FuncBody,
        params: Vec<(Symbol, TypeId, Type)>,
        capture_bindings: &'a FxHashMap<Symbol, CaptureBinding>,
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
            default_return: DefaultReturn::Zero,
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
) -> (FxHashMap<Symbol, (Variable, TypeId)>, Option<Captures<'a>>) {
    // Create entry block and switch to it
    let entry_block = builder.create_block();
    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);

    // Get block params
    let block_params = builder.block_params(entry_block).to_vec();
    let mut param_offset = config.skip_block_params;

    // Build variables map
    let mut variables: FxHashMap<Symbol, (Variable, TypeId)> = FxHashMap::default();

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
pub fn compile_function_body_with_cg(
    cg: &mut Cg,
    body: &FuncBody,
    default_return: DefaultReturn,
) -> CodegenResult<()> {
    // Push function-level RC scope for tracking RC locals
    cg.push_rc_scope();

    // Compile function body
    let (terminated, expr_value) = match body {
        FuncBody::Block(block) => {
            let terminated = cg.block(block)?;
            (terminated, None)
        }
        FuncBody::Expr(expr) => {
            let mut value = cg.expr(expr)?;

            // RC bookkeeping for expression-bodied returns (mirrors Stmt::Return logic):
            // If the return expression is a borrow (variable read, index, field access),
            // we must rc_inc before scope cleanup so the caller receives an owned +1 ref.
            let skip_var = if let ExprKind::Identifier(sym) = &expr.kind
                && let Some((var, _)) = cg.vars.get(sym)
                && (cg.rc_scopes.is_rc_local(*var)
                    || cg.rc_scopes.is_composite_rc_local(*var)
                    || cg.rc_scopes.is_union_rc_local(*var))
            {
                Some(*var)
            } else {
                None
            };
            if skip_var.is_none() && value.is_borrowed() {
                if cg.rc_state(value.type_id).needs_cleanup() {
                    cg.emit_rc_inc_for_type(value.value, value.type_id)?;
                } else if let Some(rc_tags) = cg.union_rc_variant_tags(value.type_id) {
                    // Union with RC variants (e.g. [string]?): rc_inc the inner
                    // payload so the caller's copy owns its own reference.
                    // Without this, the caller's consume_rc_args and the
                    // return value's scope-exit cleanup both rc_dec the same
                    // inner value, causing a double-free / heap corruption.
                    cg.emit_union_rc_inc(value.value, &rc_tags)?;
                }
            }

            // The return value is consumed — ownership transfers to the caller.
            value.mark_consumed();
            value.debug_assert_rc_handled("implicit return");
            (true, Some((value, skip_var)))
        }
    };

    // Emit RC cleanup for function-level scope before implicit returns.
    // Explicit returns are handled in stmt.rs (Stmt::Return).
    // If the function terminated (via explicit return/break), cleanup was already
    // emitted at that point, so we only clean up for non-terminated paths.
    if !terminated || expr_value.is_some() {
        let skip_var = expr_value.as_ref().and_then(|(_, sv)| *sv);
        cg.pop_rc_scope_with_cleanup(skip_var)?;
    } else {
        // Just pop the scope marker (cleanup was emitted by the return/break)
        cg.rc_scopes.pop_scope();
    }

    // Add implicit return if no explicit return
    if let Some((value, _skip_var)) = expr_value {
        // Check if the return type is fallible - need multi-value return
        let is_fallible_return = cg
            .return_type
            .map(|ret_type_id| cg.arena().unwrap_fallible(ret_type_id).is_some())
            .unwrap_or(false);

        if is_fallible_return {
            // Expression-bodied fallible function: the value is a pointer to (tag, payload)
            // We need to load both and return them
            let tag = cg
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), value.value, 0);

            let is_wide = cg
                .return_type
                .is_some_and(|ret| crate::types::is_wide_fallible(ret, cg.arena()));

            if is_wide {
                // Wide fallible (i128 success): load low/high from offset 8/16
                let union_size = cg.type_size(value.type_id);
                let (low, high) = if union_size > union_layout::TAG_ONLY_SIZE {
                    let low = cg
                        .builder
                        .ins()
                        .load(types::I64, MemFlags::new(), value.value, 8);
                    let high = cg
                        .builder
                        .ins()
                        .load(types::I64, MemFlags::new(), value.value, 16);
                    (low, high)
                } else {
                    let zero = cg.builder.ins().iconst(types::I64, 0);
                    (zero, zero)
                };
                cg.builder.ins().return_(&[tag, low, high]);
            } else {
                // Only load payload if union has payload data.
                // Sentinel-only unions have union_size == 8 (tag only), no payload to read.
                let union_size = cg.type_size(value.type_id);
                let payload = if union_size > union_layout::TAG_ONLY_SIZE {
                    cg.builder
                        .ins()
                        .load(types::I64, MemFlags::new(), value.value, 8)
                } else {
                    cg.builder.ins().iconst(types::I64, 0)
                };
                cg.builder.ins().return_(&[tag, payload]);
            }
        } else if let Some(ret_type_id) = cg.return_type
            && cg.is_small_struct_return(ret_type_id)
        {
            cg.emit_small_struct_return(value.value, ret_type_id);
        } else if let Some(ret_type_id) = cg.return_type
            && cg.is_sret_struct_return(ret_type_id)
        {
            cg.emit_sret_struct_return(value.value, ret_type_id);
        } else if let Some(ret_type_id) = cg.return_type
            && cg.arena().is_union(ret_type_id)
        {
            // For union return types, wrap the value in a union
            let wrapped = cg.construct_union_id(value, ret_type_id)?;
            cg.builder.ins().return_(&[wrapped.value]);
        } else {
            // Coerce the value to match the function return type if needed.
            // This handles generic functions where sema may infer a specific
            // type (e.g. i32, f64) for an expression, but the function signature
            // uses i64 for the generic type parameter.
            let ret_val = cg.coerce_return_value(value.value);
            cg.builder.ins().return_(&[ret_val]);
        }
    } else if !terminated {
        match default_return {
            DefaultReturn::Empty => {
                cg.builder.ins().return_(&[]);
            }
            DefaultReturn::Zero => {
                let ret_type = cg
                    .builder
                    .func
                    .signature
                    .returns
                    .first()
                    .map(|r| r.value_type)
                    .unwrap_or(types::I64);
                let zero = if ret_type == types::F64 {
                    cg.builder.ins().f64const(0.0)
                } else if ret_type == types::F32 {
                    cg.builder.ins().f32const(0.0)
                } else {
                    cg.builder.ins().iconst(ret_type, 0)
                };
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
    substitutions: Option<&FxHashMap<vole_identity::NameId, TypeId>>,
) -> CodegenResult<()> {
    // Auto-detect sret convention: if return type is a large struct (3+ flat slots),
    // the signature has a hidden sret pointer as the first parameter.
    let config = if let Some(ret_type_id) = config.return_type_id {
        let arena = env.analyzed.type_arena();
        let entities = env.analyzed.query().registry();
        if let Some(flat_count) =
            crate::structs::struct_flat_slot_count(ret_type_id, arena, entities)
        {
            if flat_count > crate::MAX_SMALL_STRUCT_FIELDS {
                config.with_sret()
            } else {
                config
            }
        } else {
            config
        }
    } else {
        config
    };

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
///
/// This helper handles the common pattern at the end of function compilation:
/// - Return the expression value if present
/// - Add implicit return based on `default_return` if not terminated
/// - Seal all blocks and finalize the builder
///
/// # Arguments
/// * `builder` - The FunctionBuilder to finalize (consumed)
/// * `expr_value` - Optional compiled expression value to return
/// * `terminated` - Whether the function body already terminated (return/break)
/// * `default_return` - What to return when not terminated (Empty or Zero)
pub fn finalize_function_body(
    mut builder: FunctionBuilder,
    expr_value: Option<&crate::types::CompiledValue>,
    terminated: bool,
    default_return: DefaultReturn,
) {
    if let Some(value) = expr_value {
        builder.ins().return_(&[value.value]);
    } else if !terminated {
        match default_return {
            DefaultReturn::Empty => {
                builder.ins().return_(&[]);
            }
            DefaultReturn::Zero => {
                let ret_type = builder
                    .func
                    .signature
                    .returns
                    .first()
                    .map(|r| r.value_type)
                    .unwrap_or(types::I64);
                let zero = if ret_type == types::F64 {
                    builder.ins().f64const(0.0)
                } else if ret_type == types::F32 {
                    builder.ins().f32const(0.0)
                } else {
                    builder.ins().iconst(ret_type, 0)
                };
                builder.ins().return_(&[zero]);
            }
        }
    }
    builder.seal_all_blocks();
    builder.finalize();
}
