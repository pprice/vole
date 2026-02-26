// src/codegen/compiler/common.rs
//
// Shared function compilation infrastructure.
// This module provides a unified helper for the common pattern across all
// function compilation paths (top-level funcs, methods, lambdas).

use rustc_hash::FxHashMap;

use cranelift::prelude::{FunctionBuilder, InstBuilder, MemFlags, Type, Variable, types};
use vole_frontend::{FuncBody, Symbol};
use vole_sema::type_arena::TypeId;
use vole_vir::{VirBody, VirExpr, VirStmt};

use crate::context::{Captures, Cg};
use crate::errors::CodegenResult;
use crate::lambda::CaptureBinding;
use crate::types::{CodegenCtx, CompileEnv, CompiledValue};
use crate::union_layout;

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
    /// True when compiling an Iterable default method body.
    /// Affects RC lifecycle for closure parameters passed to pipeline/terminal methods.
    pub in_iterable_default_body: bool,
}

impl<'a> FunctionCompileConfig<'a> {
    /// Create a config for a top-level function (no self, no captures)
    pub fn top_level(
        _body: &'a FuncBody,
        params: Vec<(Symbol, TypeId, Type)>,
        return_type_id: Option<TypeId>,
    ) -> Self {
        Self {
            params,
            self_binding: None,
            capture_bindings: None,
            closure_ptr_type: None,
            return_type_id,
            skip_block_params: 0,
            default_return: DefaultReturn::Empty,
            in_iterable_default_body: false,
        }
    }

    /// Set skip_block_params to 1 (for sret hidden parameter).
    pub fn with_sret(mut self) -> Self {
        self.skip_block_params = 1;
        self
    }

    /// Mark this as an Iterable default method body compilation.
    pub fn with_iterable_default_body(mut self) -> Self {
        self.in_iterable_default_body = true;
        self
    }

    /// Create a config for a method (has self, no captures)
    pub fn method(
        _body: &'a FuncBody,
        params: Vec<(Symbol, TypeId, Type)>,
        self_binding: (Symbol, TypeId, Type),
        return_type_id: Option<TypeId>,
    ) -> Self {
        Self {
            params,
            self_binding: Some(self_binding),
            capture_bindings: None,
            closure_ptr_type: None,
            return_type_id,
            skip_block_params: 0,
            default_return: DefaultReturn::Empty,
            in_iterable_default_body: false,
        }
    }

    /// Create a config for a lambda (pure or capturing, skips closure ptr param)
    ///
    /// If `capture_bindings` is Some, the lambda captures variables from its
    /// environment and the closure pointer is used to access them. If None,
    /// the closure pointer parameter is still present (for calling convention
    /// consistency) but ignored.
    pub fn lambda(
        _body: &'a FuncBody,
        params: Vec<(Symbol, TypeId, Type)>,
        return_type_id: TypeId,
        capture_bindings: Option<&'a FxHashMap<Symbol, CaptureBinding>>,
        closure_ptr_type: Type,
    ) -> Self {
        Self {
            params,
            self_binding: None,
            capture_bindings,
            closure_ptr_type: if capture_bindings.is_some() {
                Some(closure_ptr_type)
            } else {
                None
            },
            return_type_id: Some(return_type_id),
            skip_block_params: 1, // Skip the closure pointer
            default_return: DefaultReturn::Zero,
            in_iterable_default_body: false,
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

/// Emit the implicit return for a function body.
///
/// For expression bodies, emit the appropriate return instruction based on
/// the return type (fallible, struct, union, or normal). For block bodies
/// that didn't terminate, emit a default return (empty or zero).
fn emit_implicit_return(
    cg: &mut Cg,
    expr_value: Option<CompiledValue>,
    terminated: bool,
    default_return: DefaultReturn,
) -> CodegenResult<()> {
    if let Some(value) = expr_value {
        // Check if the return type is fallible - need multi-value return
        let is_fallible_return = cg
            .return_type
            .map(|ret_type_id| cg.arena().unwrap_fallible(ret_type_id).is_some())
            .unwrap_or(false);

        // Check if the function has a void return type. Expression-bodied default methods
        // like `=> self.iter().for_each(f)` produce a void value that must not be returned.
        // The Cranelift signature for void functions has no return values.
        let is_void_return = cg
            .return_type
            .map(|ret_type_id| cg.arena().is_void(ret_type_id))
            .unwrap_or(false);

        if is_void_return {
            // Void-return expression body: discard the expression value and return nothing.
            // This happens for Iterable default methods like `for_each` whose body is
            // `=> self.iter().for_each(f)`, which evaluates to void but must not be returned.
            cg.builder.ins().return_(&[]);
        } else if is_fallible_return {
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
                    let low = cg.builder.ins().load(
                        types::I64,
                        MemFlags::new(),
                        value.value,
                        union_layout::PAYLOAD_OFFSET,
                    );
                    let high = cg
                        .builder
                        .ins()
                        .load(types::I64, MemFlags::new(), value.value, 16);
                    (low, high)
                } else {
                    let zero = cg.iconst_cached(types::I64, 0);
                    (zero, zero)
                };
                cg.builder.ins().return_(&[tag, low, high]);
            } else {
                let payload = cg.load_union_payload(value.value, value.type_id, types::I64);
                cg.builder.ins().return_(&[tag, payload]);
            }
        } else if let Some(ret_type_id) = cg.return_type
            && cg.is_small_struct_return(ret_type_id)
        {
            cg.emit_small_struct_return(value.value, ret_type_id)?;
        } else if let Some(ret_type_id) = cg.return_type
            && cg.is_sret_struct_return(ret_type_id)
        {
            cg.emit_sret_struct_return(value.value, ret_type_id)?;
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
                } else if ret_type == types::F128 {
                    let zero_bits = cg.iconst_cached(types::I128, 0);
                    cg.builder
                        .ins()
                        .bitcast(types::F128, MemFlags::new(), zero_bits)
                } else {
                    cg.iconst_cached(ret_type, 0)
                };
                cg.builder.ins().return_(&[zero]);
            }
        }
    }

    Ok(())
}

/// Compile a VIR function body using the Cg context.
///
/// Walks `VirBody` (typed VIR nodes). All expression and statement kinds are
/// fully lowered to VIR.
///
/// # Body structure
/// - `trailing: Some(expr)` — expression body (`=> expr`), treated as implicit return.
/// - `trailing: None` — block body; the trailing-expression heuristic peeks into the
///   last `VirStmt::Expr` to detect a trailing expression for implicit return.
pub(crate) fn compile_vir_body_with_cg(
    cg: &mut Cg,
    body: &VirBody,
    default_return: DefaultReturn,
) -> CodegenResult<()> {
    cg.push_rc_scope();

    let (terminated, expr_value) = if let Some(trailing) = &body.trailing {
        // Expression body — compile all preceding stmts, then the trailing expr.
        let mut terminated = false;
        for vir_stmt in &body.stmts {
            if terminated {
                break;
            }
            terminated = cg.compile_vir_stmt(vir_stmt)?;
        }
        if terminated {
            (true, None)
        } else {
            let value = compile_trailing_vir_expr(cg, trailing)?;
            (true, Some(value))
        }
    } else {
        // Block body — check for trailing expression heuristic.
        compile_vir_block_body(cg, &body.stmts)?
    };

    // RC scope cleanup.
    if !terminated || expr_value.is_some() {
        let skip_var = expr_value.as_ref().and_then(|(_, sv)| *sv);
        cg.pop_rc_scope_with_cleanup(skip_var)?;
    } else {
        cg.rc_scopes.pop_scope();
    }

    let return_value = expr_value.map(|(value, _)| value);
    emit_implicit_return(cg, return_value, terminated, default_return)?;

    Ok(())
}

/// Compile the trailing VIR expression of an expression-bodied function.
///
/// Handles RC bookkeeping for implicit returns.
fn compile_trailing_vir_expr(
    cg: &mut Cg,
    vir_expr: &VirExpr,
) -> CodegenResult<(CompiledValue, Option<Variable>)> {
    let mut value = cg.compile_vir_expr(vir_expr)?;

    // RC bookkeeping: detect identifier borrows that need rc_inc.
    let skip_var = extract_vir_rc_skip_var(cg, vir_expr);

    if skip_var.is_none() && value.is_borrowed() {
        if cg.rc_state(value.type_id).needs_cleanup() {
            cg.emit_rc_inc_for_type(value.value, value.type_id)?;
        } else if let Some(rc_tags) = cg.rc_state(value.type_id).union_variants() {
            cg.emit_union_rc_inc(value.value, rc_tags)?;
        }
    }

    value.mark_consumed();
    value.debug_assert_rc_handled("VIR implicit return");
    Ok((value, skip_var))
}

/// Compile a VIR block body (trailing=None), with trailing-expression detection.
///
/// Peeks into the last statement to detect a trailing expression for the
/// Rust-like implicit return heuristic via `VirStmt::Expr` variants.
#[allow(clippy::type_complexity)]
fn compile_vir_block_body(
    cg: &mut Cg,
    stmts: &[VirStmt],
) -> CodegenResult<(bool, Option<(CompiledValue, Option<Variable>)>)> {
    let has_trailing_expr = cg.return_type.is_some_and(|ret| !cg.arena().is_void(ret))
        && matches!(
            stmts.last(),
            Some(VirStmt::Expr { value }) if !value.is_void_if()
        );

    if has_trailing_expr {
        // Compile all statements except the trailing expression
        let mut terminated = false;
        for vir_stmt in &stmts[..stmts.len() - 1] {
            if terminated {
                break;
            }
            terminated = cg.compile_vir_stmt(vir_stmt)?;
        }
        if terminated {
            return Ok((true, None));
        }
        // Compile the trailing expression
        let (value, skip_var) = match stmts.last() {
            Some(VirStmt::Expr { value: vir_expr }) => {
                let compiled = cg.compile_vir_expr(vir_expr)?;
                let skip_var = extract_vir_rc_skip_var(cg, vir_expr);
                (compiled, skip_var)
            }
            _ => unreachable!(),
        };
        let mut value = value;
        if skip_var.is_none() && value.is_borrowed() {
            if cg.rc_state(value.type_id).needs_cleanup() {
                cg.emit_rc_inc_for_type(value.value, value.type_id)?;
            } else if let Some(rc_tags) = cg.rc_state(value.type_id).union_variants() {
                cg.emit_union_rc_inc(value.value, rc_tags)?;
            }
        }
        value.mark_consumed();
        value.debug_assert_rc_handled("VIR implicit block return");
        Ok((false, Some((value, skip_var))))
    } else {
        // No trailing expression — compile all statements
        let mut terminated = false;
        for vir_stmt in stmts {
            if terminated {
                break;
            }
            terminated = cg.compile_vir_stmt(vir_stmt)?;
        }
        Ok((terminated, None))
    }
}

/// Extract the RC skip variable from a VIR expression.
///
/// Handles `VirExpr::LocalLoad` (lowered identifiers).
fn extract_vir_rc_skip_var(cg: &Cg, vir_expr: &VirExpr) -> Option<Variable> {
    match vir_expr {
        VirExpr::LocalLoad { name, .. } => extract_rc_skip_var_for_sym(cg, *name),
        _ => None,
    }
}

/// Check if a symbol name is bound to an RC-tracked local variable.
fn extract_rc_skip_var_for_sym(cg: &Cg, sym: Symbol) -> Option<Variable> {
    if let Some((var, _)) = cg.vars.get(&sym)
        && (cg.rc_scopes.is_rc_local(*var)
            || cg.rc_scopes.is_composite_rc_local(*var)
            || cg.rc_scopes.is_union_rc_local(*var))
    {
        Some(*var)
    } else {
        None
    }
}

/// Compile a function using its VIR representation.
///
/// Uses shared setup (entry block, parameter binding, Cg creation) and then
/// compiles the body via [`compile_vir_body_with_cg`].
///
/// Substitutions are still passed through because some VIR variants (e.g.
/// `MethodCall`) delegate to old codegen helpers that read the NodeMap with
/// generic TypeIds requiring substitution.
pub(crate) fn compile_function_inner_with_vir<'ctx>(
    mut builder: FunctionBuilder,
    codegen_ctx: &mut CodegenCtx<'ctx>,
    env: &CompileEnv<'ctx>,
    config: FunctionCompileConfig,
    vir_body: &VirBody,
    module_id: Option<vole_identity::ModuleId>,
    substitutions: Option<&FxHashMap<vole_identity::NameId, TypeId>>,
) -> CodegenResult<()> {
    // Auto-detect sret convention.
    let config = if let Some(ret_type_id) = config.return_type_id {
        let arena = env.analyzed.type_arena();
        let entities = env.analyzed.entity_registry();
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

    let (variables, captures) = setup_function_entry(&mut builder, &config);

    let mut cg = Cg::new(&mut builder, codegen_ctx, env)
        .with_callable_backend_preference(crate::CallableBackendPreference::PreferInline)
        .with_vars(variables)
        .with_return_type(config.return_type_id)
        .with_captures(captures)
        .with_module(module_id)
        .with_substitutions(substitutions);

    if config.in_iterable_default_body {
        cg = cg.with_iterable_default_body();
    }

    compile_vir_body_with_cg(&mut cg, vir_body, config.default_return)?;

    drop(cg);

    builder.seal_all_blocks();
    builder.finalize();

    Ok(())
}

/// Compile a VIR-monomorphized function body using only VIR data.
///
/// Unlike [`compile_function_inner_with_vir`] which requires a
/// [`FunctionCompileConfig`] (which includes an AST body reference),
/// this helper works entirely from VIR: the parameter list is extracted
/// from the `VirFunction` and no AST body is needed.
///
/// Used for functions produced by VIR monomorphization that have no
/// corresponding AST declaration.
pub(crate) fn compile_vir_monomorph_function<'ctx>(
    mut builder: FunctionBuilder,
    codegen_ctx: &mut CodegenCtx<'ctx>,
    env: &CompileEnv<'ctx>,
    vir_func: &vole_vir::func::VirFunction,
) -> CodegenResult<()> {
    let return_type_id = Some(crate::types::vir_conversions::vir_to_sema_type_id(
        vir_func.return_type,
        &env.analyzed.vir_program.type_table,
        env.analyzed.type_arena(),
    ))
    .filter(|id| !id.is_void());

    // Auto-detect sret convention.
    let skip_block_params = if return_type_id.is_some() {
        let entities = env.analyzed.entity_registry();
        if let Some(flat_count) = crate::types::vir_struct_helpers::vir_struct_flat_slot_count(
            vir_func.return_type,
            &env.analyzed.vir_program.type_table,
            entities,
        ) {
            if flat_count > crate::MAX_SMALL_STRUCT_FIELDS {
                1
            } else {
                0
            }
        } else {
            0
        }
    } else {
        0
    };

    // Create entry block.
    let entry_block = builder.create_block();
    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);

    let block_params = builder.block_params(entry_block).to_vec();
    let mut variables: FxHashMap<Symbol, (Variable, TypeId)> = FxHashMap::default();
    let ptr = codegen_ctx.ptr_type();
    let vir_table = &env.analyzed.vir_program.type_table;

    for (i, (name, type_id, _vir_ty)) in vir_func.params.iter().enumerate() {
        let cl_ty = crate::types::vir_conversions::vir_type_to_cranelift(*type_id, vir_table, ptr);
        let var = builder.declare_var(cl_ty);
        builder.def_var(var, block_params[skip_block_params + i]);
        variables.insert(
            *name,
            (
                var,
                crate::types::vir_conversions::vir_to_sema_type_id(
                    *type_id,
                    vir_table,
                    env.analyzed.type_arena(),
                ),
            ),
        );
    }

    let mut cg = Cg::new(&mut builder, codegen_ctx, env)
        .with_callable_backend_preference(crate::CallableBackendPreference::PreferInline)
        .with_vars(variables)
        .with_return_type(return_type_id);

    compile_vir_body_with_cg(&mut cg, &vir_func.body, DefaultReturn::Empty)?;

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
pub(crate) fn finalize_function_body(
    mut builder: FunctionBuilder,
    expr_value: Option<&CompiledValue>,
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
                } else if ret_type == types::F128 {
                    let zero_bits = builder.ins().iconst(types::I128, 0);
                    builder
                        .ins()
                        .bitcast(types::F128, MemFlags::new(), zero_bits)
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
