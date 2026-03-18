// src/codegen/compiler/common.rs
//
// Shared function compilation infrastructure.
// This module provides a unified helper for the common pattern across all
// function compilation paths (top-level funcs, methods, lambdas).

use rustc_hash::FxHashMap;

use cranelift::prelude::{FunctionBuilder, InstBuilder, MemFlags, Type, Variable, types};
use vole_identity::Symbol;
use vole_identity::VirTypeId;
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
    /// Parameters: (name, vir_type_id, cranelift_type)
    pub params: Vec<(Symbol, VirTypeId, Type)>,
    /// Self binding for methods: (name, vir_type_id, cranelift_type)
    pub self_binding: Option<(Symbol, VirTypeId, Type)>,
    /// Capture bindings for closures. If Some, the first block param is the closure pointer.
    pub capture_bindings: Option<&'a FxHashMap<Symbol, CaptureBinding>>,
    /// Cranelift type for the closure pointer (needed when capture_bindings is Some)
    pub closure_ptr_type: Option<Type>,
    /// Return type (for nested return type context)
    pub return_type_id: Option<VirTypeId>,
    /// Number of block params to skip before binding user params.
    /// Used for lambdas where the first param is the closure pointer,
    /// or for sret functions where the first param is the return buffer pointer.
    pub skip_block_params: usize,
    /// What to return when the block doesn't terminate explicitly
    pub default_return: DefaultReturn,
    /// Concrete VirTypeId for `Self` in interface default method bodies.
    ///
    /// During VIR lowering, `Self` (Placeholder) maps to `VirTypeId::UNKNOWN`.
    /// When set, `try_substitute_type_v` replaces UNKNOWN with this type.
    pub self_vir_type: Option<VirTypeId>,
}

impl<'a> FunctionCompileConfig<'a> {
    /// Create a config for a top-level function (no self, no captures)
    pub fn top_level(
        params: Vec<(Symbol, VirTypeId, Type)>,
        return_type_id: Option<VirTypeId>,
    ) -> Self {
        Self {
            params,
            self_binding: None,
            capture_bindings: None,
            closure_ptr_type: None,
            return_type_id,
            skip_block_params: 0,
            default_return: DefaultReturn::Empty,
            self_vir_type: None,
        }
    }

    /// Set skip_block_params to 1 (for sret hidden parameter).
    pub fn with_sret(mut self) -> Self {
        self.skip_block_params = 1;
        self
    }

    /// Set the concrete Self type for interface default method bodies.
    pub fn with_self_vir_type(mut self, self_vir_ty: VirTypeId) -> Self {
        self.self_vir_type = Some(self_vir_ty);
        self
    }

    /// Create a config for a method (has self, no captures)
    pub fn method(
        params: Vec<(Symbol, VirTypeId, Type)>,
        self_binding: (Symbol, VirTypeId, Type),
        return_type_id: Option<VirTypeId>,
    ) -> Self {
        Self {
            params,
            self_binding: Some(self_binding),
            capture_bindings: None,
            closure_ptr_type: None,
            return_type_id,
            skip_block_params: 0,
            default_return: DefaultReturn::Empty,
            self_vir_type: None,
        }
    }

    /// Create a config for a lambda (pure or capturing, skips closure ptr param)
    ///
    /// If `capture_bindings` is Some, the lambda captures variables from its
    /// environment and the closure pointer is used to access them. If None,
    /// the closure pointer parameter is still present (for calling convention
    /// consistency) but ignored.
    pub fn lambda(
        params: Vec<(Symbol, VirTypeId, Type)>,
        return_type_id: VirTypeId,
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
            self_vir_type: None,
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
    _vir_type_table: &vole_vir::type_table::VirTypeTable,
) -> (
    FxHashMap<Symbol, (Variable, VirTypeId)>,
    Option<Captures<'a>>,
) {
    // Create entry block and switch to it
    let entry_block = builder.create_block();
    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);

    // Get block params
    let block_params = builder.block_params(entry_block).to_vec();
    let mut param_offset = config.skip_block_params;

    // Build variables map
    let mut variables: FxHashMap<Symbol, (Variable, VirTypeId)> = FxHashMap::default();

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
    if let Some((self_sym, self_vir_ty, self_cranelift_type)) = config.self_binding {
        let self_var = builder.declare_var(self_cranelift_type);
        builder.def_var(self_var, block_params[param_offset]);
        variables.insert(self_sym, (self_var, self_vir_ty));
        param_offset += 1;
    }

    // Bind regular parameters
    for (i, (name, vir_ty, cranelift_type)) in config.params.iter().enumerate() {
        let var = builder.declare_var(*cranelift_type);
        builder.def_var(var, block_params[param_offset + i]);
        variables.insert(*name, (var, *vir_ty));
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
        // If the expression is never-typed (e.g. `unreachable`), a trap was
        // already emitted.  The builder auto-started a new dead block after
        // the trap; just emit another trap to fill it — no real return needed.
        if value.type_id == VirTypeId::NEVER {
            cg.builder.ins().trap(crate::trap_codes::UNREACHABLE);
            return Ok(());
        }

        // Dispatch on the pre-computed return ABI instead of querying type
        // properties.  The return_abi is set during Cg construction from the
        // VIR function's return type.
        match cg.return_abi {
            vole_vir::func::ReturnAbi::Void => {
                cg.builder.ins().return_(&[]);
            }
            vole_vir::func::ReturnAbi::Fallible => {
                let tag = cg
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), value.value, 0);
                let payload = cg.load_union_payload_v(value.value, value.type_id, types::I64);
                cg.builder.ins().return_(&[tag, payload]);
            }
            vole_vir::func::ReturnAbi::WideFallible => {
                let tag = cg
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), value.value, 0);
                let union_size = cg.type_size_v(value.type_id);
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
            }
            vole_vir::func::ReturnAbi::SmallStruct { .. } => {
                let ret_vir_ty = cg
                    .return_type
                    .expect("SmallStruct ABI requires return type");
                cg.emit_small_struct_return_v(value.value, ret_vir_ty)?;
            }
            vole_vir::func::ReturnAbi::SretStruct { .. } => {
                let ret_vir_ty = cg.return_type.expect("SretStruct ABI requires return type");
                cg.emit_sret_struct_return_v(value.value, ret_vir_ty)?;
            }
            vole_vir::func::ReturnAbi::UnionPtr => {
                let ret_vir_ty = cg.return_type.expect("UnionPtr ABI requires return type");
                let wrapped = cg.construct_union_id_v(value, ret_vir_ty)?;
                cg.builder.ins().return_(&[wrapped.value]);
            }
            vole_vir::func::ReturnAbi::Single | vole_vir::func::ReturnAbi::Wide => {
                let ret_val = cg.coerce_return_value(value.value);
                cg.builder.ins().return_(&[ret_val]);
            }
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
        if cg.cached_rc_state_v(value.type_id).needs_cleanup() {
            cg.emit_rc_inc_for_type_v(value.value, value.type_id)?;
        } else if let Some(rc_tags) = cg.cached_rc_state_v(value.type_id).union_variants() {
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
#[expect(clippy::type_complexity)]
fn compile_vir_block_body(
    cg: &mut Cg,
    stmts: &[VirStmt],
) -> CodegenResult<(bool, Option<(CompiledValue, Option<Variable>)>)> {
    let has_trailing_expr = cg
        .return_type
        .is_some_and(|ret| !cg.vir_query_is_void_v(ret))
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
            if cg.cached_rc_state_v(value.type_id).needs_cleanup() {
                cg.emit_rc_inc_for_type_v(value.value, value.type_id)?;
            } else if let Some(rc_tags) = cg.cached_rc_state_v(value.type_id).union_variants() {
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
/// `MethodCall`) delegate to old codegen helpers with generic TypeIds
/// requiring substitution.
pub(crate) fn compile_function_inner_with_vir<'ctx>(
    mut builder: FunctionBuilder,
    codegen_ctx: &mut CodegenCtx<'ctx>,
    env: &CompileEnv<'ctx>,
    config: FunctionCompileConfig,
    vir_body: &VirBody,
    module_id: Option<vole_identity::ModuleId>,
    substitutions: Option<&FxHashMap<vole_identity::NameId, VirTypeId>>,
) -> CodegenResult<()> {
    // Auto-detect sret convention from ReturnAbi.
    let config = if let Some(ret_vir_ty) = config.return_type_id {
        let vir_table = &env.analyzed.type_table;
        let struct_slots = crate::types::vir_struct_helpers::vir_struct_flat_slot_count(
            ret_vir_ty,
            vir_table,
            env.analyzed,
        );
        let abi = vole_vir::func::ReturnAbi::classify(ret_vir_ty, vir_table, struct_slots);
        if abi.is_sret() {
            config.with_sret()
        } else {
            config
        }
    } else {
        config
    };

    let vir_type_table = &env.analyzed.type_table;
    let (variables, captures) = setup_function_entry(&mut builder, &config, vir_type_table);

    let mut cg = Cg::new(&mut builder, codegen_ctx, env)
        .with_callable_backend_preference(crate::CallableBackendPreference::PreferInline)
        .with_vars(variables)
        .with_return_type_v(config.return_type_id)
        .with_captures(captures)
        .with_module(module_id)
        .with_substitutions(substitutions);

    if let Some(self_vir_ty) = config.self_vir_type {
        cg = cg.with_self_vir_type(self_vir_ty);
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
    let has_return = vir_func.return_type != VirTypeId::VOID;

    // Determine sret convention from the return type using codegen's full
    // struct flat slot count (which handles union-payload fields etc.).
    let skip_block_params = if has_return {
        let struct_slots = crate::types::vir_struct_helpers::vir_struct_flat_slot_count(
            vir_func.return_type,
            &env.analyzed.type_table,
            env.analyzed,
        );
        let abi = vole_vir::func::ReturnAbi::classify(
            vir_func.return_type,
            &env.analyzed.type_table,
            struct_slots,
        );
        if abi.is_sret() { 1 } else { 0 }
    } else {
        0
    };

    // Create entry block.
    let entry_block = builder.create_block();
    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);

    let block_params = builder.block_params(entry_block).to_vec();
    let ptr = codegen_ctx.ptr_type();
    let vir_table = &env.analyzed.type_table;

    // Declare Cranelift variables for each param (type conversion deferred to Cg bridge).
    let param_info: Vec<(Symbol, Variable, VirTypeId)> = vir_func
        .params
        .iter()
        .enumerate()
        .map(|(i, (name, vir_ty, _))| {
            let cl_ty =
                crate::types::vir_conversions::vir_type_to_cranelift(*vir_ty, vir_table, ptr);
            let var = builder.declare_var(cl_ty);
            builder.def_var(var, block_params[skip_block_params + i]);
            (*name, var, *vir_ty)
        })
        .collect();

    // Create Cg first, then populate vars with VirTypeId directly.
    let mut cg = Cg::new(&mut builder, codegen_ctx, env)
        .with_callable_backend_preference(crate::CallableBackendPreference::PreferInline);

    // Populate vars directly with VirTypeId (no bridge needed).
    for (name, var, vir_ty) in &param_info {
        cg.vars.insert(*name, (*var, *vir_ty));
    }

    // Set return type and recompute ABI with codegen's full struct slot
    // count (vir_func.return_abi may lack struct info if lowered by sema).
    if has_return {
        cg.return_type = Some(vir_func.return_type);
        let struct_slots = cg.vir_struct_flat_slot_count(vir_func.return_type);
        cg.return_abi = vole_vir::func::ReturnAbi::classify(
            vir_func.return_type,
            cg.vir_type_table(),
            struct_slots,
        );
    }

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
