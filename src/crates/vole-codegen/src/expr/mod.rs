// src/codegen/expr/mod.rs
//
// Expression compilation - impl Cg methods.
// The main expr() router lives here; specific expression categories are in sub-modules.

mod as_cast;
mod control_flow;
mod error_patterns;
mod indexing;
mod literal;
mod null_ops;
mod pattern_match;
mod unary_assign;

use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};

use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::union_layout;

use vole_frontend::ast::YieldExpr;
use vole_frontend::{BinaryOp, Expr, ExprKind, Symbol};
use vole_identity::ModuleId;
use vole_sema::type_arena::TypeId;
use vole_vir::{CallTarget, CoerceKind, VirBinOp, VirExpr, VirUnOp};

use super::context::Cg;
use super::types::{CompiledValue, RcLifecycle, type_id_to_cranelift};

impl Cg<'_, '_, '_> {
    /// Compile an expression.
    pub fn expr(&mut self, expr: &Expr) -> CodegenResult<CompiledValue> {
        // Check for captures first if in closure context
        if self.has_captures()
            && let ExprKind::Identifier(sym) = &expr.kind
            && let Some(binding) = self.get_capture(sym).copied()
        {
            return self.load_capture(&binding);
        }

        // Check if this expression was synthesized as an implicit `it` lambda.
        // If so, compile it as a lambda (closure) instead of a bare expression.
        // Skip this check if `it` is already bound in scope — that means we're
        // inside the lambda body itself, compiling the inner expression.
        if self.get_it_lambda_info(expr.id).is_some() {
            let it_sym = self.interner().lookup("it");
            let it_already_bound = it_sym.is_some_and(|sym| self.vars.contains_key(&sym));
            if !it_already_bound {
                let result = self.compile_it_lambda(expr, expr.id)?;
                return Ok(self.mark_rc_owned(result));
            }
        }

        match &expr.kind {
            ExprKind::IntLiteral(n, _) => {
                // Look up inferred type from semantic analysis for bidirectional type inference.
                // Uses get_expr_type helper to check module-specific expr_types when compiling prelude.
                // Falls back to I64 for interface default methods which are analyzed once but
                // compiled multiple times for different implementing types - the single recorded
                // type from sema may not match the compilation context.
                let type_id = self.get_expr_type(&expr.id).unwrap_or(TypeId::I64);
                Ok(self.int_const(*n, type_id))
            }
            ExprKind::FloatLiteral(n, _) => {
                // Look up inferred type from semantic analysis for bidirectional type inference.
                // Falls back to F64 for interface default methods (see IntLiteral comment above).
                let type_id = self.get_expr_type(&expr.id).unwrap_or(TypeId::F64);
                Ok(self.float_const(*n, type_id))
            }
            ExprKind::BoolLiteral(b) => Ok(self.bool_const(*b)),
            ExprKind::Identifier(sym) => self.identifier(*sym, expr),
            ExprKind::Binary(bin) => self.binary(bin, expr.span.line),
            ExprKind::Unary(un) => self.unary(un),
            ExprKind::Assign(assign) => self.assign(assign),
            ExprKind::CompoundAssign(compound) => {
                self.compound_assign(compound, expr.span.line, expr.id)
            }
            ExprKind::Grouping(inner) => self.expr(inner),
            ExprKind::StringLiteral(s) => self.string_literal(s),
            ExprKind::Call(call) => {
                let result = self.call(call, expr.span.line, expr.id)?;
                Ok(self.mark_rc_owned(result))
            }
            ExprKind::InterpolatedString(parts) => self.interpolated_string(parts),
            ExprKind::Range(range) => self.range(range),
            ExprKind::ArrayLiteral(elements) => {
                let result = self.array_literal(elements, expr)?;
                Ok(self.mark_rc_owned(result))
            }
            ExprKind::RepeatLiteral { element, count } => {
                let result = self.repeat_literal(element, *count, expr)?;
                Ok(self.mark_rc_owned(result))
            }
            ExprKind::Index(idx) => self.index(&idx.object, &idx.index, expr.id),
            ExprKind::Match(match_expr) => self.match_expr(match_expr, expr.id),
            ExprKind::Is(is_expr) => self.is_expr(is_expr, expr.id),
            ExprKind::AsCast(as_cast) => self.as_cast_expr(as_cast, expr.id, expr.span.line),
            ExprKind::NullCoalesce(nc) => self.null_coalesce(nc, expr.id),
            ExprKind::Lambda(lambda) => {
                let result = self.lambda(lambda, expr.id)?;
                Ok(self.mark_rc_owned(result))
            }
            ExprKind::TypeLiteral(_) => Err(CodegenError::unsupported(
                "type expressions as runtime values",
            )),
            ExprKind::StructLiteral(sl) => {
                let result = self.struct_literal(sl, expr)?;
                Ok(self.mark_rc_owned(result))
            }
            ExprKind::FieldAccess(fa) => self.field_access(fa),
            ExprKind::OptionalChain(_) | ExprKind::OptionalMethodCall(_) => {
                self.optional_chain(expr, expr.id)
            }
            ExprKind::MethodCall(mc) => {
                let result = self.method_call(mc, expr.id)?;
                Ok(self.mark_rc_owned(result))
            }
            ExprKind::Try(inner) => self.try_propagate(inner),
            ExprKind::Import(_) => {
                // Import expressions produce a compile-time module value
                // At runtime this is just a placeholder - actual function calls
                // go through the method resolution mechanism
                // We need to retrieve the actual Module type from semantic analysis
                let type_id = self
                    .get_expr_type(&expr.id)
                    .unwrap_or(self.arena().primitives.i64);
                Ok(CompiledValue::new(
                    self.iconst_cached(types::I64, 0),
                    types::I64,
                    type_id,
                ))
            }
            ExprKind::Yield(yield_expr) => self.compile_yield(yield_expr),
            ExprKind::Block(block_expr) => self.block_expr(block_expr),
            ExprKind::If(if_expr) => self.if_expr(if_expr, expr.id),
            ExprKind::When(when_expr) => self.when_expr(when_expr, expr.id),
            ExprKind::MetaAccess(meta_access) => {
                let result = crate::reflection::compile_meta_access(self, expr.id, meta_access)?;
                Ok(result)
            }
            ExprKind::Unreachable => self.unreachable_expr(expr.span.line),
        }
    }

    // =========================================================================
    // Identifier and module binding resolution
    // =========================================================================

    /// Compile an identifier lookup
    fn identifier(&mut self, sym: Symbol, expr: &Expr) -> CodegenResult<CompiledValue> {
        // Sentinel values (nil, Done, user-defined) are always available as i8(0).
        // First try the sema-provided type, then fall back to name resolution.
        {
            let sentinel_type_id = self
                .get_expr_type(&expr.id)
                .filter(|&tid| self.arena().is_sentinel(tid))
                .or_else(|| {
                    let name = self.interner().resolve(sym);
                    let module_id = self.current_module.unwrap_or(self.env.analyzed.module_id);
                    let type_def_id = self.query().resolve_type_def_by_str(module_id, name)?;
                    if self.query().is_sentinel_type(type_def_id) {
                        self.query().sentinel_base_type(type_def_id)
                    } else {
                        None
                    }
                });
            if let Some(type_id) = sentinel_type_id {
                let value = self.iconst_cached(types::I8, 0);
                return Ok(CompiledValue::new(value, types::I8, type_id));
            }
        }

        if let Some((var, type_id)) = self.vars.get(&sym) {
            let val = self.builder.use_var(*var);
            let ty = self.builder.func.dfg.value_type(val);

            // Check for narrowed type from semantic analysis.
            // In monomorphized generic bodies we substitute both the union and the
            // narrowed type, then verify the narrowed type is an actual variant of
            // the resolved union before extracting the payload.
            if let Some(raw_narrowed_type_id) = self.get_expr_type(&expr.id) {
                let resolved_union_type_id = self.try_substitute_type(*type_id);
                let narrowed_type_id = self.try_substitute_type(raw_narrowed_type_id);
                if self.arena().is_union(resolved_union_type_id)
                    && !self.arena().is_union(narrowed_type_id)
                    && narrowed_type_id != resolved_union_type_id
                {
                    let narrowed_variant = self
                        .arena()
                        .unwrap_union(resolved_union_type_id)
                        .and_then(|variants| {
                            variants
                                .iter()
                                .copied()
                                .find(|&variant| variant == narrowed_type_id)
                                .or_else(|| {
                                    if self.arena().is_integer(narrowed_type_id) {
                                        variants
                                            .iter()
                                            .copied()
                                            .find(|&variant| self.arena().is_integer(variant))
                                    } else {
                                        None
                                    }
                                })
                        });
                    if let Some(narrowed_variant) = narrowed_variant {
                        // Union layout: [tag:1][padding:7][payload]
                        let payload_ty =
                            type_id_to_cranelift(narrowed_variant, self.arena(), self.ptr_type());
                        let payload =
                            self.load_union_payload(val, resolved_union_type_id, payload_ty);
                        let mut cv = CompiledValue::new(payload, payload_ty, narrowed_variant);
                        // The extracted payload is borrowed from the union variable —
                        // callers must rc_inc if they take ownership.
                        self.mark_borrowed_if_rc(&mut cv);
                        return Ok(cv);
                    }
                }
            }

            // Check for narrowed type from unknown
            if let Some(narrowed_type_id) = self.get_expr_type(&expr.id)
                && self.arena().is_unknown(*type_id)
                && !self.arena().is_unknown(narrowed_type_id)
            {
                // TaggedValue layout: [tag:8][value:8]
                // Extract the value from offset 8 and convert to proper type
                let raw_value = self.builder.ins().load(
                    types::I64,
                    MemFlags::new(),
                    val,
                    union_layout::PAYLOAD_OFFSET,
                );
                let extracted = self.extract_unknown_value(raw_value, narrowed_type_id);
                return Ok(extracted);
            }

            let mut cv = CompiledValue::new(val, ty, *type_id);
            self.mark_borrowed_if_rc(&mut cv);
            // Union variables with RC variants are managed by scope-level
            // union cleanup (UnionRcLocal). Mark them Borrowed so that
            // match arm payload extraction knows the inner payload will be
            // dec'd at scope exit and does not emit a redundant rc_dec.
            if cv.rc_lifecycle == RcLifecycle::Untracked
                && self.rc_state(*type_id).union_variants().is_some()
            {
                cv.mark_borrowed();
            }
            Ok(cv)
        } else if let Some(&(module_id, export_name, export_type_id)) =
            self.lookup_module_binding(&sym)
        {
            // Module binding - look up the constant value
            self.module_binding_value(module_id, export_name, export_type_id)
        } else if let Some(global_init) = self.global_init(sym).cloned() {
            // Compile global's initializer inline
            let mut value = self.expr(&global_init)?;

            // If the global has a declared interface type, box the value
            // Use GlobalDef.type_id instead of re-resolving TypeExpr
            let name_table = self.name_table();
            let module_id = self.current_module().unwrap_or(self.env.analyzed.module_id);
            if let Some(name_id) = name_table.name_id(module_id, &[sym], self.interner())
                && let Some(global_def) = self.query().global(name_id)
            {
                value = self.coerce_to_type(value, global_def.type_id)?;
            }
            Ok(value)
        } else if let Some(func_type_id) = self.get_expr_type(&expr.id)
            && self.arena().is_function(func_type_id)
        {
            // Identifier refers to a named function - create a closure wrapper
            self.function_reference(sym, func_type_id)
        } else if let Some(sentinel_type_id) = self.get_expr_type(&expr.id)
            && self.arena().is_sentinel(sentinel_type_id)
        {
            // Bare identifier refers to a sentinel type - emit i8(0)
            let value = self.iconst_cached(types::I8, 0);
            Ok(CompiledValue::new(value, types::I8, sentinel_type_id))
        } else {
            Err(CodegenError::not_found(
                "variable",
                self.interner().resolve(sym),
            ))
        }
    }

    /// Compile a module binding value (from destructuring import).
    /// Returns the constant value for constants, or an error for functions.
    fn module_binding_value(
        &mut self,
        module_id: ModuleId,
        export_name: Symbol,
        export_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let export_name_str = self.interner().resolve(export_name);
        let module_path = self.name_table().module_path(module_id).to_string();

        // Get the name_id for this export
        let name_id = crate::types::module_name_id(self.analyzed(), module_id, export_name_str);

        // Look up constant value in module metadata
        let const_val = {
            let arena = self.arena();
            name_id.and_then(|nid| {
                arena
                    .module_metadata(module_id)
                    .and_then(|meta| meta.constants.get(&nid).cloned())
            })
        };

        if let Some(const_val) = const_val {
            let arena = self.arena();
            let f64_id = arena.f64();
            let i64_id = arena.i64();
            let bool_id = arena.bool();
            match const_val {
                vole_sema::types::ConstantValue::F64(v) => {
                    let val = self.builder.ins().f64const(v);
                    Ok(CompiledValue::new(val, types::F64, f64_id))
                }
                vole_sema::types::ConstantValue::I64(v) => {
                    let val = self.iconst_cached(types::I64, v);
                    Ok(CompiledValue::new(val, types::I64, i64_id))
                }
                vole_sema::types::ConstantValue::Bool(v) => {
                    let val = self.iconst_cached(types::I8, if v { 1 } else { 0 });
                    Ok(CompiledValue::new(val, types::I8, bool_id))
                }
                vole_sema::types::ConstantValue::String(s) => self.string_literal(&s),
            }
        } else if self.arena().is_function(export_type_id) {
            // Functions cannot be used as values directly - must be called
            Err(CodegenError::unsupported_with_context(
                "function as value",
                format!("use {}() to call the function", export_name_str),
            ))
        } else if self.arena().is_sentinel(export_type_id) {
            // Sentinel exports are zero-field structs - emit i8(0)
            let value = self.iconst_cached(types::I8, 0);
            Ok(CompiledValue::new(value, types::I8, export_type_id))
        } else {
            Err(CodegenError::not_found(
                "module export constant",
                format!("{}.{}", module_path, export_name_str),
            ))
        }
    }

    // =========================================================================
    // Function reference / closure wrapper
    // =========================================================================

    /// Create a closure wrapper function that adapts a regular function to closure
    /// calling convention. The wrapper takes (closure_ptr, params...) and calls
    /// the original function with just (params...).
    fn create_closure_wrapper(
        &mut self,
        orig_func_id: FuncId,
        param_ids: &[TypeId],
        return_type_id: TypeId,
    ) -> CodegenResult<FuncId> {
        use cranelift::prelude::FunctionBuilderContext;

        let wrapper_index = self.next_lambda_id();

        // Build wrapper signature: (closure_ptr, params...) -> return_type
        let param_types = self.cranelift_types(param_ids);
        let return_cr_type = self.cranelift_type(return_type_id);
        let is_void_return = self.arena().is_void(return_type_id);

        let mut wrapper_sig = self.jit_module().make_signature();
        wrapper_sig.params.push(AbiParam::new(self.ptr_type())); // closure ptr (ignored)
        for &param_ty in &param_types {
            wrapper_sig.params.push(AbiParam::new(param_ty));
        }
        if !is_void_return {
            wrapper_sig.returns.push(AbiParam::new(return_cr_type));
        }

        // Create wrapper function
        let wrapper_func_key = self.funcs().intern_lambda(wrapper_index);
        let wrapper_name = self.funcs().display(wrapper_func_key);
        let wrapper_func_id = self
            .jit_module()
            .declare_function(
                &wrapper_name,
                cranelift_module::Linkage::Local,
                &wrapper_sig,
            )
            .map_err(CodegenError::cranelift)?;

        self.funcs().set_func_id(wrapper_func_key, wrapper_func_id);
        self.funcs()
            .set_return_type(wrapper_func_key, return_type_id);

        // Build the wrapper function body
        let mut wrapper_ctx = self.jit_module().make_context();
        wrapper_ctx.func.signature = wrapper_sig.clone();

        {
            let mut wrapper_builder_ctx = FunctionBuilderContext::new();
            let mut wrapper_builder =
                FunctionBuilder::new(&mut wrapper_ctx.func, &mut wrapper_builder_ctx);

            let entry_block = wrapper_builder.create_block();
            wrapper_builder.append_block_params_for_function_params(entry_block);
            wrapper_builder.switch_to_block(entry_block);

            let block_params = wrapper_builder.block_params(entry_block).to_vec();
            // block_params[0] is closure_ptr (ignored), block_params[1..] are the actual arguments

            // Get reference to original function
            let orig_func_ref = self
                .jit_module()
                .declare_func_in_func(orig_func_id, wrapper_builder.func);

            // Call original function with just the arguments (skip closure_ptr)
            let call_args: Vec<Value> = block_params[1..].to_vec();
            let call_inst = wrapper_builder.ins().call(orig_func_ref, &call_args);
            let results = wrapper_builder.inst_results(call_inst).to_vec();

            if results.is_empty() {
                wrapper_builder.ins().return_(&[]);
            } else {
                wrapper_builder.ins().return_(&[results[0]]);
            }

            wrapper_builder.seal_all_blocks();
            wrapper_builder.finalize();
        }

        self.jit_module()
            .define_function(wrapper_func_id, &mut wrapper_ctx)
            .map_err(CodegenError::cranelift)?;

        Ok(wrapper_func_id)
    }

    /// Compile a reference to a named function, wrapping it in a closure struct.
    /// Creates a wrapper function that adapts the function to the closure calling convention.
    fn function_reference(
        &mut self,
        sym: Symbol,
        func_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Look up the original function's FuncId using the name table
        let query = self.query();
        let module_id = self
            .current_module_id()
            .unwrap_or(self.env.analyzed.module_id);
        let name_id = query.function_name_id(module_id, sym);

        let orig_func_key = self.funcs().intern_name_id(name_id);
        let orig_func_id = self.funcs().func_id(orig_func_key).ok_or_else(|| {
            CodegenError::not_found("function id for", self.interner().resolve(sym))
        })?;

        // Unwrap function type to get params and return type
        let (param_ids, return_type_id) = {
            let arena = self.arena();
            let (params, ret, _is_closure) =
                arena.unwrap_function(func_type_id).ok_or_else(|| {
                    CodegenError::type_mismatch("closure wrapper", "function type", "non-function")
                })?;
            (params.clone(), ret)
        };

        let wrapper_func_id =
            self.create_closure_wrapper(orig_func_id, &param_ids, return_type_id)?;

        // Get the wrapper function address
        let wrapper_func_ref = self
            .codegen_ctx
            .jit_module()
            .declare_func_in_func(wrapper_func_id, self.builder.func);
        let ptr_type = self.ptr_type();
        let wrapper_func_addr = self.builder.ins().func_addr(ptr_type, wrapper_func_ref);

        // Wrap in a closure struct with zero captures
        let alloc_ref = self.runtime_func_ref(RuntimeKey::ClosureAlloc)?;
        let zero_captures = self.iconst_cached(types::I64, 0);
        let alloc_call = self
            .builder
            .ins()
            .call(alloc_ref, &[wrapper_func_addr, zero_captures]);
        let closure_ptr = self.builder.inst_results(alloc_call)[0];

        // Use closure type from sema (already has is_closure: true).
        // Mark as Owned: the closure allocation is a fresh +1 reference that
        // must be rc_dec'd when it goes out of scope or is consumed as an arg.
        let cv = CompiledValue::new(closure_ptr, self.ptr_type(), func_type_id);
        Ok(self.mark_rc_owned(cv))
    }

    // =========================================================================
    // Generator yield
    // =========================================================================

    /// Compile a yield expression inside a generator body.
    ///
    /// Calls `vole_generator_yield(yielder_ptr, value)` to suspend the coroutine,
    /// passing the yielded value to the iterator consumer.
    fn compile_yield(&mut self, yield_expr: &YieldExpr) -> CodegenResult<CompiledValue> {
        let yielder_var = self.yielder_var.ok_or_else(|| {
            CodegenError::unsupported("yield expression outside generator context")
        })?;

        // Compile the value to yield
        let value = self.expr(&yield_expr.value)?;

        // Load the yielder pointer
        let yielder_ptr = self.builder.use_var(yielder_var);

        // Call vole_generator_yield(yielder_ptr, value)
        self.call_runtime_void(RuntimeKey::GeneratorYield, &[yielder_ptr, value.value])?;

        // Yield is a statement-like expression; return a void/zero value.
        // The type doesn't matter since yield is used in statement position.
        Ok(CompiledValue::new(
            self.iconst_cached(types::I64, 0),
            types::I64,
            self.arena().primitives.i64,
        ))
    }

    // =========================================================================
    // VIR expression compilation
    // =========================================================================

    /// Compile a VIR expression node.
    ///
    /// Handles lowered VIR variants directly, and delegates `Ast` escape
    /// hatches to the existing `self.expr()` method.
    pub fn compile_vir_expr(&mut self, vir_expr: &VirExpr) -> CodegenResult<CompiledValue> {
        match vir_expr {
            // -- Lowered literals -----------------------------------------
            VirExpr::IntLiteral { value, ty } => {
                let type_id = if *ty == TypeId::UNKNOWN {
                    TypeId::I64
                } else {
                    *ty
                };
                Ok(self.int_const(*value, type_id))
            }
            VirExpr::WideLiteral { low, high, ty } => Ok(self.wide_literal_const(*low, *high, *ty)),
            VirExpr::FloatLiteral { value, ty } => {
                let type_id = if *ty == TypeId::UNKNOWN {
                    TypeId::F64
                } else {
                    *ty
                };
                Ok(self.float_const(*value, type_id))
            }
            VirExpr::BoolLiteral(b) => Ok(self.bool_const(*b)),
            VirExpr::StringLiteral(sym) => {
                let s = self.interner().resolve(*sym).to_string();
                self.string_literal(&s)
            }
            VirExpr::NilLiteral => {
                let value = self.iconst_cached(types::I8, 0);
                Ok(CompiledValue::new(value, types::I8, TypeId::NIL))
            }

            // -- Operators ------------------------------------------------
            VirExpr::BinaryOp { op, lhs, rhs, ty } => {
                self.compile_vir_binary_op(*op, lhs, rhs, *ty)
            }
            VirExpr::UnaryOp { op, operand, ty } => self.compile_vir_unary_op(*op, operand, *ty),
            VirExpr::StringConcat { parts } => self.compile_vir_string_concat(parts),

            // -- Coercion -------------------------------------------------
            VirExpr::Coerce {
                value,
                from,
                to,
                kind,
            } => {
                let compiled = self.compile_vir_expr(value)?;
                self.compile_vir_coerce(compiled, *from, *to, *kind)
            }

            // -- Calls ----------------------------------------------------
            VirExpr::Call { target, args, ty } => self.compile_vir_call(target, args, *ty),

            // -- Ast escape hatch -----------------------------------------
            VirExpr::Ast { expr, ty: _ } => self.expr(expr),

            // Future phases add arms here
            _ => todo!("VIR expr not yet implemented: {vir_expr:?}"),
        }
    }

    /// Compile a VIR binary operation by delegating to `binary_op()`.
    ///
    /// Converts `VirBinOp` back to the AST `BinaryOp` and calls the existing
    /// `binary_op()` method which handles type promotion and Cranelift emission.
    fn compile_vir_binary_op(
        &mut self,
        op: VirBinOp,
        lhs: &VirExpr,
        rhs: &VirExpr,
        _ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let left = self.compile_vir_expr(lhs)?;
        let right = self.compile_vir_expr(rhs)?;
        let ast_op = vir_binop_to_ast(op);
        // Line 0: VIR nodes don't carry span info yet (will be added later).
        self.binary_op(left, right, ast_op, 0)
    }

    /// Compile a VIR unary operation.
    ///
    /// Compiles the operand via `compile_vir_expr`, then delegates to the
    /// existing `unary()` infrastructure by constructing a temporary
    /// `UnaryExpr` AST node. Since `unary()` calls `self.expr()` on the
    /// operand (which would re-compile from AST), we instead inline the
    /// relevant Cranelift emission logic directly.
    fn compile_vir_unary_op(
        &mut self,
        op: VirUnOp,
        operand: &VirExpr,
        _ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let compiled = self.compile_vir_expr(operand)?;
        let ast_op = vir_unop_to_ast(op);
        self.emit_unary_op(ast_op, compiled)
    }

    /// Emit a unary operation on an already-compiled value.
    fn emit_unary_op(
        &mut self,
        op: vole_frontend::UnaryOp,
        operand: CompiledValue,
    ) -> CodegenResult<CompiledValue> {
        use crate::ops::try_constant_value;
        use vole_frontend::UnaryOp;

        let result = match op {
            UnaryOp::Neg => {
                if operand.ty == types::F128 {
                    let bits = self.call_runtime(RuntimeKey::F128Neg, &[operand.value])?;
                    self.builder
                        .ins()
                        .bitcast(types::F128, MemFlags::new(), bits)
                } else if operand.ty.is_float() {
                    self.builder.ins().fneg(operand.value)
                } else if let Some(c) = try_constant_value(self.builder.func, operand.value) {
                    self.iconst_cached(operand.ty, -c)
                } else {
                    self.builder.ins().ineg(operand.value)
                }
            }
            UnaryOp::Not => {
                let op_val = if operand.ty != types::I8 {
                    self.builder.ins().ireduce(types::I8, operand.value)
                } else {
                    operand.value
                };
                if let Some(c) = try_constant_value(self.builder.func, op_val) {
                    self.iconst_cached(types::I8, if c == 0 { 1 } else { 0 })
                } else {
                    let one = self.iconst_cached(types::I8, 1);
                    self.builder.ins().isub(one, op_val)
                }
            }
            UnaryOp::BitNot => self.builder.ins().bnot(operand.value),
        };
        Ok(operand.with_value(result))
    }

    /// Compile a VIR `StringConcat` by delegating to the existing
    /// `string_concat()` method.
    fn compile_vir_string_concat(
        &mut self,
        parts: &[vole_vir::VirRef],
    ) -> CodegenResult<CompiledValue> {
        debug_assert!(
            parts.len() >= 2,
            "StringConcat should have at least 2 parts"
        );
        let left = self.compile_vir_expr(&parts[0])?;
        let right = self.compile_vir_expr(&parts[1])?;
        self.string_concat(left, right)
    }

    /// Compile a VIR type coercion.
    ///
    /// Dispatches on `CoerceKind` to emit the appropriate Cranelift
    /// instructions for numeric conversions.  Complex coercions (Box,
    /// Unbox, IteratorWrap) are deferred to a later VIR phase.
    fn compile_vir_coerce(
        &mut self,
        value: CompiledValue,
        from: TypeId,
        to: TypeId,
        kind: CoerceKind,
    ) -> CodegenResult<CompiledValue> {
        use crate::ops::{sextend_const, uextend_const};

        let target_ty = self.cranelift_type(to);
        let result = match kind {
            CoerceKind::IntExtend => {
                if self.arena().is_unsigned(from) {
                    uextend_const(self.builder, target_ty, value.value)
                } else {
                    sextend_const(self.builder, target_ty, value.value)
                }
            }
            CoerceKind::IntTruncate => self.builder.ins().ireduce(target_ty, value.value),
            CoerceKind::IntToFloat => {
                if self.arena().is_unsigned(from) {
                    self.builder.ins().fcvt_from_uint(target_ty, value.value)
                } else {
                    self.builder.ins().fcvt_from_sint(target_ty, value.value)
                }
            }
            CoerceKind::FloatToInt => {
                if self.arena().is_unsigned(to) {
                    self.builder.ins().fcvt_to_uint(target_ty, value.value)
                } else {
                    self.builder.ins().fcvt_to_sint(target_ty, value.value)
                }
            }
            CoerceKind::FloatExtend => self.builder.ins().fpromote(target_ty, value.value),
            CoerceKind::FloatTruncate => self.builder.ins().fdemote(target_ty, value.value),
            CoerceKind::Box => {
                todo!("VIR CoerceKind::Box not yet emitted by lowering")
            }
            CoerceKind::Unbox => {
                todo!("VIR CoerceKind::Unbox not yet emitted by lowering")
            }
            CoerceKind::IteratorWrap => {
                todo!("VIR CoerceKind::IteratorWrap not yet emitted by lowering")
            }
        };
        Ok(CompiledValue::new(result, target_ty, to))
    }

    /// Compile a VIR call expression.
    ///
    /// Dispatches on `CallTarget` to select the correct calling convention.
    /// Currently only `CallTarget::Direct` is implemented; other targets
    /// are deferred to later VIR phases.
    fn compile_vir_call(
        &mut self,
        target: &CallTarget,
        args: &[vole_vir::VirRef],
        ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        match target {
            CallTarget::Direct { function_id } => {
                self.compile_vir_direct_call(*function_id, args, ty)
            }
            _ => todo!("VIR CallTarget not yet implemented: {target:?}"),
        }
    }

    /// Compile a direct call to a known function via its `FunctionId`.
    ///
    /// Resolves the sema `FunctionId` to a Cranelift `FuncId` through the
    /// entity registry and function registry, compiles VIR arguments, and
    /// emits the call instruction.
    fn compile_vir_direct_call(
        &mut self,
        function_id: vole_identity::FunctionId,
        args: &[vole_vir::VirRef],
        return_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Resolve FunctionId → NameId → FunctionKey → FuncId
        let func_def = self.query().get_function(function_id);
        let full_name_id = func_def.full_name_id;
        let func_key = self.funcs().intern_name_id(full_name_id);
        let func_id = self
            .funcs_ref()
            .func_id(func_key)
            .ok_or_else(|| CodegenError::not_found("compiled function for VIR direct call", ""))?;

        let func_ref = self
            .codegen_ctx
            .jit_module()
            .declare_func_in_func(func_id, self.builder.func);

        // Compile VIR arguments
        let mut arg_values = Vec::with_capacity(args.len());
        let mut rc_temps = Vec::new();
        for arg in args {
            let compiled = self.compile_vir_expr(arg)?;
            if compiled.is_owned() {
                rc_temps.push(compiled);
            }
            arg_values.push(compiled.value);
        }

        let call_inst = self.emit_call(func_ref, &arg_values);

        // Dec RC temp args after the call has consumed them
        self.consume_rc_args(&mut rc_temps)?;

        self.call_result(call_inst, return_ty)
    }
}

/// Convert a VIR binary operator to its AST equivalent.
fn vir_binop_to_ast(op: VirBinOp) -> BinaryOp {
    match op {
        VirBinOp::Add => BinaryOp::Add,
        VirBinOp::Sub => BinaryOp::Sub,
        VirBinOp::Mul => BinaryOp::Mul,
        VirBinOp::Div => BinaryOp::Div,
        VirBinOp::Mod => BinaryOp::Mod,
        VirBinOp::Eq => BinaryOp::Eq,
        VirBinOp::Ne => BinaryOp::Ne,
        VirBinOp::Lt => BinaryOp::Lt,
        VirBinOp::Le => BinaryOp::Le,
        VirBinOp::Gt => BinaryOp::Gt,
        VirBinOp::Ge => BinaryOp::Ge,
        VirBinOp::And => BinaryOp::And,
        VirBinOp::Or => BinaryOp::Or,
        VirBinOp::BitAnd => BinaryOp::BitAnd,
        VirBinOp::BitOr => BinaryOp::BitOr,
        VirBinOp::BitXor => BinaryOp::BitXor,
        VirBinOp::Shl => BinaryOp::Shl,
        VirBinOp::Shr => BinaryOp::Shr,
    }
}

/// Convert a VIR unary operator to its AST equivalent.
fn vir_unop_to_ast(op: VirUnOp) -> vole_frontend::UnaryOp {
    match op {
        VirUnOp::Neg => vole_frontend::UnaryOp::Neg,
        VirUnOp::Not => vole_frontend::UnaryOp::Not,
        VirUnOp::BitNot => vole_frontend::UnaryOp::BitNot,
    }
}
