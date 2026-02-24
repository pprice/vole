// src/codegen/expr/mod.rs
//
// Expression compilation - impl Cg methods.
// The main expr() router lives here; specific expression categories are in sub-modules.

mod as_cast;
mod control_flow;
mod error_patterns;
mod field_ops;
mod indexing;
mod literal;
mod null_ops;
mod pattern_match;
mod unary_assign;
mod vir_calls;

use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};
use smallvec::smallvec;

use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::union_layout;

use vole_frontend::ast::YieldExpr;
use vole_frontend::{BinaryOp, Expr, ExprKind, Symbol};
use vole_identity::{ModuleId, TypeDefId};
use vole_sema::type_arena::TypeId;
use vole_vir::{
    AsCastKind, CoerceKind, IsCheckResult, VirBinOp, VirExpr, VirMetaKind, VirStringPart, VirUnOp,
};

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

    /// Compile a VIR yield expression inside a generator body.
    ///
    /// Like [`compile_yield`] but operates on a VIR `VirRef` value instead of
    /// an AST `YieldExpr`.
    fn compile_vir_yield(&mut self, value: &VirExpr) -> CodegenResult<CompiledValue> {
        let yielder_var = self.yielder_var.ok_or_else(|| {
            CodegenError::unsupported("yield expression outside generator context")
        })?;

        // Compile the yielded value
        let compiled = self.compile_vir_expr(value)?;

        // Load the yielder pointer
        let yielder_ptr = self.builder.use_var(yielder_var);

        // Call vole_generator_yield(yielder_ptr, value)
        self.call_runtime_void(RuntimeKey::GeneratorYield, &[yielder_ptr, compiled.value])?;

        // Yield is a statement-like expression; return a void/zero value.
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
    /// All VIR variants are handled directly.  A few (`MethodCall`,
    /// `OptionalMethodCall`) delegate to existing AST-based methods for
    /// dispatch logic that has not yet been fully migrated.
    #[deny(clippy::wildcard_enum_match_arm)]
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

            // -- Simple expressions -----------------------------------------
            VirExpr::Unreachable { line } => self.unreachable_expr(*line),
            VirExpr::Import { ty } => {
                let type_id = if *ty == TypeId::UNKNOWN {
                    self.arena().primitives.i64
                } else {
                    *ty
                };
                Ok(CompiledValue::new(
                    self.iconst_cached(types::I64, 0),
                    types::I64,
                    type_id,
                ))
            }
            VirExpr::TypeLiteral => Err(CodegenError::unsupported(
                "type expressions as runtime values",
            )),
            VirExpr::Range {
                start,
                end,
                inclusive,
            } => self.compile_vir_range(start, end, *inclusive),

            // -- Operators ------------------------------------------------
            VirExpr::BinaryOp {
                op,
                lhs,
                rhs,
                ty,
                line,
            } => self.compile_vir_binary_op(*op, lhs, rhs, *ty, *line),
            VirExpr::UnaryOp { op, operand, ty } => self.compile_vir_unary_op(*op, operand, *ty),
            VirExpr::StringConcat { parts } => self.compile_vir_string_concat(parts),
            VirExpr::InterpolatedString { parts } => self.compile_vir_interpolated_string(parts),

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
            VirExpr::MethodCall {
                method_call,
                node_id,
                ty: _,
            } => {
                let result = self.method_call(method_call, *node_id)?;
                Ok(self.mark_rc_owned(result))
            }

            // -- Control flow ---------------------------------------------
            VirExpr::If {
                cond,
                then_body,
                else_body,
                ty,
            } => self.compile_vir_if(cond, then_body, else_body.as_ref(), *ty),

            VirExpr::Block {
                stmts,
                trailing,
                ty: _,
            } => self.compile_vir_block(stmts, trailing.as_deref()),

            // -- Pattern match ------------------------------------------------
            VirExpr::Match {
                scrutinee,
                arms,
                ty,
            } => self.compile_vir_match(scrutinee, arms, *ty),

            // -- Construction -------------------------------------------------
            VirExpr::ArrayLiteral { elements, ty } => {
                let result = self.compile_vir_array_literal(elements, *ty)?;
                Ok(self.mark_rc_owned(result))
            }
            VirExpr::RepeatLiteral { element, count, ty } => {
                let result = self.compile_vir_repeat_literal(element, *count, *ty)?;
                Ok(self.mark_rc_owned(result))
            }
            VirExpr::StructLiteral {
                type_def,
                fields,
                ty,
            } => {
                let result = self.compile_vir_struct_literal(*type_def, fields, *ty)?;
                Ok(self.mark_rc_owned(result))
            }
            VirExpr::ClassInstance {
                type_def,
                fields,
                ty,
            } => {
                let result = self.compile_vir_class_instance(*type_def, fields, *ty)?;
                Ok(self.mark_rc_owned(result))
            }

            // -- Field access -------------------------------------------------
            VirExpr::FieldLoad {
                object,
                field,
                storage: _,
                ty,
            } => self.compile_vir_field_load(object, *field, *ty),
            VirExpr::FieldStore {
                object,
                field,
                storage: _,
                value,
            } => self.compile_vir_field_store(object, *field, value),

            // -- Indexing ------------------------------------------------------
            VirExpr::Index {
                object,
                index,
                ty,
                union_storage,
            } => self.compile_vir_index(object, index, *ty, *union_storage),
            VirExpr::IndexStore {
                object,
                index,
                value,
                union_storage,
            } => self.compile_vir_index_store(object, index, value, *union_storage),

            // -- RC operations ------------------------------------------------
            VirExpr::RcInc { value } => {
                let compiled = self.compile_vir_expr(value)?;
                self.emit_rc_inc(compiled.value)?;
                Ok(compiled)
            }
            VirExpr::RcDec { value } => {
                let compiled = self.compile_vir_expr(value)?;
                self.emit_rc_dec(compiled.value)?;
                Ok(compiled)
            }
            VirExpr::RcMove { value } => {
                // Ownership transfer marker — no runtime effect, just pass through.
                self.compile_vir_expr(value)
            }

            // -- Type operations ------------------------------------------
            VirExpr::IsCheck {
                value,
                result,
                ty: _,
            } => self.compile_vir_is_check(value, *result),
            VirExpr::AsCast {
                value,
                target_ty,
                kind,
                result,
            } => self.compile_vir_as_cast(value, *target_ty, *kind, *result),

            // -- Reflection ---------------------------------------------------
            VirExpr::MetaAccess { kind, ty } => self.compile_vir_meta_access(kind, *ty),

            // -- Variables ------------------------------------------------
            VirExpr::LocalLoad { name, ty } => self.compile_local_load(*name, *ty),
            VirExpr::LocalStore { name, value } => self.compile_local_store(*name, value),

            // -- Null / optional operations --------------------------------
            VirExpr::NullCoalesce {
                value,
                default,
                inner_type,
                ty,
            } => self.compile_vir_null_coalesce(value, default, *inner_type, *ty),
            VirExpr::OptionalChain {
                object,
                field,
                inner_type,
                ty,
            } => self.compile_vir_optional_chain(object, *field, *inner_type, *ty),
            VirExpr::OptionalMethodCall {
                object,
                call_expr,
                inner_type,
                ty,
            } => self.compile_vir_optional_method_call(object, call_expr, *inner_type, *ty),
            VirExpr::Try {
                value,
                success_type,
            } => self.compile_vir_try(value, *success_type),

            // -- Lambda / closure ------------------------------------------
            VirExpr::Lambda {
                params,
                body,
                captures,
                ty,
            } => {
                let result = self.compile_vir_lambda(params, body, captures, *ty)?;
                Ok(self.mark_rc_owned(result))
            }

            // -- Generator ------------------------------------------------
            VirExpr::Yield { value } => self.compile_vir_yield(value),
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
        line: u32,
    ) -> CodegenResult<CompiledValue> {
        let left = self.compile_vir_expr(lhs)?;
        let right = self.compile_vir_expr(rhs)?;
        let ast_op = vir_binop_to_ast(op);
        self.binary_op(left, right, ast_op, line)
    }

    /// Compile a VIR unary operation.
    ///
    /// Compiles the operand via `compile_vir_expr`, then delegates to
    /// `emit_unary_op` which handles the Cranelift emission directly.
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

    /// Compile a VIR `InterpolatedString`.
    ///
    /// Each part is either a literal (compiled as a static string) or an
    /// expression with a `StringConversion` annotation.  Single-part
    /// interpolations preserve the borrowed/owned lifecycle of the original
    /// expression.  Multi-part interpolations use StringBuilder for a
    /// single allocation.
    fn compile_vir_interpolated_string(
        &mut self,
        parts: &[VirStringPart],
    ) -> CodegenResult<CompiledValue> {
        if parts.is_empty() {
            return self.string_literal("");
        }

        // Collect all string values and track which are owned for cleanup.
        let mut string_values: Vec<Value> = Vec::new();
        let mut owned_flags: Vec<bool> = Vec::new();
        for part in parts {
            let (str_val, is_owned) = match part {
                VirStringPart::Literal(sym) => {
                    let s = self.interner().resolve(*sym).to_string();
                    (self.string_literal(&s)?.value, true)
                }
                VirStringPart::Expr { value, conversion } => {
                    let compiled = self.compile_vir_expr(value)?;
                    #[allow(clippy::wildcard_enum_match_arm)] // sema enum, not VIR dispatch
                    match conversion {
                        vole_sema::StringConversion::Identity => {
                            (compiled.value, compiled.is_owned())
                        }
                        _ => (self.apply_string_conversion(compiled, conversion)?, true),
                    }
                }
            };
            string_values.push(str_val);
            owned_flags.push(is_owned);
        }

        // Single part: return directly, preserving borrowed/owned lifecycle.
        if string_values.len() == 1 {
            let mut cv = self.string_temp(string_values[0]);
            if !owned_flags[0] {
                cv.mark_borrowed();
            }
            return Ok(cv);
        }

        // Multi-part: use StringBuilder for a single allocation.
        let sb = self.call_runtime(RuntimeKey::SbNew, &[])?;
        for &sv in &string_values {
            self.call_runtime_void(RuntimeKey::SbPushString, &[sb, sv])?;
        }
        let result = self.call_runtime(RuntimeKey::SbFinish, &[sb])?;

        // Free owned input parts — builder has copied the bytes.
        for (val, is_owned) in string_values.iter().zip(owned_flags.iter()) {
            if *is_owned {
                self.emit_rc_dec(*val)?;
            }
        }

        Ok(self.string_temp(result))
    }

    /// Compile a VIR type coercion.
    ///
    /// Dispatches on `CoerceKind` to emit the appropriate Cranelift
    /// instructions for numeric conversions, interface boxing/unboxing,
    /// and iterator wrapping.
    fn compile_vir_coerce(
        &mut self,
        value: CompiledValue,
        from: TypeId,
        to: TypeId,
        kind: CoerceKind,
    ) -> CodegenResult<CompiledValue> {
        use crate::ops::{sextend_const, uextend_const};

        let target_ty = self.cranelift_type(to);
        match kind {
            CoerceKind::IntExtend => {
                let result = if self.arena().is_unsigned(from) {
                    uextend_const(self.builder, target_ty, value.value)
                } else {
                    sextend_const(self.builder, target_ty, value.value)
                };
                Ok(CompiledValue::new(result, target_ty, to))
            }
            CoerceKind::IntTruncate => {
                let result = self.builder.ins().ireduce(target_ty, value.value);
                Ok(CompiledValue::new(result, target_ty, to))
            }
            CoerceKind::IntToFloat => {
                let result = if self.arena().is_unsigned(from) {
                    self.builder.ins().fcvt_from_uint(target_ty, value.value)
                } else {
                    self.builder.ins().fcvt_from_sint(target_ty, value.value)
                };
                Ok(CompiledValue::new(result, target_ty, to))
            }
            CoerceKind::FloatToInt => {
                let result = if self.arena().is_unsigned(to) {
                    self.builder.ins().fcvt_to_uint(target_ty, value.value)
                } else {
                    self.builder.ins().fcvt_to_sint(target_ty, value.value)
                };
                Ok(CompiledValue::new(result, target_ty, to))
            }
            CoerceKind::FloatExtend => {
                let result = self.builder.ins().fpromote(target_ty, value.value);
                Ok(CompiledValue::new(result, target_ty, to))
            }
            CoerceKind::FloatTruncate => {
                let result = self.builder.ins().fdemote(target_ty, value.value);
                Ok(CompiledValue::new(result, target_ty, to))
            }
            CoerceKind::Box => self.compile_coerce_box(value, to),
            CoerceKind::Unbox => self.compile_coerce_unbox(value, to),
            CoerceKind::IteratorWrap => self.compile_coerce_iterator_wrap(value, to),
        }
    }

    /// Box a concrete value as an interface type.
    ///
    /// Allocates `[data_ptr, vtable_ptr]` on the heap and generates the
    /// vtable for the concrete type implementing the interface.  Delegates
    /// to the existing `box_interface_value` infrastructure.
    fn compile_coerce_box(
        &mut self,
        value: CompiledValue,
        interface_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        self.box_interface_value(value, interface_type_id)
    }

    /// Unbox an interface pointer back to the concrete value.
    ///
    /// Loads the data word at offset 0 from the interface box `[data, vtable]`
    /// and converts it back to the concrete Cranelift type.
    fn compile_coerce_unbox(
        &mut self,
        value: CompiledValue,
        concrete_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let ptr_ty = self.ptr_type();
        let data_word = self
            .builder
            .ins()
            .load(ptr_ty, MemFlags::new(), value.value, 0);
        let concrete_val = self.convert_from_i64_storage(data_word, concrete_type_id);
        let concrete_ty = self.cranelift_type(concrete_type_id);
        Ok(CompiledValue::new(
            concrete_val,
            concrete_ty,
            concrete_type_id,
        ))
    }

    /// Wrap a concrete iterator as a `RuntimeIterator`.
    ///
    /// 1. Extracts the element type from the target `RuntimeIterator(elem)`.
    /// 2. Looks up the `Iterator<elem>` interface type.
    /// 3. Boxes the value as that interface.
    /// 4. Wraps via `InterfaceIter` runtime call.
    /// 5. Consumes the intermediate boxed interface.
    fn compile_coerce_iterator_wrap(
        &mut self,
        value: CompiledValue,
        runtime_iter_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Extract element type from RuntimeIterator(elem)
        let elem_type_id = self
            .arena()
            .unwrap_runtime_iterator(runtime_iter_type_id)
            .ok_or_else(|| {
                CodegenError::internal("IteratorWrap target is not a RuntimeIterator type")
            })?;

        // Look up Iterator<elem> interface type
        let iterator_type_def = self
            .name_table()
            .well_known
            .iterator_type_def
            .ok_or_else(|| CodegenError::internal("Iterator type_def not found"))?;
        let interface_type_id = self
            .arena()
            .lookup_interface(iterator_type_def, smallvec![elem_type_id])
            .ok_or_else(|| {
                CodegenError::internal("Iterator<T> interface type not found in arena")
            })?;

        // Box as Iterator<elem> interface
        let mut boxed = self.box_interface_value(value, interface_type_id)?;

        // Wrap via InterfaceIter runtime call
        let wrapped = self.call_runtime(RuntimeKey::InterfaceIter, &[boxed.value])?;

        // Release the intermediate boxed interface (InterfaceIter took its own ref)
        self.consume_rc_value(&mut boxed)?;

        Ok(CompiledValue::owned(
            wrapped,
            types::I64,
            runtime_iter_type_id,
        ))
    }

    /// Compile a VIR `LocalLoad` — variable/identifier lookup.
    ///
    /// Handles four cases in priority order:
    /// 1. **Sentinel types** — if `ty` is a sentinel, emit `i8(0)`.
    /// 2. **Local variables** — look up in `self.vars`, with union narrowing
    ///    and unknown extraction when `ty` differs from the declared type.
    /// 3. **Non-local identifiers** — module bindings, globals, function refs,
    ///    and sentinel fallback are delegated to the full `identifier()` path
    ///    (these will migrate to dedicated VIR nodes later).
    fn compile_local_load(&mut self, sym: Symbol, ty: TypeId) -> CodegenResult<CompiledValue> {
        // 1. Sentinel types — always i8(0).
        if self.arena().is_sentinel(ty) {
            let value = self.iconst_cached(types::I8, 0);
            return Ok(CompiledValue::new(value, types::I8, ty));
        }

        // 2. Captured variable — load from closure environment.
        if self.has_captures()
            && let Some(binding) = self.get_capture(&sym).copied()
        {
            return self.load_capture(&binding);
        }

        // 3. Local variable — vars map lookup with narrowing.
        if let Some((var, var_type_id)) = self.vars.get(&sym) {
            return self.compile_local_var_load(*var, *var_type_id, ty);
        }

        // 4. Non-local fallback: module bindings, globals, function refs.
        self.compile_non_local_load(sym, ty)
    }

    /// Load a local variable from the vars map, handling union narrowing,
    /// unknown extraction, and RC lifecycle marking.
    fn compile_local_var_load(
        &mut self,
        var: Variable,
        var_type_id: TypeId,
        narrowed_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let val = self.builder.use_var(var);
        let cl_ty = self.builder.func.dfg.value_type(val);

        // Union narrowing: if VIR type differs from declared type, extract
        // the payload from the tagged union.
        let resolved_union_type_id = self.try_substitute_type(var_type_id);
        let narrowed_type_id = self.try_substitute_type(narrowed_ty);
        if self.arena().is_union(resolved_union_type_id)
            && !self.arena().is_union(narrowed_type_id)
            && narrowed_type_id != resolved_union_type_id
            && let Some(narrowed_variant) =
                self.find_union_variant(resolved_union_type_id, narrowed_type_id)
        {
            let payload_ty = type_id_to_cranelift(narrowed_variant, self.arena(), self.ptr_type());
            let payload = self.load_union_payload(val, resolved_union_type_id, payload_ty);
            let mut cv = CompiledValue::new(payload, payload_ty, narrowed_variant);
            self.mark_borrowed_if_rc(&mut cv);
            return Ok(cv);
        }

        // Unknown extraction: if declared type is unknown but VIR type is
        // concrete, extract the value from the TaggedValue.
        if self.arena().is_unknown(var_type_id) && !self.arena().is_unknown(narrowed_type_id) {
            let raw_value = self.builder.ins().load(
                types::I64,
                MemFlags::new(),
                val,
                union_layout::PAYLOAD_OFFSET,
            );
            let extracted = self.extract_unknown_value(raw_value, narrowed_type_id);
            return Ok(extracted);
        }

        // Simple local: no narrowing needed.
        let mut cv = CompiledValue::new(val, cl_ty, var_type_id);
        self.mark_borrowed_if_rc(&mut cv);
        if cv.rc_lifecycle == RcLifecycle::Untracked
            && self.rc_state(var_type_id).union_variants().is_some()
        {
            cv.mark_borrowed();
        }
        Ok(cv)
    }

    /// Find a union variant matching the narrowed type, with integer fallback.
    fn find_union_variant(
        &self,
        union_type_id: TypeId,
        narrowed_type_id: TypeId,
    ) -> Option<TypeId> {
        self.arena()
            .unwrap_union(union_type_id)
            .and_then(|variants| {
                variants
                    .iter()
                    .copied()
                    .find(|&v| v == narrowed_type_id)
                    .or_else(|| {
                        if self.arena().is_integer(narrowed_type_id) {
                            variants
                                .iter()
                                .copied()
                                .find(|&v| self.arena().is_integer(v))
                        } else {
                            None
                        }
                    })
            })
    }

    /// Handle non-local identifier resolution: module bindings, globals,
    /// function references, and sentinel fallback.
    fn compile_non_local_load(&mut self, sym: Symbol, ty: TypeId) -> CodegenResult<CompiledValue> {
        // Module binding
        if let Some(&(module_id, export_name, export_type_id)) = self.lookup_module_binding(&sym) {
            return self.module_binding_value(module_id, export_name, export_type_id);
        }

        // Global initializer
        if let Some(global_init) = self.global_init(sym).cloned() {
            let mut value = self.expr(&global_init)?;
            let name_table = self.name_table();
            let module_id = self.current_module().unwrap_or(self.env.analyzed.module_id);
            if let Some(name_id) = name_table.name_id(module_id, &[sym], self.interner())
                && let Some(global_def) = self.query().global(name_id)
            {
                value = self.coerce_to_type(value, global_def.type_id)?;
            }
            return Ok(value);
        }

        // Function reference
        if self.arena().is_function(ty) {
            return self.function_reference(sym, ty);
        }

        // Sentinel fallback (name-based resolution)
        let name = self.interner().resolve(sym);
        let module_id = self.current_module.unwrap_or(self.env.analyzed.module_id);
        if let Some(type_def_id) = self.query().resolve_type_def_by_str(module_id, name)
            && self.query().is_sentinel_type(type_def_id)
            && let Some(sentinel_type_id) = self.query().sentinel_base_type(type_def_id)
        {
            let value = self.iconst_cached(types::I8, 0);
            return Ok(CompiledValue::new(value, types::I8, sentinel_type_id));
        }

        Err(CodegenError::not_found(
            "variable",
            self.interner().resolve(sym),
        ))
    }

    /// Compile a VIR `LocalStore` — variable assignment.
    ///
    /// Handles simple variable assignment with RC bookkeeping, captured
    /// variable stores, and type coercion.  Field and index assignment
    /// targets are handled by `VirExpr::FieldStore` and `VirExpr::IndexStore`.
    pub(crate) fn compile_local_store(
        &mut self,
        sym: Symbol,
        value_expr: &VirExpr,
    ) -> CodegenResult<CompiledValue> {
        // Snapshot RC state before evaluating the new value.
        let (rc_old, composite_rc_old, union_rc_old) = self.snapshot_rc_for_reassignment(&sym);

        let mut value = self.compile_vir_expr(value_expr)?;

        // Captured variable — store through closure environment.
        if let Some(binding) = self.get_capture(&sym).copied() {
            return self.store_capture(&binding, value);
        }

        let (var, var_type_id) = self
            .vars
            .get(&sym)
            .ok_or_else(|| CodegenError::not_found("variable", self.interner().resolve(sym)))?;
        let var = *var;
        let var_type_id = *var_type_id;

        value = self.coerce_to_type(value, var_type_id)?;

        // RC bookkeeping: inc new if borrowed, store, dec old.
        if rc_old.is_some() && value.is_borrowed() {
            self.emit_rc_inc_for_type(value.value, var_type_id)?;
        }
        self.builder.def_var(var, value.value);
        if let Some(old_val) = rc_old {
            self.emit_rc_dec_for_type(old_val, var_type_id)?;
        }

        // Composite RC: dec each RC field of the old struct.
        if let Some((old_ptr, offsets)) = composite_rc_old {
            for off in &offsets {
                let field_ptr = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), old_ptr, *off);
                self.emit_rc_dec(field_ptr)?;
            }
            self.rc_scopes.update_composite_offsets(var, offsets);
        }

        // Union RC: dec the RC payload of the old union value.
        if let Some((old_ptr, rc_tags)) = union_rc_old {
            self.emit_union_rc_dec(old_ptr, &rc_tags)?;
        }

        value.mark_consumed();
        value.debug_assert_rc_handled("assign to variable");
        Ok(value)
    }

    // =========================================================================
    // VIR MetaAccess
    // =========================================================================

    /// Compile a VIR `MetaAccess` expression (`.@meta`).
    ///
    /// Dispatches on `VirMetaKind`:
    /// - `Static`: builds a cached TypeMeta for the compile-time-known type.
    ///   In monomorphized contexts, re-derives the TypeDefId from the object's
    ///   concrete type to handle stale sema annotations.
    /// - `Dynamic`: loads the meta getter from the interface vtable and calls it.
    /// - `TypeParam`: resolves the type parameter via substitutions, then
    ///   dispatches to the static or dynamic path.
    fn compile_vir_meta_access(
        &mut self,
        kind: &VirMetaKind,
        ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        use crate::reflection::{
            compile_dynamic_meta_from_value, compile_static_meta_with_type,
            resolve_reflection_types,
        };

        let result_ty = if ty == TypeId::UNKNOWN {
            resolve_reflection_types(self)
                .ok()
                .map(|i| i.type_meta_type_id)
                .unwrap_or(TypeId::UNKNOWN)
        } else {
            ty
        };

        match kind {
            VirMetaKind::Static { type_def, object } => {
                let effective_type_def = if self.substitutions.is_some() {
                    self.resolve_vir_static_meta_type_def(object.as_deref())
                        .unwrap_or(*type_def)
                } else {
                    *type_def
                };
                compile_static_meta_with_type(self, effective_type_def, result_ty)
            }
            VirMetaKind::Dynamic { value } => {
                let obj = self.compile_vir_expr(value)?;
                compile_dynamic_meta_from_value(self, obj, result_ty)
            }
            VirMetaKind::TypeParam { name_id, value } => {
                self.compile_vir_type_param_meta(*name_id, value, result_ty)
            }
        }
    }

    /// Re-derive the TypeDefId for a static meta access in a monomorphized context.
    ///
    /// When codegen compiles multiple monomorphizations of a generic function,
    /// sema's `MetaAccessKind::Static` annotation may refer to the wrong TypeDefId
    /// because all monomorphizations share the same NodeId and the last re-analysis
    /// overwrites earlier ones.  This function re-derives the correct TypeDefId
    /// from the object's concrete type in the current codegen scope.
    fn resolve_vir_static_meta_type_def(&self, object: Option<&VirExpr>) -> Option<TypeDefId> {
        let object = object?;
        #[allow(clippy::wildcard_enum_match_arm)] // predicate query, not dispatch
        let object_type_id = match object {
            VirExpr::LocalLoad { name, .. } => self.vars.get(name).map(|(_, ty)| *ty)?,
            _ => return None,
        };
        let (type_def_id, _, _) = self.arena().unwrap_nominal(object_type_id)?;
        Some(type_def_id)
    }

    /// Resolve a `TypeParam` meta access by looking up the concrete type from
    /// the current monomorphization substitutions.
    fn compile_vir_type_param_meta(
        &mut self,
        name_id: vole_identity::NameId,
        value: &VirExpr,
        result_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        use crate::reflection::{compile_dynamic_meta_from_value, compile_static_meta_with_type};

        let substitutions = self.substitutions.ok_or_else(|| {
            CodegenError::unsupported(
                "T.@meta requires concrete type (not in a monomorphized context)",
            )
        })?;

        let concrete_type_id = substitutions.get(&name_id).copied().ok_or_else(|| {
            let param_name = self
                .query()
                .last_segment(name_id)
                .unwrap_or_else(|| "?".to_string());
            CodegenError::unsupported_with_context(
                "T.@meta: no substitution for type parameter",
                param_name,
            )
        })?;

        // Interface types require dynamic dispatch via vtable.
        if self.arena().is_interface(concrete_type_id) {
            let obj = self.compile_vir_expr(value)?;
            return compile_dynamic_meta_from_value(self, obj, result_ty);
        }

        // Concrete nominal types (class/struct) are resolved statically.
        if let Some((type_def_id, _, _)) = self.arena().unwrap_nominal(concrete_type_id) {
            return compile_static_meta_with_type(self, type_def_id, result_ty);
        }

        // Unsupported concrete type (primitive, array, function, etc.)
        let display = self.arena().display_basic(concrete_type_id);
        Err(CodegenError::unsupported_with_context(
            "T.@meta: concrete type does not support reflection",
            display,
        ))
    }

    // =========================================================================
    // VIR IsCheck / AsCast
    // =========================================================================

    /// Compile a VIR `IsCheck` expression.
    ///
    /// The `result` field carries the sema-computed decision so codegen is
    /// purely mechanical: static true/false or a runtime tag/unknown check.
    fn compile_vir_is_check(
        &mut self,
        value: &VirExpr,
        result: IsCheckResult,
    ) -> CodegenResult<CompiledValue> {
        match result {
            IsCheckResult::AlwaysTrue => {
                // Compile value for side-effects, then return true.
                let _value = self.compile_vir_expr(value)?;
                Ok(self.bool_const(true))
            }
            IsCheckResult::AlwaysFalse => {
                let _value = self.compile_vir_expr(value)?;
                Ok(self.bool_const(false))
            }
            IsCheckResult::CheckTag(tag_index) => {
                let compiled = self.compile_vir_expr(value)?;
                let cmp = self.tag_eq(compiled.value, tag_index as i64);
                Ok(self.bool_value(cmp))
            }
            IsCheckResult::CheckUnknown(tested_type_id) => {
                let compiled = self.compile_vir_expr(value)?;
                let cmp = self.compile_unknown_is_check(compiled.value, tested_type_id);
                Ok(self.bool_value(cmp))
            }
        }
    }

    /// Compile a VIR `AsCast` expression (`as?` or `as!`).
    ///
    /// Dispatches on the sema-computed `IsCheckResult` embedded in the VIR
    /// node.  `kind` distinguishes checked (as?) from unchecked (as!) casts.
    ///
    /// `target_ty` is the sema expression type:
    ///   - For `as?`: `T | nil` (nullable result)
    ///   - For `as!`: `T` (the tested type directly)
    fn compile_vir_as_cast(
        &mut self,
        value_expr: &VirExpr,
        target_ty: TypeId,
        kind: AsCastKind,
        result: IsCheckResult,
    ) -> CodegenResult<CompiledValue> {
        let value = self.compile_vir_expr(value_expr)?;
        match result {
            IsCheckResult::AlwaysTrue => self.vir_as_cast_always_true(kind, value, target_ty),
            IsCheckResult::AlwaysFalse => self.vir_as_cast_always_false(kind, target_ty),
            IsCheckResult::CheckTag(tag_index) => {
                self.vir_as_cast_check_tag(kind, value, tag_index, target_ty)
            }
            IsCheckResult::CheckUnknown(tested_type_id) => {
                self.vir_as_cast_check_unknown(kind, value, tested_type_id, target_ty)
            }
        }
    }

    /// Handle `as` cast when sema determined it always succeeds.
    fn vir_as_cast_always_true(
        &mut self,
        kind: AsCastKind,
        value: CompiledValue,
        target_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        match kind {
            AsCastKind::Checked => {
                // target_ty is T | nil — wrap the value.
                self.coerce_to_type(value, target_ty)
            }
            AsCastKind::Unchecked => {
                // Value is already T — pass through.
                Ok(value)
            }
        }
    }

    /// Handle `as` cast when sema determined it always fails.
    fn vir_as_cast_always_false(
        &mut self,
        kind: AsCastKind,
        target_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        match kind {
            AsCastKind::Checked => {
                // target_ty is T | nil — always returns nil.
                self.compile_nil_for_optional(target_ty)
            }
            AsCastKind::Unchecked => {
                // Always panics.
                self.emit_panic_static("as! cast failed: value is not the expected type", 0)?;
                Ok(CompiledValue::new(
                    self.iconst_cached(types::I64, 0),
                    types::I64,
                    TypeId::NEVER,
                ))
            }
        }
    }

    /// Handle union tag check for `as` cast: branch on tag, extract payload.
    fn vir_as_cast_check_tag(
        &mut self,
        kind: AsCastKind,
        value: CompiledValue,
        tag_index: u32,
        target_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Derive the tested type from the union variants.
        let tested_type_id = self
            .arena()
            .unwrap_union(value.type_id)
            .and_then(|variants| variants.get(tag_index as usize).copied())
            .ok_or_else(|| {
                CodegenError::internal("as cast CheckTag: cannot derive tested type from union")
            })?;
        let is_match = self.tag_eq(value.value, tag_index as i64);
        match kind {
            AsCastKind::Checked => {
                // target_ty is T | nil
                self.as_cast_safe_branch_with_type(is_match, target_ty, |cg| {
                    cg.extract_union_payload_typed(value, tested_type_id)
                })
            }
            AsCastKind::Unchecked => {
                // target_ty is T
                self.as_cast_unsafe_branch_with_type(is_match, tested_type_id, 0, |cg| {
                    cg.extract_union_payload_typed(value, tested_type_id)
                })
            }
        }
    }

    /// Handle unknown type check for `as` cast: branch on runtime tag.
    fn vir_as_cast_check_unknown(
        &mut self,
        kind: AsCastKind,
        value: CompiledValue,
        tested_type_id: TypeId,
        target_ty: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let tag = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), value.value, 0);
        let expected_tag = crate::types::unknown_type_tag(tested_type_id, self.arena());
        let expected_val = self.iconst_cached(types::I64, expected_tag as i64);
        let is_match = self.builder.ins().icmp(IntCC::Equal, tag, expected_val);
        match kind {
            AsCastKind::Checked => {
                // target_ty is T | nil
                self.as_cast_safe_branch_with_type(is_match, target_ty, |cg| {
                    let raw_value = cg.builder.ins().load(
                        types::I64,
                        MemFlags::new(),
                        value.value,
                        union_layout::PAYLOAD_OFFSET,
                    );
                    Ok(cg.extract_unknown_value(raw_value, tested_type_id))
                })
            }
            AsCastKind::Unchecked => {
                self.as_cast_unsafe_branch_with_type(is_match, tested_type_id, 0, |cg| {
                    let raw_value = cg.builder.ins().load(
                        types::I64,
                        MemFlags::new(),
                        value.value,
                        union_layout::PAYLOAD_OFFSET,
                    );
                    Ok(cg.extract_unknown_value(raw_value, tested_type_id))
                })
            }
        }
    }

    // VIR call dispatch is in the `vir_calls` submodule.
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
