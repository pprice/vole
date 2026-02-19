// src/codegen/expr/mod.rs
//
// Expression compilation - impl Cg methods.
// The main expr() router lives here; specific expression categories are in sub-modules.

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
use vole_frontend::{Expr, ExprKind, Symbol};
use vole_identity::ModuleId;
use vole_sema::entity_defs::TypeDefKind;
use vole_sema::type_arena::TypeId;

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
            ExprKind::CompoundAssign(compound) => self.compound_assign(compound, expr.span.line),
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
            ExprKind::Index(idx) => self.index(&idx.object, &idx.index),
            ExprKind::Match(match_expr) => self.match_expr(match_expr, expr.id),
            ExprKind::Is(is_expr) => self.is_expr(is_expr, expr.id),
            ExprKind::NullCoalesce(nc) => self.null_coalesce(nc),
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
            ExprKind::OptionalChain(oc) => self.optional_chain(oc, expr.id),
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
                    let kind = self.registry().get_type(type_def_id).kind;
                    if kind == TypeDefKind::Sentinel {
                        self.registry().get_type(type_def_id).base_type_id
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
            // optional_chain knows the inner payload will be dec'd at scope
            // exit and does not emit a redundant rc_dec.
            if cv.rc_lifecycle == RcLifecycle::Untracked
                && self.rc_state(*type_id).union_variants().is_some()
            {
                cv.mark_borrowed();
            }
            Ok(cv)
        } else if let Some(&(module_id, export_name, export_type_id)) =
            self.module_bindings.get(&sym)
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
}
