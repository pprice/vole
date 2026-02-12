// src/codegen/expr.rs
//
// Expression compilation - impl Cg methods.

use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;
use cranelift_module::Module;

use crate::RuntimeFn;
use crate::errors::{CodegenError, CodegenResult};
use rustc_hash::FxHashMap;

use vole_frontend::{
    AssignTarget, BlockExpr, Expr, ExprKind, IfExpr, MatchExpr, NodeId, Pattern, PatternKind,
    RangeExpr, RecordFieldPattern, Symbol, TypeExpr, UnaryOp, WhenExpr,
};
use vole_identity::ModuleId;
use vole_sema::IsCheckResult;
use vole_sema::entity_defs::TypeDefKind;
use vole_sema::type_arena::TypeId;

use super::context::Cg;
use super::control_flow::match_switch;
use super::structs::{convert_to_i64_for_storage, get_field_slot_and_type_id_cg};
use super::types::{
    CompiledValue, FALLIBLE_PAYLOAD_OFFSET, FALLIBLE_SUCCESS_TAG, RcLifecycle,
    array_element_tag_id, fallible_error_tag_by_id, load_fallible_payload, load_fallible_tag,
    tuple_layout_id, type_id_to_cranelift,
};

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
                    self.builder.ins().iconst(types::I64, 0),
                    types::I64,
                    type_id,
                ))
            }
            ExprKind::Yield(_) => {
                // Yield should be caught in semantic analysis
                Err(CodegenError::unsupported(
                    "yield expression outside generator context",
                ))
            }
            ExprKind::Block(block_expr) => self.block_expr(block_expr),
            ExprKind::If(if_expr) => self.if_expr(if_expr, expr.id),
            ExprKind::When(when_expr) => self.when_expr(when_expr, expr.id),
            ExprKind::Unreachable => self.unreachable_expr(expr.span.line),
        }
    }

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
                let value = self.builder.ins().iconst(types::I8, 0);
                return Ok(CompiledValue::new(value, types::I8, type_id));
            }
        }

        if let Some((var, type_id)) = self.vars.get(&sym) {
            let val = self.builder.use_var(*var);
            let ty = self.builder.func.dfg.value_type(val);

            // Check for narrowed type from semantic analysis
            if let Some(narrowed_type_id) = self.get_expr_type(&expr.id)
                && self.arena().is_union(*type_id)
                && !self.arena().is_union(narrowed_type_id)
            {
                // Union layout: [tag:1][padding:7][payload]
                let payload_ty =
                    type_id_to_cranelift(narrowed_type_id, self.arena(), self.ptr_type());
                // Only load payload if union has payload data.
                // Sentinel-only unions have union_size == 8 (tag only), no payload to read.
                let union_size = self.type_size(*type_id);
                let payload = if union_size > 8 {
                    self.builder.ins().load(payload_ty, MemFlags::new(), val, 8)
                } else {
                    self.builder.ins().iconst(payload_ty, 0)
                };
                let mut cv = CompiledValue::new(payload, payload_ty, narrowed_type_id);
                // The extracted payload is borrowed from the union variable —
                // callers must rc_inc if they take ownership.
                self.mark_borrowed_if_rc(&mut cv);
                return Ok(cv);
            }

            // Check for narrowed type from unknown
            if let Some(narrowed_type_id) = self.get_expr_type(&expr.id)
                && self.arena().is_unknown(*type_id)
                && !self.arena().is_unknown(narrowed_type_id)
            {
                // TaggedValue layout: [tag:8][value:8]
                // Extract the value from offset 8 and convert to proper type
                let raw_value = self.builder.ins().load(types::I64, MemFlags::new(), val, 8);
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
                && self.union_rc_variant_tags(*type_id).is_some()
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
            let value = self.builder.ins().iconst(types::I8, 0);
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
                    let val = self.builder.ins().iconst(types::I64, v);
                    Ok(CompiledValue::new(val, types::I64, i64_id))
                }
                vole_sema::types::ConstantValue::Bool(v) => {
                    let val = self.builder.ins().iconst(types::I8, if v { 1 } else { 0 });
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
            let value = self.builder.ins().iconst(types::I8, 0);
            Ok(CompiledValue::new(value, types::I8, export_type_id))
        } else {
            Err(CodegenError::not_found(
                "module export constant",
                format!("{}.{}", module_path, export_name_str),
            ))
        }
    }

    /// Compile a reference to a named function, wrapping it in a closure struct.
    /// Creates a wrapper function that adapts the function to the closure calling convention.
    fn function_reference(
        &mut self,
        sym: Symbol,
        func_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        use cranelift::prelude::FunctionBuilderContext;

        // Look up the original function's FuncId using the name table
        let query = self.query();
        let module_id = self
            .current_module_id()
            .unwrap_or(self.env.analyzed.module_id);
        let name_id = query.function_name_id(module_id, sym);

        let orig_func_key = self.funcs().intern_name_id(name_id);
        let orig_func_id = self.funcs().func_id(orig_func_key).ok_or_else(|| {
            CodegenError::not_found("function id for", self.interner().resolve(sym)).to_string()
        })?;

        // Unwrap function type to get params and return type
        let (param_ids, return_type_id) = {
            let arena = self.arena();
            let (params, ret, _is_closure) = arena
                .unwrap_function(func_type_id)
                .ok_or_else(|| "Expected function type".to_string())?;
            (params.clone(), ret)
        };

        // Create a wrapper function that adapts the original function to closure calling convention.
        // The wrapper takes (closure_ptr, params...) and calls the original function with just (params...).
        let wrapper_index = self.next_lambda_id();

        // Build wrapper signature: (closure_ptr, params...) -> return_type
        let param_types = self.cranelift_types(&param_ids);
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
            .map_err(|e| CodegenError::internal_with_context("cranelift error", e.to_string()))?;

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
            .map_err(|e| format!("Failed to define function wrapper: {:?}", e))?;

        // Get the wrapper function address
        let wrapper_func_ref = self
            .codegen_ctx
            .jit_module()
            .declare_func_in_func(wrapper_func_id, self.builder.func);
        let ptr_type = self.ptr_type();
        let wrapper_func_addr = self.builder.ins().func_addr(ptr_type, wrapper_func_ref);

        // Wrap in a closure struct with zero captures
        let alloc_ref = self.runtime_func_ref(RuntimeFn::ClosureAlloc)?;
        let zero_captures = self.builder.ins().iconst(types::I64, 0);
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

    /// Compile a unary expression
    fn unary(&mut self, un: &vole_frontend::UnaryExpr) -> CodegenResult<CompiledValue> {
        let operand = self.expr(&un.operand)?;
        let result = match un.op {
            UnaryOp::Neg => {
                if operand.ty.is_float() {
                    self.builder.ins().fneg(operand.value)
                } else {
                    self.builder.ins().ineg(operand.value)
                }
            }
            UnaryOp::Not => {
                // Boolean not: 1 - value.  Operand may be wider than i8 when
                // a boolean flows through block parameters (e.g. deeply nested
                // when/match expressions), so narrow to i8 first.
                let op_val = if operand.ty != types::I8 {
                    self.builder.ins().ireduce(types::I8, operand.value)
                } else {
                    operand.value
                };
                let one = self.builder.ins().iconst(types::I8, 1);
                self.builder.ins().isub(one, op_val)
            }
            UnaryOp::BitNot => self.builder.ins().bnot(operand.value),
        };
        Ok(operand.with_value(result))
    }

    /// Compile an assignment expression
    fn assign(&mut self, assign: &vole_frontend::AssignExpr) -> CodegenResult<CompiledValue> {
        match &assign.target {
            AssignTarget::Discard => {
                // Discard pattern: _ = expr
                // Compile the expression for side effects, discard result
                let mut value = self.expr(&assign.value)?;
                // Consume RC value since the result is discarded
                self.consume_rc_value(&mut value)?;
                // Return a void value
                Ok(CompiledValue::new(
                    self.builder.ins().iconst(types::I64, 0),
                    types::I64,
                    TypeId::VOID,
                ))
            }
            AssignTarget::Variable(sym) => {
                // Read the old value BEFORE evaluating the new expression,
                // so we can rc_dec it after the assignment.
                let rc_old = if self.rc_scopes.has_active_scope() {
                    if let Some(&(var, type_id)) = self.vars.get(sym) {
                        if self.rc_state(type_id).needs_cleanup() {
                            Some(self.builder.use_var(var))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                };

                // For composite types (structs with RC fields), snapshot the old
                // struct pointer so we can rc_dec its RC fields after overwrite.
                let composite_rc_old = if self.rc_scopes.has_active_scope() {
                    if let Some(&(var, type_id)) = self.vars.get(sym) {
                        if let Some(offsets) = self.deep_rc_field_offsets(type_id) {
                            Some((self.builder.use_var(var), offsets))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                };

                // For union types with RC variants, snapshot the old union pointer
                // so we can rc_dec its payload after overwrite.
                let union_rc_old = if self.rc_scopes.has_active_scope() {
                    if let Some(&(var, type_id)) = self.vars.get(sym) {
                        if let Some(rc_tags) = self.union_rc_variant_tags(type_id) {
                            Some((self.builder.use_var(var), rc_tags))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                };

                let mut value = self.expr(&assign.value)?;

                // Check for captured variable assignment
                if let Some(binding) = self.get_capture(sym).copied() {
                    return self.store_capture(&binding, value);
                }

                let (var, var_type_id) = self.vars.get(sym).ok_or_else(|| {
                    format!("undefined variable: {}", self.interner().resolve(*sym))
                })?;
                let var = *var;
                let var_type_id = *var_type_id;

                value = self.coerce_to_type(value, var_type_id)?;

                // RC bookkeeping for reassignment:
                // 1. rc_inc new value if it's a borrow (variable copy)
                // 2. Store the new value
                // 3. rc_dec old value (after store, in case old == new)
                if rc_old.is_some() && value.is_borrowed() {
                    self.emit_rc_inc_for_type(value.value, var_type_id)?;
                }
                self.builder.def_var(var, value.value);
                if let Some(old_val) = rc_old {
                    self.emit_rc_dec_for_type(old_val, var_type_id)?;
                }

                // Composite RC reassignment: rc_dec each RC field of the OLD struct.
                // The new struct's fields are already alive (fresh from the literal).
                if let Some((old_ptr, offsets)) = composite_rc_old {
                    for off in &offsets {
                        let field_ptr =
                            self.builder
                                .ins()
                                .load(types::I64, MemFlags::new(), old_ptr, *off);
                        self.emit_rc_dec(field_ptr)?;
                    }
                    // Update the composite RC local's offsets so scope-exit cleanup
                    // covers nested RC fields in the new value too.
                    self.rc_scopes.update_composite_offsets(var, offsets);
                }

                // Union RC reassignment: rc_dec the RC payload of the OLD union value.
                // The new value's payload is already alive (fresh from the expression).
                if let Some((old_ptr, rc_tags)) = union_rc_old {
                    self.emit_union_rc_dec(old_ptr, &rc_tags)?;
                }

                // The assignment consumed the temp — ownership transfers
                // to the variable binding; scope cleanup handles the dec.
                value.mark_consumed();
                value.debug_assert_rc_handled("assign to variable");
                Ok(value)
            }
            AssignTarget::Field { object, field, .. } => {
                self.field_assign(object, *field, &assign.value)
            }
            AssignTarget::Index { object, index } => {
                self.index_assign(object, index, &assign.value)
            }
        }
    }

    /// Compile an unreachable expression (never type / bottom type)
    /// This emits a panic with file:line info if reached at runtime.
    fn unreachable_expr(&mut self, line: u32) -> CodegenResult<CompiledValue> {
        // Emit panic with location - this code should never be reached at runtime
        self.emit_panic_static("unreachable code reached", line)?;

        // Return a dummy value with the never type
        // The actual value doesn't matter since control never reaches here
        Ok(CompiledValue::new(
            self.builder.ins().iconst(types::I64, 0),
            types::I64,
            TypeId::NEVER,
        ))
    }

    /// Compile an array or tuple literal
    fn array_literal(&mut self, elements: &[Expr], expr: &Expr) -> CodegenResult<CompiledValue> {
        // Check the inferred type from semantic analysis (module-aware)
        let inferred_type_id = self.get_expr_type(&expr.id);

        // If it's a tuple, use stack allocation
        if let Some(type_id) = inferred_type_id {
            let elem_type_ids = self.arena().unwrap_tuple(type_id).cloned();
            if let Some(elem_type_ids) = elem_type_ids {
                return self.tuple_literal(elements, &elem_type_ids, type_id);
            }
        }

        // Otherwise, create a dynamic array
        let arr_ptr = self.call_runtime(RuntimeFn::ArrayNew, &[])?;
        let array_push_ref = self.runtime_func_ref(RuntimeFn::ArrayPush)?;

        for elem in elements {
            let compiled = self.expr(elem)?;

            // Structs are stack-allocated; copy to heap so the data survives
            // if the array escapes the current stack frame (e.g. returned from a function).
            let mut compiled = if self.arena().is_struct(compiled.type_id) {
                self.copy_struct_to_heap(compiled)?
            } else {
                compiled
            };

            // RC: inc borrowed RC elements so the array gets its own reference.
            self.rc_inc_borrowed_for_container(&compiled)?;

            // i128 cannot fit in a TaggedValue (u64 payload) - reject at compile time
            if compiled.ty == types::I128 {
                return Err(CodegenError::type_mismatch(
                    "array element",
                    "a type that fits in 64 bits",
                    "i128 (128-bit values cannot be stored in arrays)",
                ));
            }

            // Compute tag before using builder to avoid borrow conflict
            let tag = {
                let arena = self.arena();
                array_element_tag_id(compiled.type_id, arena)
            };
            let tag_val = self.builder.ins().iconst(types::I64, tag);
            let value_bits = convert_to_i64_for_storage(self.builder, &compiled);

            let push_args = self.coerce_call_args(array_push_ref, &[arr_ptr, tag_val, value_bits]);
            self.builder.ins().call(array_push_ref, &push_args);

            // The element value is consumed into the array container.
            compiled.mark_consumed();
        }

        // Use type from ExpressionData - sema always records array/tuple types
        let array_type_id = inferred_type_id.unwrap_or_else(|| {
            unreachable!(
                "array literal at line {} has no type from sema",
                expr.span.line
            )
        });
        Ok(CompiledValue::new(arr_ptr, self.ptr_type(), array_type_id))
    }

    /// Compile a tuple literal to stack-allocated memory
    fn tuple_literal(
        &mut self,
        elements: &[Expr],
        elem_type_ids: &[TypeId],
        tuple_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Calculate layout using TypeId-based function
        let (total_size, offsets) = tuple_layout_id(
            elem_type_ids,
            self.ptr_type(),
            self.registry(),
            self.arena(),
        );

        // Create stack slot for the tuple
        let slot = self.alloc_stack(total_size);

        // Compile and store each element
        for (i, elem) in elements.iter().enumerate() {
            let mut compiled = self.expr(elem)?;
            let offset = offsets[i];

            // RC: inc borrowed RC elements so the tuple gets its own reference.
            self.rc_inc_borrowed_for_container(&compiled)?;

            // Store the value at its offset in the tuple
            self.builder.ins().stack_store(compiled.value, slot, offset);
            // The element value is consumed into the tuple container.
            compiled.mark_consumed();
            compiled.debug_assert_rc_handled("tuple element");
        }

        // Return pointer to the tuple
        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

        // Use TypeId from ExpressionData (passed from caller)
        Ok(CompiledValue::new(ptr, ptr_type, tuple_type_id))
    }

    /// Compile a repeat literal [expr; N] to a fixed-size array
    fn repeat_literal(
        &mut self,
        element: &Expr,
        count: usize,
        expr: &Expr,
    ) -> CodegenResult<CompiledValue> {
        // Compile the element once
        let mut elem_value = self.expr(element)?;

        // Each element is aligned to 8 bytes
        let elem_size = 8u32;
        let total_size = elem_size * (count as u32);

        // Create stack slot for the fixed array
        let slot = self.alloc_stack(total_size);

        // Store the element value at each position.
        // For RC elements, each copy needs rc_inc since multiple slots share the
        // same pointer. When the element is borrowed (e.g. a variable reference),
        // ALL copies including the first need rc_inc because the source variable's
        // own cleanup will rc_dec independently of the array's composite cleanup.
        // When the element is owned (e.g. a fresh call result), the first copy
        // takes ownership (no inc) and subsequent copies need inc.
        let needs_rc =
            self.rc_scopes.has_active_scope() && self.rc_state(elem_value.type_id).needs_cleanup();
        let is_borrowed = elem_value.is_borrowed();
        for i in 0..count {
            if needs_rc && (i > 0 || is_borrowed) {
                self.emit_rc_inc_for_type(elem_value.value, elem_value.type_id)?;
            }
            let offset = (i as i32) * (elem_size as i32);
            self.builder
                .ins()
                .stack_store(elem_value.value, slot, offset);
        }
        // The element value is consumed into the repeat array container.
        elem_value.mark_consumed();
        elem_value.debug_assert_rc_handled("repeat array element");

        // Return pointer to the array
        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

        // Get the full type from sema - sema always records repeat literal types
        let type_id = self.get_expr_type(&expr.id).unwrap_or_else(|| {
            unreachable!(
                "repeat literal at line {} has no type from sema",
                expr.span.line
            )
        });

        Ok(CompiledValue::new(ptr, ptr_type, type_id))
    }

    /// Compile a range expression (start..end or start..=end)
    /// Returns a pointer to a stack slot containing (start: i64, end: i64)
    /// For inclusive ranges, we store end + 1 so the iterator uses exclusive end
    fn range(&mut self, range: &RangeExpr) -> CodegenResult<CompiledValue> {
        let start = self.expr(&range.start)?;
        let end_val = self.expr(&range.end)?;

        // For inclusive ranges (start..=end), add 1 to end so we can use exclusive end internally
        let end = if range.inclusive {
            self.builder.ins().iadd_imm(end_val.value, 1)
        } else {
            end_val.value
        };

        // Create a stack slot to hold (start, end) - 16 bytes
        let slot = self.alloc_stack(16);

        // Store start at offset 0
        self.builder.ins().stack_store(start.value, slot, 0);
        // Store end at offset 8
        self.builder.ins().stack_store(end, slot, 8);

        // Return pointer to the slot
        let ptr_type = self.ptr_type();
        let range_type_id = self.arena().range();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

        Ok(CompiledValue::new(ptr, ptr_type, range_type_id))
    }

    /// Compile an index expression
    fn index(&mut self, object: &Expr, index: &Expr) -> CodegenResult<CompiledValue> {
        let obj = self.expr(object)?;

        let arena = self.arena();

        // Try tuple first
        if let Some(elem_type_ids) = arena.unwrap_tuple(obj.type_id).cloned() {
            // Tuple indexing - must be constant index (checked in sema)
            if let ExprKind::IntLiteral(i, _) = &index.kind {
                let i = *i as usize;
                let (_, offsets) = tuple_layout_id(
                    &elem_type_ids,
                    self.ptr_type(),
                    self.registry(),
                    self.arena(),
                );
                let offset = offsets[i];
                let elem_type_id = elem_type_ids[i];
                let elem_cr_type =
                    type_id_to_cranelift(elem_type_id, self.arena(), self.ptr_type());

                let value =
                    self.builder
                        .ins()
                        .load(elem_cr_type, MemFlags::new(), obj.value, offset);

                let mut cv = CompiledValue::new(value, elem_cr_type, elem_type_id);
                self.mark_borrowed_if_rc(&mut cv);
                return Ok(cv);
            } else {
                return Err(CodegenError::unsupported("non-constant tuple index"));
            }
        }

        // Try fixed array
        if let Some((element_id, size)) = arena.unwrap_fixed_array(obj.type_id) {
            // Fixed array indexing
            let elem_size = 8i32; // All elements aligned to 8 bytes
            let elem_cr_type = type_id_to_cranelift(element_id, self.arena(), self.ptr_type());

            // Calculate offset: base + (index * elem_size)
            let offset = if let ExprKind::IntLiteral(i, _) = &index.kind {
                // Constant index - bounds check at compile time already done in sema
                let i = *i as usize;
                if i >= size {
                    return Err(CodegenError::internal_with_context(
                        "array index out of bounds",
                        format!("index {} for array of size {}", i, size),
                    ));
                }
                self.builder.ins().iconst(types::I64, (i as i64) * 8)
            } else {
                // Runtime index - add bounds check
                let idx = self.expr(index)?;
                let size_val = self.builder.ins().iconst(types::I64, size as i64);

                // Check if index < 0 or index >= size
                // We treat index as unsigned, so negative becomes very large
                let in_bounds =
                    self.builder
                        .ins()
                        .icmp(IntCC::UnsignedLessThan, idx.value, size_val);

                // Trap if out of bounds
                self.builder
                    .ins()
                    .trapz(in_bounds, TrapCode::unwrap_user(2));

                let elem_size_val = self.builder.ins().iconst(types::I64, elem_size as i64);
                self.builder.ins().imul(idx.value, elem_size_val)
            };

            let elem_ptr = self.builder.ins().iadd(obj.value, offset);
            let value = self
                .builder
                .ins()
                .load(elem_cr_type, MemFlags::new(), elem_ptr, 0);

            let mut cv = CompiledValue::new(value, elem_cr_type, element_id);
            self.mark_borrowed_if_rc(&mut cv);
            return Ok(cv);
        }

        // Try dynamic array
        if let Some(element_id) = arena.unwrap_array(obj.type_id) {
            // Dynamic array indexing with CSE caching
            let idx = self.expr(index)?;

            let raw_value =
                self.call_runtime_cached(RuntimeFn::ArrayGetValue, &[obj.value, idx.value])?;
            // Union elements in dynamic arrays are stored as heap buffers
            // (16 bytes: [tag, is_rc, pad(6), payload]). Copy to a stack
            // slot to prevent use-after-free when the array is mutated.
            if self.arena().is_union(element_id) {
                let cv = self.copy_union_heap_to_stack(raw_value, element_id);
                return Ok(cv);
            }
            let mut cv = self.convert_field_value(raw_value, element_id);
            self.mark_borrowed_if_rc(&mut cv);
            return Ok(cv);
        }

        let type_name = self.arena().display_basic(obj.type_id);
        Err(CodegenError::type_mismatch(
            "index expression",
            "array or string",
            type_name,
        ))
    }

    /// Compile an index assignment
    fn index_assign(
        &mut self,
        object: &Expr,
        index: &Expr,
        value: &Expr,
    ) -> CodegenResult<CompiledValue> {
        let arr = self.expr(object)?;
        let val = self.expr(value)?;

        let arena = self.arena();
        let fixed_array_info = arena.unwrap_fixed_array(arr.type_id);
        let is_dynamic_array = arena.is_array(arr.type_id);

        if let Some((elem_type_id, size)) = fixed_array_info {
            // Fixed array assignment - store directly at offset
            let elem_size = 8i32; // All elements aligned to 8 bytes

            // Calculate offset
            let offset = if let ExprKind::IntLiteral(i, _) = &index.kind {
                let i = *i as usize;
                if i >= size {
                    return Err(CodegenError::internal_with_context(
                        "array index out of bounds",
                        format!("index {} for array of size {}", i, size),
                    ));
                }
                self.builder.ins().iconst(types::I64, (i as i64) * 8)
            } else {
                // Runtime index - add bounds check
                let idx = self.expr(index)?;
                let size_val = self.builder.ins().iconst(types::I64, size as i64);

                // Check if index < 0 or index >= size
                let in_bounds =
                    self.builder
                        .ins()
                        .icmp(IntCC::UnsignedLessThan, idx.value, size_val);

                // Trap if out of bounds
                self.builder
                    .ins()
                    .trapz(in_bounds, TrapCode::unwrap_user(2));

                let elem_size_val = self.builder.ins().iconst(types::I64, elem_size as i64);
                self.builder.ins().imul(idx.value, elem_size_val)
            };

            let elem_ptr = self.builder.ins().iadd(arr.value, offset);

            // RC bookkeeping for fixed array element overwrite:
            // 1. Load old element value
            // 2. rc_inc new if it's a borrow
            // 3. Store new value
            // 4. rc_dec old (after store, in case old == new)
            let rc_old = if self.rc_scopes.has_active_scope()
                && self.rc_state(elem_type_id).needs_cleanup()
            {
                Some(
                    self.builder
                        .ins()
                        .load(types::I64, MemFlags::new(), elem_ptr, 0),
                )
            } else {
                None
            };
            if rc_old.is_some() && val.is_borrowed() {
                self.emit_rc_inc_for_type(val.value, elem_type_id)?;
            }
            self.builder
                .ins()
                .store(MemFlags::new(), val.value, elem_ptr, 0);
            if let Some(old_val) = rc_old {
                self.emit_rc_dec_for_type(old_val, elem_type_id)?;
            }

            // The assignment consumed the temp — ownership transfers
            // to the array element; the container's cleanup handles the dec.
            let mut val = val;
            val.mark_consumed();
            val.debug_assert_rc_handled("fixed array index assign");
            Ok(val)
        } else if is_dynamic_array {
            // Dynamic array assignment
            let idx = self.expr(index)?;

            // If the array element type is a union, box the value into a union pointer.
            let elem_type = self.arena().unwrap_array(arr.type_id);
            let val = if let Some(elem_id) = elem_type {
                if self.arena().is_union(elem_id) && !self.arena().is_union(val.type_id) {
                    self.construct_union_heap_id(val, elem_id)?
                } else {
                    val
                }
            } else {
                val
            };

            // i128 cannot fit in a TaggedValue (u64 payload)
            if val.ty == types::I128 {
                return Err(CodegenError::type_mismatch(
                    "array element assignment",
                    "a type that fits in 64 bits",
                    "i128 (128-bit values cannot be stored in arrays)",
                ));
            }

            let set_value_ref = self.runtime_func_ref(RuntimeFn::ArraySet)?;
            // Compute tag before using builder to avoid borrow conflict
            let tag = {
                let arena = self.arena();
                array_element_tag_id(val.type_id, arena)
            };
            let tag_val = self.builder.ins().iconst(types::I64, tag);
            let value_bits = convert_to_i64_for_storage(self.builder, &val);

            let set_args =
                self.coerce_call_args(set_value_ref, &[arr.value, idx.value, tag_val, value_bits]);
            self.builder.ins().call(set_value_ref, &set_args);

            // The assignment consumed the temp — ownership transfers
            // to the dynamic array element.
            let mut val = val;
            val.mark_consumed();
            val.debug_assert_rc_handled("dynamic array index assign");
            Ok(val)
        } else {
            // Error: not an indexable type
            let type_name = self.arena().display_basic(arr.type_id);
            Err(CodegenError::type_mismatch(
                "index assignment",
                "array",
                type_name,
            ))
        }
    }

    /// Resolve a simple TypeExpr to a TypeId (for monomorphized generic fallback).
    /// Handles primitive types, named types (nil, Done, etc.), never, unknown - enough
    /// for `is` checks in generic function bodies that sema didn't analyze.
    fn resolve_simple_type_expr(&self, type_expr: &TypeExpr) -> Option<TypeId> {
        use vole_frontend::{PrimitiveType, TypeExpr as TE};
        let arena = self.arena();
        match type_expr {
            TE::Never => Some(TypeId::NEVER),
            TE::Unknown => Some(TypeId::UNKNOWN),
            TE::Primitive(p) => Some(match p {
                PrimitiveType::Bool => TypeId::BOOL,
                PrimitiveType::I8 => arena.i8(),
                PrimitiveType::I16 => arena.i16(),
                PrimitiveType::I32 => arena.i32(),
                PrimitiveType::I64 => arena.i64(),
                PrimitiveType::I128 => arena.i128(),
                PrimitiveType::U8 => arena.u8(),
                PrimitiveType::U16 => arena.u16(),
                PrimitiveType::U32 => arena.u32(),
                PrimitiveType::U64 => arena.u64(),
                PrimitiveType::F32 => arena.f32(),
                PrimitiveType::F64 => arena.f64(),
                PrimitiveType::String => arena.string(),
            }),
            TE::Named(sym) => {
                // Resolve named types (sentinels, structs, classes, etc.) through the
                // name resolution system. Uses current module context or main module.
                let name = self.interner().resolve(*sym);
                let module_id = self.current_module.unwrap_or(self.env.analyzed.module_id);
                let query = self.query();
                let type_def_id = query.resolve_type_def_by_str(module_id, name)?;
                self.registry().get_type(type_def_id).base_type_id
            }
            _ => None,
        }
    }

    /// Recover the concrete pattern type for a typed record arm.
    ///
    /// Prefer sema's `IsCheckResult` (which already includes generic inference),
    /// then fall back to simple type resolution for non-generic monomorph cases.
    fn pattern_type_id_for_record_arm(
        &self,
        scrutinee_type_id: TypeId,
        pattern_id: NodeId,
        type_expr: &TypeExpr,
    ) -> Option<TypeId> {
        let is_record_type = |ty: TypeId| {
            self.arena().unwrap_nominal(ty).is_some_and(|(_, _, kind)| {
                kind.is_class_or_struct()
                    || matches!(kind, vole_sema::type_arena::NominalKind::Error)
            })
        };

        if let Some(is_check_result) = self.get_is_check_result(pattern_id) {
            match is_check_result {
                IsCheckResult::CheckTag(tag) => {
                    let variants = self.arena().unwrap_union(scrutinee_type_id)?;
                    return variants
                        .get(tag as usize)
                        .copied()
                        .filter(|&ty| is_record_type(ty));
                }
                IsCheckResult::AlwaysTrue => {
                    if is_record_type(scrutinee_type_id) {
                        return Some(scrutinee_type_id);
                    }
                    return None;
                }
                IsCheckResult::AlwaysFalse => return None,
                IsCheckResult::CheckUnknown(_) => {}
            }
        }

        self.resolve_simple_type_expr(type_expr)
            .filter(|&ty| is_record_type(ty))
    }

    fn type_expr_terminal_symbol(type_expr: &TypeExpr) -> Option<Symbol> {
        match type_expr {
            TypeExpr::Named(sym) | TypeExpr::Generic { name: sym, .. } => Some(*sym),
            TypeExpr::QualifiedPath { segments, .. } => segments.last().copied(),
            _ => None,
        }
    }

    /// Compute IsCheckResult at codegen time for monomorphized generic functions.
    /// Sema skips generic function bodies, so `is` expressions inside them have no
    /// pre-computed result. This uses the substituted value type to compute it.
    fn compute_is_check_result(
        &self,
        value_type_id: TypeId,
        tested_type_id: TypeId,
    ) -> IsCheckResult {
        let arena = self.arena();
        if value_type_id.is_unknown() {
            IsCheckResult::CheckUnknown(tested_type_id)
        } else if let Some(variants) = arena.unwrap_union(value_type_id) {
            if let Some(index) = variants.iter().position(|&v| v == tested_type_id) {
                IsCheckResult::CheckTag(index as u32)
            } else {
                IsCheckResult::AlwaysFalse
            }
        } else if value_type_id == tested_type_id {
            IsCheckResult::AlwaysTrue
        } else {
            IsCheckResult::AlwaysFalse
        }
    }

    /// Try to statically determine the result of an `is` check without compiling the value.
    /// Returns Some(IsCheckResult) if the result is known, None if compilation is needed.
    /// Used to eliminate dead branches in monomorphized generics.
    pub(crate) fn try_static_is_check(
        &self,
        is_expr: &vole_frontend::IsExpr,
        expr_id: NodeId,
    ) -> Option<IsCheckResult> {
        // First check sema's pre-computed result
        if let Some(result) = self.get_is_check_result(expr_id) {
            return Some(result);
        }

        // For monomorphized generics: compute from the value's variable type
        let tested_type_id = self.resolve_simple_type_expr(&is_expr.type_expr)?;

        // Get the value's type from the variable scope (for identifiers)
        let value_type_id = match &is_expr.value.kind {
            ExprKind::Identifier(sym) => self.vars.get(sym).map(|(_, tid)| *tid)?,
            _ => return None,
        };

        Some(self.compute_is_check_result(value_type_id, tested_type_id))
    }

    /// Compile an `is` type check expression
    fn is_expr(
        &mut self,
        is_expr: &vole_frontend::IsExpr,
        expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let value = self.expr(&is_expr.value)?;

        // Look up pre-computed type check result from sema (module-aware).
        // Falls back to computing it at codegen time for monomorphized generic functions,
        // since sema skips generic function bodies.
        let is_check_result = match self.get_is_check_result(expr_id) {
            Some(result) => result,
            None => {
                // Monomorphized generic: compute from substituted types
                let tested_type_id = self
                    .resolve_simple_type_expr(&is_expr.type_expr)
                    .ok_or_else(|| {
                        "is expression in monomorphized generic: cannot resolve tested type"
                            .to_string()
                    })?;
                self.compute_is_check_result(value.type_id, tested_type_id)
            }
        };

        match is_check_result {
            IsCheckResult::AlwaysTrue => Ok(self.bool_const(true)),
            IsCheckResult::AlwaysFalse => Ok(self.bool_const(false)),
            IsCheckResult::CheckTag(tag_index) => {
                let result = self.tag_eq(value.value, tag_index as i64);
                Ok(self.bool_value(result))
            }
            IsCheckResult::CheckUnknown(tested_type_id) => {
                // Check if the unknown value's tag matches the tested type
                // TaggedValue layout: [tag: u64 at offset 0][value: u64 at offset 8]
                let tag = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), value.value, 0);
                let expected_tag = crate::types::unknown_type_tag(tested_type_id, self.arena());
                let expected_val = self.builder.ins().iconst(types::I64, expected_tag as i64);
                let result = self.builder.ins().icmp(IntCC::Equal, tag, expected_val);
                Ok(self.bool_value(result))
            }
        }
    }

    /// Compile a type pattern check for match expressions
    /// Returns Some(comparison_value) if a runtime check is needed, None if always matches
    fn compile_type_pattern_check(
        &mut self,
        scrutinee: &CompiledValue,
        pattern_id: NodeId,
    ) -> CodegenResult<Option<Value>> {
        // Look up pre-computed type check result from sema (module-aware)
        let is_check_result = self
            .get_is_check_result(pattern_id)
            .expect("INTERNAL: type pattern: missing IsCheckResult from sema");

        match is_check_result {
            IsCheckResult::AlwaysTrue => Ok(None), // Always matches
            IsCheckResult::AlwaysFalse => {
                // Never matches
                let never_match = self.builder.ins().iconst(types::I8, 0);
                Ok(Some(never_match))
            }
            IsCheckResult::CheckTag(tag_index) => {
                let result = self.tag_eq(scrutinee.value, tag_index as i64);
                Ok(Some(result))
            }
            IsCheckResult::CheckUnknown(tested_type_id) => {
                // Check if the unknown value's tag matches the tested type
                // TaggedValue layout: [tag: u64 at offset 0][value: u64 at offset 8]
                let tag = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), scrutinee.value, 0);
                let expected_tag = crate::types::unknown_type_tag(tested_type_id, self.arena());
                let expected_val = self.builder.ins().iconst(types::I64, expected_tag as i64);
                let result = self.builder.ins().icmp(IntCC::Equal, tag, expected_val);
                Ok(Some(result))
            }
        }
    }

    /// Compile an equality check for two values based on their Vole type.
    /// Handles string comparison via runtime function, floats via fcmp, and integers via icmp.
    fn compile_equality_check(
        &mut self,
        type_id: TypeId,
        left: Value,
        right: Value,
    ) -> CodegenResult<Value> {
        let arena = self.arena();
        Ok(if arena.is_string(type_id) {
            if self.funcs().has_runtime(RuntimeFn::StringEq) {
                self.call_runtime(RuntimeFn::StringEq, &[left, right])?
            } else {
                self.builder.ins().icmp(IntCC::Equal, left, right)
            }
        } else if arena.is_float(type_id) {
            self.builder.ins().fcmp(FloatCC::Equal, left, right)
        } else if type_id.is_integer() || type_id.is_bool() {
            self.builder.ins().icmp(IntCC::Equal, left, right)
        } else {
            panic!("compile_equality_check: unexpected type {type_id:?} for equality comparison")
        })
    }

    /// Compile a null coalesce expression (??)
    fn null_coalesce(
        &mut self,
        nc: &vole_frontend::NullCoalesceExpr,
    ) -> CodegenResult<CompiledValue> {
        // Check if the source is a variable (needs rc_inc because union cleanup
        // will also dec the payload) vs a temporary (ownership transfers directly).
        let source_is_variable =
            matches!(&nc.value.kind, ExprKind::Identifier(sym) if self.vars.contains_key(sym));

        let value = self.expr(&nc.value)?;
        let nil_tag = self.find_nil_variant(value.type_id).ok_or_else(|| {
            CodegenError::type_mismatch("null coalesce operator", "optional type", "non-optional")
        })?;

        let is_nil = self.tag_eq(value.value, nil_tag as i64);

        let nil_block = self.builder.create_block();
        let not_nil_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        let inner_type_id = self
            .arena()
            .unwrap_optional(value.type_id)
            .expect("INTERNAL: unwrap expr: expected optional type");
        let cranelift_type = type_id_to_cranelift(inner_type_id, self.arena(), self.ptr_type());
        self.builder.append_block_param(merge_block, cranelift_type);

        let result_needs_rc =
            self.rc_scopes.has_active_scope() && self.rc_state(inner_type_id).needs_cleanup();

        self.builder
            .ins()
            .brif(is_nil, nil_block, &[], not_nil_block, &[]);

        self.switch_and_seal(nil_block);
        let default_val = self.expr(&nc.default)?;
        // RC: inc borrowed default values so the result gets its own reference.
        if result_needs_rc && default_val.is_borrowed() {
            self.emit_rc_inc_for_type(default_val.value, inner_type_id)?;
        }
        let default_coerced = if default_val.ty != cranelift_type {
            if default_val.ty.is_int() && cranelift_type.is_int() {
                if cranelift_type.bytes() < default_val.ty.bytes() {
                    self.builder
                        .ins()
                        .ireduce(cranelift_type, default_val.value)
                } else {
                    self.builder
                        .ins()
                        .sextend(cranelift_type, default_val.value)
                }
            } else {
                default_val.value
            }
        } else {
            default_val.value
        };
        let default_arg = BlockArg::from(default_coerced);
        self.builder.ins().jump(merge_block, &[default_arg]);

        self.switch_and_seal(not_nil_block);
        // Only load payload if union has payload data.
        // Sentinel-only unions have union_size == 8 (tag only), no payload to read.
        let union_size = self.type_size(value.type_id);
        let payload = if union_size > 8 {
            let loaded = self
                .builder
                .ins()
                .load(cranelift_type, MemFlags::new(), value.value, 8);
            // RC: if the source is a variable, its union cleanup will dec the
            // payload at scope exit, so we need rc_inc to keep the extracted
            // value alive. If the source is a temporary (function call, etc.),
            // ownership transfers directly — no inc needed.
            if result_needs_rc && source_is_variable {
                self.emit_rc_inc_for_type(loaded, inner_type_id)?;
            }
            loaded
        } else {
            self.builder.ins().iconst(cranelift_type, 0)
        };
        let payload_arg = BlockArg::from(payload);
        self.builder.ins().jump(merge_block, &[payload_arg]);

        self.switch_and_seal(merge_block);

        let result = self.builder.block_params(merge_block)[0];
        let cv = CompiledValue::new(result, cranelift_type, inner_type_id);
        Ok(self.mark_rc_owned(cv))
    }

    /// Load a captured variable from closure
    pub(crate) fn load_capture(
        &mut self,
        binding: &super::lambda::CaptureBinding,
    ) -> CodegenResult<CompiledValue> {
        let closure_var = self
            .closure_var()
            .ok_or_else(|| "Closure variable not available for capture access".to_string())?;
        let closure_ptr = self.builder.use_var(closure_var);

        let index_val = self.builder.ins().iconst(types::I64, binding.index as i64);
        let heap_ptr =
            self.call_runtime(RuntimeFn::ClosureGetCapture, &[closure_ptr, index_val])?;

        let cranelift_ty = self.cranelift_type(binding.vole_type);
        let value = self
            .builder
            .ins()
            .load(cranelift_ty, MemFlags::new(), heap_ptr, 0);

        // Capture loads are borrows — the closure owns the reference via its
        // capture slot.  Marking as Borrowed ensures the return path inc's the
        // value when it leaves the closure body, giving the caller a +1 ref.
        let mut cv = CompiledValue::new(value, cranelift_ty, binding.vole_type);
        self.mark_borrowed_if_rc(&mut cv);
        Ok(cv)
    }

    /// Store a value to a captured variable in closure
    fn store_capture(
        &mut self,
        binding: &super::lambda::CaptureBinding,
        mut value: CompiledValue,
    ) -> CodegenResult<CompiledValue> {
        let closure_var = self
            .closure_var()
            .ok_or_else(|| "Closure variable not available for capture access".to_string())?;
        let closure_ptr = self.builder.use_var(closure_var);

        let index_val = self.builder.ins().iconst(types::I64, binding.index as i64);
        let heap_ptr =
            self.call_runtime(RuntimeFn::ClosureGetCapture, &[closure_ptr, index_val])?;

        let cranelift_ty = self.cranelift_type(binding.vole_type);
        self.builder
            .ins()
            .store(MemFlags::new(), value.value, heap_ptr, 0);

        // The value is consumed into the captured variable storage.
        value.mark_consumed();
        value.debug_assert_rc_handled("closure capture assign");
        Ok(CompiledValue::new(
            value.value,
            cranelift_ty,
            binding.vole_type,
        ))
    }

    /// Compile a match expression
    #[tracing::instrument(skip(self, match_expr), fields(arms = match_expr.arms.len()))]
    pub fn match_expr(
        &mut self,
        match_expr: &MatchExpr,
        expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let scrutinee = self.expr(&match_expr.scrutinee)?;
        let scrutinee_type_id = scrutinee.type_id;
        let scrutinee_type_str = self.arena().display_basic(scrutinee_type_id);
        tracing::trace!(scrutinee_type = %scrutinee_type_str, "match scrutinee");

        // Get the result type from semantic analysis (same as when_expr / if_expr)
        let mut result_type_id = self
            .get_expr_type_substituted(&expr_id)
            .unwrap_or(TypeId::VOID);
        // Match expressions that mix a non-union value with `nil` can be inferred
        // as the non-union value in some monomorphized contexts, which erases nil
        // arms to zero values. If this function returns a union type, use that
        // union return type for the match result.
        if !self.arena().is_union(result_type_id) {
            let has_nil_arm = match_expr.arms.iter().any(|arm| {
                self.get_expr_type_substituted(&arm.body.id)
                    .is_some_and(|ty| self.arena().is_nil(ty))
            });
            if has_nil_arm && let Some(ret_type_id) = self.return_type {
                let ret_type_id = self.try_substitute_type(ret_type_id);
                if self.arena().is_union(ret_type_id) {
                    result_type_id = ret_type_id;
                }
            }
        }
        let result_cranelift_type = self.cranelift_type(result_type_id);
        let is_void = self.arena().is_void(result_type_id);

        // Try Switch optimization for dense integer literal arms (O(1) dispatch)
        if let Some(analysis) = match_switch::analyze_switch(match_expr, scrutinee_type_id) {
            tracing::trace!(arms = analysis.arm_values.len(), "using switch dispatch");
            return self.emit_switch_match(
                match_expr,
                analysis,
                scrutinee,
                result_type_id,
                result_cranelift_type,
                is_void,
            );
        }

        let merge_block = self.builder.create_block();
        if !is_void {
            self.builder
                .append_block_param(merge_block, result_cranelift_type);
        }

        // Create a trap block for non-exhaustive match (should be unreachable)
        let trap_block = self.builder.create_block();

        let arm_blocks: Vec<Block> = match_expr
            .arms
            .iter()
            .map(|_| self.builder.create_block())
            .collect();

        if !arm_blocks.is_empty() {
            self.builder.ins().jump(arm_blocks[0], &[]);
        } else if !is_void {
            let default_val = self.typed_zero(result_cranelift_type);
            let default_arg = BlockArg::from(default_val);
            self.builder.ins().jump(merge_block, &[default_arg]);
        } else {
            self.builder.ins().jump(merge_block, &[]);
        }

        for (i, arm) in match_expr.arms.iter().enumerate() {
            let arm_block = arm_blocks[i];
            // For the last arm, if pattern fails, go to trap (should be unreachable)
            let next_block = arm_blocks.get(i + 1).copied().unwrap_or(trap_block);

            self.builder.switch_to_block(arm_block);
            self.invalidate_value_caches();

            let mut arm_variables = self.vars.clone();
            // Track the effective arm block (may change for conditional extraction)
            let mut effective_arm_block = arm_block;

            let pattern_matches = match &arm.pattern.kind {
                PatternKind::Wildcard => None,
                PatternKind::Identifier { name } => {
                    // Check if sema recognized this as a type pattern by looking for
                    // a pre-computed IsCheckResult. This handles all type patterns
                    // including sentinel types (Done, nil) from prelude modules.
                    if self.get_is_check_result(arm.pattern.id).is_some() {
                        // Type pattern - compare against union variant tag
                        self.compile_type_pattern_check(&scrutinee, arm.pattern.id)?
                    } else {
                        // Regular identifier binding
                        let var = self.builder.declare_var(scrutinee.ty);
                        self.builder.def_var(var, scrutinee.value);
                        arm_variables.insert(*name, (var, scrutinee_type_id));
                        None
                    }
                }
                PatternKind::Type { type_expr: _ } => {
                    self.compile_type_pattern_check(&scrutinee, arm.pattern.id)?
                }
                PatternKind::Literal(lit_expr) => {
                    // Save and restore vars for pattern matching
                    let saved_vars = std::mem::replace(&mut self.vars, arm_variables.clone());
                    let lit_val = self.expr(lit_expr)?;
                    arm_variables = std::mem::replace(&mut self.vars, saved_vars);

                    // Coerce literal value to match scrutinee's Cranelift type.
                    // This handles suffixed literals like `191_i64` matched against
                    // an i32 scrutinee (sema reports an error but codegen continues).
                    let coerced_lit =
                        self.convert_for_select(lit_val.value, lit_val.ty, scrutinee.ty);

                    // Use Vole type (not Cranelift type) to determine comparison method
                    let cmp = self.compile_equality_check(
                        scrutinee_type_id,
                        scrutinee.value,
                        coerced_lit,
                    )?;
                    Some(cmp)
                }
                PatternKind::Val { name } => {
                    // Val pattern - compare against existing variable's value.
                    // Check local variables first, then fall back to captures
                    // (for lambdas referencing outer scope variables).
                    let (var_val, var_type_id) =
                        if let Some(&(var, var_type_id)) = arm_variables.get(name) {
                            (self.builder.use_var(var), var_type_id)
                        } else if let Some(binding) = self.get_capture(name).copied() {
                            let captured = self.load_capture(&binding)?;
                            (captured.value, captured.type_id)
                        } else {
                            return Err("undefined variable in val pattern".to_string().into());
                        };

                    let cmp = self.compile_equality_check(var_type_id, scrutinee.value, var_val)?;
                    Some(cmp)
                }
                PatternKind::Success { inner } => {
                    // Check if tag == FALLIBLE_SUCCESS_TAG (0)
                    let tag = load_fallible_tag(self.builder, scrutinee.value);
                    let is_success =
                        self.builder
                            .ins()
                            .icmp_imm(IntCC::Equal, tag, FALLIBLE_SUCCESS_TAG);

                    // If there's an inner pattern, we need to extract payload and bind it
                    if let Some(inner_pat) = inner {
                        // Extract the success type from scrutinee's vole_type
                        // Get types before using builder to avoid borrow conflict
                        let fallible_types = self.arena().unwrap_fallible(scrutinee_type_id);
                        if let Some((success_type_id, _error_type_id)) = fallible_types {
                            let ptr_type = self.ptr_type();
                            let payload_ty = {
                                let arena = self.arena();
                                type_id_to_cranelift(success_type_id, arena, ptr_type)
                            };
                            let payload =
                                load_fallible_payload(self.builder, scrutinee.value, payload_ty);

                            // Handle inner pattern (usually an identifier binding)
                            if let PatternKind::Identifier { name } = &inner_pat.kind {
                                let var = self.builder.declare_var(payload_ty);
                                self.builder.def_var(var, payload);
                                arm_variables.insert(*name, (var, success_type_id));
                            }
                        }
                    }
                    Some(is_success)
                }
                PatternKind::Error { inner } => {
                    // Load the tag from fallible structure
                    let tag = load_fallible_tag(self.builder, scrutinee.value);
                    self.compile_error_pattern(inner, &scrutinee, tag, &mut arm_variables)?
                }
                PatternKind::Tuple { elements } => {
                    // Tuple destructuring in match - extract elements and bind
                    // Use arena methods for layout computation
                    // Extract all type info before using builder to avoid borrow conflicts
                    let elem_type_ids = self.arena().unwrap_tuple(scrutinee.type_id).cloned();
                    if let Some(elem_type_ids) = elem_type_ids {
                        let ptr_type = self.ptr_type();
                        let offsets = {
                            let arena = self.arena();
                            let (_, offsets) =
                                tuple_layout_id(&elem_type_ids, ptr_type, self.registry(), arena);
                            offsets
                        };
                        // Precompute cranelift types for each element
                        let elem_cr_types = self.cranelift_types(&elem_type_ids);
                        for (i, pat) in elements.iter().enumerate() {
                            if let PatternKind::Identifier { name } = &pat.kind {
                                let offset = offsets[i];
                                let elem_type_id = elem_type_ids[i];
                                let elem_cr_type = elem_cr_types[i];
                                let value = self.builder.ins().load(
                                    elem_cr_type,
                                    MemFlags::new(),
                                    scrutinee.value,
                                    offset,
                                );
                                let var = self.builder.declare_var(elem_cr_type);
                                self.builder.def_var(var, value);
                                arm_variables.insert(*name, (var, elem_type_id));
                            }
                            // Other pattern types in tuple (like wildcards) are ignored
                        }
                    }
                    None // Tuple patterns always match (type checked in sema)
                }
                PatternKind::Record { type_name, fields } => {
                    // Destructuring in match - TypeName { x, y } or { x, y }
                    let (pattern_check, pattern_type_id) = if let Some(type_expr) = type_name {
                        // Typed destructure pattern - need to check type first
                        let pattern_check =
                            self.compile_type_pattern_check(&scrutinee, arm.pattern.id)?;
                        let pattern_type_id = self.pattern_type_id_for_record_arm(
                            scrutinee_type_id,
                            arm.pattern.id,
                            type_expr,
                        );
                        (pattern_check, pattern_type_id)
                    } else {
                        // Untyped destructure pattern - always matches (type checked in sema)
                        (None, None)
                    };

                    // For typed patterns on union types, we must defer field extraction
                    // until after the pattern check passes to avoid accessing invalid memory
                    let is_conditional_extract =
                        pattern_check.is_some() && self.arena().is_union(scrutinee_type_id);

                    if is_conditional_extract {
                        // Create an extraction block that only runs if pattern matches
                        let extract_block = self.builder.create_block();

                        // Branch: if pattern matches -> extract_block, else -> next_block
                        let cond = pattern_check
                            .expect("INTERNAL: match pattern: missing pattern_check condition");
                        let cond_i32 = self.cond_to_i32(cond);
                        self.builder
                            .ins()
                            .brif(cond_i32, extract_block, &[], next_block, &[]);
                        self.builder.seal_block(arm_block);
                        // extract_block becomes the effective arm block for sealing later
                        effective_arm_block = extract_block;

                        // Extract block: extract fields from union payload
                        self.builder.switch_to_block(extract_block);

                        let (field_source, field_source_type_id) =
                            if let Some(pt_id) = pattern_type_id {
                                // Extract payload from union at offset 8
                                let payload = self.builder.ins().load(
                                    types::I64,
                                    MemFlags::new(),
                                    scrutinee.value,
                                    8,
                                );
                                (payload, pt_id)
                            } else {
                                (scrutinee.value, scrutinee_type_id)
                            };

                        // Extract and bind fields
                        self.extract_record_fields(
                            fields,
                            field_source,
                            field_source_type_id,
                            &mut arm_variables,
                        )?;

                        // extract_block continues to guard/body logic
                        // We stay in extract_block - it becomes the effective "arm block"
                        // Return None since the pattern check is already done via brif
                        None
                    } else {
                        // Non-conditional case: extract fields directly
                        // Determine the value to extract fields from
                        let (field_source, field_source_type_id) =
                            if self.arena().is_union(scrutinee_type_id) {
                                if let Some(pt_id) = pattern_type_id {
                                    let payload = self.builder.ins().load(
                                        types::I64,
                                        MemFlags::new(),
                                        scrutinee.value,
                                        8,
                                    );
                                    (payload, pt_id)
                                } else {
                                    (scrutinee.value, scrutinee_type_id)
                                }
                            } else {
                                (scrutinee.value, scrutinee_type_id)
                            };

                        // Extract and bind fields
                        self.extract_record_fields(
                            fields,
                            field_source,
                            field_source_type_id,
                            &mut arm_variables,
                        )?;

                        pattern_check
                    }
                }
            };

            // Save and restore vars for guard evaluation
            let guard_result = if let Some(guard) = &arm.guard {
                let saved_vars = std::mem::replace(&mut self.vars, arm_variables.clone());
                let guard_val = self.expr(guard)?;
                arm_variables = std::mem::replace(&mut self.vars, saved_vars);
                Some(guard_val.value)
            } else {
                None
            };

            let should_execute = match (pattern_matches, guard_result) {
                (None, None) => None,
                (Some(p), None) => Some(p),
                (None, Some(g)) => Some(g),
                (Some(p), Some(g)) => Some(self.builder.ins().band(p, g)),
            };

            let body_block = self.builder.create_block();

            if let Some(cond) = should_execute {
                let cond_i32 = self.cond_to_i32(cond);
                self.builder
                    .ins()
                    .brif(cond_i32, body_block, &[], next_block, &[]);
            } else {
                self.builder.ins().jump(body_block, &[]);
            }

            // Seal the effective arm block (may be extract_block for conditional patterns)
            self.builder.seal_block(effective_arm_block);

            self.builder.switch_to_block(body_block);

            // Compile body with the arm's variables
            let saved_vars = std::mem::replace(&mut self.vars, arm_variables);
            let mut body_val = self.expr(&arm.body)?;
            let _ = std::mem::replace(&mut self.vars, saved_vars);

            if body_val.type_id == TypeId::NEVER {
                // Divergent arm (unreachable/panic) — terminate with trap
                self.builder.ins().trap(TrapCode::unwrap_user(1));
            } else if !is_void {
                body_val = self.coerce_to_type(body_val, result_type_id)?;
                // If the arm body produces a borrowed RC value, emit rc_inc so
                // the match result owns its reference (mirroring if_expr_blocks).
                // Without this, borrowed payloads extracted from unions would be
                // freed by both the union cleanup and the result variable cleanup.
                let result_needs_rc = self.rc_state(result_type_id).needs_cleanup();
                if result_needs_rc && body_val.is_borrowed() {
                    self.emit_rc_inc_for_type(body_val.value, result_type_id)?;
                }

                let converted =
                    self.convert_for_select(body_val.value, body_val.ty, result_cranelift_type);
                self.builder.ins().jump(merge_block, &[converted.into()]);
            } else {
                self.builder.ins().jump(merge_block, &[]);
            }
            self.builder.seal_block(body_block);
        }

        // Fill in trap block (should be unreachable if match is exhaustive)
        self.switch_and_seal(trap_block);
        self.builder.ins().trap(TrapCode::unwrap_user(1));

        self.switch_and_seal(merge_block);
        self.invalidate_value_caches();

        // Clean up fallible scrutinee payload.
        // Fallible structs are stack-allocated (tag + payload) and never RC-tracked,
        // so the RC payload inside them leaks unless we explicitly rc_dec it here.
        // Each match arm already rc_inc'd any borrowed payload it returns, so this
        // rc_dec balances the original reference from the callee.
        self.cleanup_fallible_scrutinee(&scrutinee, scrutinee_type_id)?;

        if !is_void {
            let result = self.builder.block_params(merge_block)[0];
            let mut cv = CompiledValue::new(result, result_cranelift_type, result_type_id);
            if self.rc_state(result_type_id).needs_cleanup() {
                cv.rc_lifecycle = RcLifecycle::Owned;
            }
            Ok(cv)
        } else {
            Ok(self.void_value())
        }
    }

    /// Emit a match expression using Cranelift's Switch for O(1) dispatch.
    ///
    /// Creates a body block for each arm plus a default block, wires up the Switch,
    /// then compiles each arm body and merges results.
    fn emit_switch_match(
        &mut self,
        match_expr: &MatchExpr,
        analysis: match_switch::SwitchAnalysis,
        scrutinee: CompiledValue,
        result_type_id: TypeId,
        result_cranelift_type: Type,
        is_void: bool,
    ) -> CodegenResult<CompiledValue> {
        use cranelift::frontend::Switch;

        let merge_block = self.builder.create_block();
        if !is_void {
            self.builder
                .append_block_param(merge_block, result_cranelift_type);
        }

        // Create body blocks for each arm
        let body_blocks: Vec<Block> = match_expr
            .arms
            .iter()
            .map(|_| self.builder.create_block())
            .collect();

        // Default block: wildcard arm or trap
        let default_block = if let Some(wc_idx) = analysis.wildcard_idx {
            body_blocks[wc_idx]
        } else {
            self.builder.create_block()
        };

        // Build and emit the Switch
        let mut switch = Switch::new();
        for &(arm_idx, value) in &analysis.arm_values {
            // Use two's complement representation so negative i64 values
            // map to the upper half of u64 range (fits within i64 type bounds)
            let entry = value as u64 as u128;
            switch.set_entry(entry, body_blocks[arm_idx]);
        }
        switch.emit(self.builder, scrutinee.value, default_block);

        // If there's no wildcard, the default block is a trap
        if analysis.wildcard_idx.is_none() {
            self.switch_and_seal(default_block);
            self.builder.ins().trap(TrapCode::unwrap_user(1));
        }

        // Whether the result type needs RC cleanup
        let result_needs_rc = !is_void && self.rc_state(result_type_id).needs_cleanup();

        // Compile each arm body
        for (i, arm) in match_expr.arms.iter().enumerate() {
            self.builder.switch_to_block(body_blocks[i]);
            self.builder.seal_block(body_blocks[i]);
            self.invalidate_value_caches();

            let mut body_val = self.expr(&arm.body)?;

            if body_val.type_id == TypeId::NEVER {
                // Divergent arm (unreachable/panic) — terminate with trap
                self.builder.ins().trap(TrapCode::unwrap_user(1));
            } else if !is_void {
                body_val = self.coerce_to_type(body_val, result_type_id)?;
                if result_needs_rc && body_val.is_borrowed() {
                    self.emit_rc_inc_for_type(body_val.value, result_type_id)?;
                }
                let converted =
                    self.convert_for_select(body_val.value, body_val.ty, result_cranelift_type);
                self.builder.ins().jump(merge_block, &[converted.into()]);
            } else {
                self.builder.ins().jump(merge_block, &[]);
            }
        }

        self.switch_and_seal(merge_block);
        self.invalidate_value_caches();

        if !is_void {
            let result = self.builder.block_params(merge_block)[0];
            let mut cv = CompiledValue::new(result, result_cranelift_type, result_type_id);
            if result_needs_rc {
                cv.rc_lifecycle = RcLifecycle::Owned;
            }
            Ok(cv)
        } else {
            Ok(self.void_value())
        }
    }

    /// Emit rc_dec for the payload inside a fallible scrutinee after a match.
    ///
    /// Fallible returns are stack-allocated `(tag, payload)` structs that are
    /// never RC-tracked.  When a match arm extracts the payload and rc_inc's it
    /// (because the variable read is Borrowed), the original reference inside
    /// the fallible struct must be decremented to avoid a leak.
    ///
    /// If only one variant's payload is RC, we branch on the tag so we only
    /// rc_dec when that variant was active.
    fn cleanup_fallible_scrutinee(
        &mut self,
        scrutinee: &CompiledValue,
        scrutinee_type_id: TypeId,
    ) -> CodegenResult<()> {
        let fallible_types = self.arena().unwrap_fallible(scrutinee_type_id);
        let Some((success_type_id, error_type_id)) = fallible_types else {
            return Ok(());
        };

        let success_rc = self.rc_state(success_type_id).needs_cleanup();
        // Error types may have RC payloads even though the error struct itself
        // isn't RC-tracked.  Single-field error structs store their field value
        // directly as the payload (no wrapping pointer), so if that field is RC
        // we must rc_dec the payload.
        let error_rc = self.rc_state(error_type_id).needs_cleanup()
            || self.fallible_error_payload_needs_rc(error_type_id);

        if !success_rc && !error_rc {
            return Ok(());
        }

        let payload = load_fallible_payload(self.builder, scrutinee.value, types::I64);

        if success_rc && error_rc {
            // Both variants need cleanup — unconditional rc_dec
            self.emit_rc_dec(payload)?;
        } else {
            // Only one variant needs cleanup — branch on tag
            let tag = load_fallible_tag(self.builder, scrutinee.value);
            let is_success = self
                .builder
                .ins()
                .icmp_imm(IntCC::Equal, tag, FALLIBLE_SUCCESS_TAG);

            let dec_block = self.builder.create_block();
            let cont_block = self.builder.create_block();

            let cond = self.cond_to_i32(is_success);
            if success_rc {
                // rc_dec only on success path
                self.builder
                    .ins()
                    .brif(cond, dec_block, &[], cont_block, &[]);
            } else {
                // rc_dec only on error path
                self.builder
                    .ins()
                    .brif(cond, cont_block, &[], dec_block, &[]);
            }

            self.builder.switch_to_block(dec_block);
            self.builder.seal_block(dec_block);
            self.emit_rc_dec(payload)?;
            self.builder.ins().jump(cont_block, &[]);

            self.builder.switch_to_block(cont_block);
            self.builder.seal_block(cont_block);
        }

        Ok(())
    }

    /// Check whether the payload stored for an error variant is an RC value
    /// and is safe to unconditionally rc_dec.
    ///
    /// Single-field error structs (e.g. `NotFound { path: string }`) store the
    /// field value directly as the fallible payload.  If that single field is
    /// RC-managed the payload pointer must be rc_dec'd.
    ///
    /// For union error types, this returns true only when ALL variants are safe
    /// to rc_dec: either 0 fields (payload=null, rc_dec is no-op) or 1 RC field.
    /// Mixed unions (some RC, some non-RC single-field) are NOT safe and we skip
    /// cleanup to avoid calling rc_dec on non-pointer values.
    fn fallible_error_payload_needs_rc(&self, error_type_id: TypeId) -> bool {
        if self.error_type_single_field_is_rc(error_type_id) {
            return true;
        }
        let arena = self.arena();
        if let Some(variants) = arena.unwrap_union(error_type_id) {
            // All variants must be safe for unconditional rc_dec:
            // - 0 fields: payload is null (rc_dec is no-op)
            // - 1 RC field: payload is an RC pointer (rc_dec works)
            // If ANY variant has 1 non-RC field or 2+ fields, we can't safely rc_dec.
            let any_rc = variants
                .iter()
                .any(|&tid| self.error_type_single_field_is_rc(tid));
            let all_safe = any_rc
                && variants
                    .iter()
                    .all(|&tid| self.error_variant_safe_for_rc_dec(tid));
            return all_safe;
        }
        false
    }

    /// Check if an error variant is safe for unconditional rc_dec.
    /// True for: 0 fields (null payload) or 1 RC field.
    fn error_variant_safe_for_rc_dec(&self, type_id: TypeId) -> bool {
        let arena = self.arena();
        let type_def_id = arena
            .unwrap_error(type_id)
            .or_else(|| arena.unwrap_struct(type_id).map(|(id, _)| id));
        let Some(type_def_id) = type_def_id else {
            return false;
        };
        let fields: Vec<_> = self.query().fields_on_type(type_def_id).collect();
        match fields.len() {
            0 => true, // null payload, rc_dec is no-op
            1 => {
                let field = self.query().get_field(fields[0]);
                self.rc_state(field.ty).needs_cleanup()
            }
            _ => false, // 2+ fields = stack pointer, NOT safe for rc_dec
        }
    }

    /// Check if an error/struct type has exactly one field and that field is RC.
    fn error_type_single_field_is_rc(&self, type_id: TypeId) -> bool {
        let arena = self.arena();
        let type_def_id = arena
            .unwrap_error(type_id)
            .or_else(|| arena.unwrap_struct(type_id).map(|(id, _)| id));
        let Some(type_def_id) = type_def_id else {
            return false;
        };
        let fields: Vec<_> = self.query().fields_on_type(type_def_id).collect();
        if fields.len() != 1 {
            return false;
        }
        let field = self.query().get_field(fields[0]);
        self.rc_state(field.ty).needs_cleanup()
    }

    /// Compile a try expression (propagation)
    ///
    /// On success: returns unwrapped value
    /// On error: propagates by returning from function with (tag: i64, payload: i64)
    fn try_propagate(&mut self, inner: &Expr) -> CodegenResult<CompiledValue> {
        // Compile the inner fallible expression
        let fallible = self.expr(inner)?;

        let success_type_id = {
            let arena = self.arena();
            match arena.unwrap_fallible(fallible.type_id) {
                Some((success_id, _error_id)) => success_id,
                None => {
                    return Err(CodegenError::type_mismatch(
                        "try operator",
                        "fallible type",
                        "non-fallible",
                    ));
                }
            }
        };

        // Load the tag from the fallible (stored at offset 0 in stack slot)
        let tag = load_fallible_tag(self.builder, fallible.value);

        // Check if success (tag == 0)
        let is_success = self
            .builder
            .ins()
            .icmp_imm(IntCC::Equal, tag, FALLIBLE_SUCCESS_TAG);

        // Create blocks
        let success_block = self.builder.create_block();
        let error_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        // Get payload type for success using TypeId
        let payload_ty = self.cranelift_type(success_type_id);
        self.builder.append_block_param(merge_block, payload_ty);

        // Branch based on tag
        self.builder
            .ins()
            .brif(is_success, success_block, &[], error_block, &[]);

        // Error block: propagate by returning (tag, payload) for multi-value return
        // Payload is stored as i64 in the stack slot
        self.switch_and_seal(error_block);
        let error_payload_i64 = load_fallible_payload(self.builder, fallible.value, types::I64);
        self.builder.ins().return_(&[tag, error_payload_i64]);

        // Success block: extract payload and jump to merge
        // The payload is stored as i64 in the stack slot, convert to actual type
        self.switch_and_seal(success_block);
        let payload_i64 = load_fallible_payload(self.builder, fallible.value, types::I64);
        // Convert i64 back to the actual success type
        let payload = self.convert_from_i64_storage(payload_i64, success_type_id);
        let payload_arg = BlockArg::from(payload);
        self.builder.ins().jump(merge_block, &[payload_arg]);

        // Merge block: continue with extracted value
        self.switch_and_seal(merge_block);
        let result = self.builder.block_params(merge_block)[0];

        Ok(CompiledValue::new(result, payload_ty, success_type_id))
    }

    /// Compile a block expression: { stmts; trailing_expr }
    fn block_expr(&mut self, block: &BlockExpr) -> CodegenResult<CompiledValue> {
        self.push_rc_scope();

        // Compile statements
        for stmt in &block.stmts {
            self.stmt(stmt)?;
        }

        // Compile trailing expression if present, otherwise return void
        let result = if let Some(ref trailing) = block.trailing_expr {
            self.expr(trailing)?
        } else {
            self.void_value()
        };

        // If the trailing expression is a local variable being returned from this
        // scope, skip its cleanup — ownership transfers to the caller.
        let skip_var = if let Some(ref trailing) = block.trailing_expr
            && let ExprKind::Identifier(sym) = &trailing.kind
            && let Some((var, _)) = self.vars.get(sym)
        {
            Some(*var)
        } else {
            None
        };

        self.pop_rc_scope_with_cleanup(skip_var)?;
        Ok(result)
    }

    /// Compile an if expression: if cond { then } else { else }
    ///
    /// Optimization: Uses Cranelift's `select` instruction for simple conditionals
    /// where both branches are pure expressions (no side effects, no control flow).
    /// This avoids creating 4 separate blocks and enables better register allocation.
    fn if_expr(&mut self, if_expr: &IfExpr, expr_id: NodeId) -> CodegenResult<CompiledValue> {
        // Get the result type from semantic analysis (stored on the if expression itself)
        let result_type_id = self
            .get_expr_type_substituted(&expr_id)
            .unwrap_or(self.arena().primitives.void);

        // Check for statically known `is` condition (important for monomorphized generics
        // where sema didn't analyze the body and dead branches may contain invalid code).
        if let ExprKind::Is(is) = &if_expr.condition.kind
            && let Some(static_result) = self.try_static_is_check(is, if_expr.condition.id)
        {
            match static_result {
                IsCheckResult::AlwaysTrue => return self.expr(&if_expr.then_branch),
                IsCheckResult::AlwaysFalse => {
                    return if let Some(ref else_branch) = if_expr.else_branch {
                        self.expr(else_branch)
                    } else {
                        Ok(self.void_value())
                    };
                }
                _ => {} // Runtime check needed, fall through
            }
        }

        let is_void = self.arena().is_void(result_type_id);

        // Check if we can use select optimization:
        // - Must have an else branch
        // - Both branches must be selectable (pure expressions)
        // - Result must be non-void (select needs a value)
        // Don't use select for RC types — select evaluates both arms eagerly,
        // so the unused RC arm would leak. Block-based if only evaluates the
        // taken branch.
        let can_use_select = !is_void
            && !self.rc_state(result_type_id).needs_cleanup()
            && if_expr.else_branch.is_some()
            && if_expr.then_branch.is_selectable()
            && if_expr
                .else_branch
                .as_ref()
                .is_some_and(|e| e.is_selectable());

        if can_use_select {
            return self.if_expr_select(if_expr, result_type_id);
        }

        // Fall back to standard block-based compilation
        self.if_expr_blocks(if_expr, result_type_id, is_void)
    }

    /// Compile if expression using select instruction (optimized path).
    ///
    /// Generates code like:
    /// ```clif
    /// v0 = <condition>
    /// v1 = <then_value>
    /// v2 = <else_value>
    /// v3 = select v0, v1, v2
    /// ```
    fn if_expr_select(
        &mut self,
        if_expr: &IfExpr,
        result_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Compile condition
        let condition = self.expr(&if_expr.condition)?;

        // Compile both branches (they're pure, so order doesn't matter)
        let then_result = self.expr(&if_expr.then_branch)?;
        let else_result = self.expr(
            if_expr
                .else_branch
                .as_ref()
                .expect("INTERNAL: select-style if: missing else branch"),
        )?;

        let result_cranelift_type =
            type_id_to_cranelift(result_type_id, self.arena(), self.ptr_type());

        // Ensure both values have the same type (may need conversion)
        let then_val =
            self.convert_for_select(then_result.value, then_result.ty, result_cranelift_type);
        let else_val =
            self.convert_for_select(else_result.value, else_result.ty, result_cranelift_type);

        // Extend condition to i8 if needed (select expects i8/i16/i32/i64 condition)
        let cond_val = if condition.ty == types::I8 {
            condition.value
        } else {
            self.builder.ins().ireduce(types::I8, condition.value)
        };

        // Use select instruction: select(cond, if_true, if_false)
        let result = self.builder.ins().select(cond_val, then_val, else_val);

        Ok(CompiledValue::new(
            result,
            result_cranelift_type,
            result_type_id,
        ))
    }

    /// Convert a value for use in select (ensure matching types).
    fn convert_for_select(&mut self, value: Value, _from_ty: Type, to_ty: Type) -> Value {
        // Use the actual Cranelift value type rather than the reported type,
        // since CompiledValue.ty can be stale when values flow through deeply
        // nested when/match block parameters.
        let actual_ty = self.builder.func.dfg.value_type(value);
        if actual_ty == to_ty {
            return value;
        }
        // Handle integer width mismatches
        if actual_ty.is_int() && to_ty.is_int() {
            if to_ty.bits() < actual_ty.bits() {
                return self.builder.ins().ireduce(to_ty, value);
            } else if to_ty.bits() > actual_ty.bits() {
                return self.builder.ins().sextend(to_ty, value);
            }
        }
        // Handle float promotions/demotions
        if actual_ty == types::F32 && to_ty == types::F64 {
            return self.builder.ins().fpromote(types::F64, value);
        }
        if actual_ty == types::F64 && to_ty == types::F32 {
            return self.builder.ins().fdemote(types::F32, value);
        }
        // Handle int-to-float bitcast (e.g. iterator loop vars stored as i64
        // but semantically f64)
        if actual_ty.is_int() && to_ty.is_float() {
            if actual_ty.bits() == to_ty.bits() {
                return self.builder.ins().bitcast(to_ty, MemFlags::new(), value);
            } else if actual_ty.bits() > to_ty.bits() {
                let narrowed = self
                    .builder
                    .ins()
                    .ireduce(Type::int(to_ty.bits() as u16).unwrap(), value);
                return self.builder.ins().bitcast(to_ty, MemFlags::new(), narrowed);
            }
        }
        // For same-size types or unknown conversions, return as-is
        value
    }

    /// Compile if expression using blocks (standard path).
    fn if_expr_blocks(
        &mut self,
        if_expr: &IfExpr,
        result_type_id: TypeId,
        is_void: bool,
    ) -> CodegenResult<CompiledValue> {
        let condition = self.expr(&if_expr.condition)?;

        let result_cranelift_type =
            type_id_to_cranelift(result_type_id, self.arena(), self.ptr_type());

        // Create basic blocks
        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        // Add block parameter for the result
        if !is_void {
            self.builder
                .append_block_param(merge_block, result_cranelift_type);
        }

        // Branch based on condition
        self.builder
            .ins()
            .brif(condition.value, then_block, &[], else_block, &[]);

        let result_needs_rc = !is_void && self.rc_state(result_type_id).needs_cleanup();

        // Compile then branch
        self.switch_and_seal(then_block);
        self.invalidate_value_caches();
        let then_result = self.expr(&if_expr.then_branch)?;
        if then_result.type_id == TypeId::NEVER {
            // Divergent branch (unreachable/panic) — terminate with trap
            self.builder.ins().trap(TrapCode::unwrap_user(1));
        } else if !is_void {
            if result_needs_rc && then_result.is_borrowed() {
                self.emit_rc_inc_for_type(then_result.value, result_type_id)?;
            }
            let converted =
                self.convert_for_select(then_result.value, then_result.ty, result_cranelift_type);
            self.builder.ins().jump(merge_block, &[converted.into()]);
        } else {
            self.builder.ins().jump(merge_block, &[]);
        }

        // Compile else branch
        self.switch_and_seal(else_block);
        self.invalidate_value_caches();
        let else_result = if let Some(ref else_branch) = if_expr.else_branch {
            self.expr(else_branch)?
        } else {
            // No else branch - result is void/nil
            self.void_value()
        };
        if else_result.type_id == TypeId::NEVER {
            // Divergent branch (unreachable/panic) — terminate with trap
            self.builder.ins().trap(TrapCode::unwrap_user(1));
        } else if !is_void {
            if result_needs_rc && else_result.is_borrowed() {
                self.emit_rc_inc_for_type(else_result.value, result_type_id)?;
            }
            let converted =
                self.convert_for_select(else_result.value, else_result.ty, result_cranelift_type);
            self.builder.ins().jump(merge_block, &[converted.into()]);
        } else {
            self.builder.ins().jump(merge_block, &[]);
        }

        // Continue in merge block
        self.switch_and_seal(merge_block);
        self.invalidate_value_caches();

        if !is_void {
            let result = self.builder.block_params(merge_block)[0];
            let mut cv = CompiledValue::new(result, result_cranelift_type, result_type_id);
            if result_needs_rc {
                cv.rc_lifecycle = RcLifecycle::Owned;
            }
            Ok(cv)
        } else {
            Ok(self.void_value())
        }
    }

    /// Compile a when expression (subject-less conditional chain)
    ///
    /// Control flow for `when { cond1 => body1, cond2 => body2, _ => body3 }`:
    /// ```text
    /// entry:
    ///     eval cond1
    ///     brif -> body1, check2
    /// check2:
    ///     eval cond2
    ///     brif -> body2, body3
    /// body1: jump merge(result1)
    /// body2: jump merge(result2)
    /// body3: jump merge(result3)
    /// merge: return block_param
    /// ```
    ///
    /// Optimization: For binary when expressions (one condition + wildcard),
    /// uses Cranelift's `select` instruction if both bodies are selectable.
    fn when_expr(&mut self, when_expr: &WhenExpr, expr_id: NodeId) -> CodegenResult<CompiledValue> {
        // Get the result type from semantic analysis (stored on the when expression itself)
        let result_type_id = self
            .get_expr_type_substituted(&expr_id)
            .unwrap_or(self.arena().primitives.void);

        let is_void = self.arena().is_void(result_type_id);

        // Check if we can use select optimization for binary when:
        // - Exactly 2 arms
        // - First arm has a condition, second is wildcard
        // - Both bodies are selectable (pure expressions)
        // - Result is non-void
        // - Result is not RC-managed (select evaluates both arms, so an unused
        //   RC arm would leak; block-based when only evaluates the taken branch)
        let can_use_select = !is_void
            && !self.rc_state(result_type_id).needs_cleanup()
            && when_expr.arms.len() == 2
            && when_expr.arms[0].condition.is_some()
            && when_expr.arms[1].condition.is_none()
            && when_expr.arms[0].body.is_selectable()
            && when_expr.arms[1].body.is_selectable();

        if can_use_select {
            return self.when_expr_select(when_expr, result_type_id);
        }

        // Fall back to standard block-based compilation
        self.when_expr_blocks(when_expr, result_type_id, is_void)
    }

    /// Compile binary when expression using select instruction (optimized path).
    ///
    /// For `when { cond => then, _ => else }`, generates:
    /// ```clif
    /// v0 = <cond>
    /// v1 = <then_value>
    /// v2 = <else_value>
    /// v3 = select v0, v1, v2
    /// ```
    fn when_expr_select(
        &mut self,
        when_expr: &WhenExpr,
        result_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Compile condition (first arm)
        let condition = self.expr(
            when_expr.arms[0]
                .condition
                .as_ref()
                .expect("INTERNAL: when expr: first arm has no condition"),
        )?;

        // Compile both bodies (they're pure, so order doesn't matter)
        let then_result = self.expr(&when_expr.arms[0].body)?;
        let else_result = self.expr(&when_expr.arms[1].body)?;

        let result_cranelift_type =
            type_id_to_cranelift(result_type_id, self.arena(), self.ptr_type());

        // Ensure both values have the same type (may need conversion)
        let then_val =
            self.convert_for_select(then_result.value, then_result.ty, result_cranelift_type);
        let else_val =
            self.convert_for_select(else_result.value, else_result.ty, result_cranelift_type);

        // Extend condition to i8 if needed
        let cond_val = if condition.ty == types::I8 {
            condition.value
        } else {
            self.builder.ins().ireduce(types::I8, condition.value)
        };

        // Use select instruction
        let result = self.builder.ins().select(cond_val, then_val, else_val);

        Ok(CompiledValue::new(
            result,
            result_cranelift_type,
            result_type_id,
        ))
    }

    /// Compile when expression using blocks (standard path).
    fn when_expr_blocks(
        &mut self,
        when_expr: &WhenExpr,
        result_type_id: TypeId,
        is_void: bool,
    ) -> CodegenResult<CompiledValue> {
        let result_cranelift_type =
            type_id_to_cranelift(result_type_id, self.arena(), self.ptr_type());

        // Create merge block
        let merge_block = self.builder.create_block();
        if !is_void {
            self.builder
                .append_block_param(merge_block, result_cranelift_type);
        }

        // Find the wildcard arm index (there must be one - sema ensures this)
        let wildcard_idx = when_expr
            .arms
            .iter()
            .position(|arm| arm.condition.is_none())
            .unwrap_or(when_expr.arms.len() - 1);

        // Create body blocks for each arm
        let body_blocks: Vec<_> = when_expr
            .arms
            .iter()
            .map(|_| self.builder.create_block())
            .collect();

        // Create condition evaluation blocks for arms 1..n-1 (not first, not wildcard)
        // cond_blocks[i] is where we evaluate condition for arm i+1
        let cond_blocks: Vec<_> = (0..when_expr.arms.len().saturating_sub(1))
            .filter(|&i| i + 1 < when_expr.arms.len() && when_expr.arms[i + 1].condition.is_some())
            .map(|_| self.builder.create_block())
            .collect();

        let mut cond_block_idx = 0;

        // Process each conditional arm (skip wildcard - it's reached via brif "else" path)
        for (i, arm) in when_expr.arms.iter().enumerate() {
            if arm.condition.is_none() {
                // Wildcard arm - don't emit jump, brif already routes here
                // The wildcard body will be compiled in the body blocks loop
                break;
            }

            // Evaluate condition in current block
            let cond_result = self.expr(
                arm.condition
                    .as_ref()
                    .expect("INTERNAL: when expr: non-wildcard arm has no condition"),
            )?;

            // Determine "else" target (where to go if condition is false)
            let else_target = if i + 1 < when_expr.arms.len() {
                if when_expr.arms[i + 1].condition.is_none() {
                    // Next is wildcard - go directly to its body
                    body_blocks[i + 1]
                } else {
                    // Next has condition - go to condition evaluation block
                    cond_blocks[cond_block_idx]
                }
            } else {
                // Shouldn't happen (wildcard required), but go to wildcard
                body_blocks[wildcard_idx]
            };

            // Branch to body or next condition
            self.builder
                .ins()
                .brif(cond_result.value, body_blocks[i], &[], else_target, &[]);

            // If next arm has a condition, switch to its evaluation block
            if i + 1 < when_expr.arms.len() && when_expr.arms[i + 1].condition.is_some() {
                self.switch_and_seal(else_target);
                self.invalidate_value_caches();
                cond_block_idx += 1;
            }
        }

        // Whether the result type needs RC cleanup. When it does, each arm must
        // ensure the value flowing into the merge block is "owned" (has a +1 ref
        // that the consumer will balance). Borrowed arm results (variable reads)
        // get an rc_inc; Owned arm results (fresh allocations) already have +1.
        let result_needs_rc = !is_void && self.rc_state(result_type_id).needs_cleanup();

        // Compile body blocks
        for (i, arm) in when_expr.arms.iter().enumerate() {
            self.switch_and_seal(body_blocks[i]);
            self.invalidate_value_caches();

            let body_result = self.expr(&arm.body)?;

            // Divergent arms (unreachable, panic) already emitted a trap.
            // The current block is an unreachable continuation — terminate
            // it with a trap instead of a jump with a mistyped dummy value.
            if body_result.type_id == TypeId::NEVER {
                self.builder.ins().trap(TrapCode::unwrap_user(1));
                continue;
            }

            if !is_void {
                // For RC types, ensure each arm contributes an owned +1 ref.
                if result_needs_rc && body_result.is_borrowed() {
                    self.emit_rc_inc_for_type(body_result.value, result_type_id)?;
                }
                let converted = self.convert_for_select(
                    body_result.value,
                    body_result.ty,
                    result_cranelift_type,
                );
                self.builder.ins().jump(merge_block, &[converted.into()]);
            } else {
                self.builder.ins().jump(merge_block, &[]);
            }
        }

        // Continue in merge block
        self.switch_and_seal(merge_block);
        self.invalidate_value_caches();

        if !is_void {
            let result = self.builder.block_params(merge_block)[0];
            let mut cv = CompiledValue::new(result, result_cranelift_type, result_type_id);
            // For RC types, each arm ensured a +1 ref, so the merge result is
            // effectively Owned. Mark it so the consumer doesn't add another inc.
            if result_needs_rc {
                cv.rc_lifecycle = RcLifecycle::Owned;
            }
            Ok(cv)
        } else {
            Ok(self.void_value())
        }
    }

    // =========================================================================
    // Error pattern helpers (extracted from match_expr for readability)
    // =========================================================================

    /// Compile an error pattern match, returning the condition value.
    fn compile_error_pattern(
        &mut self,
        inner: &Option<Box<Pattern>>,
        scrutinee: &CompiledValue,
        tag: Value,
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
    ) -> CodegenResult<Option<Value>> {
        let Some(inner_pat) = inner else {
            // Bare error pattern: error => ...
            let is_error = self
                .builder
                .ins()
                .icmp_imm(IntCC::NotEqual, tag, FALLIBLE_SUCCESS_TAG);
            return Ok(Some(is_error));
        };

        match &inner_pat.kind {
            PatternKind::Identifier { name } => {
                self.compile_error_identifier_pattern(*name, scrutinee, tag, arm_variables)
            }
            PatternKind::Record {
                type_name: Some(type_expr),
                fields,
            } => {
                if let Some(name) = Self::type_expr_terminal_symbol(type_expr) {
                    self.compile_error_record_pattern(name, fields, scrutinee, tag, arm_variables)
                } else {
                    let is_error =
                        self.builder
                            .ins()
                            .icmp_imm(IntCC::NotEqual, tag, FALLIBLE_SUCCESS_TAG);
                    Ok(Some(is_error))
                }
            }
            _ => {
                // Catch-all for other patterns (like wildcard)
                let is_error =
                    self.builder
                        .ins()
                        .icmp_imm(IntCC::NotEqual, tag, FALLIBLE_SUCCESS_TAG);
                Ok(Some(is_error))
            }
        }
    }

    /// Compile an identifier pattern inside an error pattern.
    /// Handles both specific error types (error DivByZero) and catch-all bindings (error e).
    fn compile_error_identifier_pattern(
        &mut self,
        name: Symbol,
        scrutinee: &CompiledValue,
        tag: Value,
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
    ) -> CodegenResult<Option<Value>> {
        // Check if this is an error type name by looking in the fallible's error union.
        // This handles error types from imported modules that aren't in the consumer's scope.
        let is_error_type = self
            .resolve_type(name)
            .is_some_and(|type_id| self.query().get_type(type_id).kind == TypeDefKind::ErrorType)
            || {
                // Fallback: check if name matches an error type in the fallible's error union
                let arena = self.arena();
                arena
                    .unwrap_fallible(scrutinee.type_id)
                    .and_then(|(_, error_type_id)| {
                        fallible_error_tag_by_id(
                            error_type_id,
                            name,
                            arena,
                            self.interner(),
                            self.name_table(),
                            self.registry(),
                        )
                    })
                    .is_some()
            };

        if is_error_type {
            return self.compile_specific_error_type_pattern(name, scrutinee, tag);
        }

        // Catch-all error binding: error e => ...
        let is_error = self
            .builder
            .ins()
            .icmp_imm(IntCC::NotEqual, tag, FALLIBLE_SUCCESS_TAG);

        // Extract error type and bind
        // Get types before using builder to avoid borrow conflict
        let error_type_opt = self.arena().unwrap_fallible(scrutinee.type_id);
        if let Some((_, error_type_id)) = error_type_opt {
            let ptr_type = self.ptr_type();
            let payload_ty = {
                let arena = self.arena();
                type_id_to_cranelift(error_type_id, arena, ptr_type)
            };
            let payload = load_fallible_payload(self.builder, scrutinee.value, payload_ty);
            let var = self.builder.declare_var(payload_ty);
            self.builder.def_var(var, payload);
            arm_variables.insert(name, (var, error_type_id));
        }

        Ok(Some(is_error))
    }

    /// Compile a specific error type pattern (e.g., error DivByZero).
    fn compile_specific_error_type_pattern(
        &mut self,
        name: Symbol,
        scrutinee: &CompiledValue,
        tag: Value,
    ) -> CodegenResult<Option<Value>> {
        let arena = self.arena();
        let Some((_success_type_id, error_type_id)) = arena.unwrap_fallible(scrutinee.type_id)
        else {
            // Not matching on a fallible type
            return Ok(Some(self.builder.ins().iconst(types::I8, 0)));
        };

        let name_table = self.name_table();
        let Some(error_tag) = fallible_error_tag_by_id(
            error_type_id,
            name,
            arena,
            self.interner(),
            name_table,
            self.registry(),
        ) else {
            // Error type not found in fallible - will never match
            return Ok(Some(self.builder.ins().iconst(types::I8, 0)));
        };

        let is_this_error = self.builder.ins().icmp_imm(IntCC::Equal, tag, error_tag);
        Ok(Some(is_this_error))
    }

    /// Extract and bind fields from a destructure pattern source.
    ///
    /// For class/instance types, uses `InstanceGetField` runtime call.
    /// For struct types (auto-boxed in unions), uses `struct_field_load` since the
    /// source pointer is a raw heap pointer, not an `RcInstance`.
    fn extract_record_fields(
        &mut self,
        fields: &[RecordFieldPattern],
        field_source: Value,
        field_source_type_id: TypeId,
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
    ) -> CodegenResult<()> {
        let is_struct = self.arena().is_struct(field_source_type_id);
        for field_pattern in fields {
            let field_name = self.interner().resolve(field_pattern.field_name);
            let (slot, field_type_id) =
                get_field_slot_and_type_id_cg(field_source_type_id, field_name, self)?;

            let converted = if is_struct {
                // Struct was auto-boxed: field_source is a raw heap pointer
                // with fields at flat offsets, same layout as stack structs
                self.struct_field_load(field_source, slot, field_type_id, field_source_type_id)?
            } else if crate::types::is_wide_type(field_type_id, self.arena()) {
                // i128 fields use 2 consecutive slots
                let get_func_ref = self.runtime_func_ref(RuntimeFn::InstanceGetField)?;
                let value = crate::structs::helpers::load_wide_field(
                    self.builder,
                    get_func_ref,
                    field_source,
                    slot,
                );
                CompiledValue::new(value, types::I128, field_type_id)
            } else {
                // Class/instance: use runtime InstanceGetField
                let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
                let result_raw =
                    self.call_runtime(RuntimeFn::InstanceGetField, &[field_source, slot_val])?;
                self.convert_field_value(result_raw, field_type_id)
            };
            let var = self.builder.declare_var(converted.ty);
            self.builder.def_var(var, converted.value);
            arm_variables.insert(field_pattern.binding, (var, field_type_id));
        }
        Ok(())
    }

    /// Compile a destructure pattern inside an error pattern (e.g., error Overflow { value, max }).
    fn compile_error_record_pattern(
        &mut self,
        name: Symbol,
        fields: &[RecordFieldPattern],
        scrutinee: &CompiledValue,
        tag: Value,
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
    ) -> CodegenResult<Option<Value>> {
        // Look up error type_def_id via EntityRegistry, with fallback to
        // searching the fallible's error union for imported module error types
        let error_type_id = self
            .resolve_type(name)
            .and_then(|type_id| {
                let type_def = self.query().get_type(type_id);
                if type_def.kind == TypeDefKind::ErrorType && type_def.error_info.is_some() {
                    Some(type_id)
                } else {
                    None
                }
            })
            .or_else(|| {
                // Fallback: search error types in the fallible's error union by name
                let name_str = self.interner().resolve(name);
                let arena = self.arena();
                let (_, error_union_id) = arena.unwrap_fallible(scrutinee.type_id)?;
                self.find_error_type_in_union(error_union_id, name_str)
            });

        let Some(error_type_def_id) = error_type_id else {
            // Unknown error type
            return Ok(Some(self.builder.ins().iconst(types::I8, 0)));
        };

        let arena = self.arena();
        let Some((_success_type_id, fallible_error_type_id)) =
            arena.unwrap_fallible(scrutinee.type_id)
        else {
            return Ok(Some(self.builder.ins().iconst(types::I8, 0)));
        };

        let name_table = self.name_table();
        let Some(error_tag) = fallible_error_tag_by_id(
            fallible_error_type_id,
            name,
            arena,
            self.interner(),
            name_table,
            self.registry(),
        ) else {
            // Error type not found in fallible
            return Ok(Some(self.builder.ins().iconst(types::I8, 0)));
        };

        let is_this_error = self.builder.ins().icmp_imm(IntCC::Equal, tag, error_tag);

        // Get fields from EntityRegistry
        let error_fields: Vec<_> = self
            .query()
            .fields_on_type(error_type_def_id)
            .map(|field_id| self.query().get_field(field_id).clone())
            .collect();

        // Fallible layout (consistent with external functions in runtime):
        // - Offset 0: tag (i64)
        // - Offset 8: payload (i64)
        //   - For 0 fields: 0
        //   - For 1 non-wide field: the field value directly (inline)
        //   - For 1 wide (i128) field or 2+ fields: pointer to field data
        //
        // Load the payload from the fallible
        let payload = self.builder.ins().load(
            types::I64,
            MemFlags::new(),
            scrutinee.value,
            FALLIBLE_PAYLOAD_OFFSET,
        );

        // For single non-wide field errors, the payload IS the field value
        // For single wide (i128) field or multi-field errors, payload is a pointer to field data
        let has_any_wide = error_fields
            .iter()
            .any(|f| crate::types::is_wide_type(f.ty, self.arena()));
        let inline_single_field = error_fields.len() == 1 && !has_any_wide;

        // Precompute field byte offsets (i128 fields use 16 bytes, others 8)
        let field_byte_offsets: Vec<i32> = {
            let arena = self.arena();
            let mut offset = 0i32;
            error_fields
                .iter()
                .map(|f| {
                    let current = offset;
                    offset += if crate::types::is_wide_type(f.ty, arena) {
                        16
                    } else {
                        8
                    };
                    current
                })
                .collect()
        };

        for field_pattern in fields {
            let field_name = self.interner().resolve(field_pattern.field_name);

            // Find the field index and type in the error type
            let Some((field_idx, field_def)) = error_fields.iter().enumerate().find(|(_, f)| {
                self.name_table().last_segment_str(f.name_id).as_deref() == Some(field_name)
            }) else {
                continue;
            };

            let field_ty_id = field_def.ty;
            let is_wide = crate::types::is_wide_type(field_ty_id, self.arena());

            // Load the field value
            if inline_single_field {
                // For single non-wide field errors, the payload is the value directly
                let converted = self.convert_field_value(payload, field_ty_id);
                let var = self.builder.declare_var(converted.ty);
                self.builder.def_var(var, converted.value);
                arm_variables.insert(field_pattern.binding, (var, field_ty_id));
            } else if is_wide {
                // Wide (i128) field in multi-field or single-wide-field error
                let field_offset = field_byte_offsets[field_idx];
                let low =
                    self.builder
                        .ins()
                        .load(types::I64, MemFlags::new(), payload, field_offset);
                let high =
                    self.builder
                        .ins()
                        .load(types::I64, MemFlags::new(), payload, field_offset + 8);
                let i128_val = super::structs::reconstruct_i128(self.builder, low, high);
                let var = self.builder.declare_var(types::I128);
                self.builder.def_var(var, i128_val);
                arm_variables.insert(field_pattern.binding, (var, field_ty_id));
            } else {
                // Non-wide field in multi-field error, payload is a pointer to field data
                let field_offset = field_byte_offsets[field_idx];
                let raw_value =
                    self.builder
                        .ins()
                        .load(types::I64, MemFlags::new(), payload, field_offset);
                let converted = self.convert_field_value(raw_value, field_ty_id);
                let var = self.builder.declare_var(converted.ty);
                self.builder.def_var(var, converted.value);
                arm_variables.insert(field_pattern.binding, (var, field_ty_id));
            }
        }

        Ok(Some(is_this_error))
    }
}
