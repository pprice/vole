// src/codegen/expr.rs
//
// Expression compilation - impl Cg methods.

use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;
use cranelift_module::Module;

use crate::RuntimeFn;
use crate::errors::CodegenError;
use std::collections::HashMap;

use vole_frontend::{
    AssignTarget, BlockExpr, Expr, ExprKind, IfExpr, MatchExpr, Pattern, RangeExpr,
    RecordFieldPattern, Symbol, UnaryOp, WhenExpr,
};
use vole_sema::entity_defs::TypeDefKind;

use super::context::Cg;
use super::structs::{convert_to_i64_for_storage, get_field_slot_and_type_id_cg};
use super::types::{
    CompiledValue, FALLIBLE_PAYLOAD_OFFSET, FALLIBLE_SUCCESS_TAG, array_element_tag_id,
    fallible_error_tag_by_id, load_fallible_payload, load_fallible_tag, tuple_layout_id,
    type_id_to_cranelift,
};
use vole_sema::type_arena::TypeId;

impl Cg<'_, '_, '_> {
    /// Compile an expression.
    pub fn expr(&mut self, expr: &Expr) -> Result<CompiledValue, String> {
        // Check for captures first if in closure context
        if self.has_captures()
            && let ExprKind::Identifier(sym) = &expr.kind
            && let Some(binding) = self.get_capture(sym).copied()
        {
            return self.load_capture(&binding);
        }

        match &expr.kind {
            ExprKind::IntLiteral(n) => {
                // Look up inferred type from semantic analysis for bidirectional type inference
                // Uses get_expr_type helper to check module-specific expr_types when compiling prelude
                let type_id = self.get_expr_type(&expr.id).unwrap_or(TypeId::I64);
                Ok(self.int_const(*n, type_id))
            }
            ExprKind::FloatLiteral(n) => {
                // Look up inferred type from semantic analysis for bidirectional type inference
                let type_id = self.get_expr_type(&expr.id).unwrap_or(TypeId::F64);
                Ok(self.float_const(*n, type_id))
            }
            ExprKind::BoolLiteral(b) => Ok(self.bool_const(*b)),
            ExprKind::Identifier(sym) => self.identifier(*sym, expr),
            ExprKind::Binary(bin) => self.binary(bin),
            ExprKind::Unary(un) => self.unary(un),
            ExprKind::Assign(assign) => self.assign(assign),
            ExprKind::CompoundAssign(compound) => self.compound_assign(compound),
            ExprKind::Grouping(inner) => self.expr(inner),
            ExprKind::StringLiteral(s) => self.string_literal(s),
            ExprKind::Call(call) => self.call(call, expr.span.line, expr.id),
            ExprKind::InterpolatedString(parts) => self.interpolated_string(parts),
            ExprKind::Range(range) => self.range(range),
            ExprKind::ArrayLiteral(elements) => self.array_literal(elements, expr),
            ExprKind::RepeatLiteral { element, count } => {
                self.repeat_literal(element, *count, expr)
            }
            ExprKind::Index(idx) => self.index(&idx.object, &idx.index),
            ExprKind::Match(match_expr) => self.match_expr(match_expr),
            ExprKind::Nil => Ok(self.nil_value()),
            ExprKind::Done => Ok(self.done_value()),
            ExprKind::Is(is_expr) => self.is_expr(is_expr),
            ExprKind::NullCoalesce(nc) => self.null_coalesce(nc),
            ExprKind::Lambda(lambda) => self.lambda(lambda, expr.id),
            ExprKind::TypeLiteral(_) => {
                Err(CodegenError::unsupported("type expressions as runtime values").into())
            }
            ExprKind::StructLiteral(sl) => self.struct_literal(sl, expr),
            ExprKind::FieldAccess(fa) => self.field_access(fa),
            ExprKind::OptionalChain(oc) => self.optional_chain(oc, expr.id),
            ExprKind::MethodCall(mc) => self.method_call(mc, expr.id),
            ExprKind::Try(inner) => self.try_propagate(inner),
            ExprKind::Import(_) => {
                // Import expressions produce a compile-time module value
                // At runtime this is just a placeholder - actual function calls
                // go through the method resolution mechanism
                // We need to retrieve the actual Module type from semantic analysis
                let type_id = self
                    .get_expr_type(&expr.id)
                    .unwrap_or(self.arena().primitives.i64);
                Ok(CompiledValue {
                    value: self.builder.ins().iconst(types::I64, 0),
                    ty: types::I64,
                    type_id,
                })
            }
            ExprKind::Yield(_) => {
                // Yield should be caught in semantic analysis
                Err(CodegenError::unsupported("yield expression outside generator context").into())
            }
            ExprKind::Block(block_expr) => self.block_expr(block_expr),
            ExprKind::If(if_expr) => self.if_expr(if_expr),
            ExprKind::When(when_expr) => self.when_expr(when_expr),
        }
    }

    /// Compile an identifier lookup
    fn identifier(&mut self, sym: Symbol, expr: &Expr) -> Result<CompiledValue, String> {
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
                    type_id_to_cranelift(narrowed_type_id, &self.arena(), self.ptr_type());
                let payload = self.builder.ins().load(payload_ty, MemFlags::new(), val, 8);
                return Ok(CompiledValue {
                    value: payload,
                    ty: payload_ty,
                    type_id: narrowed_type_id,
                });
            }

            Ok(CompiledValue {
                value: val,
                ty,
                type_id: *type_id,
            })
        } else if let Some(global_init) = self.global_init(sym).cloned() {
            // Compile global's initializer inline
            let mut value = self.expr(&global_init)?;

            // If the global has a declared interface type, box the value
            // Use GlobalDef.type_id instead of re-resolving TypeExpr
            let name_table = self.name_table();
            let module_id = self
                .current_module()
                .unwrap_or_else(|| name_table.main_module());
            if let Some(name_id) = name_table.name_id(module_id, &[sym], self.interner()) {
                drop(name_table);
                if let Some(global_def) = self.query().global(name_id) {
                    value = self.coerce_to_type(value, global_def.type_id)?;
                }
            }
            Ok(value)
        } else if let Some(func_type_id) = self.get_expr_type(&expr.id)
            && self.arena().is_function(func_type_id)
        {
            // Identifier refers to a named function - create a closure wrapper
            self.function_reference(sym, func_type_id)
        } else {
            Err(CodegenError::not_found("variable", self.interner().resolve(sym)).into())
        }
    }

    /// Compile a reference to a named function, wrapping it in a closure struct.
    /// Creates a wrapper function that adapts the function to the closure calling convention.
    fn function_reference(
        &mut self,
        sym: Symbol,
        func_type_id: TypeId,
    ) -> Result<CompiledValue, String> {
        use cranelift::prelude::FunctionBuilderContext;

        // Look up the original function's FuncId using the name table
        let query = self.query();
        let name_id = query.function_name_id(query.main_module(), sym);

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
        let (wrapper_name_id, wrapper_func_key) = self.funcs().intern_lambda_name(wrapper_index);
        let wrapper_name = self
            .funcs()
            .name_table_rc()
            .borrow()
            .display(wrapper_name_id);
        let wrapper_func_id = self
            .jit_module()
            .declare_function(
                &wrapper_name,
                cranelift_module::Linkage::Local,
                &wrapper_sig,
            )
            .map_err(|e| e.to_string())?;

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

        // Create closure type directly using arena (is_closure: true)
        let closure_type_id = self.update().function(param_ids, return_type_id, true);
        Ok(CompiledValue {
            value: closure_ptr,
            ty: self.ptr_type(),
            type_id: closure_type_id,
        })
    }

    /// Compile a unary expression
    fn unary(&mut self, un: &vole_frontend::UnaryExpr) -> Result<CompiledValue, String> {
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
                let one = self.builder.ins().iconst(types::I8, 1);
                self.builder.ins().isub(one, operand.value)
            }
            UnaryOp::BitNot => self.builder.ins().bnot(operand.value),
        };
        Ok(operand.with_value(result))
    }

    /// Compile an assignment expression
    fn assign(&mut self, assign: &vole_frontend::AssignExpr) -> Result<CompiledValue, String> {
        match &assign.target {
            AssignTarget::Variable(sym) => {
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
                self.builder.def_var(var, value.value);
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

    /// Compile an array or tuple literal
    fn array_literal(&mut self, elements: &[Expr], expr: &Expr) -> Result<CompiledValue, String> {
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

        for elem in elements.iter() {
            let compiled = self.expr(elem)?;

            // Compute tag before using builder to avoid borrow conflict
            let tag = {
                let arena = self.arena();
                array_element_tag_id(compiled.type_id, &arena)
            };
            let tag_val = self.builder.ins().iconst(types::I64, tag);
            let value_bits = convert_to_i64_for_storage(self.builder, &compiled);

            self.builder
                .ins()
                .call(array_push_ref, &[arr_ptr, tag_val, value_bits]);
        }

        // Use type from ExpressionData - sema always records array/tuple types
        let array_type_id = inferred_type_id.unwrap_or_else(|| {
            unreachable!(
                "array literal at line {} has no type from sema",
                expr.span.line
            )
        });
        Ok(CompiledValue {
            value: arr_ptr,
            ty: self.ptr_type(),
            type_id: array_type_id,
        })
    }

    /// Compile a tuple literal to stack-allocated memory
    fn tuple_literal(
        &mut self,
        elements: &[Expr],
        elem_type_ids: &[TypeId],
        tuple_type_id: TypeId,
    ) -> Result<CompiledValue, String> {
        // Calculate layout using TypeId-based function
        let (total_size, offsets) = tuple_layout_id(
            elem_type_ids,
            self.ptr_type(),
            self.query().registry(),
            &self.arena(),
        );

        // Create stack slot for the tuple
        let slot = self.alloc_stack(total_size);

        // Compile and store each element
        for (i, elem) in elements.iter().enumerate() {
            let compiled = self.expr(elem)?;
            let offset = offsets[i];

            // Store the value at its offset in the tuple
            self.builder.ins().stack_store(compiled.value, slot, offset);
        }

        // Return pointer to the tuple
        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

        // Use TypeId from ExpressionData (passed from caller)
        Ok(CompiledValue {
            value: ptr,
            ty: ptr_type,
            type_id: tuple_type_id,
        })
    }

    /// Compile a repeat literal [expr; N] to a fixed-size array
    fn repeat_literal(
        &mut self,
        element: &Expr,
        count: usize,
        expr: &Expr,
    ) -> Result<CompiledValue, String> {
        // Compile the element once
        let elem_value = self.expr(element)?;

        // Each element is aligned to 8 bytes
        let elem_size = 8u32;
        let total_size = elem_size * (count as u32);

        // Create stack slot for the fixed array
        let slot = self.alloc_stack(total_size);

        // Store the element value at each position
        for i in 0..count {
            let offset = (i as i32) * (elem_size as i32);
            self.builder
                .ins()
                .stack_store(elem_value.value, slot, offset);
        }

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

        Ok(CompiledValue {
            value: ptr,
            ty: ptr_type,
            type_id,
        })
    }

    /// Compile a range expression (start..end or start..=end)
    /// Returns a pointer to a stack slot containing (start: i64, end: i64)
    /// For inclusive ranges, we store end + 1 so the iterator uses exclusive end
    fn range(&mut self, range: &RangeExpr) -> Result<CompiledValue, String> {
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

        Ok(CompiledValue {
            value: ptr,
            ty: ptr_type,
            type_id: range_type_id,
        })
    }

    /// Compile an index expression
    fn index(&mut self, object: &Expr, index: &Expr) -> Result<CompiledValue, String> {
        let obj = self.expr(object)?;

        let arena = self.arena();

        // Try tuple first
        if let Some(elem_type_ids) = arena.unwrap_tuple(obj.type_id).cloned() {
            drop(arena);
            // Tuple indexing - must be constant index (checked in sema)
            if let ExprKind::IntLiteral(i) = &index.kind {
                let i = *i as usize;
                let (_, offsets) = tuple_layout_id(
                    &elem_type_ids,
                    self.ptr_type(),
                    self.query().registry(),
                    &self.arena(),
                );
                let offset = offsets[i];
                let elem_type_id = elem_type_ids[i];
                let elem_cr_type =
                    type_id_to_cranelift(elem_type_id, &self.arena(), self.ptr_type());

                let value =
                    self.builder
                        .ins()
                        .load(elem_cr_type, MemFlags::new(), obj.value, offset);

                return Ok(CompiledValue {
                    value,
                    ty: elem_cr_type,
                    type_id: elem_type_id,
                });
            } else {
                return Err("tuple index must be a constant".to_string());
            }
        }

        // Try fixed array
        if let Some((element_id, size)) = arena.unwrap_fixed_array(obj.type_id) {
            drop(arena);
            // Fixed array indexing
            let elem_size = 8i32; // All elements aligned to 8 bytes
            let elem_cr_type = type_id_to_cranelift(element_id, &self.arena(), self.ptr_type());

            // Calculate offset: base + (index * elem_size)
            let offset = if let ExprKind::IntLiteral(i) = &index.kind {
                // Constant index - bounds check at compile time already done in sema
                let i = *i as usize;
                if i >= size {
                    return Err(format!(
                        "index {} out of bounds for fixed array of size {}",
                        i, size
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

            return Ok(CompiledValue {
                value,
                ty: elem_cr_type,
                type_id: element_id,
            });
        }

        // Try dynamic array
        if let Some(element_id) = arena.unwrap_array(obj.type_id) {
            drop(arena);
            // Dynamic array indexing with CSE caching
            let idx = self.expr(index)?;

            let raw_value =
                self.call_runtime_cached(RuntimeFn::ArrayGetValue, &[obj.value, idx.value])?;
            return Ok(self.convert_field_value(raw_value, element_id));
        }

        drop(arena);
        let type_name = self.arena().display_basic(obj.type_id);
        Err(format!("cannot index type {}", type_name))
    }

    /// Compile an index assignment
    fn index_assign(
        &mut self,
        object: &Expr,
        index: &Expr,
        value: &Expr,
    ) -> Result<CompiledValue, String> {
        let arr = self.expr(object)?;
        let val = self.expr(value)?;

        let arena = self.arena();
        let fixed_array_info = arena.unwrap_fixed_array(arr.type_id);
        let is_dynamic_array = arena.is_array(arr.type_id);
        drop(arena);

        if let Some((_elem_type_id, size)) = fixed_array_info {
            // Fixed array assignment - store directly at offset
            let elem_size = 8i32; // All elements aligned to 8 bytes

            // Calculate offset
            let offset = if let ExprKind::IntLiteral(i) = &index.kind {
                let i = *i as usize;
                if i >= size {
                    return Err(format!(
                        "index {} out of bounds for fixed array of size {}",
                        i, size
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
            self.builder
                .ins()
                .store(MemFlags::new(), val.value, elem_ptr, 0);

            Ok(val)
        } else if is_dynamic_array {
            // Dynamic array assignment
            let idx = self.expr(index)?;

            let set_value_ref = self.runtime_func_ref(RuntimeFn::ArraySet)?;
            // Compute tag before using builder to avoid borrow conflict
            let tag = {
                let arena = self.arena();
                array_element_tag_id(val.type_id, &arena)
            };
            let tag_val = self.builder.ins().iconst(types::I64, tag);
            let value_bits = convert_to_i64_for_storage(self.builder, &val);

            self.builder
                .ins()
                .call(set_value_ref, &[arr.value, idx.value, tag_val, value_bits]);

            Ok(val)
        } else {
            // Error: not an indexable type
            let type_name = self.arena().display_basic(arr.type_id);
            Err(format!("cannot assign to index of type {}", type_name))
        }
    }

    /// Compile an `is` type check expression
    fn is_expr(&mut self, is_expr: &vole_frontend::IsExpr) -> Result<CompiledValue, String> {
        let value = self.expr(&is_expr.value)?;
        let tested_type_id = self.resolve_type_expr(&is_expr.type_expr);

        let arena = self.arena();
        if let Some(variants) = arena.unwrap_union(value.type_id) {
            let expected_tag = variants
                .iter()
                .position(|&v| v == tested_type_id)
                .unwrap_or(usize::MAX);
            drop(arena);

            let result = self.tag_eq(value.value, expected_tag as i64);
            Ok(self.bool_value(result))
        } else {
            drop(arena);
            // O(1) type comparison with TypeId
            Ok(self.bool_const(value.type_id == tested_type_id))
        }
    }

    /// Compile a type pattern check for match expressions
    /// Returns Some(comparison_value) if a runtime check is needed, None if always matches
    fn compile_type_pattern_check(
        &mut self,
        scrutinee: &CompiledValue,
        pattern_type_id: TypeId,
    ) -> Result<Option<Value>, String> {
        let arena = self.arena();
        if let Some(variants) = arena.unwrap_union(scrutinee.type_id) {
            let expected_tag = variants
                .iter()
                .position(|&v| v == pattern_type_id)
                .unwrap_or(usize::MAX);
            drop(arena);

            if expected_tag == usize::MAX {
                // Pattern type not in union - will never match
                let never_match = self.builder.ins().iconst(types::I8, 0);
                return Ok(Some(never_match));
            }

            let result = self.tag_eq(scrutinee.value, expected_tag as i64);
            Ok(Some(result))
        } else {
            drop(arena);
            // Non-union scrutinee - pattern matches if types are equal (O(1) with TypeId)
            if scrutinee.type_id == pattern_type_id {
                Ok(None) // Always matches
            } else {
                // Never matches
                let never_match = self.builder.ins().iconst(types::I8, 0);
                Ok(Some(never_match))
            }
        }
    }

    /// Compile an equality check for two values based on their Vole type.
    /// Handles string comparison via runtime function, f64 via fcmp, and integers via icmp.
    fn compile_equality_check(
        &mut self,
        type_id: TypeId,
        left: Value,
        right: Value,
    ) -> Result<Value, String> {
        let arena = self.arena();
        Ok(if arena.is_string(type_id) {
            drop(arena);
            if self.funcs().has_runtime(RuntimeFn::StringEq) {
                self.call_runtime(RuntimeFn::StringEq, &[left, right])?
            } else {
                self.builder.ins().icmp(IntCC::Equal, left, right)
            }
        } else if type_id == arena.f64() {
            drop(arena);
            self.builder.ins().fcmp(FloatCC::Equal, left, right)
        } else {
            drop(arena);
            self.builder.ins().icmp(IntCC::Equal, left, right)
        })
    }

    /// Compile a null coalesce expression (??)
    fn null_coalesce(
        &mut self,
        nc: &vole_frontend::NullCoalesceExpr,
    ) -> Result<CompiledValue, String> {
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
            .expect("unwrap expression requires optional type");
        let cranelift_type = type_id_to_cranelift(inner_type_id, &self.arena(), self.ptr_type());
        self.builder.append_block_param(merge_block, cranelift_type);

        self.builder
            .ins()
            .brif(is_nil, nil_block, &[], not_nil_block, &[]);

        self.switch_and_seal(nil_block);
        let default_val = self.expr(&nc.default)?;
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
        let payload = self
            .builder
            .ins()
            .load(cranelift_type, MemFlags::new(), value.value, 8);
        let payload_arg = BlockArg::from(payload);
        self.builder.ins().jump(merge_block, &[payload_arg]);

        self.switch_and_seal(merge_block);

        let result = self.builder.block_params(merge_block)[0];
        Ok(CompiledValue {
            value: result,
            ty: cranelift_type,
            type_id: inner_type_id,
        })
    }

    /// Load a captured variable from closure
    pub(crate) fn load_capture(
        &mut self,
        binding: &super::lambda::CaptureBinding,
    ) -> Result<CompiledValue, String> {
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

        Ok(CompiledValue {
            value,
            ty: cranelift_ty,
            type_id: binding.vole_type,
        })
    }

    /// Store a value to a captured variable in closure
    fn store_capture(
        &mut self,
        binding: &super::lambda::CaptureBinding,
        value: CompiledValue,
    ) -> Result<CompiledValue, String> {
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

        Ok(CompiledValue {
            value: value.value,
            ty: cranelift_ty,
            type_id: binding.vole_type,
        })
    }

    /// Compile a match expression
    #[tracing::instrument(skip(self, match_expr), fields(arms = match_expr.arms.len()))]
    pub fn match_expr(&mut self, match_expr: &MatchExpr) -> Result<CompiledValue, String> {
        let scrutinee = self.expr(&match_expr.scrutinee)?;
        let scrutinee_type_id = scrutinee.type_id;
        let scrutinee_type_str = self.arena().display_basic(scrutinee_type_id);
        tracing::trace!(scrutinee_type = %scrutinee_type_str, "match scrutinee");

        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I64);

        // Create a trap block for non-exhaustive match (should be unreachable)
        let trap_block = self.builder.create_block();

        let arm_blocks: Vec<Block> = match_expr
            .arms
            .iter()
            .map(|_| self.builder.create_block())
            .collect();

        if !arm_blocks.is_empty() {
            self.builder.ins().jump(arm_blocks[0], &[]);
        } else {
            let default_val = self.builder.ins().iconst(types::I64, 0);
            let default_arg = BlockArg::from(default_val);
            self.builder.ins().jump(merge_block, &[default_arg]);
        }

        let mut result_type_id = TypeId::VOID;

        for (i, arm) in match_expr.arms.iter().enumerate() {
            let arm_block = arm_blocks[i];
            // For the last arm, if pattern fails, go to trap (should be unreachable)
            let next_block = arm_blocks.get(i + 1).copied().unwrap_or(trap_block);

            self.builder.switch_to_block(arm_block);

            let mut arm_variables = self.vars.clone();
            // Track the effective arm block (may change for conditional extraction)
            let mut effective_arm_block = arm_block;

            let pattern_matches = match &arm.pattern {
                Pattern::Wildcard(_) => None,
                Pattern::Identifier { name, .. } => {
                    // Check if this identifier is a type name (class/record)
                    // Need to look up TypeDefId from Symbol first
                    let query = self.query();
                    let module_id = self
                        .current_module_id()
                        .unwrap_or_else(|| query.main_module());

                    let type_def_id = query
                        .try_name_id(module_id, &[*name])
                        .and_then(|name_id| query.try_type_def_id(name_id));

                    if let Some(type_meta) = type_def_id.and_then(|id| self.type_meta().get(&id)) {
                        // Type pattern - compare against union variant tag
                        self.compile_type_pattern_check(&scrutinee, type_meta.vole_type)?
                    } else {
                        // Regular identifier binding
                        let var = self.builder.declare_var(scrutinee.ty);
                        self.builder.def_var(var, scrutinee.value);
                        arm_variables.insert(*name, (var, scrutinee_type_id));
                        None
                    }
                }
                Pattern::Type { type_expr, .. } => {
                    let pattern_type_id = self.resolve_type_expr(type_expr);
                    self.compile_type_pattern_check(&scrutinee, pattern_type_id)?
                }
                Pattern::Literal(lit_expr) => {
                    // Save and restore vars for pattern matching
                    let saved_vars = std::mem::replace(&mut self.vars, arm_variables.clone());
                    let lit_val = self.expr(lit_expr)?;
                    arm_variables = std::mem::replace(&mut self.vars, saved_vars);

                    // Use Vole type (not Cranelift type) to determine comparison method
                    let cmp = self.compile_equality_check(
                        scrutinee_type_id,
                        scrutinee.value,
                        lit_val.value,
                    )?;
                    Some(cmp)
                }
                Pattern::Val { name, .. } => {
                    // Val pattern - compare against existing variable's value
                    let (var, var_type_id) = *arm_variables
                        .get(name)
                        .ok_or_else(|| "undefined variable in val pattern".to_string())?;
                    let var_val = self.builder.use_var(var);

                    let cmp = self.compile_equality_check(var_type_id, scrutinee.value, var_val)?;
                    Some(cmp)
                }
                Pattern::Success { inner, .. } => {
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
                                type_id_to_cranelift(success_type_id, &arena, ptr_type)
                            };
                            let payload =
                                load_fallible_payload(self.builder, scrutinee.value, payload_ty);

                            // Handle inner pattern (usually an identifier binding)
                            if let Pattern::Identifier { name, .. } = inner_pat.as_ref() {
                                let var = self.builder.declare_var(payload_ty);
                                self.builder.def_var(var, payload);
                                arm_variables.insert(*name, (var, success_type_id));
                            }
                        }
                    }
                    Some(is_success)
                }
                Pattern::Error { inner, .. } => {
                    // Load the tag from fallible structure
                    let tag = load_fallible_tag(self.builder, scrutinee.value);
                    self.compile_error_pattern(inner, &scrutinee, tag, &mut arm_variables)?
                }
                Pattern::Tuple { elements, .. } => {
                    // Tuple destructuring in match - extract elements and bind
                    // Use arena methods for layout computation
                    // Extract all type info before using builder to avoid borrow conflicts
                    let elem_type_ids = self.arena().unwrap_tuple(scrutinee.type_id).cloned();
                    if let Some(elem_type_ids) = elem_type_ids {
                        let ptr_type = self.ptr_type();
                        let offsets = {
                            let arena = self.arena();
                            let (_, offsets) = tuple_layout_id(
                                &elem_type_ids,
                                ptr_type,
                                self.query().registry(),
                                &arena,
                            );
                            offsets
                        };
                        // Precompute cranelift types for each element
                        let elem_cr_types = self.cranelift_types(&elem_type_ids);
                        for (i, pattern) in elements.iter().enumerate() {
                            if let Pattern::Identifier { name, .. } = pattern {
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
                Pattern::Record {
                    type_name, fields, ..
                } => {
                    // Record destructuring in match - TypeName { x, y } or { x, y }
                    let (pattern_check, pattern_type_id) = if let Some(name) = type_name {
                        // Typed record pattern - need to check type first
                        // Look up TypeDefId from Symbol
                        let query = self.query();
                        let module_id = self
                            .current_module_id()
                            .unwrap_or_else(|| query.main_module());

                        let type_def_id = query
                            .try_name_id(module_id, &[*name])
                            .and_then(|name_id| query.try_type_def_id(name_id));

                        if let Some(type_meta) =
                            type_def_id.and_then(|id| self.type_meta().get(&id))
                        {
                            (
                                self.compile_type_pattern_check(&scrutinee, type_meta.vole_type)?,
                                Some(type_meta.vole_type),
                            )
                        } else {
                            // Unknown type name - never matches
                            (Some(self.builder.ins().iconst(types::I8, 0)), None)
                        }
                    } else {
                        // Untyped record pattern - always matches (type checked in sema)
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
                        let cond = pattern_check.unwrap();
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
                        for field_pattern in fields {
                            let field_name = self.interner().resolve(field_pattern.field_name);
                            let (slot, field_type_id) = get_field_slot_and_type_id_cg(
                                field_source_type_id,
                                field_name,
                                self,
                            )?;
                            let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
                            let result_raw = self.call_runtime(
                                RuntimeFn::InstanceGetField,
                                &[field_source, slot_val],
                            )?;
                            let converted = self.convert_field_value(result_raw, field_type_id);
                            let var = self.builder.declare_var(converted.ty);
                            self.builder.def_var(var, converted.value);
                            arm_variables.insert(field_pattern.binding, (var, field_type_id));
                        }

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
                        for field_pattern in fields {
                            let field_name = self.interner().resolve(field_pattern.field_name);
                            let (slot, field_type_id) = get_field_slot_and_type_id_cg(
                                field_source_type_id,
                                field_name,
                                self,
                            )?;
                            let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
                            let result_raw = self.call_runtime(
                                RuntimeFn::InstanceGetField,
                                &[field_source, slot_val],
                            )?;
                            let converted = self.convert_field_value(result_raw, field_type_id);
                            let var = self.builder.declare_var(converted.ty);
                            self.builder.def_var(var, converted.value);
                            arm_variables.insert(field_pattern.binding, (var, field_type_id));
                        }

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
            let body_val = self.expr(&arm.body)?;
            let _ = std::mem::replace(&mut self.vars, saved_vars);

            if i == 0 {
                result_type_id = body_val.type_id;
            }

            let result_val = if body_val.ty != types::I64 {
                match body_val.ty {
                    types::I8 => self.builder.ins().sextend(types::I64, body_val.value),
                    types::I32 => self.builder.ins().sextend(types::I64, body_val.value),
                    _ => body_val.value,
                }
            } else {
                body_val.value
            };

            let result_arg = BlockArg::from(result_val);
            self.builder.ins().jump(merge_block, &[result_arg]);
            self.builder.seal_block(body_block);
        }

        // Fill in trap block (should be unreachable if match is exhaustive)
        self.switch_and_seal(trap_block);
        self.builder.ins().trap(TrapCode::unwrap_user(1));

        self.switch_and_seal(merge_block);

        let merged_value = self.builder.block_params(merge_block)[0];

        // Reduce back to the correct type based on result_type_id
        let target_cty = self.cranelift_type(result_type_id);
        let (result, result_ty) = if target_cty != types::I64 && target_cty.is_int() {
            (
                self.builder.ins().ireduce(target_cty, merged_value),
                target_cty,
            )
        } else {
            (merged_value, types::I64)
        };

        Ok(CompiledValue {
            value: result,
            ty: result_ty,
            type_id: result_type_id,
        })
    }

    /// Compile a try expression (propagation)
    ///
    /// On success: returns unwrapped value
    /// On error: propagates by returning from function
    fn try_propagate(&mut self, inner: &Expr) -> Result<CompiledValue, String> {
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
                    )
                    .into());
                }
            }
        };

        // Load the tag
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

        // Error block: propagate by returning the fallible value
        self.switch_and_seal(error_block);
        self.builder.ins().return_(&[fallible.value]);

        // Success block: extract payload and jump to merge
        self.switch_and_seal(success_block);
        let payload = load_fallible_payload(self.builder, fallible.value, payload_ty);
        let payload_arg = BlockArg::from(payload);
        self.builder.ins().jump(merge_block, &[payload_arg]);

        // Merge block: continue with extracted value
        self.switch_and_seal(merge_block);
        let result = self.builder.block_params(merge_block)[0];

        Ok(CompiledValue {
            value: result,
            ty: payload_ty,
            type_id: success_type_id,
        })
    }

    /// Compile a block expression: { stmts; trailing_expr }
    fn block_expr(&mut self, block: &BlockExpr) -> Result<CompiledValue, String> {
        // Compile statements
        for stmt in &block.stmts {
            self.stmt(stmt)?;
        }

        // Compile trailing expression if present, otherwise return void
        if let Some(ref trailing) = block.trailing_expr {
            self.expr(trailing)
        } else {
            Ok(self.void_value())
        }
    }

    /// Compile an if expression: if cond { then } else { else }
    fn if_expr(&mut self, if_expr: &IfExpr) -> Result<CompiledValue, String> {
        let condition = self.expr(&if_expr.condition)?;

        // Get the result type from semantic analysis
        let result_type_id = self
            .get_expr_type(&if_expr.then_branch.id)
            .unwrap_or(self.arena().primitives.void);

        let is_void = self.arena().is_void(result_type_id);
        let result_cranelift_type =
            type_id_to_cranelift(result_type_id, &self.arena(), self.ptr_type());

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

        // Compile then branch
        self.switch_and_seal(then_block);
        let then_result = self.expr(&if_expr.then_branch)?;
        if !is_void {
            self.builder
                .ins()
                .jump(merge_block, &[then_result.value.into()]);
        } else {
            self.builder.ins().jump(merge_block, &[]);
        }

        // Compile else branch
        self.switch_and_seal(else_block);
        let else_result = if let Some(ref else_branch) = if_expr.else_branch {
            self.expr(else_branch)?
        } else {
            // No else branch - result is void/nil
            self.void_value()
        };
        if !is_void {
            self.builder
                .ins()
                .jump(merge_block, &[else_result.value.into()]);
        } else {
            self.builder.ins().jump(merge_block, &[]);
        }

        // Continue in merge block
        self.switch_and_seal(merge_block);

        if !is_void {
            let result = self.builder.block_params(merge_block)[0];
            Ok(CompiledValue {
                value: result,
                ty: result_cranelift_type,
                type_id: result_type_id,
            })
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
    fn when_expr(&mut self, when_expr: &WhenExpr) -> Result<CompiledValue, String> {
        // Get the result type from semantic analysis (from first arm body)
        let result_type_id = if !when_expr.arms.is_empty() {
            self.get_expr_type(&when_expr.arms[0].body.id)
                .unwrap_or(self.arena().primitives.void)
        } else {
            self.arena().primitives.void
        };

        let is_void = self.arena().is_void(result_type_id);
        let result_cranelift_type =
            type_id_to_cranelift(result_type_id, &self.arena(), self.ptr_type());

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
            let cond_result = self.expr(arm.condition.as_ref().unwrap())?;

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
                cond_block_idx += 1;
            }
        }

        // Compile body blocks
        for (i, arm) in when_expr.arms.iter().enumerate() {
            self.switch_and_seal(body_blocks[i]);

            let body_result = self.expr(&arm.body)?;

            if !is_void {
                self.builder
                    .ins()
                    .jump(merge_block, &[body_result.value.into()]);
            } else {
                self.builder.ins().jump(merge_block, &[]);
            }
        }

        // Continue in merge block
        self.switch_and_seal(merge_block);

        if !is_void {
            let result = self.builder.block_params(merge_block)[0];
            Ok(CompiledValue {
                value: result,
                ty: result_cranelift_type,
                type_id: result_type_id,
            })
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
        arm_variables: &mut HashMap<Symbol, (Variable, TypeId)>,
    ) -> Result<Option<Value>, String> {
        let Some(inner_pat) = inner else {
            // Bare error pattern: error => ...
            let is_error = self
                .builder
                .ins()
                .icmp_imm(IntCC::NotEqual, tag, FALLIBLE_SUCCESS_TAG);
            return Ok(Some(is_error));
        };

        match inner_pat.as_ref() {
            Pattern::Identifier { name, .. } => {
                self.compile_error_identifier_pattern(*name, scrutinee, tag, arm_variables)
            }
            Pattern::Record {
                type_name: Some(name),
                fields,
                ..
            } => self.compile_error_record_pattern(*name, fields, scrutinee, tag, arm_variables),
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
        arm_variables: &mut HashMap<Symbol, (Variable, TypeId)>,
    ) -> Result<Option<Value>, String> {
        // Check if this is an error type name via EntityRegistry
        let is_error_type = self
            .resolve_type(name)
            .is_some_and(|type_id| self.query().get_type(type_id).kind == TypeDefKind::ErrorType);

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
                type_id_to_cranelift(error_type_id, &arena, ptr_type)
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
    ) -> Result<Option<Value>, String> {
        let arena = self.arena();
        let Some((_success_type_id, error_type_id)) = arena.unwrap_fallible(scrutinee.type_id)
        else {
            // Not matching on a fallible type
            drop(arena);
            return Ok(Some(self.builder.ins().iconst(types::I8, 0)));
        };

        let name_table = self.name_table();
        let Some(error_tag) = fallible_error_tag_by_id(
            error_type_id,
            name,
            &arena,
            self.interner(),
            &name_table,
            self.query().registry(),
        ) else {
            // Error type not found in fallible - will never match
            drop(name_table);
            drop(arena);
            return Ok(Some(self.builder.ins().iconst(types::I8, 0)));
        };
        drop(name_table);
        drop(arena);

        let is_this_error = self.builder.ins().icmp_imm(IntCC::Equal, tag, error_tag);
        Ok(Some(is_this_error))
    }

    /// Compile a record pattern inside an error pattern (e.g., error Overflow { value, max }).
    fn compile_error_record_pattern(
        &mut self,
        name: Symbol,
        fields: &[RecordFieldPattern],
        scrutinee: &CompiledValue,
        tag: Value,
        arm_variables: &mut HashMap<Symbol, (Variable, TypeId)>,
    ) -> Result<Option<Value>, String> {
        // Look up error type_def_id via EntityRegistry
        let error_type_id = self.resolve_type(name).and_then(|type_id| {
            let type_def = self.query().get_type(type_id);
            if type_def.kind == TypeDefKind::ErrorType && type_def.error_info.is_some() {
                Some(type_id)
            } else {
                None
            }
        });

        let Some(error_type_def_id) = error_type_id else {
            // Unknown error type
            return Ok(Some(self.builder.ins().iconst(types::I8, 0)));
        };

        let arena = self.arena();
        let Some((_success_type_id, fallible_error_type_id)) =
            arena.unwrap_fallible(scrutinee.type_id)
        else {
            drop(arena);
            return Ok(Some(self.builder.ins().iconst(types::I8, 0)));
        };

        let name_table = self.name_table();
        let Some(error_tag) = fallible_error_tag_by_id(
            fallible_error_type_id,
            name,
            &arena,
            self.interner(),
            &name_table,
            self.query().registry(),
        ) else {
            // Error type not found in fallible
            drop(name_table);
            drop(arena);
            return Ok(Some(self.builder.ins().iconst(types::I8, 0)));
        };
        drop(name_table);
        drop(arena);

        let is_this_error = self.builder.ins().icmp_imm(IntCC::Equal, tag, error_tag);

        // Get fields from EntityRegistry
        let error_fields: Vec<_> = self
            .query()
            .fields_on_type(error_type_def_id)
            .map(|field_id| self.query().get_field(field_id).clone())
            .collect();

        // Error fields are stored inline in the fallible structure
        // Layout: tag at offset 0, fields at offset 8, 16, 24, ...
        for field_pattern in fields.iter() {
            let field_name = self.interner().resolve(field_pattern.field_name);

            // Find the field index and type in the error type
            let Some((field_idx, field_def)) = error_fields.iter().enumerate().find(|(_, f)| {
                self.name_table().last_segment_str(f.name_id).as_deref() == Some(field_name)
            }) else {
                continue;
            };

            // Calculate field offset: payload starts at offset 8, each field is 8 bytes
            let field_offset = FALLIBLE_PAYLOAD_OFFSET + (field_idx as i32 * 8);

            // Load the field value as i64 (stored as i64)
            let raw_value =
                self.builder
                    .ins()
                    .load(types::I64, MemFlags::new(), scrutinee.value, field_offset);

            // Convert from i64 to the actual field type
            let field_ty_id = field_def.ty;
            let converted = self.convert_field_value(raw_value, field_ty_id);
            let var = self.builder.declare_var(converted.ty);
            self.builder.def_var(var, converted.value);
            arm_variables.insert(field_pattern.binding, (var, field_ty_id));
        }

        Ok(Some(is_this_error))
    }
}
