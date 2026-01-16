// src/codegen/stmt.rs
//
// Statement and block compilation - impl Cg methods.

use std::collections::HashMap;

use cranelift::prelude::*;

use crate::codegen::RuntimeFn;
use crate::errors::CodegenError;
use crate::frontend::{self, ExprKind, LetInit, Pattern, RaiseStmt, Stmt, Symbol};
use crate::sema::types::NominalType;
use crate::sema::{LegacyType, PrimitiveType};

use super::compiler::ControlFlowCtx;
use super::context::{Cg, ControlFlow};
use super::structs::{convert_field_value, convert_to_i64_for_storage, get_field_slot_and_type};
use super::types::{
    CompileCtx, CompiledValue, FALLIBLE_PAYLOAD_OFFSET, FALLIBLE_SUCCESS_TAG, FALLIBLE_TAG_OFFSET,
    box_interface_value, fallible_error_tag, resolve_type_expr, tuple_layout, type_size,
    type_to_cranelift,
};

/// Compile a block of statements (wrapper for compatibility)
pub(super) fn compile_block(
    builder: &mut FunctionBuilder,
    block: &frontend::Block,
    variables: &mut HashMap<Symbol, (Variable, LegacyType)>,
    _cf_ctx: &mut ControlFlowCtx,
    ctx: &mut CompileCtx,
) -> Result<bool, String> {
    // Note: cf_ctx is ignored as top-level blocks don't have loops yet
    let mut cf = ControlFlow::new();
    let mut cg = Cg::new(builder, variables, ctx, &mut cf);
    cg.block(block)
}

/// Wrap a value in a union representation (wrapper for compatibility)
#[allow(dead_code)] // Used by compiler.rs during migration
pub(super) fn construct_union(
    builder: &mut FunctionBuilder,
    value: CompiledValue,
    union_type: &LegacyType,
    pointer_type: Type,
    arena: &std::rc::Rc<std::cell::RefCell<crate::sema::type_arena::TypeArena>>,
    entity_registry: &crate::sema::EntityRegistry,
) -> Result<CompiledValue, String> {
    let LegacyType::Union(variants) = union_type else {
        return Err(
            CodegenError::type_mismatch("union construction", "union type", "non-union").into(),
        );
    };

    // Convert value's type_id to legacy for comparison
    let value_legacy_type = arena.borrow().to_type(value.type_id);

    // If the value is already the same union type, just return it
    if &value_legacy_type == union_type {
        return Ok(value);
    }

    let (tag, actual_value, actual_type) = if let Some(pos) =
        variants.iter().position(|v| v == &value_legacy_type)
    {
        (pos, value.value, value_legacy_type.clone())
    } else {
        let compatible = variants.iter().enumerate().find(|(_, v)| {
            value_legacy_type.is_integer() && v.is_integer() && value_legacy_type.can_widen_to(v)
                || v.is_integer() && value_legacy_type.is_integer()
        });

        match compatible {
            Some((pos, variant_type)) => {
                let target_ty = type_to_cranelift(variant_type, pointer_type);
                let narrowed = if target_ty.bytes() < value.ty.bytes() {
                    builder.ins().ireduce(target_ty, value.value)
                } else if target_ty.bytes() > value.ty.bytes() {
                    builder.ins().sextend(target_ty, value.value)
                } else {
                    value.value
                };
                (pos, narrowed, variant_type.clone())
            }
            None => {
                return Err(CodegenError::type_mismatch(
                    "union variant",
                    format!("one of {:?}", variants),
                    format!("{:?}", value_legacy_type),
                )
                .into());
            }
        }
    };

    let union_size = type_size(union_type, pointer_type, entity_registry, &arena.borrow());
    let slot = builder.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        union_size,
        0,
    ));

    let tag_val = builder.ins().iconst(types::I8, tag as i64);
    builder.ins().stack_store(tag_val, slot, 0);

    if actual_type != LegacyType::Nil {
        builder.ins().stack_store(actual_value, slot, 8);
    }

    let ptr = builder.ins().stack_addr(pointer_type, slot, 0);
    // Intern the union type for the return value
    let interned_union_type = arena.borrow_mut().from_type(union_type);
    Ok(CompiledValue {
        value: ptr,
        ty: pointer_type,
        type_id: interned_union_type,
    })
}

impl Cg<'_, '_, '_> {
    /// Compile a block of statements. Returns true if terminated (return/break).
    pub fn block(&mut self, block: &frontend::Block) -> Result<bool, String> {
        let mut terminated = false;
        for stmt in &block.stmts {
            if terminated {
                break;
            }
            terminated = self.stmt(stmt)?;
        }
        Ok(terminated)
    }

    /// Compile a statement. Returns true if terminated (return/break).
    pub fn stmt(&mut self, stmt: &Stmt) -> Result<bool, String> {
        match stmt {
            Stmt::Let(let_stmt) => {
                // Type aliases don't generate code
                let init_expr = match &let_stmt.init {
                    LetInit::Expr(e) => e,
                    LetInit::TypeAlias(_) => return Ok(false),
                };
                let init = self.expr(init_expr)?;

                let mut declared_type_opt = None;
                // final_type is LegacyType during computation, converted to VoleType at the end
                let (mut final_value, mut final_type) = if let Some(ty_expr) = &let_stmt.ty {
                    let declared_type = resolve_type_expr(ty_expr, self.ctx);
                    declared_type_opt = Some(declared_type.clone());

                    if matches!(&declared_type, LegacyType::Union(_))
                        && !self.is_union(init.type_id)
                    {
                        let wrapped = self.construct_union(init, &declared_type)?;
                        (wrapped.value, self.to_legacy(wrapped.type_id))
                    } else if declared_type.is_integer() && self.type_is_integer(init.type_id) {
                        let declared_cty = type_to_cranelift(&declared_type, self.ctx.pointer_type);
                        let init_cty = init.ty;
                        if declared_cty.bits() < init_cty.bits() {
                            let narrowed = self.builder.ins().ireduce(declared_cty, init.value);
                            (narrowed, declared_type)
                        } else if declared_cty.bits() > init_cty.bits() {
                            let widened = self.builder.ins().sextend(declared_cty, init.value);
                            (widened, declared_type)
                        } else {
                            (init.value, declared_type)
                        }
                    } else if declared_type == LegacyType::Primitive(PrimitiveType::F32)
                        && self.type_is_float(init.type_id)
                        && init.ty == types::F64
                    {
                        // f64 -> f32: demote to narrower float
                        let narrowed = self.builder.ins().fdemote(types::F32, init.value);
                        (narrowed, declared_type)
                    } else if declared_type == LegacyType::Primitive(PrimitiveType::F64)
                        && self.type_is_float(init.type_id)
                        && init.ty == types::F32
                    {
                        // f32 -> f64: promote to wider float
                        let widened = self.builder.ins().fpromote(types::F64, init.value);
                        (widened, declared_type)
                    } else if let LegacyType::Nominal(NominalType::Interface(_)) = &declared_type {
                        // For functional interfaces, keep the actual function type from the lambda
                        // This preserves the is_closure flag for proper calling convention
                        (init.value, self.to_legacy(init.type_id))
                    } else {
                        (init.value, declared_type)
                    }
                } else {
                    (init.value, self.to_legacy(init.type_id))
                };

                if let Some(declared_type) = declared_type_opt
                    && matches!(
                        declared_type,
                        LegacyType::Nominal(NominalType::Interface(_))
                    )
                    && !matches!(final_type, LegacyType::Nominal(NominalType::Interface(_)))
                {
                    let boxed = box_interface_value(
                        self.builder,
                        self.ctx,
                        CompiledValue {
                            value: final_value,
                            ty: type_to_cranelift(&final_type, self.ctx.pointer_type),
                            type_id: self.intern_type(&final_type),
                        },
                        &declared_type,
                    )?;
                    final_value = boxed.value;
                    final_type = self.to_legacy(boxed.type_id);
                }

                let cranelift_ty = type_to_cranelift(&final_type, self.ctx.pointer_type);
                let var = self.builder.declare_var(cranelift_ty);
                self.builder.def_var(var, final_value);
                self.vars.insert(let_stmt.name, (var, final_type));
                Ok(false)
            }

            Stmt::LetTuple(let_tuple) => {
                // Compile the initializer - should be a tuple, fixed array, or record
                let init = self.expr(&let_tuple.init)?;
                let init_legacy_type = self.to_legacy(init.type_id);

                // Recursively compile the destructuring pattern
                self.compile_destructure_pattern(
                    &let_tuple.pattern,
                    init.value,
                    &init_legacy_type,
                )?;
                Ok(false)
            }

            Stmt::Expr(expr_stmt) => {
                self.expr(&expr_stmt.expr)?;
                Ok(false)
            }

            Stmt::Return(ret) => {
                let return_type = self.ctx.current_function_return_type.clone();
                if let Some(value) = &ret.value {
                    let compiled = self.expr(value)?;

                    // Box concrete types to interface representation if needed
                    // But skip boxing for RuntimeIterator - it's the raw representation of Iterator
                    if let Some(LegacyType::Nominal(NominalType::Interface(_))) = &return_type
                        && !self.is_interface(compiled.type_id)
                        && !self.is_runtime_iterator(compiled.type_id)
                    {
                        let return_type =
                            return_type.as_ref().expect("return type should be present");
                        let boxed =
                            box_interface_value(self.builder, self.ctx, compiled, return_type)?;
                        self.builder.ins().return_(&[boxed.value]);
                        return Ok(true);
                    }

                    // Check if the function has a fallible return type
                    if let Some(LegacyType::Fallible(ft)) = &return_type {
                        // For fallible functions, wrap the success value in a fallible struct
                        let fallible_size =
                            type_size(&LegacyType::Fallible(ft.clone()), self.ctx.pointer_type, &self.ctx.analyzed.entity_registry, &self.ctx.arena.borrow());

                        // Allocate stack slot for the fallible result
                        let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                            StackSlotKind::ExplicitSlot,
                            fallible_size,
                            0,
                        ));

                        // Store the success tag at offset 0
                        let tag_val = self.builder.ins().iconst(types::I64, FALLIBLE_SUCCESS_TAG);
                        self.builder
                            .ins()
                            .stack_store(tag_val, slot, FALLIBLE_TAG_OFFSET);

                        // Store the success value at the payload offset
                        // Convert to i64 if needed for storage
                        let store_value = convert_to_i64_for_storage(self.builder, &compiled);
                        self.builder
                            .ins()
                            .stack_store(store_value, slot, FALLIBLE_PAYLOAD_OFFSET);

                        // Get the pointer to the fallible result
                        let fallible_ptr =
                            self.builder
                                .ins()
                                .stack_addr(self.ctx.pointer_type, slot, 0);

                        self.builder.ins().return_(&[fallible_ptr]);
                    } else if let Some(LegacyType::Union(variants)) =
                        &self.ctx.current_function_return_type
                    {
                        // For union return types, wrap the value in a union
                        let union_type = LegacyType::Union(variants.clone());
                        let wrapped = self.construct_union(compiled, &union_type)?;
                        self.builder.ins().return_(&[wrapped.value]);
                    } else {
                        // Non-fallible function, return value directly
                        self.builder.ins().return_(&[compiled.value]);
                    }
                } else {
                    self.builder.ins().return_(&[]);
                }
                Ok(true)
            }

            Stmt::While(while_stmt) => {
                let header_block = self.builder.create_block();
                let body_block = self.builder.create_block();
                let exit_block = self.builder.create_block();

                self.builder.ins().jump(header_block, &[]);

                self.builder.switch_to_block(header_block);
                let cond = self.expr(&while_stmt.condition)?;
                let cond_i32 = self.cond_to_i32(cond.value);
                self.builder
                    .ins()
                    .brif(cond_i32, body_block, &[], exit_block, &[]);

                self.builder.switch_to_block(body_block);
                self.cf.push_loop(exit_block, header_block);
                let body_terminated = self.block(&while_stmt.body)?;
                self.cf.pop_loop();

                if !body_terminated {
                    self.builder.ins().jump(header_block, &[]);
                }

                self.builder.switch_to_block(exit_block);

                self.builder.seal_block(header_block);
                self.builder.seal_block(body_block);
                self.builder.seal_block(exit_block);

                Ok(false)
            }

            Stmt::If(if_stmt) => {
                let cond = self.expr(&if_stmt.condition)?;
                let cond_i32 = self.cond_to_i32(cond.value);

                let then_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();

                self.builder
                    .ins()
                    .brif(cond_i32, then_block, &[], else_block, &[]);

                self.builder.switch_to_block(then_block);
                let then_terminated = self.block(&if_stmt.then_branch)?;
                if !then_terminated {
                    self.builder.ins().jump(merge_block, &[]);
                }

                self.builder.switch_to_block(else_block);
                let else_terminated = if let Some(else_branch) = &if_stmt.else_branch {
                    self.block(else_branch)?
                } else {
                    false
                };
                if !else_terminated {
                    self.builder.ins().jump(merge_block, &[]);
                }

                self.builder.switch_to_block(merge_block);

                self.builder.seal_block(then_block);
                self.builder.seal_block(else_block);
                self.builder.seal_block(merge_block);

                Ok(then_terminated && else_terminated)
            }

            Stmt::For(for_stmt) => {
                if let ExprKind::Range(range) = &for_stmt.iterable.kind {
                    self.for_range(for_stmt, range)
                } else {
                    // Check if iterable is an Iterator type or string type
                    let iterable_type = self.ctx.get_expr_type_legacy(&for_stmt.iterable.id);
                    let is_iterator = iterable_type
                        .as_ref()
                        .is_some_and(|ty| self.is_iterator_type(ty));
                    let is_string = iterable_type.is_some_and(|ty| {
                        matches!(ty, LegacyType::Primitive(PrimitiveType::String))
                    });
                    if is_iterator {
                        self.for_iterator(for_stmt)
                    } else if is_string {
                        self.for_string(for_stmt)
                    } else {
                        self.for_array(for_stmt)
                    }
                }
            }

            Stmt::Break(_) => {
                if let Some(exit_block) = self.cf.loop_exit() {
                    self.builder.ins().jump(exit_block, &[]);
                }
                Ok(true)
            }

            Stmt::Continue(_) => {
                if let Some(continue_block) = self.cf.loop_continue() {
                    self.builder.ins().jump(continue_block, &[]);
                    let unreachable = self.builder.create_block();
                    self.builder.switch_to_block(unreachable);
                    self.builder.seal_block(unreachable);
                }
                Ok(true)
            }

            Stmt::Raise(raise_stmt) => self.raise_stmt(raise_stmt),
        }
    }

    /// Compile a for loop over a range
    fn for_range(
        &mut self,
        for_stmt: &frontend::ForStmt,
        range: &frontend::RangeExpr,
    ) -> Result<bool, String> {
        let start_val = self.expr(&range.start)?;
        let end_val = self.expr(&range.end)?;

        let var = self.builder.declare_var(types::I64);
        self.builder.def_var(var, start_val.value);
        self.vars.insert(
            for_stmt.var_name,
            (var, LegacyType::Primitive(PrimitiveType::I64)),
        );

        let header = self.builder.create_block();
        let body_block = self.builder.create_block();
        let continue_block = self.builder.create_block();
        let exit_block = self.builder.create_block();

        self.builder.ins().jump(header, &[]);

        self.builder.switch_to_block(header);
        let current = self.builder.use_var(var);
        let cmp = if range.inclusive {
            self.builder
                .ins()
                .icmp(IntCC::SignedLessThanOrEqual, current, end_val.value)
        } else {
            self.builder
                .ins()
                .icmp(IntCC::SignedLessThan, current, end_val.value)
        };
        self.builder
            .ins()
            .brif(cmp, body_block, &[], exit_block, &[]);

        self.builder.switch_to_block(body_block);
        self.cf.push_loop(exit_block, continue_block);
        let body_terminated = self.block(&for_stmt.body)?;
        self.cf.pop_loop();

        if !body_terminated {
            self.builder.ins().jump(continue_block, &[]);
        }

        self.builder.switch_to_block(continue_block);
        let current = self.builder.use_var(var);
        let next = self.builder.ins().iadd_imm(current, 1);
        self.builder.def_var(var, next);
        self.builder.ins().jump(header, &[]);

        self.builder.switch_to_block(exit_block);

        self.builder.seal_block(header);
        self.builder.seal_block(body_block);
        self.builder.seal_block(continue_block);
        self.builder.seal_block(exit_block);

        Ok(false)
    }

    /// Compile a for loop over an array
    fn for_array(&mut self, for_stmt: &frontend::ForStmt) -> Result<bool, String> {
        let arr = self.expr(&for_stmt.iterable)?;
        let arr_legacy_type = self.to_legacy(arr.type_id);

        let len_val = self.call_runtime(RuntimeFn::ArrayLen, &[arr.value])?;

        let idx_var = self.builder.declare_var(types::I64);
        let zero = self.builder.ins().iconst(types::I64, 0);
        self.builder.def_var(idx_var, zero);

        let elem_type = match &arr_legacy_type {
            LegacyType::Array(elem) => elem.as_ref().clone(),
            _ => LegacyType::Primitive(PrimitiveType::I64),
        };

        let elem_var = self.builder.declare_var(types::I64);
        self.builder.def_var(elem_var, zero);
        self.vars.insert(for_stmt.var_name, (elem_var, elem_type));

        let header = self.builder.create_block();
        let body_block = self.builder.create_block();
        let continue_block = self.builder.create_block();
        let exit_block = self.builder.create_block();

        self.builder.ins().jump(header, &[]);

        self.builder.switch_to_block(header);
        let current_idx = self.builder.use_var(idx_var);
        let cmp = self
            .builder
            .ins()
            .icmp(IntCC::SignedLessThan, current_idx, len_val);
        self.builder
            .ins()
            .brif(cmp, body_block, &[], exit_block, &[]);

        self.builder.switch_to_block(body_block);

        let current_idx = self.builder.use_var(idx_var);
        let elem_val = self.call_runtime(RuntimeFn::ArrayGetValue, &[arr.value, current_idx])?;
        self.builder.def_var(elem_var, elem_val);

        self.cf.push_loop(exit_block, continue_block);
        let body_terminated = self.block(&for_stmt.body)?;
        self.cf.pop_loop();

        if !body_terminated {
            self.builder.ins().jump(continue_block, &[]);
        }

        self.builder.switch_to_block(continue_block);
        let current_idx = self.builder.use_var(idx_var);
        let next_idx = self.builder.ins().iadd_imm(current_idx, 1);
        self.builder.def_var(idx_var, next_idx);
        self.builder.ins().jump(header, &[]);

        self.builder.switch_to_block(exit_block);

        self.builder.seal_block(header);
        self.builder.seal_block(body_block);
        self.builder.seal_block(continue_block);
        self.builder.seal_block(exit_block);

        Ok(false)
    }

    /// Check if a type is an Iterator<T> type
    fn is_iterator_type(&self, ty: &LegacyType) -> bool {
        match ty {
            LegacyType::Nominal(NominalType::Interface(iface)) => self
                .ctx
                .analyzed
                .name_table
                .well_known
                .is_iterator_type_def(iface.type_def_id),
            _ => false,
        }
    }

    /// Extract element type from Iterator<T>
    fn iterator_element_type(&self, ty: &LegacyType) -> LegacyType {
        match ty {
            LegacyType::Nominal(NominalType::Interface(iface)) => iface
                .type_args
                .first()
                .cloned()
                .unwrap_or(LegacyType::Primitive(PrimitiveType::I64)),
            LegacyType::RuntimeIterator(elem) => (**elem).clone(),
            _ => LegacyType::Primitive(PrimitiveType::I64),
        }
    }

    /// Compile a for loop over an iterator
    fn for_iterator(&mut self, for_stmt: &frontend::ForStmt) -> Result<bool, String> {
        let iter = self.expr(&for_stmt.iterable)?;
        let iter_legacy_type = self.to_legacy(iter.type_id);
        let elem_type = self.iterator_element_type(&iter_legacy_type);

        // Create a stack slot for the out_value parameter
        let slot_data = self.builder.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            8,
            0,
        ));
        let slot_addr = self
            .builder
            .ins()
            .stack_addr(self.ctx.pointer_type, slot_data, 0);

        // Initialize element variable
        let elem_var = self.builder.declare_var(types::I64);
        let zero = self.builder.ins().iconst(types::I64, 0);
        self.builder.def_var(elem_var, zero);
        self.vars.insert(for_stmt.var_name, (elem_var, elem_type));

        let header = self.builder.create_block();
        let body_block = self.builder.create_block();
        let continue_block = self.builder.create_block();
        let exit_block = self.builder.create_block();

        self.builder.ins().jump(header, &[]);

        // Header: call iter_next, check result
        self.builder.switch_to_block(header);
        let has_value = self.call_runtime(RuntimeFn::ArrayIterNext, &[iter.value, slot_addr])?;
        let is_done = self.builder.ins().icmp_imm(IntCC::Equal, has_value, 0);
        self.builder
            .ins()
            .brif(is_done, exit_block, &[], body_block, &[]);

        // Body: load value from stack slot, run body
        self.builder.switch_to_block(body_block);
        let elem_val = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), slot_addr, 0);
        self.builder.def_var(elem_var, elem_val);

        self.cf.push_loop(exit_block, continue_block);
        let body_terminated = self.block(&for_stmt.body)?;
        self.cf.pop_loop();

        if !body_terminated {
            self.builder.ins().jump(continue_block, &[]);
        }

        // Continue: jump back to header
        self.builder.switch_to_block(continue_block);
        self.builder.ins().jump(header, &[]);

        self.builder.switch_to_block(exit_block);

        self.builder.seal_block(header);
        self.builder.seal_block(body_block);
        self.builder.seal_block(continue_block);
        self.builder.seal_block(exit_block);

        Ok(false)
    }

    /// Compile a for loop over a string (iterating characters)
    fn for_string(&mut self, for_stmt: &frontend::ForStmt) -> Result<bool, String> {
        // Compile the string expression
        let string_val = self.expr(&for_stmt.iterable)?;

        // Create a string chars iterator from the string
        let iter_val = self.call_runtime(RuntimeFn::StringCharsIter, &[string_val.value])?;

        // Create a stack slot for the out_value parameter
        let slot_data = self.builder.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            8,
            0,
        ));
        let slot_addr = self
            .builder
            .ins()
            .stack_addr(self.ctx.pointer_type, slot_data, 0);

        // Initialize element variable (each character is returned as a string)
        let elem_var = self.builder.declare_var(types::I64);
        let zero = self.builder.ins().iconst(types::I64, 0);
        self.builder.def_var(elem_var, zero);
        self.vars.insert(
            for_stmt.var_name,
            (elem_var, LegacyType::Primitive(PrimitiveType::String)),
        );

        let header = self.builder.create_block();
        let body_block = self.builder.create_block();
        let continue_block = self.builder.create_block();
        let exit_block = self.builder.create_block();

        self.builder.ins().jump(header, &[]);

        // Header: call iter_next, check result
        self.builder.switch_to_block(header);
        let has_value = self.call_runtime(RuntimeFn::ArrayIterNext, &[iter_val, slot_addr])?;
        let is_done = self.builder.ins().icmp_imm(IntCC::Equal, has_value, 0);
        self.builder
            .ins()
            .brif(is_done, exit_block, &[], body_block, &[]);

        // Body: load value from stack slot, run body
        self.builder.switch_to_block(body_block);
        let elem_val = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), slot_addr, 0);
        self.builder.def_var(elem_var, elem_val);

        self.cf.push_loop(exit_block, continue_block);
        let body_terminated = self.block(&for_stmt.body)?;
        self.cf.pop_loop();

        if !body_terminated {
            self.builder.ins().jump(continue_block, &[]);
        }

        // Continue: jump back to header
        self.builder.switch_to_block(continue_block);
        self.builder.ins().jump(header, &[]);

        self.builder.switch_to_block(exit_block);

        self.builder.seal_block(header);
        self.builder.seal_block(body_block);
        self.builder.seal_block(continue_block);
        self.builder.seal_block(exit_block);

        Ok(false)
    }

    /// Wrap a value in a union representation (stack slot with tag + payload)
    pub fn construct_union(
        &mut self,
        value: CompiledValue,
        union_type: &LegacyType,
    ) -> Result<CompiledValue, String> {
        let LegacyType::Union(variants) = union_type else {
            return Err(CodegenError::type_mismatch(
                "union construction",
                "union type",
                "non-union",
            )
            .into());
        };

        // Convert value's vole_type to legacy for comparisons
        let value_legacy_type = self.to_legacy(value.type_id);

        // If the value is already the same union type, just return it
        if &value_legacy_type == union_type {
            return Ok(value);
        }

        let (tag, actual_value, actual_type) =
            if let Some(pos) = variants.iter().position(|v| v == &value_legacy_type) {
                (pos, value.value, value_legacy_type.clone())
            } else {
                let compatible = variants.iter().enumerate().find(|(_, v)| {
                    value_legacy_type.is_integer()
                        && v.is_integer()
                        && value_legacy_type.can_widen_to(v)
                        || v.is_integer() && value_legacy_type.is_integer()
                });

                match compatible {
                    Some((pos, variant_type)) => {
                        let target_ty = type_to_cranelift(variant_type, self.ctx.pointer_type);
                        let narrowed = if target_ty.bytes() < value.ty.bytes() {
                            self.builder.ins().ireduce(target_ty, value.value)
                        } else if target_ty.bytes() > value.ty.bytes() {
                            self.builder.ins().sextend(target_ty, value.value)
                        } else {
                            value.value
                        };
                        (pos, narrowed, variant_type.clone())
                    }
                    None => {
                        return Err(CodegenError::type_mismatch(
                            "union variant",
                            format!("one of {:?}", variants),
                            format!("{:?}", value_legacy_type),
                        )
                        .into());
                    }
                }
            };

        let union_size = type_size(union_type, self.ctx.pointer_type, &self.ctx.analyzed.entity_registry, &self.ctx.arena.borrow());
        let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            union_size,
            0,
        ));

        let tag_val = self.builder.ins().iconst(types::I8, tag as i64);
        self.builder.ins().stack_store(tag_val, slot, 0);

        if actual_type != LegacyType::Nil {
            self.builder.ins().stack_store(actual_value, slot, 8);
        }

        let ptr = self
            .builder
            .ins()
            .stack_addr(self.ctx.pointer_type, slot, 0);
        Ok(CompiledValue {
            value: ptr,
            ty: self.ctx.pointer_type,
            type_id: self.intern_type(union_type),
        })
    }

    /// Recursively compile a destructuring pattern, binding variables for the values extracted
    fn compile_destructure_pattern(
        &mut self,
        pattern: &Pattern,
        value: Value,
        ty: &LegacyType,
    ) -> Result<(), String> {
        match pattern {
            Pattern::Identifier { name, .. } => {
                let cr_type = type_to_cranelift(ty, self.ctx.pointer_type);
                let var = self.builder.declare_var(cr_type);
                self.builder.def_var(var, value);
                self.vars.insert(*name, (var, ty.clone()));
            }
            Pattern::Wildcard(_) => {
                // Wildcard - nothing to bind
            }
            Pattern::Tuple { elements, .. } => match ty {
                LegacyType::Tuple(elem_types) => {
                    let (_, offsets) = tuple_layout(elem_types, self.ctx.pointer_type, &self.ctx.analyzed.entity_registry, &self.ctx.arena.borrow());
                    for (i, elem_pattern) in elements.iter().enumerate() {
                        let offset = offsets[i];
                        let elem_type = &elem_types[i];
                        let elem_cr_type = type_to_cranelift(elem_type, self.ctx.pointer_type);
                        let elem_value =
                            self.builder
                                .ins()
                                .load(elem_cr_type, MemFlags::new(), value, offset);
                        self.compile_destructure_pattern(elem_pattern, elem_value, elem_type)?;
                    }
                }
                LegacyType::FixedArray { element, .. } => {
                    let elem_cr_type = type_to_cranelift(element, self.ctx.pointer_type);
                    let elem_size = type_size(element, self.ctx.pointer_type, &self.ctx.analyzed.entity_registry, &self.ctx.arena.borrow()).div_ceil(8) * 8;
                    for (i, elem_pattern) in elements.iter().enumerate() {
                        let offset = (i as i32) * (elem_size as i32);
                        let elem_value =
                            self.builder
                                .ins()
                                .load(elem_cr_type, MemFlags::new(), value, offset);
                        self.compile_destructure_pattern(elem_pattern, elem_value, element)?;
                    }
                }
                _ => {}
            },
            Pattern::Record { fields, .. } => {
                // Record destructuring - extract fields via runtime
                for field_pattern in fields {
                    let field_name = self.ctx.interner.resolve(field_pattern.field_name);
                    let (slot, field_type) = get_field_slot_and_type(ty, field_name, self.ctx)?;
                    let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
                    let result_raw =
                        self.call_runtime(RuntimeFn::InstanceGetField, &[value, slot_val])?;
                    let (result_val, cranelift_ty) =
                        convert_field_value(self.builder, result_raw, &field_type);
                    let var = self.builder.declare_var(cranelift_ty);
                    self.builder.def_var(var, result_val);
                    self.vars
                        .insert(field_pattern.binding, (var, field_type.clone()));
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// Compile a raise statement: raise ErrorName { field: value, ... }
    ///
    /// This allocates a fallible result on the stack with:
    /// - Tag at offset 0 (error tag from fallible_error_tag())
    /// - Error fields at payload offset 8+
    ///
    /// Then returns from the function with the fallible pointer.
    fn raise_stmt(&mut self, raise_stmt: &RaiseStmt) -> Result<bool, String> {
        // Get the current function's return type - must be Fallible
        let return_type = self
            .ctx
            .current_function_return_type
            .as_ref()
            .ok_or("raise statement used outside of a function with declared return type")?;

        let fallible_type = match return_type {
            LegacyType::Fallible(ft) => ft,
            _ => {
                return Err(CodegenError::type_mismatch(
                    "raise statement",
                    "fallible return type",
                    format!("{:?}", return_type),
                )
                .into());
            }
        };

        // Get the error tag for this error type
        let error_tag = fallible_error_tag(
            fallible_type,
            raise_stmt.error_name,
            self.ctx.interner,
            &self.ctx.analyzed.name_table,
            &self.ctx.analyzed.entity_registry,
        )
        .ok_or_else(|| {
            format!(
                "Error type {} not found in fallible type",
                self.ctx.interner.resolve(raise_stmt.error_name)
            )
        })?;

        // Calculate the size of the fallible type
        let fallible_size = type_size(return_type, self.ctx.pointer_type, &self.ctx.analyzed.entity_registry, &self.ctx.arena.borrow());

        // Allocate stack slot for the fallible result
        let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            fallible_size,
            0,
        ));

        // Store the error tag at offset 0
        let tag_val = self.builder.ins().iconst(types::I64, error_tag);
        self.builder
            .ins()
            .stack_store(tag_val, slot, FALLIBLE_TAG_OFFSET);

        // Get the error type_def_id to look up field order from EntityRegistry
        let raise_error_name = self.ctx.interner.resolve(raise_stmt.error_name);
        let error_type_def_id = match fallible_type.error_type.as_ref() {
            LegacyType::Nominal(NominalType::Error(info)) => {
                let name =
                    self.ctx.analyzed.name_table.last_segment_str(
                        self.ctx.analyzed.entity_registry.name_id(info.type_def_id),
                    );
                if name.as_deref() == Some(raise_error_name) {
                    Some(info.type_def_id)
                } else {
                    None
                }
            }
            LegacyType::Union(variants) => variants.iter().find_map(|v| {
                if let LegacyType::Nominal(NominalType::Error(info)) = v {
                    let name = self.ctx.analyzed.name_table.last_segment_str(
                        self.ctx.analyzed.entity_registry.name_id(info.type_def_id),
                    );
                    if name.as_deref() == Some(raise_error_name) {
                        return Some(info.type_def_id);
                    }
                }
                None
            }),
            _ => None,
        }
        .ok_or_else(|| {
            format!(
                "Could not find error type info for {}",
                self.ctx.interner.resolve(raise_stmt.error_name)
            )
        })?;

        // Get fields from EntityRegistry
        let error_fields: Vec<_> = self
            .ctx
            .analyzed
            .entity_registry
            .fields_on_type(error_type_def_id)
            .map(|field_id| self.ctx.analyzed.entity_registry.get_field(field_id))
            .collect();

        // Store each field value at the appropriate offset in the payload
        // Fields are stored sequentially at 8-byte intervals (i64 storage)
        for (field_idx, field_def) in error_fields.iter().enumerate() {
            // Find the matching field in the raise statement
            let field_name = self
                .ctx
                .analyzed
                .name_table
                .last_segment_str(field_def.name_id)
                .unwrap_or_default();
            let field_init = raise_stmt
                .fields
                .iter()
                .find(|f| self.ctx.interner.resolve(f.name) == field_name)
                .ok_or_else(|| format!("Missing field {} in raise statement", &field_name))?;

            // Compile the field value expression
            let field_value = self.expr(&field_init.value)?;

            // Convert to i64 for storage (same as struct fields)
            let store_value = convert_to_i64_for_storage(self.builder, &field_value);

            // Calculate field offset: payload starts at offset 8, each field is 8 bytes
            let field_offset = FALLIBLE_PAYLOAD_OFFSET + (field_idx as i32 * 8);

            // Store the field value
            self.builder
                .ins()
                .stack_store(store_value, slot, field_offset);
        }

        // Get the pointer to the fallible result
        let fallible_ptr = self
            .builder
            .ins()
            .stack_addr(self.ctx.pointer_type, slot, 0);

        // Return from the function with the fallible pointer
        self.builder.ins().return_(&[fallible_ptr]);

        // Raise always terminates the current block
        Ok(true)
    }
}
