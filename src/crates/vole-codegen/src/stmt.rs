// src/codegen/stmt.rs
//
// Statement and block compilation - impl Cg methods.

use cranelift::prelude::*;

use crate::RuntimeFn;
use crate::errors::CodegenError;
use vole_frontend::{self, ExprKind, LetInit, Pattern, PatternKind, RaiseStmt, Stmt, Symbol};
use vole_sema::IsCheckResult;
use vole_sema::type_arena::TypeId;

use super::context::Cg;
use super::structs::{convert_to_i64_for_storage, get_field_slot_and_type_id_cg};
use super::types::{
    CompiledValue, FALLIBLE_SUCCESS_TAG, convert_to_type, fallible_error_tag_by_id,
    tuple_layout_id, type_id_to_cranelift,
};

/// Check if a block contains a `continue` statement (recursively).
///
/// This is used to determine if a for loop needs a separate continue block.
/// Loops without continue can use an optimized 3-block structure.
fn block_contains_continue(block: &vole_frontend::Block) -> bool {
    for stmt in &block.stmts {
        if stmt_contains_continue(stmt) {
            return true;
        }
    }
    false
}

/// Check if a statement contains a `continue` (recursively).
fn stmt_contains_continue(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Continue(_) => true,
        Stmt::If(if_stmt) => {
            block_contains_continue(&if_stmt.then_branch)
                || if_stmt
                    .else_branch
                    .as_ref()
                    .is_some_and(block_contains_continue)
        }
        // Note: we don't check nested loops because continue in a nested loop
        // doesn't affect the outer loop
        Stmt::While(_) | Stmt::For(_) => false,
        Stmt::Let(_)
        | Stmt::LetTuple(_)
        | Stmt::Expr(_)
        | Stmt::Return(_)
        | Stmt::Break(_)
        | Stmt::Raise(_) => false,
    }
}

impl Cg<'_, '_, '_> {
    /// Pre-register a recursive lambda binding before compilation.
    ///
    /// For recursive lambdas (lambdas that capture themselves), we need the binding
    /// in vars before compiling so capture bindings get the correct type.
    /// Returns Some(var) if pre-registered, None otherwise.
    fn preregister_recursive_lambda(
        &mut self,
        name: Symbol,
        init_expr: &vole_frontend::Expr,
    ) -> Option<Variable> {
        let ExprKind::Lambda(lambda) = &init_expr.kind else {
            return None;
        };
        let captures = lambda.captures.borrow();
        if !captures.iter().any(|c| c.name == name) {
            return None;
        }
        let func_type_id = self.get_expr_type(&init_expr.id)?;
        let cranelift_ty = self.cranelift_type(func_type_id);
        let var = self.builder.declare_var(cranelift_ty);
        self.vars.insert(name, (var, func_type_id));
        Some(var)
    }

    /// Compile a function body (block or expression).
    ///
    /// Returns (terminated, optional_value):
    /// - For blocks: (true if explicitly terminated, None)
    /// - For expressions: (true, Some(value))
    pub fn compile_body(
        &mut self,
        body: &vole_frontend::FuncBody,
    ) -> Result<(bool, Option<CompiledValue>), String> {
        match body {
            vole_frontend::FuncBody::Block(block) => {
                let terminated = self.block(block)?;
                Ok((terminated, None))
            }
            vole_frontend::FuncBody::Expr(expr) => {
                let value = self.expr(expr)?;
                Ok((true, Some(value)))
            }
        }
    }

    /// Compile a block of statements. Returns true if terminated (return/break).
    ///
    /// Note: This does NOT push/pop RC scopes. Statement blocks (if/while/for bodies)
    /// do not introduce new variable scopes in Vole — variables declared inside are
    /// visible to the enclosing scope. RC cleanup for these variables happens when
    /// their enclosing function or block_expr scope exits.
    pub fn block(&mut self, block: &vole_frontend::Block) -> Result<bool, String> {
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

                // Pre-register recursive lambdas so they can capture themselves
                let preregistered_var = self.preregister_recursive_lambda(let_stmt.name, init_expr);

                // Set self_capture context for recursive lambdas
                if preregistered_var.is_some() {
                    self.self_capture = Some(let_stmt.name);
                }

                let init = self.expr(init_expr)?;

                // Clear self_capture context
                self.self_capture = None;

                // Struct copy: when binding a struct value, copy to a new stack slot
                // to maintain value semantics (structs are stack-allocated value types)
                let init = if self.arena().is_struct(init.type_id) {
                    self.copy_struct_value(init)?
                } else {
                    init
                };

                // Look up the declared type from sema (pre-computed for let statements with type annotations)
                let declared_type_id_opt = self.get_declared_var_type(&init_expr.id);

                let (mut final_value, mut final_type_id) = if let Some(declared_type_id) =
                    declared_type_id_opt
                {
                    let arena = self.arena();
                    let is_declared_union = arena.is_union(declared_type_id);
                    let is_declared_integer = arena.is_integer(declared_type_id);
                    let is_declared_f32 = declared_type_id == arena.f32();
                    let is_declared_f64 = declared_type_id == arena.f64();
                    let is_declared_interface = arena.is_interface(declared_type_id);
                    let is_declared_unknown = arena.is_unknown(declared_type_id);

                    if is_declared_unknown && !self.arena().is_unknown(init.type_id) {
                        // Box value to unknown type (TaggedValue)
                        let boxed = self.box_to_unknown(init)?;
                        (boxed.value, boxed.type_id)
                    } else if is_declared_union && !self.arena().is_union(init.type_id) {
                        let wrapped = self.construct_union_id(init, declared_type_id)?;
                        (wrapped.value, wrapped.type_id)
                    } else if is_declared_integer && init.type_id.is_integer() {
                        let arena = self.arena();
                        let declared_cty =
                            type_id_to_cranelift(declared_type_id, arena, self.ptr_type());
                        let init_cty = init.ty;
                        if declared_cty.bits() < init_cty.bits() {
                            let narrowed = self.builder.ins().ireduce(declared_cty, init.value);
                            (narrowed, declared_type_id)
                        } else if declared_cty.bits() > init_cty.bits() {
                            let widened = self.builder.ins().sextend(declared_cty, init.value);
                            (widened, declared_type_id)
                        } else {
                            (init.value, declared_type_id)
                        }
                    } else if is_declared_f32 && init.type_id.is_float() && init.ty == types::F64 {
                        // f64 -> f32: demote to narrower float
                        let narrowed = self.builder.ins().fdemote(types::F32, init.value);
                        (narrowed, declared_type_id)
                    } else if is_declared_f64 && init.type_id.is_float() && init.ty == types::F32 {
                        // f32 -> f64: promote to wider float
                        let widened = self.builder.ins().fpromote(types::F64, init.value);
                        (widened, declared_type_id)
                    } else if is_declared_interface {
                        // For functional interfaces, keep the actual function type from the lambda
                        // This preserves the is_closure flag for proper calling convention
                        (init.value, init.type_id)
                    } else {
                        (init.value, declared_type_id)
                    }
                } else {
                    (init.value, init.type_id)
                };

                // Box value if assigning to interface type
                if let Some(declared_type_id) = declared_type_id_opt {
                    let arena = self.arena();
                    let is_declared_interface = arena.is_interface(declared_type_id);
                    let is_final_interface = arena.is_interface(final_type_id);

                    if is_declared_interface && !is_final_interface {
                        let arena = self.arena();
                        let cranelift_ty =
                            type_id_to_cranelift(final_type_id, arena, self.ptr_type());
                        let boxed = self.box_interface_value(
                            CompiledValue {
                                value: final_value,
                                ty: cranelift_ty,
                                type_id: final_type_id,
                            },
                            declared_type_id,
                        )?;
                        final_value = boxed.value;
                        final_type_id = boxed.type_id;
                    }
                }

                // Use preregistered var for recursive lambdas, otherwise declare new
                let var = if let Some(var) = preregistered_var {
                    self.builder.def_var(var, final_value);
                    // vars already has the entry from preregistration
                    var
                } else {
                    let cranelift_ty = self.cranelift_type(final_type_id);
                    let var = self.builder.declare_var(cranelift_ty);
                    self.builder.def_var(var, final_value);
                    self.vars.insert(let_stmt.name, (var, final_type_id));
                    var
                };

                // Register RC locals for drop-flag tracking and emit rc_inc if needed.
                // Variable copies (let y = x) need rc_inc because we're creating a
                // new reference to the same heap object. Ownership transfers (let x =
                // new_string(), let x = "literal") don't need inc — the value is born
                // with refcount=1 for us.
                if self.rc_scopes.has_active_scope() && self.needs_rc_cleanup(final_type_id) {
                    if self.expr_needs_rc_inc(init_expr) {
                        self.emit_rc_inc(final_value)?;
                    }
                    let drop_flag = self.register_rc_local(var, final_type_id);
                    crate::rc_cleanup::set_drop_flag_live(self.builder, drop_flag);
                }

                Ok(false)
            }

            Stmt::LetTuple(let_tuple) => {
                // Compile the initializer - should be a tuple, fixed array, or class
                let init = self.expr(&let_tuple.init)?;

                // Recursively compile the destructuring pattern
                self.compile_destructure_pattern(&let_tuple.pattern, init.value, init.type_id)?;
                Ok(false)
            }

            Stmt::Expr(expr_stmt) => {
                let result = self.expr(&expr_stmt.expr)?;
                if result.type_id == TypeId::NEVER {
                    // The expression diverges (e.g. `unreachable`, `panic`).
                    // emit_panic_static creates an unreachable continuation block
                    // that needs a terminator so Cranelift doesn't complain about
                    // an unfilled block.
                    self.builder.ins().trap(TrapCode::unwrap_user(1));
                    Ok(true)
                } else {
                    Ok(false)
                }
            }

            Stmt::Return(ret) => {
                let return_type_id = self.return_type;
                if let Some(value) = &ret.value {
                    let compiled = self.expr(value)?;

                    // RC bookkeeping for return values:
                    // - RC local variable: skip its cleanup (ownership transfers to caller)
                    // - Non-RC local / borrow (index, field, loop var): rc_inc for caller
                    // - Fresh allocation (call, literal): already owned, no action needed
                    let skip_var = if let ExprKind::Identifier(sym) = &value.kind
                        && let Some((var, _)) = self.vars.get(sym)
                        && self.rc_scopes.is_rc_local(*var)
                    {
                        Some(*var)
                    } else {
                        None
                    };
                    if skip_var.is_none()
                        && self.needs_rc_cleanup(compiled.type_id)
                        && self.expr_needs_rc_inc(value)
                    {
                        self.emit_rc_inc(compiled.value)?;
                    }
                    self.emit_rc_cleanup_all_scopes(skip_var)?;

                    // Box concrete types to interface representation if needed
                    // But skip boxing for RuntimeIterator - it's the raw representation of Iterator
                    if let Some(ret_type_id) = return_type_id
                        && self.arena().is_interface(ret_type_id)
                        && !self.arena().is_interface(compiled.type_id)
                        && !self.arena().is_runtime_iterator(compiled.type_id)
                    {
                        let boxed = self.box_interface_value(compiled, ret_type_id)?;
                        self.builder.ins().return_(&[boxed.value]);
                        return Ok(true);
                    }

                    // Check if the function has a fallible return type using arena methods
                    if let Some(ret_type_id) = return_type_id
                        && self.arena().unwrap_fallible(ret_type_id).is_some()
                    {
                        // For fallible functions, return (tag, payload) directly in registers
                        // Both tag and payload are i64 for uniform representation
                        let tag_val = self.builder.ins().iconst(types::I64, FALLIBLE_SUCCESS_TAG);

                        // Convert payload to i64 for uniform representation
                        let payload_val = convert_to_i64_for_storage(self.builder, &compiled);

                        self.builder.ins().return_(&[tag_val, payload_val]);
                    } else if let Some(ret_type_id) = return_type_id
                        && self.is_small_struct_return(ret_type_id)
                    {
                        // Small struct (1-2 flat slots): return values in registers
                        let flat_count = self
                            .struct_flat_slot_count(ret_type_id)
                            .expect("small struct return must have flat slot count");
                        let struct_ptr = compiled.value;
                        let mut return_vals = Vec::with_capacity(2);
                        for i in 0..flat_count {
                            let offset = (i as i32) * 8;
                            let val = self.builder.ins().load(
                                types::I64,
                                MemFlags::new(),
                                struct_ptr,
                                offset,
                            );
                            return_vals.push(val);
                        }
                        // Pad to 2 registers for consistent convention
                        while return_vals.len() < 2 {
                            return_vals.push(self.builder.ins().iconst(types::I64, 0));
                        }
                        self.builder.ins().return_(&return_vals);
                    } else if let Some(ret_type_id) = return_type_id
                        && self.is_sret_struct_return(ret_type_id)
                    {
                        // Large struct (3+ flat slots): copy all flat slots into sret buffer
                        let entry_block = self
                            .builder
                            .func
                            .layout
                            .entry_block()
                            .expect("function must have an entry block");
                        let sret_ptr = self.builder.block_params(entry_block)[0];
                        let flat_count = self
                            .struct_flat_slot_count(ret_type_id)
                            .expect("sret struct return must have flat slot count");
                        let struct_ptr = compiled.value;
                        for i in 0..flat_count {
                            let offset = (i as i32) * 8;
                            let val = self.builder.ins().load(
                                types::I64,
                                MemFlags::new(),
                                struct_ptr,
                                offset,
                            );
                            self.builder
                                .ins()
                                .store(MemFlags::new(), val, sret_ptr, offset);
                        }
                        self.builder.ins().return_(&[sret_ptr]);
                    } else if let Some(ret_type_id) = return_type_id
                        && self.arena().is_union(ret_type_id)
                    {
                        // For union return types, wrap the value in a union
                        let wrapped = self.construct_union_id(compiled, ret_type_id)?;
                        self.builder.ins().return_(&[wrapped.value]);
                    } else {
                        // Non-fallible function, return value directly
                        // Convert to return type if needed (e.g., i64 -> i128)
                        // Access arena via env to avoid borrow conflict with builder
                        let return_value = if let Some(ret_type_id) = return_type_id {
                            let arena = self.env.analyzed.type_arena();
                            let ptr_type = self.ptr_type();
                            let target_ty = type_id_to_cranelift(ret_type_id, arena, ptr_type);
                            convert_to_type(self.builder, compiled, target_ty, arena)
                        } else {
                            compiled.value
                        };
                        self.builder.ins().return_(&[return_value]);
                    }
                } else {
                    // Void return — cleanup all RC locals
                    self.emit_rc_cleanup_all_scopes(None)?;
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
                self.compile_loop_body(&while_stmt.body, exit_block, header_block)?;

                self.builder.switch_to_block(exit_block);

                self.builder.seal_block(header_block);
                self.builder.seal_block(body_block);
                self.builder.seal_block(exit_block);

                Ok(false)
            }

            Stmt::If(if_stmt) => {
                // Check for statically known `is` condition (dead branch elimination
                // for monomorphized generics where sema didn't analyze the body).
                if let ExprKind::Is(is) = &if_stmt.condition.kind
                    && let Some(static_result) = self.try_static_is_check(is, if_stmt.condition.id)
                {
                    match static_result {
                        IsCheckResult::AlwaysTrue => {
                            return self.block(&if_stmt.then_branch);
                        }
                        IsCheckResult::AlwaysFalse => {
                            return if let Some(else_branch) = &if_stmt.else_branch {
                                self.block(else_branch)
                            } else {
                                Ok(false)
                            };
                        }
                        _ => {} // Runtime check needed, fall through
                    }
                }

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

                // If both branches terminated, the merge block is unreachable.
                // Cranelift still requires it to be filled, so emit a trap.
                if then_terminated && else_terminated {
                    self.builder
                        .ins()
                        .trap(TrapCode::user(1).expect("trap code 1 must be valid"));
                }

                self.builder.seal_block(then_block);
                self.builder.seal_block(else_block);
                self.builder.seal_block(merge_block);

                Ok(then_terminated && else_terminated)
            }

            Stmt::For(for_stmt) => {
                if let ExprKind::Range(range) = &for_stmt.iterable.kind {
                    self.for_range(for_stmt, range)
                } else {
                    // Check if iterable is an Iterator type or string type using TypeId (module-aware)
                    let iterable_type_id = self.get_expr_type(&for_stmt.iterable.id);
                    let is_iterator =
                        iterable_type_id.is_some_and(|id| self.is_iterator_type_id(id));
                    let is_string = iterable_type_id.is_some_and(|id| self.arena().is_string(id));
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
                    // Clean up RC locals from scopes inside the loop
                    if let Some(depth) = self.cf.loop_rc_depth() {
                        self.emit_rc_cleanup_from_depth(depth)?;
                    }
                    self.builder.ins().jump(exit_block, &[]);
                }
                Ok(true)
            }

            Stmt::Continue(_) => {
                if let Some(continue_block) = self.cf.loop_continue() {
                    // Clean up RC locals from scopes inside the loop
                    if let Some(depth) = self.cf.loop_rc_depth() {
                        self.emit_rc_cleanup_from_depth(depth)?;
                    }
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

    /// Compile a for loop over a range.
    ///
    /// Uses an optimized 3-block structure (header, body, exit) when the loop body
    /// doesn't contain `continue` statements. For loops with `continue`, uses the
    /// standard 4-block structure (header, body, continue, exit) to ensure the
    /// counter is incremented before jumping back to header.
    fn for_range(
        &mut self,
        for_stmt: &vole_frontend::ForStmt,
        range: &vole_frontend::RangeExpr,
    ) -> Result<bool, String> {
        let start_val = self.expr(&range.start)?;
        let end_val = self.expr(&range.end)?;

        let var = self.builder.declare_var(types::I64);
        self.builder.def_var(var, start_val.value);
        self.vars.insert(for_stmt.var_name, (var, TypeId::I64));

        // Check if the loop body contains continue statements
        let has_continue = block_contains_continue(&for_stmt.body);

        if has_continue {
            // Standard 4-block structure for loops with continue
            self.for_range_with_continue(for_stmt, range, var, end_val.value)
        } else {
            // Optimized 3-block structure: inline increment at end of body
            self.for_range_optimized(for_stmt, range, var, end_val.value)
        }
    }

    /// Optimized for_range with 3 blocks (header, body, exit).
    ///
    /// The counter increment is inlined at the end of the body, saving one block
    /// and one jump instruction per iteration.
    fn for_range_optimized(
        &mut self,
        for_stmt: &vole_frontend::ForStmt,
        range: &vole_frontend::RangeExpr,
        var: Variable,
        end_val: Value,
    ) -> Result<bool, String> {
        let header = self.builder.create_block();
        let body_block = self.builder.create_block();
        let exit_block = self.builder.create_block();

        self.builder.ins().jump(header, &[]);

        // Header: check loop condition
        self.builder.switch_to_block(header);
        let current = self.builder.use_var(var);
        let cmp = if range.inclusive {
            self.builder
                .ins()
                .icmp(IntCC::SignedLessThanOrEqual, current, end_val)
        } else {
            self.builder
                .ins()
                .icmp(IntCC::SignedLessThan, current, end_val)
        };
        self.builder
            .ins()
            .brif(cmp, body_block, &[], exit_block, &[]);

        // Body: compile loop body, then increment and loop back
        self.builder.switch_to_block(body_block);
        // Register loop context - continue jumps to header (but there's no continue in this path)
        let rc_depth = self.rc_scope_depth();
        self.cf.push_loop(exit_block, header, rc_depth);
        let terminated = self.block(&for_stmt.body)?;
        self.cf.pop_loop();

        if !terminated {
            // Inline the counter increment at end of body
            let current = self.builder.use_var(var);
            let next = self.builder.ins().iadd_imm(current, 1);
            self.builder.def_var(var, next);
            self.builder.ins().jump(header, &[]);
        }

        // Finalize: switch to exit and seal all blocks
        self.builder.switch_to_block(exit_block);
        self.builder.seal_block(header);
        self.builder.seal_block(body_block);
        self.builder.seal_block(exit_block);

        Ok(false)
    }

    /// Standard for_range with 4 blocks (header, body, continue, exit).
    ///
    /// Used when the loop body contains `continue` statements, which need to
    /// jump to the continue block to increment the counter before looping.
    fn for_range_with_continue(
        &mut self,
        for_stmt: &vole_frontend::ForStmt,
        range: &vole_frontend::RangeExpr,
        var: Variable,
        end_val: Value,
    ) -> Result<bool, String> {
        let header = self.builder.create_block();
        let body_block = self.builder.create_block();
        let continue_block = self.builder.create_block();
        let exit_block = self.builder.create_block();

        self.builder.ins().jump(header, &[]);

        // Header: check loop condition
        self.builder.switch_to_block(header);
        let current = self.builder.use_var(var);
        let cmp = if range.inclusive {
            self.builder
                .ins()
                .icmp(IntCC::SignedLessThanOrEqual, current, end_val)
        } else {
            self.builder
                .ins()
                .icmp(IntCC::SignedLessThan, current, end_val)
        };
        self.builder
            .ins()
            .brif(cmp, body_block, &[], exit_block, &[]);

        // Body: compile loop body
        self.builder.switch_to_block(body_block);
        self.compile_loop_body(&for_stmt.body, exit_block, continue_block)?;

        // Continue: increment counter and jump to header
        self.builder.switch_to_block(continue_block);
        let current = self.builder.use_var(var);
        let next = self.builder.ins().iadd_imm(current, 1);
        self.builder.def_var(var, next);
        self.builder.ins().jump(header, &[]);

        self.finalize_for_loop(header, body_block, continue_block, exit_block);

        Ok(false)
    }

    /// Compile a for loop over an array
    fn for_array(&mut self, for_stmt: &vole_frontend::ForStmt) -> Result<bool, String> {
        let arr = self.expr(&for_stmt.iterable)?;

        // Get element type using arena method
        let elem_type_id = self
            .arena()
            .unwrap_array(arr.type_id)
            .unwrap_or_else(|| self.arena().i64());

        let len_val = self.call_runtime(RuntimeFn::ArrayLen, &[arr.value])?;

        let idx_var = self.builder.declare_var(types::I64);
        let zero = self.builder.ins().iconst(types::I64, 0);
        self.builder.def_var(idx_var, zero);

        let elem_var = self.builder.declare_var(types::I64);
        self.builder.def_var(elem_var, zero);
        self.vars
            .insert(for_stmt.var_name, (elem_var, elem_type_id));

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

        self.compile_loop_body(&for_stmt.body, exit_block, continue_block)?;

        self.builder.switch_to_block(continue_block);
        let current_idx = self.builder.use_var(idx_var);
        let next_idx = self.builder.ins().iadd_imm(current_idx, 1);
        self.builder.def_var(idx_var, next_idx);
        self.builder.ins().jump(header, &[]);

        self.finalize_for_loop(header, body_block, continue_block, exit_block);

        Ok(false)
    }

    /// Check if a type is an Iterator<T> type using TypeId
    fn is_iterator_type_id(&self, ty: TypeId) -> bool {
        let arena = self.arena();
        if let Some((type_def_id, _)) = arena.unwrap_interface(ty) {
            self.name_table()
                .well_known
                .is_iterator_type_def(type_def_id)
        } else {
            false
        }
    }

    /// Compile a for loop over an iterator
    fn for_iterator(&mut self, for_stmt: &vole_frontend::ForStmt) -> Result<bool, String> {
        let iter = self.expr(&for_stmt.iterable)?;

        // Get element type using arena methods
        let elem_type_id = {
            let arena = self.arena();
            if let Some(elem_id) = arena.unwrap_runtime_iterator(iter.type_id) {
                elem_id
            } else if let Some((_, type_args)) = arena.unwrap_interface(iter.type_id) {
                type_args.first().copied().unwrap_or_else(|| arena.i64())
            } else {
                arena.i64()
            }
        };

        // Create a stack slot for the out_value parameter
        let slot_data = self.alloc_stack(8);
        let ptr_type = self.ptr_type();
        let slot_addr = self.builder.ins().stack_addr(ptr_type, slot_data, 0);

        // Initialize element variable
        let elem_var = self.builder.declare_var(types::I64);
        let zero = self.builder.ins().iconst(types::I64, 0);
        self.builder.def_var(elem_var, zero);
        self.vars
            .insert(for_stmt.var_name, (elem_var, elem_type_id));

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

        self.compile_loop_body(&for_stmt.body, exit_block, continue_block)?;

        // Continue: jump back to header
        self.builder.switch_to_block(continue_block);
        self.builder.ins().jump(header, &[]);

        self.finalize_for_loop(header, body_block, continue_block, exit_block);

        Ok(false)
    }

    /// Compile a for loop over a string (iterating characters)
    fn for_string(&mut self, for_stmt: &vole_frontend::ForStmt) -> Result<bool, String> {
        // Compile the string expression
        let string_val = self.expr(&for_stmt.iterable)?;

        // Create a string chars iterator from the string
        let iter_val = self.call_runtime(RuntimeFn::StringCharsIter, &[string_val.value])?;

        // Create a stack slot for the out_value parameter
        let slot_data = self.alloc_stack(8);
        let ptr_type = self.ptr_type();
        let slot_addr = self.builder.ins().stack_addr(ptr_type, slot_data, 0);

        // Initialize element variable (each character is returned as a string)
        let elem_var = self.builder.declare_var(types::I64);
        let zero = self.builder.ins().iconst(types::I64, 0);
        self.builder.def_var(elem_var, zero);
        self.vars
            .insert(for_stmt.var_name, (elem_var, TypeId::STRING));

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

        self.compile_loop_body(&for_stmt.body, exit_block, continue_block)?;

        // Continue: jump back to header
        self.builder.switch_to_block(continue_block);
        self.builder.ins().jump(header, &[]);

        self.finalize_for_loop(header, body_block, continue_block, exit_block);

        Ok(false)
    }

    /// Wrap a value in a union representation.
    pub fn construct_union_id(
        &mut self,
        value: CompiledValue,
        union_type_id: TypeId,
    ) -> Result<CompiledValue, String> {
        let arena = self.arena();
        let variants = arena.unwrap_union(union_type_id).ok_or_else(|| {
            CodegenError::type_mismatch("union construction", "union type", "non-union").to_string()
        })?;
        let variants = variants.clone();

        // If the value is already the same union type, just return it
        if value.type_id == union_type_id {
            return Ok(value);
        }

        // If the value is a struct, box it first (auto-boxing for union storage)
        let value = if self.arena().is_struct(value.type_id) {
            self.copy_struct_to_heap(value)?
        } else {
            value
        };

        // Find the position of value's type in variants
        let (tag, actual_value, actual_type_id) =
            if let Some(pos) = variants.iter().position(|&v| v == value.type_id) {
                (pos, value.value, value.type_id)
            } else {
                // Try to find a compatible integer type for widening/narrowing
                let arena = self.arena();
                let value_is_integer = arena.is_integer(value.type_id);

                let compatible = if value_is_integer {
                    variants
                        .iter()
                        .enumerate()
                        .find(|(_, v)| arena.is_integer(**v))
                        .map(|(pos, v)| (pos, *v))
                } else {
                    None
                };

                match compatible {
                    Some((pos, variant_type_id)) => {
                        let target_ty = self.cranelift_type(variant_type_id);
                        let actual = if target_ty.bytes() < value.ty.bytes() {
                            self.builder.ins().ireduce(target_ty, value.value)
                        } else if target_ty.bytes() > value.ty.bytes() {
                            self.builder.ins().sextend(target_ty, value.value)
                        } else {
                            value.value
                        };
                        (pos, actual, variant_type_id)
                    }
                    None => {
                        return Err(CodegenError::type_mismatch(
                            "union variant",
                            "compatible type",
                            "incompatible type",
                        )
                        .into());
                    }
                }
            };

        let union_size = self.type_size(union_type_id);
        let slot = self.alloc_stack(union_size);

        let tag_val = self.builder.ins().iconst(types::I8, tag as i64);
        self.builder.ins().stack_store(tag_val, slot, 0);

        // Sentinel types (nil, Done, user-defined) have no payload - only the tag matters
        if !self.arena().is_sentinel(actual_type_id) {
            self.builder.ins().stack_store(actual_value, slot, 8);
        }

        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
        Ok(CompiledValue {
            value: ptr,
            ty: ptr_type,
            type_id: union_type_id,
        })
    }

    /// Recursively compile a destructuring pattern, binding variables for the values extracted
    fn compile_destructure_pattern(
        &mut self,
        pattern: &Pattern,
        value: Value,
        ty_id: TypeId,
    ) -> Result<(), String> {
        match &pattern.kind {
            PatternKind::Identifier { name } => {
                let cr_type = self.cranelift_type(ty_id);
                let var = self.builder.declare_var(cr_type);
                self.builder.def_var(var, value);
                self.vars.insert(*name, (var, ty_id));
            }
            PatternKind::Wildcard => {
                // Wildcard - nothing to bind
            }
            PatternKind::Tuple { elements } => {
                let arena = self.arena();

                // Try tuple first
                if let Some(elem_type_ids) = arena.unwrap_tuple(ty_id).cloned() {
                    let (_, offsets) = tuple_layout_id(
                        &elem_type_ids,
                        self.ptr_type(),
                        self.query().registry(),
                        self.arena(),
                    );
                    for (i, elem_pattern) in elements.iter().enumerate() {
                        let offset = offsets[i];
                        let elem_type_id = elem_type_ids[i];
                        let elem_cr_type = self.cranelift_type(elem_type_id);
                        let elem_value =
                            self.builder
                                .ins()
                                .load(elem_cr_type, MemFlags::new(), value, offset);
                        self.compile_destructure_pattern(elem_pattern, elem_value, elem_type_id)?;
                    }
                // Try fixed array
                } else if let Some((element_id, _)) = arena.unwrap_fixed_array(ty_id) {
                    let elem_cr_type = self.cranelift_type(element_id);
                    let elem_size = self.type_size(element_id).div_ceil(8) * 8;
                    for (i, elem_pattern) in elements.iter().enumerate() {
                        let offset = (i as i32) * (elem_size as i32);
                        let elem_value =
                            self.builder
                                .ins()
                                .load(elem_cr_type, MemFlags::new(), value, offset);
                        self.compile_destructure_pattern(elem_pattern, elem_value, element_id)?;
                    }
                }
            }
            PatternKind::Record { fields, .. } => {
                // Check if this is a module type - if so, register module bindings
                let module_info = self.arena().unwrap_module(ty_id).cloned();
                if let Some(module_info) = module_info {
                    self.compile_module_destructure(fields, &module_info)?;
                    return Ok(());
                }

                // Record destructuring - extract fields
                let is_struct = self.arena().is_struct(ty_id);
                for field_pattern in fields {
                    let field_name = self.interner().resolve(field_pattern.field_name);
                    let (slot, field_type_id) =
                        get_field_slot_and_type_id_cg(ty_id, field_name, self)?;

                    let converted = if is_struct {
                        // Structs are stack-allocated: load field directly from pointer + offset
                        self.struct_field_load(value, slot, field_type_id, ty_id)?
                    } else {
                        // Classes are heap-allocated: use runtime field access
                        let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
                        let result_raw =
                            self.call_runtime(RuntimeFn::InstanceGetField, &[value, slot_val])?;
                        self.convert_field_value(result_raw, field_type_id)
                    };

                    let var = self.builder.declare_var(converted.ty);
                    self.builder.def_var(var, converted.value);
                    self.vars
                        .insert(field_pattern.binding, (var, field_type_id));
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// Compile module destructuring - registers bindings for module exports.
    /// No runtime code is generated; bindings are used at compile time for calls.
    fn compile_module_destructure(
        &mut self,
        fields: &[vole_frontend::RecordFieldPattern],
        module_info: &vole_sema::type_arena::InternedModule,
    ) -> Result<(), String> {
        for field_pattern in fields {
            let export_name = field_pattern.field_name;
            let export_name_str = self.interner().resolve(export_name);

            // Find the export type in the module
            let export_type_id = module_info
                .exports
                .iter()
                .find(|(name_id, _)| {
                    self.name_table().last_segment_str(*name_id).as_deref() == Some(export_name_str)
                })
                .map(|(_, ty)| *ty);

            if let Some(export_type_id) = export_type_id {
                // Register the module binding: local_name -> (module_id, export_name, type_id)
                self.module_bindings.insert(
                    field_pattern.binding,
                    (module_info.module_id, export_name, export_type_id),
                );
            } else {
                return Err(format!("Module export '{}' not found", export_name_str));
            }
        }
        Ok(())
    }

    /// Compile a raise statement: raise ErrorName { field: value, ... }
    ///
    /// Uses multi-value return (tag, payload):
    /// - Tag: error tag (1+) from fallible_error_tag_by_id
    /// - Payload: For errors with no fields, just 0. For errors with fields,
    ///   a pointer to stack-allocated error data.
    ///
    /// Then returns from the function with (tag, payload).
    fn raise_stmt(&mut self, raise_stmt: &RaiseStmt) -> Result<bool, String> {
        // Get the current function's return type - must be Fallible
        let return_type_id = self
            .return_type
            .ok_or("raise statement used outside of a function with declared return type")?;

        // Extract the error type from the fallible return type
        let (_success_type_id, error_type_id) = self
            .arena()
            .unwrap_fallible(return_type_id)
            .ok_or_else(|| {
                CodegenError::type_mismatch(
                    "raise statement",
                    "fallible return type",
                    "non-fallible type",
                )
            })?;

        // Get the error tag for this error type
        let error_tag = fallible_error_tag_by_id(
            error_type_id,
            raise_stmt.error_name,
            self.arena(),
            self.interner(),
            self.name_table(),
            self.query().registry(),
        )
        .ok_or_else(|| {
            format!(
                "Error type {} not found in fallible type",
                self.interner().resolve(raise_stmt.error_name)
            )
        })?;

        // Get the error type_def_id to look up field order from EntityRegistry
        let raise_error_name = self.interner().resolve(raise_stmt.error_name);
        let arena = self.arena();
        let name_table = self.name_table();
        let error_type_def_id = if let Some(type_def_id) = arena.unwrap_error(error_type_id) {
            // Single error type
            let name = name_table.last_segment_str(self.query().type_name_id(type_def_id));
            if name.as_deref() == Some(raise_error_name) {
                Some(type_def_id)
            } else {
                None
            }
        } else if let Some(variants) = arena.unwrap_union(error_type_id) {
            // Union of error types
            variants.iter().find_map(|&v| {
                if let Some(type_def_id) = arena.unwrap_error(v) {
                    let name = name_table.last_segment_str(self.query().type_name_id(type_def_id));
                    if name.as_deref() == Some(raise_error_name) {
                        return Some(type_def_id);
                    }
                }
                None
            })
        } else {
            None
        }
        .ok_or_else(|| {
            format!(
                "Could not find error type info for {}",
                self.interner().resolve(raise_stmt.error_name)
            )
        })?;

        // Get fields from EntityRegistry
        let error_fields: Vec<_> = self
            .query()
            .fields_on_type(error_type_def_id)
            .map(|field_id| self.query().get_field(field_id).clone())
            .collect();

        // Create the tag value
        let tag_val = self.builder.ins().iconst(types::I64, error_tag);

        // Determine payload based on number of fields
        // This matches the layout used by external functions in runtime:
        // - 0 fields: payload is 0
        // - 1 field: payload is the field value directly (inline)
        // - 2+ fields: payload is a pointer to field data
        let payload_val = if error_fields.is_empty() {
            // No fields - payload is 0
            self.builder.ins().iconst(types::I64, 0)
        } else if error_fields.len() == 1 {
            // Single field - store inline as payload value
            let field_def = &error_fields[0];
            let field_name = self
                .name_table()
                .last_segment_str(field_def.name_id)
                .unwrap_or_default();
            let field_init = raise_stmt
                .fields
                .iter()
                .find(|f| self.interner().resolve(f.name) == field_name)
                .ok_or_else(|| format!("Missing field {} in raise statement", &field_name))?;

            let field_value = self.expr(&field_init.value)?;
            // RC: if the field value is a borrow (e.g., a parameter variable),
            // inc it so the caller gets an owned reference in the error payload.
            if self.needs_rc_cleanup(field_value.type_id)
                && self.expr_needs_rc_inc(&field_init.value)
            {
                self.emit_rc_inc(field_value.value)?;
            }
            convert_to_i64_for_storage(self.builder, &field_value)
        } else {
            // Multiple fields - allocate on stack and store field values
            let error_payload_size = (error_fields.len() * 8) as u32;
            let slot = self.alloc_stack(error_payload_size);

            // Store each field value at the appropriate offset
            for (field_idx, field_def) in error_fields.iter().enumerate() {
                let field_name = self
                    .name_table()
                    .last_segment_str(field_def.name_id)
                    .unwrap_or_default();
                let field_init = raise_stmt
                    .fields
                    .iter()
                    .find(|f| self.interner().resolve(f.name) == field_name)
                    .ok_or_else(|| format!("Missing field {} in raise statement", &field_name))?;

                let field_value = self.expr(&field_init.value)?;
                // RC: inc borrowed field values for the error payload
                if self.needs_rc_cleanup(field_value.type_id)
                    && self.expr_needs_rc_inc(&field_init.value)
                {
                    self.emit_rc_inc(field_value.value)?;
                }
                let store_value = convert_to_i64_for_storage(self.builder, &field_value);
                let field_offset = (field_idx as i32) * 8;
                self.builder
                    .ins()
                    .stack_store(store_value, slot, field_offset);
            }

            let ptr_type = self.ptr_type();
            self.builder.ins().stack_addr(ptr_type, slot, 0)
        };

        // RC cleanup: like return, clean up all RC locals before exiting.
        self.emit_rc_cleanup_all_scopes(None)?;

        // Return from the function with (tag, payload)
        self.builder.ins().return_(&[tag_val, payload_val]);

        // Raise always terminates the current block
        Ok(true)
    }
}
