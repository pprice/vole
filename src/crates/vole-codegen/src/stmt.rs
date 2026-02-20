// src/codegen/stmt.rs
//
// Statement and block compilation - impl Cg methods.

use cranelift::prelude::*;

use crate::errors::{CodegenError, CodegenResult};
use crate::union_layout;
use vole_frontend::ast::{RaiseStmt, ReturnStmt};
use vole_frontend::{self, ExprKind, LetInit, LetStmt, Pattern, PatternKind, Stmt, Symbol};
use vole_sema::IsCheckResult;
use vole_sema::type_arena::TypeId;

use super::context::Cg;
use super::structs::{
    convert_to_i64_for_storage, get_field_slot_and_type_id_cg, split_i128_for_storage,
    store_value_to_stack,
};
use super::types::{
    CompiledValue, FALLIBLE_SUCCESS_TAG, convert_to_type, is_wide_fallible, type_id_to_cranelift,
};
use crate::ops::sextend_const;

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
        let ExprKind::Lambda(_) = &init_expr.kind else {
            return None;
        };
        let analysis = self.get_lambda_analysis(init_expr.id);
        let has_self_capture = analysis
            .map(|a| a.captures.iter().any(|c| c.name == name))
            .unwrap_or(false);
        if !has_self_capture {
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
    ) -> CodegenResult<(bool, Option<CompiledValue>)> {
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
    pub fn block(&mut self, block: &vole_frontend::Block) -> CodegenResult<bool> {
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
    pub fn stmt(&mut self, stmt: &Stmt) -> CodegenResult<bool> {
        match stmt {
            Stmt::Let(let_stmt) => self.let_stmt(let_stmt),

            Stmt::LetTuple(let_tuple) => {
                // Compile the initializer - should be a tuple, fixed array, or class
                let mut init = self.expr(&let_tuple.init)?;
                let is_borrow = init.is_borrowed();

                // When the initializer is a fresh temporary (literal, call result),
                // register it as a composite RC local so its RC fields are dec'd at
                // scope exit.  When the init is a borrow (variable, index, field),
                // its source already has composite cleanup registered.
                if self.rc_scopes.has_active_scope()
                    && !is_borrow
                    && let Some(offsets) = self.rc_state(init.type_id).shallow_offsets()
                {
                    let cr_type = self.cranelift_type(init.type_id);
                    let temp_var = self.builder.declare_var(cr_type);
                    self.builder.def_var(temp_var, init.value);
                    let drop_flag = self.register_composite_rc_local(temp_var, offsets.to_vec());
                    crate::rc_cleanup::set_drop_flag_live(self, drop_flag);
                }

                // Recursively compile the destructuring pattern
                self.compile_destructure_pattern(&let_tuple.pattern, init.value, init.type_id)?;
                // The init value is consumed by the destructuring — bindings now own the elements.
                init.mark_consumed();
                init.debug_assert_rc_handled("Stmt::LetTuple");
                Ok(false)
            }

            Stmt::Expr(expr_stmt) => {
                let mut result = self.expr(&expr_stmt.expr)?;
                if result.type_id == TypeId::NEVER {
                    // The expression diverges (e.g. `unreachable`, `panic`).
                    // emit_panic_static creates an unreachable continuation block
                    // that needs a terminator so Cranelift doesn't complain about
                    // an unfilled block.
                    self.builder.ins().trap(crate::trap_codes::UNREACHABLE);
                    Ok(true)
                } else {
                    // Consume RC value if the expression result is unused
                    // (e.g. standalone function call returning a string)
                    self.consume_rc_value(&mut result)?;
                    result.debug_assert_rc_handled("Stmt::Expr");
                    Ok(false)
                }
            }

            Stmt::Return(ret) => self.return_stmt(ret),

            Stmt::While(while_stmt) => {
                let header_block = self.builder.create_block();
                let body_block = self.builder.create_block();
                let exit_block = self.builder.create_block();

                self.builder.ins().jump(header_block, &[]);

                self.switch_to_block(header_block);
                let cond = self.expr(&while_stmt.condition)?;
                self.emit_brif(cond.value, body_block, exit_block);

                self.switch_to_block(body_block);
                self.compile_loop_body(&while_stmt.body, exit_block, header_block)?;

                self.switch_to_block(exit_block);

                // Seal the header and body blocks now that their predecessors are known.
                // The exit block is NOT sealed - see finalize_for_loop for explanation.
                self.builder.seal_block(header_block);
                self.builder.seal_block(body_block);

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
                        IsCheckResult::CheckTag(_) | IsCheckResult::CheckUnknown(_) => {
                            // Runtime check needed, fall through
                        }
                    }
                }

                let cond = self.expr(&if_stmt.condition)?;

                let then_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();

                self.emit_brif(cond.value, then_block, else_block);

                self.switch_to_block(then_block);
                let then_terminated = self.block(&if_stmt.then_branch)?;
                if !then_terminated {
                    self.builder.ins().jump(merge_block, &[]);
                }

                self.switch_to_block(else_block);
                let else_terminated = if let Some(else_branch) = &if_stmt.else_branch {
                    self.block(else_branch)?
                } else {
                    false
                };
                if !else_terminated {
                    self.builder.ins().jump(merge_block, &[]);
                }

                self.switch_to_block(merge_block);

                // If both branches terminated, the merge block is unreachable.
                // Cranelift still requires it to be filled, so emit a trap.
                if then_terminated && else_terminated {
                    self.builder.ins().trap(crate::trap_codes::UNREACHABLE);
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
                    self.switch_to_block(unreachable);
                    self.builder.seal_block(unreachable);
                }
                Ok(true)
            }

            Stmt::Raise(raise_stmt) => self.raise_stmt(raise_stmt),
        }
    }

    /// Compile a let statement binding.
    fn let_stmt(&mut self, let_stmt: &LetStmt) -> CodegenResult<bool> {
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

        let declared_type_id_opt = self.get_declared_var_type(&init_expr.id);
        let init = if let Some(declared_type_id) = declared_type_id_opt {
            self.expr_with_expected_type(init_expr, declared_type_id)?
        } else {
            self.expr(init_expr)?
        };

        // Clear self_capture context
        self.self_capture = None;

        // Struct copy: when binding a struct value, copy to a new stack slot
        // to maintain value semantics (structs are stack-allocated value types)
        let mut init = if self.arena().is_struct(init.type_id) {
            self.copy_struct_value(init)?
        } else {
            init
        };

        let (final_value, final_type_id, is_stack_union) =
            self.coerce_let_init(&init, declared_type_id_opt)?;

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
        //
        // Inside a loop body, borrowed let-bindings (array index, field
        // access, variable copies) must NOT be rc_inc'd because the
        // source container keeps the value alive for the duration of
        // the iteration and the let re-executes each iteration. Without
        // per-iteration dec of the old value, each inc leaks. This
        // matches for-loop semantics where the loop variable is a raw
        // borrow. Ownership transfers (calls, literals) inside loops
        // still get normal RC tracking — they produce a fresh +1 that
        // the scope-exit dec balances against the last iteration's value.
        if self.rc_scopes.has_active_scope() && self.rc_state(final_type_id).needs_cleanup() {
            let is_borrow = init.is_borrowed();
            if self.cf.in_loop() && is_borrow {
                // Borrow inside loop: skip inc and RC registration.
                // The container (array, struct, etc.) keeps the value alive.
                // If this value is later assigned to an outer variable or
                // returned, the assign/return handlers emit their own inc.
            } else {
                if is_borrow {
                    self.emit_rc_inc_for_type(final_value, final_type_id)?;
                }
                let drop_flag = self.register_rc_local(var, final_type_id);
                crate::rc_cleanup::set_drop_flag_live(self, drop_flag);
            }
        } else if self.rc_scopes.has_active_scope() {
            // Check for composite types (struct, fixed array, tuple) with RC fields.
            // These need element-level cleanup on scope exit.
            if let Some(offsets) = self.rc_state(final_type_id).shallow_offsets() {
                // Struct copy (let b = a): the bytewise copy shares the same RC
                // pointers as the original.  rc_inc each RC field so both the
                // original and the copy own their reference and scope-exit dec
                // is balanced.  We detect copies by checking whether the init
                // expression is an identifier (variable reference) that is
                // already tracked as a composite RC local — meaning its fields
                // will also be dec'd on scope exit.
                let is_struct_copy = if let ExprKind::Identifier(sym) = &init_expr.kind {
                    self.vars
                        .get(sym)
                        .is_some_and(|&(v, _)| self.rc_scopes.is_composite_rc_local(v))
                } else {
                    false
                };
                if is_struct_copy {
                    for &off in offsets {
                        let field_ptr =
                            self.builder
                                .ins()
                                .load(types::I64, MemFlags::new(), final_value, off);
                        self.emit_rc_inc(field_ptr)?;
                    }
                }
                let drop_flag = self.register_composite_rc_local(var, offsets.to_vec());
                crate::rc_cleanup::set_drop_flag_live(self, drop_flag);
            } else if is_stack_union || self.arena().is_union(final_type_id) {
                // Register union RC cleanup for any union-typed value. This
                // includes both locally constructed unions (construct_union_id)
                // and function return values (call_result copies callee data
                // to a local [tag, payload] stack slot).
                if let Some(rc_tags) = self.rc_state(final_type_id).union_variants() {
                    // If the init value is a borrow (e.g. let g: T? = some_var),
                    // the RC value is aliased and needs rc_inc so the union
                    // owns its own reference.
                    if init.is_borrowed() {
                        self.emit_union_rc_inc(final_value, rc_tags)?;
                    }
                    let drop_flag = self.register_union_rc_local(var, rc_tags.to_vec());
                    crate::rc_cleanup::set_drop_flag_live(self, drop_flag);
                }
            }
        }

        // The init value is consumed by the let binding — the binding
        // now owns it and scope cleanup handles the eventual dec.
        init.mark_consumed();
        init.debug_assert_rc_handled("Stmt::Let");
        Ok(false)
    }

    /// Coerce a let-binding's initializer to match the declared type.
    ///
    /// Handles: unknown boxing, union wrapping, integer narrowing/widening,
    /// float promotion/demotion, and interface boxing. Returns the coerced
    /// value, its type, and whether a stack-allocated union was constructed.
    fn coerce_let_init(
        &mut self,
        init: &CompiledValue,
        declared_type_id_opt: Option<TypeId>,
    ) -> CodegenResult<(Value, TypeId, bool)> {
        let mut is_stack_union = false;

        let (mut final_value, mut final_type_id) =
            if let Some(declared_type_id) = declared_type_id_opt {
                let arena = self.arena();
                let is_declared_union = arena.is_union(declared_type_id);
                let is_declared_numeric = arena.is_numeric(declared_type_id);
                let is_declared_interface = arena.is_interface(declared_type_id);
                let is_declared_unknown = arena.is_unknown(declared_type_id);

                if is_declared_unknown && !self.arena().is_unknown(init.type_id) {
                    // Box value to unknown type (TaggedValue)
                    let boxed = self.box_to_unknown(*init)?;
                    (boxed.value, boxed.type_id)
                } else if is_declared_union && !self.arena().is_union(init.type_id) {
                    let wrapped = self.construct_union_id(*init, declared_type_id)?;
                    is_stack_union = true;
                    (wrapped.value, wrapped.type_id)
                } else if is_declared_numeric && init.type_id.is_numeric() {
                    let coerced = self.coerce_to_type(*init, declared_type_id)?;
                    (coerced.value, coerced.type_id)
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
            // RuntimeIterator is an internal concrete type that implements Iterator
            // dispatch directly via runtime_iterator_method; skip interface boxing.
            let is_runtime_iterator = arena.is_runtime_iterator(final_type_id);

            if is_declared_interface && !is_final_interface && !is_runtime_iterator {
                let arena = self.arena();
                let cranelift_ty = type_id_to_cranelift(final_type_id, arena, self.ptr_type());
                let boxed = self.box_interface_value(
                    CompiledValue::new(final_value, cranelift_ty, final_type_id),
                    declared_type_id,
                )?;
                final_value = boxed.value;
                final_type_id = boxed.type_id;
            }
        }

        Ok((final_value, final_type_id, is_stack_union))
    }

    /// Compile a return statement.
    fn return_stmt(&mut self, ret: &ReturnStmt) -> CodegenResult<bool> {
        let return_type_id = self.return_type;
        if let Some(value) = &ret.value {
            let mut compiled = self.expr(value)?;
            compiled.type_id = self.try_substitute_type(compiled.type_id);

            // RC bookkeeping for return values:
            // - RC local variable: skip its cleanup (ownership transfers to caller)
            // - Composite RC local (struct/array/tuple with RC fields): skip its
            //   cleanup too — the caller takes ownership of the whole composite
            //   and its scope-exit cleanup will handle the RC fields.
            // - Non-RC local / borrow (index, field, loop var): rc_inc for caller
            // - Fresh allocation (call, literal): already owned, no action needed
            let skip_var = if let ExprKind::Identifier(sym) = &value.kind
                && let Some((var, _)) = self.vars.get(sym)
                && (self.rc_scopes.is_rc_local(*var)
                    || self.rc_scopes.is_composite_rc_local(*var)
                    || self.rc_scopes.is_union_rc_local(*var))
            {
                Some(*var)
            } else {
                None
            };
            if skip_var.is_none() && compiled.is_borrowed() {
                if self.rc_state(compiled.type_id).needs_cleanup() {
                    self.emit_rc_inc_for_type(compiled.value, compiled.type_id)?;
                } else if let Some(rc_tags) = self.rc_state(compiled.type_id).union_variants() {
                    // Union with RC variants (e.g. [i64]?): rc_inc the inner
                    // payload so the caller's copy owns its own reference.
                    // Without this, the caller's consume_rc_args and the
                    // return value's scope-exit cleanup both rc_dec the same
                    // inner value, causing a double-free.
                    self.emit_union_rc_inc(compiled.value, rc_tags)?;
                }
            }
            self.emit_rc_cleanup_all_scopes(skip_var)?;

            // The return value is consumed — ownership transfers to the caller.
            compiled.mark_consumed();
            compiled.debug_assert_rc_handled("Stmt::Return");

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
                let tag_val = self.iconst_cached(types::I64, FALLIBLE_SUCCESS_TAG);

                if is_wide_fallible(ret_type_id, self.arena()) {
                    // i128 success: return (tag, low, high) in 3 registers
                    let (low, high) = split_i128_for_storage(self.builder, compiled.value);
                    self.builder.ins().return_(&[tag_val, low, high]);
                } else {
                    // Convert payload to i64 for uniform representation
                    let payload_val = convert_to_i64_for_storage(self.builder, &compiled);
                    self.builder.ins().return_(&[tag_val, payload_val]);
                }
            } else if let Some(ret_type_id) = return_type_id
                && self.is_small_struct_return(ret_type_id)
            {
                self.emit_small_struct_return(compiled.value, ret_type_id);
            } else if let Some(ret_type_id) = return_type_id
                && self.is_sret_struct_return(ret_type_id)
            {
                self.emit_sret_struct_return(compiled.value, ret_type_id);
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

    /// Find the union variant tag for a value's type, with integer widening/narrowing fallback.
    /// Returns (tag_index, possibly_coerced_value, actual_type_id).
    pub(crate) fn find_union_variant_tag(
        &mut self,
        value: &CompiledValue,
        union_type_id: TypeId,
        variants: &[TypeId],
    ) -> CodegenResult<(usize, Value, TypeId)> {
        let resolved_value_type_id = self.try_substitute_type(value.type_id);

        // Direct type match
        if let Some(pos) = variants.iter().position(|&v| v == resolved_value_type_id) {
            return Ok((pos, value.value, resolved_value_type_id));
        }

        // Try to find a compatible integer type for widening/narrowing
        let arena = self.arena();
        let value_is_integer = arena.is_integer(resolved_value_type_id);

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
                    sextend_const(self.builder, target_ty, value.value)
                } else {
                    value.value
                };
                Ok((pos, actual, variant_type_id))
            }
            None => {
                let expected = variants
                    .iter()
                    .map(|&variant| self.arena().display_basic(variant))
                    .collect::<Vec<_>>()
                    .join(" | ");
                let found = if let Some(name_id) = self.arena().unwrap_type_param(value.type_id) {
                    format!("{} ({:?})", self.name_table().display(name_id), name_id)
                } else {
                    self.arena().display_basic(resolved_value_type_id)
                };
                let subs = self
                    .substitutions
                    .map(|m| {
                        m.iter()
                            .map(|(k, v)| {
                                format!(
                                    "{} ({:?}) -> {}",
                                    self.name_table().display(*k),
                                    k,
                                    self.arena().display_basic(*v)
                                )
                            })
                            .collect::<Vec<_>>()
                            .join(", ")
                    })
                    .unwrap_or_else(|| "<none>".to_string());
                Err(CodegenError::type_mismatch(
                    "union variant",
                    format!("compatible type ({expected})"),
                    format!(
                        "{found} (union={}, substitutions={subs})",
                        self.arena().display_basic(union_type_id)
                    ),
                ))
            }
        }
    }

    /// Wrap a value in a union representation.
    pub fn construct_union_id(
        &mut self,
        value: CompiledValue,
        union_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let arena = self.arena();
        let variants = arena.unwrap_union(union_type_id).ok_or_else(|| {
            CodegenError::type_mismatch("union construction", "union type", "non-union")
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
            self.find_union_variant_tag(&value, union_type_id, &variants)?;

        let union_size = self.type_size(union_type_id);
        let slot = self.alloc_stack(union_size);

        let tag_val = self.iconst_cached(types::I8, tag as i64);
        self.builder.ins().stack_store(tag_val, slot, 0);

        // Store is_rc flag at offset 1 (matches heap union layout used by
        // construct_union_heap_id). copy_union_to_heap reads this byte to
        // decide whether to rc_inc the payload when promoting to the heap.
        let is_rc = self.rc_state(actual_type_id).needs_cleanup();
        let is_rc_val = self.iconst_cached(types::I8, is_rc as i64);
        self.builder
            .ins()
            .stack_store(is_rc_val, slot, union_layout::IS_RC_OFFSET);

        if union_size > union_layout::TAG_ONLY_SIZE {
            // Initialize payload bytes for payload-carrying unions. Sentinel variants
            // don't carry data, but zeroing avoids undefined behavior when generic
            // cleanup/copy paths read the payload word.
            let payload = if self.arena().is_sentinel(actual_type_id) {
                self.iconst_cached(types::I64, 0)
            } else {
                actual_value
            };
            self.builder
                .ins()
                .stack_store(payload, slot, union_layout::PAYLOAD_OFFSET);
        }

        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
        Ok(CompiledValue::new(ptr, ptr_type, union_type_id))
    }

    /// Recursively compile a destructuring pattern, binding variables for the values extracted
    fn compile_destructure_pattern(
        &mut self,
        pattern: &Pattern,
        value: Value,
        ty_id: TypeId,
    ) -> CodegenResult<()> {
        match &pattern.kind {
            PatternKind::Identifier { name } => {
                let cr_type = self.cranelift_type(ty_id);
                let var = self.builder.declare_var(cr_type);
                self.builder.def_var(var, value);
                self.vars.insert(*name, (var, ty_id));

                // Extracted elements borrow from the parent composite.
                // RC_inc + register so scope-exit dec balances the borrow.
                if self.rc_scopes.has_active_scope() && self.rc_state(ty_id).needs_cleanup() {
                    self.emit_rc_inc_for_type(value, ty_id)?;
                    let drop_flag = self.register_rc_local(var, ty_id);
                    crate::rc_cleanup::set_drop_flag_live(self, drop_flag);
                }
            }
            PatternKind::Wildcard => {
                // Wildcard - nothing to bind
            }
            PatternKind::Tuple { elements } => {
                let arena = self.arena();

                // Try tuple first
                if let Some(elem_type_ids) = arena.unwrap_tuple(ty_id).cloned() {
                    let (_, offsets) = self.tuple_layout(&elem_type_ids);
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
                        self.get_instance_field(value, slot, field_type_id)?
                    };

                    let var = self.builder.declare_var(converted.ty);
                    self.builder.def_var(var, converted.value);
                    self.vars
                        .insert(field_pattern.binding, (var, field_type_id));
                }
            }
            PatternKind::Literal(_)
            | PatternKind::Type { .. }
            | PatternKind::Val { .. }
            | PatternKind::Success { .. }
            | PatternKind::Error { .. } => {}
        }
        Ok(())
    }

    /// Compile module destructuring - registers bindings for module exports.
    /// No runtime code is generated; bindings are used at compile time for calls.
    fn compile_module_destructure(
        &mut self,
        fields: &[vole_frontend::ast::RecordFieldPattern],
        module_info: &vole_sema::type_arena::InternedModule,
    ) -> CodegenResult<()> {
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

            let Some(export_type_id) = export_type_id else {
                return Err(CodegenError::not_found("module export", export_name_str));
            };
            // Register the module binding: local_name -> (module_id, export_name, type_id)
            self.module_bindings.insert(
                field_pattern.binding,
                (module_info.module_id, export_name, export_type_id),
            );
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
    fn raise_stmt(&mut self, raise_stmt: &RaiseStmt) -> CodegenResult<bool> {
        // Get the current function's return type - must be Fallible
        let return_type_id = self.return_type.ok_or_else(|| {
            CodegenError::internal(
                "raise statement used outside of a function with declared return type",
            )
        })?;

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
        let error_tag = self
            .error_tag_for(error_type_id, raise_stmt.error_name)
            .ok_or_else(|| {
                CodegenError::not_found(
                    "error type",
                    self.interner().resolve(raise_stmt.error_name),
                )
            })?;

        // Resolve the error TypeDefId and get its fields
        let error_type_def_id =
            self.resolve_raise_error_type_def(error_type_id, raise_stmt.error_name)?;

        let error_fields: Vec<_> = self
            .query()
            .fields_on_type(error_type_def_id)
            .map(|field_id| self.query().get_field(field_id).clone())
            .collect();

        // Create the tag value
        let tag_val = self.iconst_cached(types::I64, error_tag);

        // Build the error payload from field definitions and initializers
        let payload_val = self.build_raise_payload(&error_fields, &raise_stmt.fields)?;

        // RC cleanup: like return, clean up all RC locals before exiting.
        self.emit_rc_cleanup_all_scopes(None)?;

        // Return from the function with (tag, payload) or (tag, payload, 0) for wide fallible
        if is_wide_fallible(return_type_id, self.arena()) {
            // Wide fallible: return 3 values (tag, payload, 0) for consistency
            // with the 3-register convention for i128 success values
            let zero = self.iconst_cached(types::I64, 0);
            self.builder.ins().return_(&[tag_val, payload_val, zero]);
        } else {
            self.builder.ins().return_(&[tag_val, payload_val]);
        }

        // Raise always terminates the current block
        Ok(true)
    }

    /// Resolve the TypeDefId for the named error type from a fallible error type.
    ///
    /// Handles both single error types and unions of error types by matching
    /// the error name against the type definitions.
    fn resolve_raise_error_type_def(
        &self,
        error_type_id: TypeId,
        error_name_sym: Symbol,
    ) -> CodegenResult<vole_identity::TypeDefId> {
        let raise_error_name = self.interner().resolve(error_name_sym);
        let arena = self.arena();
        let name_table = self.name_table();
        let result = if let Some(type_def_id) = arena.unwrap_error(error_type_id) {
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
        };
        result.ok_or_else(|| {
            CodegenError::not_found("error type info", self.interner().resolve(error_name_sym))
        })
    }

    /// Build the error payload value for a raise statement.
    ///
    /// Layout matches the runtime convention:
    /// - 0 fields: payload is 0
    /// - 1 field (non-wide): payload is the field value directly (inline)
    /// - 1 field (i128): payload is a pointer to stack-allocated i128 data
    /// - 2+ fields: payload is a pointer to field data (i128 fields use 16 bytes)
    fn build_raise_payload(
        &mut self,
        error_fields: &[vole_sema::entity_defs::FieldDef],
        raise_fields: &[vole_frontend::ast::StructFieldInit],
    ) -> CodegenResult<Value> {
        if error_fields.is_empty() {
            // No fields - payload is 0
            return Ok(self.iconst_cached(types::I64, 0));
        }

        if error_fields.len() == 1 && !crate::types::is_wide_type(error_fields[0].ty, self.arena())
        {
            // Single non-wide field - store inline as payload value
            let field_def = &error_fields[0];
            let field_name = self
                .name_table()
                .last_segment_str(field_def.name_id)
                .unwrap_or_default();
            let field_init = raise_fields
                .iter()
                .find(|f| self.interner().resolve(f.name) == field_name)
                .ok_or_else(|| CodegenError::not_found("raise field", &field_name))?;

            let mut field_value = self.expr(&field_init.value)?;
            // RC: if the field value is a borrow (e.g., a parameter variable),
            // inc it so the caller gets an owned reference in the error payload.
            if self.rc_state(field_value.type_id).needs_cleanup() && field_value.is_borrowed() {
                self.emit_rc_inc_for_type(field_value.value, field_value.type_id)?;
            }
            // The field value is consumed into the error payload.
            field_value.mark_consumed();
            field_value.debug_assert_rc_handled("Stmt::Raise (single field)");
            return Ok(convert_to_i64_for_storage(self.builder, &field_value));
        }

        // Multiple fields (or single i128 field) - allocate on stack and store field values.
        // i128 fields use 16 bytes (2 slots), all others use 8 bytes (1 slot).
        let error_payload_size: u32 = error_fields
            .iter()
            .map(|f| crate::types::field_byte_size(f.ty, self.arena()))
            .sum();
        let slot = self.alloc_stack(error_payload_size);

        // Store each field value at the appropriate offset
        let mut field_offset: i32 = 0;
        for field_def in error_fields {
            let field_name = self
                .name_table()
                .last_segment_str(field_def.name_id)
                .unwrap_or_default();
            let field_init = raise_fields
                .iter()
                .find(|f| self.interner().resolve(f.name) == field_name)
                .ok_or_else(|| CodegenError::not_found("raise field", &field_name))?;

            let mut field_value = self.expr(&field_init.value)?;
            // RC: inc borrowed field values for the error payload
            if self.rc_state(field_value.type_id).needs_cleanup() && field_value.is_borrowed() {
                self.emit_rc_inc_for_type(field_value.value, field_value.type_id)?;
            }
            // The field value is consumed into the error payload.
            field_value.mark_consumed();
            field_value.debug_assert_rc_handled("Stmt::Raise (multi field)");
            let bytes_stored = store_value_to_stack(self.builder, &field_value, slot, field_offset);
            field_offset += bytes_stored;
        }

        let ptr_type = self.ptr_type();
        Ok(self.builder.ins().stack_addr(ptr_type, slot, 0))
    }
}
