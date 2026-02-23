// src/codegen/vir_for_loop.rs
//
// VIR for-loop compilation - impl Cg methods.
// Handles lowered VIR `VirStmt::For` nodes.

use cranelift::prelude::*;
use smallvec::smallvec;

use crate::IntrinsicKey;
use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};
use vole_sema::type_arena::TypeId;
use vole_vir::stmt::{VirFor, VirIterKind};
use vole_vir::{VirBody, VirExpr, VirStmt};

use super::context::Cg;

// ---------------------------------------------------------------------------
// Continue-detection helpers
// ---------------------------------------------------------------------------

/// Check if a VIR body contains a `continue` statement (recursively).
///
/// Used by the optimized range loop to decide between a 3-block (no continue)
/// and 4-block (with continue) structure.
fn vir_body_contains_continue(body: &VirBody) -> bool {
    body.stmts.iter().any(vir_stmt_contains_continue)
}

/// Check if a VIR statement contains a `continue` (recursively).
fn vir_stmt_contains_continue(stmt: &VirStmt) -> bool {
    match stmt {
        VirStmt::Continue => true,
        VirStmt::Expr { value } => vir_expr_contains_continue(value),
        // Nested loops don't affect the outer loop's continue.
        VirStmt::While { .. } | VirStmt::For(_) => false,
        VirStmt::Let { .. }
        | VirStmt::LetTuple { .. }
        | VirStmt::Assign { .. }
        | VirStmt::Return { .. }
        | VirStmt::Break
        | VirStmt::Raise { .. }
        | VirStmt::RcInc { .. }
        | VirStmt::RcDec { .. }
        | VirStmt::Noop => false,
    }
}

/// Check if a VIR expression contains a `continue` in nested if/block bodies.
fn vir_expr_contains_continue(expr: &VirExpr) -> bool {
    match expr {
        VirExpr::If {
            then_body,
            else_body,
            ..
        } => {
            vir_body_contains_continue(then_body)
                || else_body.as_ref().is_some_and(vir_body_contains_continue)
        }
        VirExpr::Block { stmts, .. } => stmts.iter().any(vir_stmt_contains_continue),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// VIR for-loop compilation
// ---------------------------------------------------------------------------

impl Cg<'_, '_, '_> {
    /// Dispatch a VIR for-loop to the correct compilation strategy.
    pub(crate) fn compile_vir_for(&mut self, vir_for: &VirFor) -> CodegenResult<bool> {
        match &vir_for.kind {
            VirIterKind::Range => self.compile_vir_for_range(vir_for),
            VirIterKind::Array { .. } => self.compile_vir_for_array(vir_for),
            VirIterKind::String
            | VirIterKind::IteratorInterface { .. }
            | VirIterKind::CustomIterator { .. }
            | VirIterKind::CustomIterable { .. } => self.compile_vir_for_runtime_iter(vir_for),
        }
    }

    // ===== VIR Range loops =====

    /// Compile a VIR for-loop over a range.
    ///
    /// Expects `vir_for.iterable` to be a `VirExpr::Range { start, end, inclusive }`.
    /// Uses an optimized 3-block structure when the body has no `continue`.
    fn compile_vir_for_range(&mut self, vir_for: &VirFor) -> CodegenResult<bool> {
        let VirExpr::Range {
            start,
            end,
            inclusive,
        } = vir_for.iterable.as_ref()
        else {
            return Err(CodegenError::internal(
                "VIR for range: iterable is not a Range expression",
            ));
        };

        let start_val = self.compile_vir_expr(start)?;
        let end_val = self.compile_vir_expr(end)?;

        let var = self.builder.declare_var(types::I64);
        self.builder.def_var(var, start_val.value);
        self.vars.insert(vir_for.var_name, (var, TypeId::I64));

        let has_continue = vir_body_contains_continue(&vir_for.body);
        if has_continue {
            self.vir_range_with_continue(vir_for, var, end_val.value, *inclusive)
        } else {
            self.vir_range_optimized(vir_for, var, end_val.value, *inclusive)
        }
    }

    /// Optimized VIR range loop with 3 blocks (header, body, exit).
    fn vir_range_optimized(
        &mut self,
        vir_for: &VirFor,
        var: Variable,
        end_val: Value,
        inclusive: bool,
    ) -> CodegenResult<bool> {
        let header = self.builder.create_block();
        let body_block = self.builder.create_block();
        let exit_block = self.builder.create_block();

        self.builder.ins().jump(header, &[]);

        self.switch_to_block(header);
        let current = self.builder.use_var(var);
        let cmp = if inclusive {
            self.builder
                .ins()
                .icmp(IntCC::SignedLessThanOrEqual, current, end_val)
        } else {
            self.builder
                .ins()
                .icmp(IntCC::SignedLessThan, current, end_val)
        };
        self.emit_brif(cmp, body_block, exit_block);

        self.switch_to_block(body_block);
        let rc_depth = self.rc_scope_depth();
        self.cf.push_loop(exit_block, header, rc_depth);
        self.push_rc_scope();
        let (terminated, _) = self.compile_vir_body(&vir_for.body)?;
        self.cf.pop_loop();

        if !terminated {
            self.pop_rc_scope_with_cleanup(None)?;
            let current = self.builder.use_var(var);
            let next = self.builder.ins().iadd_imm(current, 1);
            self.builder.def_var(var, next);
            self.builder.ins().jump(header, &[]);
        } else {
            self.rc_scopes.pop_scope();
        }

        self.switch_to_block(exit_block);
        self.builder.seal_block(header);
        self.builder.seal_block(body_block);

        Ok(false)
    }

    /// VIR range loop with 4 blocks (header, body, continue, exit).
    fn vir_range_with_continue(
        &mut self,
        vir_for: &VirFor,
        var: Variable,
        end_val: Value,
        inclusive: bool,
    ) -> CodegenResult<bool> {
        let header = self.builder.create_block();
        let body_block = self.builder.create_block();
        let continue_block = self.builder.create_block();
        let exit_block = self.builder.create_block();

        self.builder.ins().jump(header, &[]);

        self.switch_to_block(header);
        let current = self.builder.use_var(var);
        let cmp = if inclusive {
            self.builder
                .ins()
                .icmp(IntCC::SignedLessThanOrEqual, current, end_val)
        } else {
            self.builder
                .ins()
                .icmp(IntCC::SignedLessThan, current, end_val)
        };
        self.emit_brif(cmp, body_block, exit_block);

        self.switch_to_block(body_block);
        self.compile_vir_loop_body(&vir_for.body, exit_block, continue_block)?;

        self.switch_to_block(continue_block);
        let current = self.builder.use_var(var);
        let next = self.builder.ins().iadd_imm(current, 1);
        self.builder.def_var(var, next);
        self.builder.ins().jump(header, &[]);

        self.finalize_for_loop(header, body_block, continue_block, exit_block);

        Ok(false)
    }

    // ===== VIR Array loops =====

    /// Compile a VIR for-loop over an array using direct index-based access.
    fn compile_vir_for_array(&mut self, vir_for: &VirFor) -> CodegenResult<bool> {
        let VirIterKind::Array {
            elem_type: elem_type_id,
            union_storage,
        } = &vir_for.kind
        else {
            unreachable!("compile_vir_for_array called with non-Array kind");
        };
        let elem_type_id = *elem_type_id;
        let union_storage = *union_storage;

        let arr = self.compile_vir_expr(&vir_for.iterable)?;

        // Track owned iterable in a dedicated RC scope.
        self.push_rc_scope();
        if arr.is_owned() && self.rc_state(arr.type_id).needs_cleanup() {
            let tracked_var = self.builder.declare_var(self.cranelift_type(arr.type_id));
            self.builder.def_var(tracked_var, arr.value);
            let drop_flag = self.register_rc_local(tracked_var, arr.type_id);
            crate::rc_cleanup::set_drop_flag_live(self, drop_flag);
        }

        let len_val = self
            .call_compiler_intrinsic_key_with_line(
                IntrinsicKey::ArrayLen,
                &[arr.value],
                TypeId::I64,
                0,
            )?
            .value;

        let idx_var = self.builder.declare_var(types::I64);
        let zero = self.iconst_cached(types::I64, 0);
        self.builder.def_var(idx_var, zero);

        let elem_cr_type = self.cranelift_type(elem_type_id);
        let elem_var = self.builder.declare_var(elem_cr_type);
        let elem_zero = self.typed_zero(elem_cr_type);
        self.builder.def_var(elem_var, elem_zero);
        self.vars.insert(vir_for.var_name, (elem_var, elem_type_id));

        let header = self.builder.create_block();
        let body_block = self.builder.create_block();
        let continue_block = self.builder.create_block();
        let exit_block = self.builder.create_block();

        self.builder.ins().jump(header, &[]);

        self.switch_to_block(header);
        let current_idx = self.builder.use_var(idx_var);
        let cmp = self
            .builder
            .ins()
            .icmp(IntCC::SignedLessThan, current_idx, len_val);
        self.emit_brif(cmp, body_block, exit_block);

        self.switch_to_block(body_block);

        let current_idx = self.builder.use_var(idx_var);
        let elem_ptr = self.dynamic_array_elem_ptr_unchecked(arr.value, current_idx);
        let value_offset = std::mem::offset_of!(vole_runtime::value::TaggedValue, value) as i32;
        let elem_val = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), elem_ptr, value_offset);
        let elem_val = self.decode_array_elem(elem_val, elem_ptr, elem_type_id, union_storage)?;
        self.builder.def_var(elem_var, elem_val);

        self.compile_vir_loop_body(&vir_for.body, exit_block, continue_block)?;

        self.switch_to_block(continue_block);
        let current_idx = self.builder.use_var(idx_var);
        let next_idx = self.builder.ins().iadd_imm(current_idx, 1);
        self.builder.def_var(idx_var, next_idx);
        self.builder.ins().jump(header, &[]);

        self.finalize_for_loop(header, body_block, continue_block, exit_block);
        self.pop_rc_scope_with_cleanup(None)?;

        Ok(false)
    }

    // ===== VIR RuntimeIterator loops =====

    /// Compile a VIR for-loop over a runtime iterator (string, interface,
    /// custom iterator, or custom iterable).
    fn compile_vir_for_runtime_iter(&mut self, vir_for: &VirFor) -> CodegenResult<bool> {
        let (iter_val, elem_type_id, needs_elem_rc_dec) = self.setup_vir_runtime_iter(vir_for)?;

        let slot_data = self.alloc_stack(8);
        let ptr_type = self.ptr_type();
        let slot_addr = self.builder.ins().stack_addr(ptr_type, slot_data, 0);

        let elem_cr_type = self.cranelift_type(elem_type_id);
        let elem_var = self.builder.declare_var(elem_cr_type);
        let elem_zero = self.typed_zero(elem_cr_type);
        self.builder.def_var(elem_var, elem_zero);
        self.vars.insert(vir_for.var_name, (elem_var, elem_type_id));

        let header = self.builder.create_block();
        let body_block = self.builder.create_block();
        let continue_block = self.builder.create_block();
        let exit_block = self.builder.create_block();

        self.builder.ins().jump(header, &[]);

        self.switch_to_block(header);
        let has_value = self.call_runtime(RuntimeKey::ArrayIterNext, &[iter_val, slot_addr])?;
        self.emit_brif(has_value, body_block, exit_block);

        self.switch_to_block(body_block);
        let raw_val = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), slot_addr, 0);
        let elem_val = self.convert_iter_elem(raw_val, elem_type_id, elem_cr_type)?;
        self.builder.def_var(elem_var, elem_val);

        self.compile_vir_loop_body(&vir_for.body, exit_block, continue_block)?;

        self.switch_to_block(continue_block);
        if needs_elem_rc_dec {
            let cur_elem = self.builder.use_var(elem_var);
            self.call_runtime_void(RuntimeKey::RcDec, &[cur_elem])?;
        }
        self.builder.ins().jump(header, &[]);

        self.finalize_for_loop(header, body_block, continue_block, exit_block);
        self.pop_rc_scope_with_cleanup(None)?;

        Ok(false)
    }

    /// Evaluate the VIR iterable and convert it to a RuntimeIterator.
    ///
    /// Returns `(iter_value, elem_type_id, needs_elem_rc_dec)`.
    fn setup_vir_runtime_iter(&mut self, vir_for: &VirFor) -> CodegenResult<(Value, TypeId, bool)> {
        match &vir_for.kind {
            VirIterKind::String => {
                let string_val = self.compile_vir_expr(&vir_for.iterable)?;
                let iter_val =
                    self.call_runtime(RuntimeKey::StringCharsIter, &[string_val.value])?;
                let iter = self.make_runtime_iter_value(iter_val, TypeId::STRING);
                self.enter_iter_rc_scope(&iter, Some(&string_val));
                Ok((iter_val, TypeId::STRING, true))
            }
            VirIterKind::IteratorInterface { elem_type } => {
                let hint = *elem_type;
                let mut iter = self.compile_vir_expr(&vir_for.iterable)?;
                let (elem_type_id, is_interface_iter) = {
                    let arena = self.arena();
                    if let Some(elem_id) = arena.unwrap_runtime_iterator(iter.type_id) {
                        (elem_id, false)
                    } else if let Some((_, type_args)) = arena.unwrap_interface(iter.type_id) {
                        (type_args.first().copied().unwrap_or(hint), true)
                    } else {
                        (hint, false)
                    }
                };
                if is_interface_iter {
                    iter = self.wrap_interface_iter(iter, elem_type_id)?;
                }
                self.enter_iter_rc_scope(&iter, None);
                Ok((iter.value, elem_type_id, false))
            }
            VirIterKind::CustomIterator { elem_type } => {
                let elem_type_id = *elem_type;
                let iterable = self.compile_vir_expr(&vir_for.iterable)?;
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
                let boxed = self.box_interface_value(iterable, interface_type_id)?;
                let iter = self.wrap_interface_iter(boxed, elem_type_id)?;
                self.enter_iter_rc_scope(&iter, None);
                Ok((iter.value, elem_type_id, false))
            }
            VirIterKind::CustomIterable { elem_type } => {
                let elem_type_id = *elem_type;
                let iterable = self.compile_vir_expr(&vir_for.iterable)?;
                let iter_value = self.call_iterable_iter_method(&iterable, elem_type_id)?;
                let iter = self.wrap_interface_iter(iter_value, elem_type_id)?;
                self.enter_iter_rc_scope(&iter, None);
                Ok((iter.value, elem_type_id, false))
            }
            VirIterKind::Range | VirIterKind::Array { .. } => {
                unreachable!("Range/Array handled before setup_vir_runtime_iter")
            }
        }
    }
}
