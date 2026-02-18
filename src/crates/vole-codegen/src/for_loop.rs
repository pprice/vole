// src/codegen/for_loop.rs
//
// For-loop compilation - impl Cg methods.
// Extracted from stmt.rs for module organization.

use cranelift::prelude::*;

use crate::IntrinsicKey;
use crate::RuntimeKey;
use crate::errors::CodegenResult;
use crate::types::CompiledValue;
use vole_frontend::{self, Stmt};
use vole_sema::type_arena::TypeId;

use super::context::Cg;

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
    /// Compile a for loop over a range.
    ///
    /// Uses an optimized 3-block structure (header, body, exit) when the loop body
    /// doesn't contain `continue` statements. For loops with `continue`, uses the
    /// standard 4-block structure (header, body, continue, exit) to ensure the
    /// counter is incremented before jumping back to header.
    pub(crate) fn for_range(
        &mut self,
        for_stmt: &vole_frontend::ast::ForStmt,
        range: &vole_frontend::ast::RangeExpr,
    ) -> CodegenResult<bool> {
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
        for_stmt: &vole_frontend::ast::ForStmt,
        range: &vole_frontend::ast::RangeExpr,
        var: Variable,
        end_val: Value,
    ) -> CodegenResult<bool> {
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
        self.emit_brif(cmp, body_block, exit_block);

        // Body: compile loop body, then increment and loop back
        self.builder.switch_to_block(body_block);
        // Register loop context - continue jumps to header (but there's no continue in this path)
        let rc_depth = self.rc_scope_depth();
        self.cf.push_loop(exit_block, header, rc_depth);
        // Push a per-iteration RC scope so temps are cleaned each iteration
        self.push_rc_scope();
        let terminated = self.block(&for_stmt.body)?;
        self.cf.pop_loop();

        if !terminated {
            // Emit per-iteration cleanup before the back-edge jump
            self.pop_rc_scope_with_cleanup(None)?;
            // Inline the counter increment at end of body
            let current = self.builder.use_var(var);
            let next = self.builder.ins().iadd_imm(current, 1);
            self.builder.def_var(var, next);
            self.builder.ins().jump(header, &[]);
        } else {
            // Body terminated — pop scope to keep stack balanced
            self.rc_scopes.pop_scope();
        }

        // Seal header and body now that their predecessors are known.
        // Exit block is NOT sealed - see finalize_for_loop for explanation.
        self.builder.switch_to_block(exit_block);
        self.builder.seal_block(header);
        self.builder.seal_block(body_block);

        Ok(false)
    }

    /// Standard for_range with 4 blocks (header, body, continue, exit).
    ///
    /// Used when the loop body contains `continue` statements, which need to
    /// jump to the continue block to increment the counter before looping.
    fn for_range_with_continue(
        &mut self,
        for_stmt: &vole_frontend::ast::ForStmt,
        range: &vole_frontend::ast::RangeExpr,
        var: Variable,
        end_val: Value,
    ) -> CodegenResult<bool> {
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
        self.emit_brif(cmp, body_block, exit_block);

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
    pub(crate) fn for_array(
        &mut self,
        for_stmt: &vole_frontend::ast::ForStmt,
    ) -> CodegenResult<bool> {
        let arr = self.expr(&for_stmt.iterable)?;

        // Track owned iterable temporaries in a dedicated scope so they are
        // cleaned up on both normal loop exit and early returns from the body.
        self.push_rc_scope();
        if arr.is_owned() && self.rc_state(arr.type_id).needs_cleanup() {
            let tracked_var = self.builder.declare_var(self.cranelift_type(arr.type_id));
            self.builder.def_var(tracked_var, arr.value);
            let drop_flag = self.register_rc_local(tracked_var, arr.type_id);
            crate::rc_cleanup::set_drop_flag_live(self.builder, drop_flag);
        }

        // Get element type using arena method
        let elem_type_id = self
            .arena()
            .unwrap_array(arr.type_id)
            .unwrap_or_else(|| self.arena().i64());
        let (elem_is_i128, elem_is_f128) = {
            let arena = self.arena();
            (elem_type_id == arena.i128(), elem_type_id == arena.f128())
        };

        let len_val = self
            .call_compiler_intrinsic_key_with_line(
                IntrinsicKey::from("array_len"),
                &[arr.value],
                TypeId::I64,
                0,
            )?
            .value;

        let idx_var = self.builder.declare_var(types::I64);
        let zero = self.builder.ins().iconst(types::I64, 0);
        self.builder.def_var(idx_var, zero);

        // Declare the element variable with its correct Cranelift type.
        // ArrayGetValue always returns i64, but the element may be a smaller
        // type (e.g. bool -> i8, i32, etc.) so we must narrow after the call.
        let elem_cr_type = self.cranelift_type(elem_type_id);
        let elem_var = self.builder.declare_var(elem_cr_type);
        let elem_zero = if elem_cr_type == types::F64 {
            self.builder.ins().f64const(0.0)
        } else if elem_cr_type == types::F32 {
            self.builder.ins().f32const(0.0)
        } else if elem_cr_type == types::F128 {
            let zero_bits = self.builder.ins().sextend(types::I128, zero);
            self.builder
                .ins()
                .bitcast(types::F128, MemFlags::new(), zero_bits)
        } else if elem_cr_type == types::I128 {
            self.builder.ins().sextend(types::I128, zero)
        } else if elem_cr_type.is_int() && elem_cr_type.bits() < 64 {
            self.builder.ins().iconst(elem_cr_type, 0)
        } else {
            zero
        };
        self.builder.def_var(elem_var, elem_zero);
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
        self.emit_brif(cmp, body_block, exit_block);

        self.builder.switch_to_block(body_block);

        let current_idx = self.builder.use_var(idx_var);
        let elem_ptr = self.dynamic_array_elem_ptr_unchecked(arr.value, current_idx);
        let value_offset = std::mem::offset_of!(vole_runtime::value::TaggedValue, value) as i32;
        let elem_val = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), elem_ptr, value_offset);
        let elem_val = if self.arena().is_union(elem_type_id) {
            if self.union_array_prefers_inline_storage(elem_type_id) {
                let tag_offset = std::mem::offset_of!(vole_runtime::value::TaggedValue, tag) as i32;
                let elem_tag =
                    self.builder
                        .ins()
                        .load(types::I64, MemFlags::new(), elem_ptr, tag_offset);
                self.decode_dynamic_array_union_element(elem_tag, elem_val, elem_type_id)
                    .value
            } else {
                self.copy_union_heap_to_stack(elem_val, elem_type_id).value
            }
        } else if elem_is_i128 || elem_is_f128 {
            let wide_bits = self.call_runtime(RuntimeKey::Wide128Unbox, &[elem_val])?;
            if elem_is_f128 {
                self.builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), wide_bits)
            } else {
                wide_bits
            }
        } else if elem_cr_type.is_int() && elem_cr_type.bits() < 64 {
            // Narrow the i64 runtime value to the element's actual Cranelift type.
            self.builder.ins().ireduce(elem_cr_type, elem_val)
        } else if elem_cr_type == types::F64 {
            self.builder
                .ins()
                .bitcast(types::F64, MemFlags::new(), elem_val)
        } else if elem_cr_type == types::F32 {
            let i32_val = self.builder.ins().ireduce(types::I32, elem_val);
            self.builder
                .ins()
                .bitcast(types::F32, MemFlags::new(), i32_val)
        } else {
            elem_val
        };
        self.builder.def_var(elem_var, elem_val);

        self.compile_loop_body(&for_stmt.body, exit_block, continue_block)?;

        self.builder.switch_to_block(continue_block);
        let current_idx = self.builder.use_var(idx_var);
        let next_idx = self.builder.ins().iadd_imm(current_idx, 1);
        self.builder.def_var(idx_var, next_idx);
        self.builder.ins().jump(header, &[]);

        self.finalize_for_loop(header, body_block, continue_block, exit_block);

        self.pop_rc_scope_with_cleanup(None)?;

        Ok(false)
    }

    /// Check if a type is an Iterator<T> type using TypeId
    pub(crate) fn is_iterator_type_id(&self, ty: TypeId) -> bool {
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
    pub(crate) fn for_iterator(
        &mut self,
        for_stmt: &vole_frontend::ast::ForStmt,
    ) -> CodegenResult<bool> {
        let mut iter = self.expr(&for_stmt.iterable)?;

        // Get element type using arena methods
        let (elem_type_id, is_interface_iter) = {
            let arena = self.arena();
            if let Some(elem_id) = arena.unwrap_runtime_iterator(iter.type_id) {
                (elem_id, false)
            } else if let Some((_, type_args)) = arena.unwrap_interface(iter.type_id) {
                (
                    type_args.first().copied().unwrap_or_else(|| arena.i64()),
                    true,
                )
            } else {
                (arena.i64(), false)
            }
        };

        // For interface-boxed iterators (user-defined Iterator<T> implementations),
        // wrap in an RcIterator via vole_interface_iter so the native loop dispatch works.
        if is_interface_iter {
            let wrapped = self.call_runtime(RuntimeKey::InterfaceIter, &[iter.value])?;
            // vole_interface_iter rc_inc'd the data_ptr inside the boxed interface,
            // so the iterator now owns its own reference. Release the caller's
            // reference to the boxed interface data_ptr to avoid leaking it.
            self.consume_rc_value(&mut iter)?;
            // Track as RuntimeIterator<T> so loop cleanup can register and release
            // it like any other RC temporary.
            let runtime_iter_type_id = self
                .arena()
                .lookup_runtime_iterator(elem_type_id)
                .unwrap_or(TypeId::STRING);
            iter = CompiledValue::owned(wrapped, types::I64, runtime_iter_type_id);
        }

        // Track owned iterator temporaries in a dedicated scope so they are
        // cleaned up even if the loop body returns early.
        self.push_rc_scope();
        if iter.is_owned() && self.rc_state(iter.type_id).needs_cleanup() {
            let tracked_var = self.builder.declare_var(self.cranelift_type(iter.type_id));
            self.builder.def_var(tracked_var, iter.value);
            let drop_flag = self.register_rc_local(tracked_var, iter.type_id);
            crate::rc_cleanup::set_drop_flag_live(self.builder, drop_flag);
        }

        // Create a stack slot for the out_value parameter
        let slot_data = self.alloc_stack(8);
        let ptr_type = self.ptr_type();
        let slot_addr = self.builder.ins().stack_addr(ptr_type, slot_data, 0);

        // Initialize element variable with its correct Cranelift type.
        // ArrayIterNext returns i64, but the element may be a different type
        // (e.g. f64, f32, bool) so we must narrow/bitcast after the call,
        // matching what for_array does.
        let elem_cr_type = self.cranelift_type(elem_type_id);
        let elem_var = self.builder.declare_var(elem_cr_type);
        let zero_i64 = self.builder.ins().iconst(types::I64, 0);
        let elem_zero = if elem_cr_type == types::F64 {
            self.builder.ins().f64const(0.0)
        } else if elem_cr_type == types::F32 {
            self.builder.ins().f32const(0.0)
        } else if elem_cr_type == types::F128 {
            let zero_bits = self.builder.ins().sextend(types::I128, zero_i64);
            self.builder
                .ins()
                .bitcast(types::F128, MemFlags::new(), zero_bits)
        } else if elem_cr_type == types::I128 {
            self.builder.ins().sextend(types::I128, zero_i64)
        } else if elem_cr_type.is_int() && elem_cr_type.bits() < 64 {
            self.builder.ins().iconst(elem_cr_type, 0)
        } else {
            zero_i64
        };
        self.builder.def_var(elem_var, elem_zero);
        self.vars
            .insert(for_stmt.var_name, (elem_var, elem_type_id));

        let header = self.builder.create_block();
        let body_block = self.builder.create_block();
        let continue_block = self.builder.create_block();
        let exit_block = self.builder.create_block();

        self.builder.ins().jump(header, &[]);

        // Header: call iter_next, check result
        self.builder.switch_to_block(header);
        let has_value = self.call_runtime(RuntimeKey::ArrayIterNext, &[iter.value, slot_addr])?;
        let is_done = self.builder.ins().icmp_imm(IntCC::Equal, has_value, 0);
        self.emit_brif(is_done, exit_block, body_block);

        // Body: load value from stack slot, narrow to element type, run body
        self.builder.switch_to_block(body_block);
        let raw_val = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), slot_addr, 0);
        // Convert from i64 storage to the element's actual Cranelift type
        let elem_val = if elem_type_id == self.arena().i128() || elem_type_id == self.arena().f128()
        {
            let wide_bits = self.call_runtime(RuntimeKey::Wide128Unbox, &[raw_val])?;
            if elem_type_id == self.arena().f128() {
                self.builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), wide_bits)
            } else {
                wide_bits
            }
        } else if elem_cr_type == types::F64 {
            self.builder
                .ins()
                .bitcast(types::F64, MemFlags::new(), raw_val)
        } else if elem_cr_type == types::F32 {
            let i32_val = self.builder.ins().ireduce(types::I32, raw_val);
            self.builder
                .ins()
                .bitcast(types::F32, MemFlags::new(), i32_val)
        } else if elem_cr_type.is_int() && elem_cr_type.bits() < 64 {
            self.builder.ins().ireduce(elem_cr_type, raw_val)
        } else {
            raw_val
        };
        self.builder.def_var(elem_var, elem_val);

        self.compile_loop_body(&for_stmt.body, exit_block, continue_block)?;

        // Continue: jump back to header
        self.builder.switch_to_block(continue_block);
        self.builder.ins().jump(header, &[]);

        self.finalize_for_loop(header, body_block, continue_block, exit_block);

        self.pop_rc_scope_with_cleanup(None)?;

        Ok(false)
    }

    /// Compile a for loop over a string (iterating characters)
    pub(crate) fn for_string(
        &mut self,
        for_stmt: &vole_frontend::ast::ForStmt,
    ) -> CodegenResult<bool> {
        // Compile the string expression
        let string_val = self.expr(&for_stmt.iterable)?;

        // Create a string chars iterator from the string
        let iter_val = self.call_runtime(RuntimeKey::StringCharsIter, &[string_val.value])?;

        // Track owned temporaries in a dedicated scope so early returns from
        // the loop body still clean up the iterator and source string.
        self.push_rc_scope();
        if string_val.is_owned() && self.rc_state(string_val.type_id).needs_cleanup() {
            let tracked_string = self
                .builder
                .declare_var(self.cranelift_type(string_val.type_id));
            self.builder.def_var(tracked_string, string_val.value);
            let drop_flag = self.register_rc_local(tracked_string, string_val.type_id);
            crate::rc_cleanup::set_drop_flag_live(self.builder, drop_flag);
        }
        let iter_type_id = self
            .arena()
            .lookup_runtime_iterator(TypeId::STRING)
            .unwrap_or(TypeId::STRING);
        let tracked_iter = self.builder.declare_var(self.cranelift_type(iter_type_id));
        self.builder.def_var(tracked_iter, iter_val);
        let iter_drop_flag = self.register_rc_local(tracked_iter, iter_type_id);
        crate::rc_cleanup::set_drop_flag_live(self.builder, iter_drop_flag);

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
        let has_value = self.call_runtime(RuntimeKey::ArrayIterNext, &[iter_val, slot_addr])?;
        let is_done = self.builder.ins().icmp_imm(IntCC::Equal, has_value, 0);
        self.emit_brif(is_done, exit_block, body_block);

        // Body: load value from stack slot, run body
        self.builder.switch_to_block(body_block);
        let elem_val = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), slot_addr, 0);
        self.builder.def_var(elem_var, elem_val);

        self.compile_loop_body(&for_stmt.body, exit_block, continue_block)?;

        // Continue: free the current iteration's char string before looping back.
        // Each iteration produces a new owned string from string_chars_next.
        self.builder.switch_to_block(continue_block);
        let cur_elem = self.builder.use_var(elem_var);
        self.call_runtime_void(RuntimeKey::RcDec, &[cur_elem])?;
        self.builder.ins().jump(header, &[]);

        self.finalize_for_loop(header, body_block, continue_block, exit_block);

        // No dangling char string on exit: the exit branch is taken when
        // iter_next returns 0 (no new value loaded), and the continue block
        // already freed the previous iteration's char string.

        self.pop_rc_scope_with_cleanup(None)?;

        Ok(false)
    }
}
