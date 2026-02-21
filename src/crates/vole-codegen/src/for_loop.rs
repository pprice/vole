// src/codegen/for_loop.rs
//
// For-loop compilation - impl Cg methods.
// Extracted from stmt.rs for module organization.

use cranelift::prelude::*;
use smallvec::smallvec;

use crate::IntrinsicKey;
use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::CompiledValue;
use vole_frontend::{self, ExprKind, Stmt};
use vole_sema::IterableKind;
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
    /// Dispatch a for-loop to the correct compilation strategy based on sema's
    /// `IterableKind` annotation.
    pub(crate) fn compile_for_stmt(
        &mut self,
        for_stmt: &vole_frontend::ast::ForStmt,
    ) -> CodegenResult<bool> {
        // Range literals can be detected syntactically — they don't need sema annotation
        if let ExprKind::Range(range) = &for_stmt.iterable.kind {
            return self.for_range(for_stmt, range);
        }

        let kind = self.get_iterable_kind(for_stmt.iterable.id).unwrap_or({
            // Fallback for invalid/error types: treat as array
            IterableKind::Array {
                elem_type: TypeId::I64,
            }
        });

        match kind {
            IterableKind::Range => {
                // Range expressions are handled above via syntactic check.
                // This branch covers the edge case where sema marks a non-literal
                // expression as Range (shouldn't happen in practice).
                self.for_array(for_stmt)
            }
            IterableKind::Array { .. } => self.for_array(for_stmt),
            _ => self.for_runtime_iterator(for_stmt, kind),
        }
    }

    // ===== Range loops =====

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
        self.switch_to_block(header);
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
        self.switch_to_block(body_block);
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
        self.switch_to_block(exit_block);
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
        self.switch_to_block(header);
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
        self.switch_to_block(body_block);
        self.compile_loop_body(&for_stmt.body, exit_block, continue_block)?;

        // Continue: increment counter and jump to header
        self.switch_to_block(continue_block);
        let current = self.builder.use_var(var);
        let next = self.builder.ins().iadd_imm(current, 1);
        self.builder.def_var(var, next);
        self.builder.ins().jump(header, &[]);

        self.finalize_for_loop(header, body_block, continue_block, exit_block);

        Ok(false)
    }

    // ===== Array loops (index-based, not RuntimeIterator) =====

    /// Compile a for loop over an array using direct index-based access.
    ///
    /// Kept separate from the RuntimeIterator path because arrays use optimized
    /// direct element access with union/wide-type handling that the runtime
    /// iterator API doesn't support.
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
            crate::rc_cleanup::set_drop_flag_live(self, drop_flag);
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
                IntrinsicKey::ArrayLen,
                &[arr.value],
                TypeId::I64,
                0,
            )?
            .value;

        let idx_var = self.builder.declare_var(types::I64);
        let zero = self.iconst_cached(types::I64, 0);
        self.builder.def_var(idx_var, zero);

        // Declare the element variable with its correct Cranelift type.
        // ArrayGetValue always returns i64, but the element may be a smaller
        // type (e.g. bool -> i8, i32, etc.) so we must narrow after the call.
        let elem_cr_type = self.cranelift_type(elem_type_id);
        let elem_var = self.builder.declare_var(elem_cr_type);
        let elem_zero = self.typed_zero(elem_cr_type);
        self.builder.def_var(elem_var, elem_zero);
        self.vars
            .insert(for_stmt.var_name, (elem_var, elem_type_id));

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

        self.switch_to_block(continue_block);
        let current_idx = self.builder.use_var(idx_var);
        let next_idx = self.builder.ins().iadd_imm(current_idx, 1);
        self.builder.def_var(idx_var, next_idx);
        self.builder.ins().jump(header, &[]);

        self.finalize_for_loop(header, body_block, continue_block, exit_block);

        self.pop_rc_scope_with_cleanup(None)?;

        Ok(false)
    }

    // ===== RuntimeIterator loops (unified path) =====

    /// Unified for-loop over any RuntimeIterator-based iterable.
    ///
    /// Handles String, Iterator<T> interfaces, custom Iterator<T> implementors,
    /// and custom Iterable<T> types. All paths produce a RuntimeIterator, then
    /// share a single iter_next loop.
    fn for_runtime_iterator(
        &mut self,
        for_stmt: &vole_frontend::ast::ForStmt,
        kind: IterableKind,
    ) -> CodegenResult<bool> {
        // Phase 1: Evaluate iterable and convert to RuntimeIterator.
        // The setup returns the actual elem_type_id extracted from the compiled
        // iterator's type, which is more reliable than IterableKind's elem_type
        // in monomorphized generic contexts where sema annotations may be stale.
        let (iter_val, elem_type_id, needs_elem_rc_dec) =
            self.setup_runtime_iter(for_stmt, kind)?;

        // Phase 2: Set up stack slot and element variable
        let slot_data = self.alloc_stack(8);
        let ptr_type = self.ptr_type();
        let slot_addr = self.builder.ins().stack_addr(ptr_type, slot_data, 0);

        let elem_cr_type = self.cranelift_type(elem_type_id);
        let elem_var = self.builder.declare_var(elem_cr_type);
        let elem_zero = self.typed_zero(elem_cr_type);
        self.builder.def_var(elem_var, elem_zero);
        self.vars
            .insert(for_stmt.var_name, (elem_var, elem_type_id));

        // Phase 3: The iter_next loop
        let header = self.builder.create_block();
        let body_block = self.builder.create_block();
        let continue_block = self.builder.create_block();
        let exit_block = self.builder.create_block();

        self.builder.ins().jump(header, &[]);

        // Header: call iter_next, check result
        self.switch_to_block(header);
        let has_value = self.call_runtime(RuntimeKey::ArrayIterNext, &[iter_val, slot_addr])?;
        self.emit_brif(has_value, body_block, exit_block);

        // Body: load value from stack slot, convert type, run body
        self.switch_to_block(body_block);
        let raw_val = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), slot_addr, 0);
        let elem_val = self.convert_iter_elem(raw_val, elem_type_id, elem_cr_type)?;
        self.builder.def_var(elem_var, elem_val);

        self.compile_loop_body(&for_stmt.body, exit_block, continue_block)?;

        // Continue: optionally free per-iteration element, then loop back
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

    /// Evaluate the iterable expression and convert it to a RuntimeIterator.
    ///
    /// Returns `(iter_value, elem_type_id, needs_elem_rc_dec)`:
    /// - `iter_value`: raw Cranelift Value for the RuntimeIterator pointer
    /// - `elem_type_id`: element type extracted from the compiled iterator's type
    /// - `needs_elem_rc_dec`: true for string chars (each char is a new allocation)
    fn setup_runtime_iter(
        &mut self,
        for_stmt: &vole_frontend::ast::ForStmt,
        kind: IterableKind,
    ) -> CodegenResult<(Value, TypeId, bool)> {
        let hint_elem_type = match kind {
            IterableKind::String => TypeId::STRING,
            IterableKind::IteratorInterface { elem_type } => elem_type,
            IterableKind::CustomIterator { elem_type } => elem_type,
            IterableKind::CustomIterable { elem_type } => elem_type,
            IterableKind::Range | IterableKind::Array { .. } => {
                unreachable!("Range/Array handled before setup_runtime_iter")
            }
        };
        match kind {
            IterableKind::String => {
                let (v, rc) = self.setup_string_iter(for_stmt)?;
                Ok((v, TypeId::STRING, rc))
            }
            IterableKind::IteratorInterface { .. } => {
                let (v, elem) = self.setup_interface_iter(for_stmt, hint_elem_type)?;
                Ok((v, elem, false))
            }
            IterableKind::CustomIterator { .. } => {
                let v = self.setup_custom_iterator(for_stmt, hint_elem_type)?;
                Ok((v, hint_elem_type, false))
            }
            IterableKind::CustomIterable { .. } => {
                let v = self.setup_custom_iterable(for_stmt, hint_elem_type)?;
                Ok((v, hint_elem_type, false))
            }
            IterableKind::Range | IterableKind::Array { .. } => {
                unreachable!("Range/Array handled before setup_runtime_iter")
            }
        }
    }

    /// Set up a string chars RuntimeIterator. Tracks source string and iterator
    /// in RC scope. Returns (iter_val, needs_elem_rc_dec=true).
    fn setup_string_iter(
        &mut self,
        for_stmt: &vole_frontend::ast::ForStmt,
    ) -> CodegenResult<(Value, bool)> {
        let string_val = self.expr(&for_stmt.iterable)?;
        let iter_val = self.call_runtime(RuntimeKey::StringCharsIter, &[string_val.value])?;

        self.push_rc_scope();
        if string_val.is_owned() && self.rc_state(string_val.type_id).needs_cleanup() {
            let tracked_string = self
                .builder
                .declare_var(self.cranelift_type(string_val.type_id));
            self.builder.def_var(tracked_string, string_val.value);
            let drop_flag = self.register_rc_local(tracked_string, string_val.type_id);
            crate::rc_cleanup::set_drop_flag_live(self, drop_flag);
        }
        let iter_type_id = self
            .arena()
            .lookup_runtime_iterator(TypeId::STRING)
            .unwrap_or(TypeId::STRING);
        let tracked_iter = self.builder.declare_var(self.cranelift_type(iter_type_id));
        self.builder.def_var(tracked_iter, iter_val);
        let iter_drop_flag = self.register_rc_local(tracked_iter, iter_type_id);
        crate::rc_cleanup::set_drop_flag_live(self, iter_drop_flag);

        // Each char is a new allocation that needs per-element cleanup.
        Ok((iter_val, true))
    }

    /// Set up an Iterator<T> interface or RuntimeIterator for iteration.
    /// Wraps interface values via InterfaceIter; RuntimeIterators pass through.
    ///
    /// Returns `(iter_value, elem_type_id)` where elem_type_id is extracted from
    /// the iterator's actual type, not the IterableKind hint (which may be stale
    /// in monomorphized generic contexts).
    fn setup_interface_iter(
        &mut self,
        for_stmt: &vole_frontend::ast::ForStmt,
        hint_elem_type: TypeId,
    ) -> CodegenResult<(Value, TypeId)> {
        let mut iter = self.expr(&for_stmt.iterable)?;

        // Extract elem_type from the iterator's actual type, falling back to hint
        let (elem_type_id, is_interface_iter) = {
            let arena = self.arena();
            if let Some(elem_id) = arena.unwrap_runtime_iterator(iter.type_id) {
                (elem_id, false)
            } else if let Some((_, type_args)) = arena.unwrap_interface(iter.type_id) {
                (type_args.first().copied().unwrap_or(hint_elem_type), true)
            } else {
                (hint_elem_type, false)
            }
        };

        if is_interface_iter {
            let wrapped = self.call_runtime(RuntimeKey::InterfaceIter, &[iter.value])?;
            self.consume_rc_value(&mut iter)?;
            iter = self.make_runtime_iter_value(wrapped, elem_type_id);
        }

        self.push_rc_scope();
        self.track_iter_in_rc_scope(&iter);
        Ok((iter.value, elem_type_id))
    }

    /// Set up a custom Iterator<T> implementor by boxing to interface, then
    /// wrapping via InterfaceIter.
    fn setup_custom_iterator(
        &mut self,
        for_stmt: &vole_frontend::ast::ForStmt,
        elem_type_id: TypeId,
    ) -> CodegenResult<Value> {
        let iterable = self.expr(&for_stmt.iterable)?;

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
        let wrapped = self.call_runtime(RuntimeKey::InterfaceIter, &[boxed.value])?;
        let mut boxed_iface = boxed;
        self.consume_rc_value(&mut boxed_iface)?;

        let iter = self.make_runtime_iter_value(wrapped, elem_type_id);
        self.push_rc_scope();
        self.track_iter_in_rc_scope(&iter);
        Ok(iter.value)
    }

    /// Set up a custom Iterable<T> by calling .iter() to get Iterator<T>,
    /// then wrapping via InterfaceIter.
    fn setup_custom_iterable(
        &mut self,
        for_stmt: &vole_frontend::ast::ForStmt,
        elem_type_id: TypeId,
    ) -> CodegenResult<Value> {
        let iterable = self.expr(&for_stmt.iterable)?;
        let iter_value = self.call_iterable_iter_method(&iterable, elem_type_id)?;

        let wrapped = self.call_runtime(RuntimeKey::InterfaceIter, &[iter_value.value])?;
        let mut iter_iface = iter_value;
        self.consume_rc_value(&mut iter_iface)?;

        let iter = self.make_runtime_iter_value(wrapped, elem_type_id);
        self.push_rc_scope();
        self.track_iter_in_rc_scope(&iter);
        Ok(iter.value)
    }

    // ===== Helpers =====

    /// Create a CompiledValue for a RuntimeIterator wrapping the given raw pointer.
    fn make_runtime_iter_value(&self, raw: Value, elem_type_id: TypeId) -> CompiledValue {
        let runtime_iter_type_id = self
            .arena()
            .lookup_runtime_iterator(elem_type_id)
            .unwrap_or(TypeId::STRING);
        CompiledValue::owned(raw, types::I64, runtime_iter_type_id)
    }

    /// Track an owned iterator in the current RC scope for cleanup.
    fn track_iter_in_rc_scope(&mut self, iter: &CompiledValue) {
        if iter.is_owned() && self.rc_state(iter.type_id).needs_cleanup() {
            let tracked_var = self.builder.declare_var(self.cranelift_type(iter.type_id));
            self.builder.def_var(tracked_var, iter.value);
            let drop_flag = self.register_rc_local(tracked_var, iter.type_id);
            crate::rc_cleanup::set_drop_flag_live(self, drop_flag);
        }
    }

    /// Convert a raw i64 value from iter_next to the element's Cranelift type.
    fn convert_iter_elem(
        &mut self,
        raw_val: Value,
        elem_type_id: TypeId,
        elem_cr_type: Type,
    ) -> CodegenResult<Value> {
        let is_i128 = elem_type_id == self.arena().i128();
        let is_f128 = elem_type_id == self.arena().f128();
        if is_i128 || is_f128 {
            let wide_bits = self.call_runtime(RuntimeKey::Wide128Unbox, &[raw_val])?;
            if is_f128 {
                Ok(self
                    .builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), wide_bits))
            } else {
                Ok(wide_bits)
            }
        } else if elem_cr_type == types::F64 {
            Ok(self
                .builder
                .ins()
                .bitcast(types::F64, MemFlags::new(), raw_val))
        } else if elem_cr_type == types::F32 {
            let i32_val = self.builder.ins().ireduce(types::I32, raw_val);
            Ok(self
                .builder
                .ins()
                .bitcast(types::F32, MemFlags::new(), i32_val))
        } else if elem_cr_type.is_int() && elem_cr_type.bits() < 64 {
            Ok(self.builder.ins().ireduce(elem_cr_type, raw_val))
        } else {
            Ok(raw_val)
        }
    }

    /// Call the `.iter()` method on an Iterable value, returning the Iterator<T> interface.
    fn call_iterable_iter_method(
        &mut self,
        iterable: &CompiledValue,
        _elem_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Get the TypeDefId and NameId for the iterable's type
        let type_def_id = {
            let arena = self.arena();
            let (tdef, _, _) = arena
                .unwrap_class_or_struct(iterable.type_id)
                .ok_or_else(|| {
                    CodegenError::internal("for_iterable: expected class/struct type")
                })?;
            tdef
        };
        let type_name_id = self.query().get_type(type_def_id).name_id;

        // Look up the "iter" method's NameId
        let iter_name_id = self
            .query()
            .try_method_name_id_by_str("iter")
            .ok_or_else(|| CodegenError::not_found("method name_id", "iter"))?;

        // Look up the compiled function key for type::iter()
        let func_key = self
            .method_func_keys()
            .get(&(type_name_id, iter_name_id))
            .copied()
            .ok_or_else(|| {
                CodegenError::not_found("iter method func_key", format!("{type_def_id:?}::iter"))
            })?;

        // Get the return type from the method binding (Iterator<T> interface)
        let return_type_id = self
            .query()
            .method_binding(type_def_id, iter_name_id)
            .map(|b| b.func_type.return_type_id)
            .unwrap_or(TypeId::VOID);

        let func_ref = self.func_ref(func_key)?;
        let args = &[iterable.value];
        let coerced = self.coerce_call_args(func_ref, args);
        let call_inst = self.builder.ins().call(func_ref, &coerced);
        self.field_cache.clear();

        self.call_result(call_inst, return_type_id)
    }
}
