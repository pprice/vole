// src/codegen/vir_for_loop.rs
//
// VIR for-loop compilation - impl Cg methods.
// Handles lowered VIR `VirStmt::For` nodes.

use cranelift::prelude::*;
use smallvec::smallvec;

use crate::IntrinsicKey;
use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};
use vole_identity::{TypeId, VirTypeId};
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
            VirIterKind::Generic { .. } => {
                unreachable!("VirIterKind::Generic should be resolved before codegen")
            }
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
        self.vars.insert(vir_for.var_name, (var, VirTypeId::I64));

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
            ..
        } = &vir_for.kind
        else {
            unreachable!("compile_vir_for_array called with non-Array kind");
        };
        let mut elem_type_id = self.cv_type_id_from_vir(self.try_substitute_type_v(*elem_type_id));
        let mut union_storage = *union_storage;

        let arr = self.compile_vir_expr(&vir_for.iterable)?;

        // TEMP(N279-C): if VIR iterator metadata degraded to `unknown`, recover
        // element typing/storage from the compiled iterable value.
        if let Some(arr_elem_vir) = self.vir_query_unwrap_array_v(arr.type_id) {
            let arr_elem_sema = self.cv_type_id_from_vir(arr_elem_vir);
            elem_type_id = arr_elem_sema;
            if union_storage.is_none() && self.vir_query_is_union_v(arr_elem_vir) {
                union_storage = Some(if self.union_array_prefers_inline_storage_v(arr_elem_vir) {
                    vole_sema::UnionStorageKind::Inline
                } else {
                    vole_sema::UnionStorageKind::Heap
                });
            }
        }

        // Track owned iterable in a dedicated RC scope.
        self.push_rc_scope();
        let arr_sema_ty = self.cv_type_id_from_vir(arr.type_id);
        if arr.is_owned() && self.rc_state(arr_sema_ty).needs_cleanup() {
            let tracked_var = self.builder.declare_var(self.cranelift_type(arr_sema_ty));
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
        self.vars.insert(
            vir_for.var_name,
            (elem_var, self.vir_lookup_or_compat(elem_type_id)),
        );

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
        self.vars.insert(
            vir_for.var_name,
            (elem_var, self.vir_lookup_or_compat(elem_type_id)),
        );

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
            VirIterKind::IteratorInterface { elem_type, .. } => {
                let hint = self.cv_type_id_from_vir(self.try_substitute_type_v(*elem_type));
                let mut iter = self.compile_vir_expr(&vir_for.iterable)?;
                let (elem_type_id, is_interface_iter) = if let Some(elem_vir) =
                    self.vir_query_unwrap_runtime_iterator_v(iter.type_id)
                {
                    (self.cv_type_id_from_vir(elem_vir), false)
                } else if let Some((_, type_args)) = self.vir_query_unwrap_interface_v(iter.type_id)
                {
                    (
                        type_args
                            .first()
                            .map(|&v| self.cv_type_id_from_vir(v))
                            .unwrap_or(hint),
                        true,
                    )
                } else {
                    (hint, false)
                };
                if is_interface_iter {
                    iter = self.wrap_interface_iter(iter, elem_type_id)?;
                }
                self.enter_iter_rc_scope(&iter, None);
                Ok((iter.value, elem_type_id, false))
            }
            VirIterKind::CustomIterator { elem_type, .. } => {
                let elem_type_id = self.cv_type_id_from_vir(self.try_substitute_type_v(*elem_type));
                let iterable = self.compile_vir_expr(&vir_for.iterable)?;
                let iterator_type_def = self
                    .name_table()
                    .well_known
                    .iterator_type_def
                    .ok_or_else(|| CodegenError::internal("Iterator type_def not found"))?;
                let interface_type_id = self
                    .vir_query_lookup_interface(iterator_type_def, smallvec![elem_type_id])
                    .ok_or_else(|| {
                        CodegenError::internal_with_context(
                            "Iterator<T> interface type not pre-interned by sema",
                            format!("elem_type_id={elem_type_id:?}"),
                        )
                    })?;
                let boxed = self.box_interface_value(iterable, interface_type_id)?;
                let iter = self.wrap_interface_iter(boxed, elem_type_id)?;
                self.enter_iter_rc_scope(&iter, None);
                Ok((iter.value, elem_type_id, false))
            }
            VirIterKind::CustomIterable { elem_type, .. } => {
                let elem_type_id = self.cv_type_id_from_vir(self.try_substitute_type_v(*elem_type));
                let iterable = self.compile_vir_expr(&vir_for.iterable)?;
                let iter_value = self.call_iterable_iter_method(&iterable, elem_type_id)?;
                let iter = self.wrap_interface_iter(iter_value, elem_type_id)?;
                self.enter_iter_rc_scope(&iter, None);
                Ok((iter.value, elem_type_id, false))
            }
            VirIterKind::Range | VirIterKind::Array { .. } => {
                unreachable!("Range/Array handled before setup_vir_runtime_iter")
            }
            VirIterKind::Generic { .. } => {
                unreachable!("VirIterKind::Generic should be resolved before codegen")
            }
        }
    }

    // =========================================================================
    // Shared for-loop helpers (moved from deleted for_loop.rs)
    // =========================================================================

    /// Create a `CompiledValue` for a `RuntimeIterator<T>` from a raw pointer.
    ///
    /// Falls back to `RuntimeIterator<i64>` when sema did not pre-intern
    /// the specific element type (e.g. propagated class method monomorphs).
    /// All RuntimeIterator types share the same physical layout (RC pointer),
    /// so the fallback is layout-safe; only VIR type metadata differs.
    pub(crate) fn make_runtime_iter_value(
        &self,
        raw: Value,
        elem_type_id: TypeId,
    ) -> super::types::CompiledValue {
        let runtime_iter_type_id = self
            .vir_query_lookup_runtime_iterator(elem_type_id)
            .or_else(|| self.vir_query_lookup_runtime_iterator(TypeId::I64))
            .expect("RuntimeIterator<i64> must always be pre-interned");
        super::types::CompiledValue::owned(raw, types::I64, self.vir_lookup(runtime_iter_type_id))
    }

    /// Track an owned iterator in the current RC scope for cleanup.
    pub(crate) fn track_iter_in_rc_scope(&mut self, iter: &super::types::CompiledValue) {
        // For RC bookkeeping in iterator contexts, bridge via cv_type_id_from_vir
        // for the needs_cleanup check — rc_state_v can disagree for iterator types.
        // register_rc_local takes VirTypeId (the stored type_id is dead_code;
        // is_interface/is_unknown are computed from the VirTypeId at registration).
        let iter_sema_ty = self.cv_type_id_from_vir(iter.type_id);
        if iter.is_owned() && self.rc_state(iter_sema_ty).needs_cleanup() {
            let tracked_var = self.builder.declare_var(self.cranelift_type(iter_sema_ty));
            self.builder.def_var(tracked_var, iter.value);
            let drop_flag = self.register_rc_local(tracked_var, iter.type_id);
            crate::rc_cleanup::set_drop_flag_live(self, drop_flag);
        }
    }

    /// Push an RC scope for iterator lifetime and track the iterator (and
    /// optionally a source value) for cleanup on scope exit.
    pub(crate) fn enter_iter_rc_scope(
        &mut self,
        iter: &super::types::CompiledValue,
        source: Option<&super::types::CompiledValue>,
    ) {
        self.push_rc_scope();
        if let Some(src) = source {
            self.track_iter_in_rc_scope(src);
        }
        self.track_iter_in_rc_scope(iter);
    }

    /// Wrap an interface value via `InterfaceIter`, consuming the old value and
    /// returning a `RuntimeIterator` `CompiledValue`.
    pub(crate) fn wrap_interface_iter(
        &mut self,
        mut iface: super::types::CompiledValue,
        elem_type_id: TypeId,
    ) -> CodegenResult<super::types::CompiledValue> {
        let wrapped = self.call_runtime(RuntimeKey::InterfaceIter, &[iface.value])?;
        self.consume_rc_value(&mut iface)?;
        Ok(self.make_runtime_iter_value(wrapped, elem_type_id))
    }

    /// Convert a raw i64 value from iter_next to the element's Cranelift type.
    pub(crate) fn convert_iter_elem(
        &mut self,
        raw_val: Value,
        elem_type_id: TypeId,
        elem_cr_type: Type,
    ) -> CodegenResult<Value> {
        if let Some(wide) = self.vir_query_wide_type(elem_type_id) {
            let wide_bits = self.call_runtime(RuntimeKey::Wide128Unbox, &[raw_val])?;
            Ok(wide.reinterpret_i128(self.builder, wide_bits))
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
    pub(crate) fn call_iterable_iter_method(
        &mut self,
        iterable: &super::types::CompiledValue,
        _elem_type_id: TypeId,
    ) -> CodegenResult<super::types::CompiledValue> {
        let type_def_id = self
            .vir_query_unwrap_nominal_v(iterable.type_id)
            .ok_or_else(|| CodegenError::internal("for_iterable: expected class/struct type"))?;
        let type_name_id = self.analyzed().entity_type_name_id(type_def_id);

        let iter_name_id = self
            .analyzed()
            .try_method_name_id_by_str("iter")
            .ok_or_else(|| CodegenError::not_found("method name_id", "iter"))?;

        let func_key = self
            .method_func_keys()
            .get(&(type_name_id, iter_name_id))
            .copied()
            .ok_or_else(|| {
                CodegenError::not_found("iter method func_key", format!("{type_def_id:?}::iter"))
            })?;

        let return_type_id = self
            .analyzed()
            .method_binding_return_type(type_def_id, iter_name_id)
            .unwrap_or(TypeId::VOID);

        let func_ref = self.func_ref(func_key)?;
        let call_inst = self.emit_call(func_ref, &[iterable.value]);

        self.call_result(call_inst, return_type_id)
    }

    /// Decode a raw array element value to the correct Cranelift type.
    ///
    /// Handles union storage (inline/heap), wide types (i128), narrow
    /// integers, and float reinterpretation.
    pub(crate) fn decode_array_elem(
        &mut self,
        elem_val: Value,
        elem_ptr: Value,
        elem_type_id: TypeId,
        union_storage: Option<vole_sema::UnionStorageKind>,
    ) -> CodegenResult<Value> {
        if elem_type_id.is_unknown() {
            let tag_offset = std::mem::offset_of!(vole_runtime::value::TaggedValue, tag) as i32;
            let elem_tag =
                self.builder
                    .ins()
                    .load(types::I64, MemFlags::new(), elem_ptr, tag_offset);
            let unknown_heap_tag = self.iconst_cached(
                types::I64,
                vole_runtime::value::RuntimeTypeId::UnknownHeap as i64,
            );
            let is_unknown_heap = self
                .builder
                .ins()
                .icmp(IntCC::Equal, elem_tag, unknown_heap_tag);
            return Ok(self
                .builder
                .ins()
                .select(is_unknown_heap, elem_val, elem_ptr));
        }

        let elem_cr_type = self.cranelift_type(elem_type_id);
        let elem_wide = self.vir_query_wide_type(elem_type_id);
        if let Some(storage) = union_storage {
            use vole_identity::UnionStorageKind;
            match storage {
                UnionStorageKind::Inline => {
                    let tag_offset =
                        std::mem::offset_of!(vole_runtime::value::TaggedValue, tag) as i32;
                    let elem_tag =
                        self.builder
                            .ins()
                            .load(types::I64, MemFlags::new(), elem_ptr, tag_offset);
                    Ok(self
                        .decode_dynamic_array_union_element(elem_tag, elem_val, elem_type_id)
                        .value)
                }
                UnionStorageKind::Heap => {
                    Ok(self.copy_union_heap_to_stack(elem_val, elem_type_id).value)
                }
            }
        } else if let Some(wide) = elem_wide {
            let wide_bits = self.call_runtime(RuntimeKey::Wide128Unbox, &[elem_val])?;
            Ok(wide.reinterpret_i128(self.builder, wide_bits))
        } else if elem_cr_type.is_int() && elem_cr_type.bits() < 64 {
            Ok(self.builder.ins().ireduce(elem_cr_type, elem_val))
        } else if elem_cr_type == types::F64 {
            Ok(self
                .builder
                .ins()
                .bitcast(types::F64, MemFlags::new(), elem_val))
        } else if elem_cr_type == types::F32 {
            let i32_val = self.builder.ins().ireduce(types::I32, elem_val);
            Ok(self
                .builder
                .ins()
                .bitcast(types::F32, MemFlags::new(), i32_val))
        } else {
            Ok(elem_val)
        }
    }
}
