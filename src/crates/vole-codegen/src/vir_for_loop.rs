// src/codegen/vir_for_loop.rs
//
// VIR for-loop compilation - impl Cg methods.
// Handles lowered VIR `VirStmt::For` nodes.

use cranelift::prelude::*;

use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};
use vole_identity::{ArrayStoreStrategy, TypeId, UnionStorageKind, VirElemConversion, VirTypeId};
use vole_vir::stmt::{VirFor, VirIterKind};
use vole_vir::{VirBody, VirExpr, VirStmt};

use super::context::Cg;

// ---------------------------------------------------------------------------
// Development safety guard: abort after too many iterator loop iterations.
// Prevents infinite loops from hanging the machine during compiler development.
// Set to `false` to disable once the iterator pipeline is stable.
// ---------------------------------------------------------------------------
const DEV_ITERATOR_GUARD_ENABLED: bool = true;
const DEV_ITERATOR_GUARD_LIMIT: i64 = u32::MAX as i64;

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
// Annotation extraction helpers
// ---------------------------------------------------------------------------

/// Extract the `VirElemConversion` from a `VirIterKind::Iterator`.
///
/// Returns `Unresolved` for non-Iterator kinds (Range, Array).
fn iter_elem_conversion(kind: &VirIterKind) -> VirElemConversion {
    match kind {
        VirIterKind::Iterator {
            elem_conversion, ..
        } => *elem_conversion,
        // Range / Array don't use the iter_next path.
        _ => VirElemConversion::Unresolved,
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
            VirIterKind::Iterator { .. } => self.compile_vir_for_runtime_iter(vir_for),
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
        // Save vars so that `let` bindings inside the loop body that shadow
        // outer variables do not leak into the outer scope after the loop.
        let saved_vars = self.vars.clone();
        let (terminated, _) = self.compile_vir_body(&vir_for.body)?;
        self.vars = saved_vars;
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
            elem_type,
            union_storage,
            store_strategy,
            elem_conversion,
            ..
        } = &vir_for.kind
        else {
            unreachable!("compile_vir_for_array called with non-Array kind");
        };
        let mut elem_vir = self.try_substitute_type_v(*elem_type);
        let mut union_storage = *union_storage;
        let mut store_strategy = *store_strategy;
        let mut elem_conversion = *elem_conversion;

        let arr = self.compile_vir_expr(&vir_for.iterable)?;

        // TEMP(N279-C): if VIR iterator metadata degraded to `unknown`, recover
        // element typing/storage from the compiled iterable value.
        if let Some(arr_elem_vir) = self.vir_query_unwrap_array_v(arr.type_id) {
            elem_vir = arr_elem_vir;
            let derived = self.array_store_strategy_v(arr_elem_vir);
            store_strategy = Some(derived);
            elem_conversion = Some(self.elem_conversion_v(arr_elem_vir));
            if union_storage.is_none() && self.vir_query_is_union_v(arr_elem_vir) {
                union_storage = Some(match derived {
                    ArrayStoreStrategy::UnionInline => UnionStorageKind::Inline,
                    _ => UnionStorageKind::Heap,
                });
            }
        }

        // Track owned iterable in a dedicated RC scope.
        self.push_rc_scope();
        if arr.is_owned() && self.cached_rc_state_v(arr.type_id).needs_cleanup() {
            let tracked_var = self.builder.declare_var(self.cranelift_type_v(arr.type_id));
            self.builder.def_var(tracked_var, arr.value);
            let drop_flag = self.register_rc_local(tracked_var, arr.type_id);
            crate::rc_cleanup::set_drop_flag_live(self, drop_flag);
        }

        let len_val = self
            .call_compiler_intrinsic_key_with_line(
                crate::IntrinsicKey::ArrayLen,
                &[arr.value],
                TypeId::I64,
                0,
            )?
            .value;

        let idx_var = self.builder.declare_var(types::I64);
        let zero = self.iconst_cached(types::I64, 0);
        self.builder.def_var(idx_var, zero);

        let elem_cr_type = self.cranelift_type_v(elem_vir);
        let elem_var = self.builder.declare_var(elem_cr_type);
        let elem_zero = self.typed_zero(elem_cr_type);
        self.builder.def_var(elem_var, elem_zero);
        self.bind_var_v(vir_for.var_name, elem_var, elem_vir);

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
        let elem_val = if let Some(strategy) = store_strategy {
            self.decode_array_elem_hinted(elem_val, elem_ptr, elem_vir, strategy, elem_conversion)?
        } else {
            self.decode_array_elem_v(elem_val, elem_ptr, elem_vir, union_storage)?
        };
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
        let (iter_val, elem_vir, needs_elem_rc_dec) = self.setup_vir_runtime_iter(vir_for)?;
        let elem_conversion = iter_elem_conversion(&vir_for.kind);

        let slot_data = self.alloc_stack(8);
        let ptr_type = self.ptr_type();
        let slot_addr = self.builder.ins().stack_addr(ptr_type, slot_data, 0);

        let elem_cr_type = self.cranelift_type_v(elem_vir);
        let elem_var = self.builder.declare_var(elem_cr_type);
        let elem_zero = self.typed_zero(elem_cr_type);
        self.builder.def_var(elem_var, elem_zero);
        self.bind_var_v(vir_for.var_name, elem_var, elem_vir);

        // DEV GUARD: iteration counter to catch infinite loops during development
        let guard_var = if DEV_ITERATOR_GUARD_ENABLED {
            let v = self.builder.declare_var(types::I64);
            let zero = self.iconst_cached(types::I64, 0);
            self.builder.def_var(v, zero);
            Some(v)
        } else {
            None
        };

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
        let elem_val = self.convert_elem_by_hint(raw_val, elem_vir, elem_conversion)?;
        self.builder.def_var(elem_var, elem_val);

        self.compile_vir_loop_body(&vir_for.body, exit_block, continue_block)?;

        self.switch_to_block(continue_block);
        if needs_elem_rc_dec {
            let cur_elem = self.builder.use_var(elem_var);
            self.call_runtime_void(RuntimeKey::RcDec, &[cur_elem])?;
        }

        // DEV GUARD: increment counter and trap if over limit
        if let Some(guard) = guard_var {
            let count = self.builder.use_var(guard);
            let next = self.builder.ins().iadd_imm(count, 1);
            self.builder.def_var(guard, next);
            let limit = self
                .builder
                .ins()
                .iconst(types::I64, DEV_ITERATOR_GUARD_LIMIT);
            let over = self
                .builder
                .ins()
                .icmp(IntCC::SignedGreaterThan, next, limit);
            self.builder.ins().trapnz(over, TrapCode::user(1).unwrap());
        }

        self.builder.ins().jump(header, &[]);

        self.finalize_for_loop(header, body_block, continue_block, exit_block);
        self.pop_rc_scope_with_cleanup(None)?;

        Ok(false)
    }

    /// Evaluate the VIR iterable and convert it to a RuntimeIterator.
    ///
    /// Returns `(iter_value, elem_vir_type, needs_elem_rc_dec)`.
    ///
    /// Determines the setup strategy from the compiled iterable's type:
    /// - String → call `StringCharsIter`
    /// - RuntimeIterator → pass through directly
    /// - Iterator interface → wrap via `InterfaceIter`
    /// - Custom iterator/iterable → box + wrap (with optional `.iter()` call)
    fn setup_vir_runtime_iter(
        &mut self,
        vir_for: &VirFor,
    ) -> CodegenResult<(Value, VirTypeId, bool)> {
        let VirIterKind::Iterator { elem_type, .. } = &vir_for.kind else {
            unreachable!("setup_vir_runtime_iter called with non-Iterator kind");
        };
        let elem_vir = self.try_substitute_type_v(*elem_type);
        let iterable = self.compile_vir_expr(&vir_for.iterable)?;
        let iterable_vir = iterable.type_id;

        // String → StringCharsIter
        if self.vir_query_is_string_v(iterable_vir) {
            let iter_val = self.call_runtime(RuntimeKey::StringCharsIter, &[iterable.value])?;
            let iter = self.make_runtime_iter_value_v(iter_val, VirTypeId::STRING);
            self.enter_iter_rc_scope(&iter, Some(&iterable));
            return Ok((iter_val, elem_vir, true));
        }

        // RuntimeIterator or Iterator<T> interface → pass through.
        // Both are thin pointers (i64) to the same runtime representation.
        if self.vir_query_is_runtime_iterator_v(iterable_vir) {
            self.enter_iter_rc_scope(&iterable, None);
            return Ok((iterable.value, elem_vir, false));
        }

        // Non-Iterator interface → wrap via InterfaceIter.
        if self.vir_query_is_interface_v(iterable_vir) {
            let iter = self.wrap_interface_iter_v(iterable, elem_vir)?;
            self.enter_iter_rc_scope(&iter, None);
            return Ok((iter.value, elem_vir, false));
        }

        // Custom iterator or iterable class/struct.
        // Determine whether this type has an `.iter()` method (Iterable) or
        // directly implements Iterator<T> (custom iterator).
        let iterator_interface_type = self.resolve_iterator_interface_for_elem(elem_vir);

        // Try custom iterable first: look up `.iter()` method on this type.
        if let Some(type_name_id) = self
            .analyzed()
            .impl_type_name_id_from_vir_type_id(iterable_vir)
            && let Some(iter_method_name_id) = self.analyzed().try_method_name_id_by_str("iter")
            && let Some(&func_key) = self
                .method_func_keys()
                .get(&(type_name_id, iter_method_name_id))
        {
            // This is a CustomIterable: call .iter() then wrap
            let interface_vir = self.try_substitute_type_v(iterator_interface_type);
            let return_type_id = self.vir_type_table().vir_to_type_id(interface_vir);
            let func_ref = self.func_ref(func_key)?;
            let call_inst = self.emit_call(func_ref, &[iterable.value]);
            let iter_value = self.call_result(call_inst, return_type_id)?;
            let iter = self.wrap_interface_iter_v(iter_value, elem_vir)?;
            self.enter_iter_rc_scope(&iter, None);
            return Ok((iter.value, elem_vir, false));
        }

        // Custom iterator: box directly as Iterator<T> interface, then wrap
        let iter =
            self.box_and_wrap_as_runtime_iterator(iterable, iterator_interface_type, elem_vir)?;
        self.enter_iter_rc_scope(&iter, None);
        Ok((iter.value, elem_vir, false))
    }

    /// Resolve the `Iterator<T>` interface VirTypeId for a given element type.
    ///
    /// Used by the for-loop setup to construct the target interface type when
    /// boxing custom iterators/iterables.
    fn resolve_iterator_interface_for_elem(&self, elem_vir: VirTypeId) -> VirTypeId {
        self.name_table()
            .well_known
            .iterator_type_def
            .and_then(|def| {
                self.vir_type_table()
                    .lookup_interface_v(def, vec![elem_vir])
            })
            .unwrap_or(VirTypeId::UNKNOWN)
    }

    // =========================================================================
    // Shared for-loop helpers (moved from deleted for_loop.rs)
    // =========================================================================

    /// Create a `CompiledValue` for a `RuntimeIterator<T>` from a raw pointer (VirTypeId-native).
    ///
    /// Falls back to `RuntimeIterator<i64>` when sema did not pre-intern
    /// the specific element type (e.g. propagated class method monomorphs).
    /// All RuntimeIterator types share the same physical layout (RC pointer),
    /// so the fallback is layout-safe; only VIR type metadata differs.
    pub(crate) fn make_runtime_iter_value_v(
        &self,
        raw: Value,
        elem_vir: VirTypeId,
    ) -> super::types::CompiledValue {
        let runtime_iter_vir = self
            .vir_query_lookup_runtime_iterator_v(elem_vir)
            .or_else(|| self.vir_query_lookup_runtime_iterator_v(VirTypeId::I64))
            .expect("RuntimeIterator<i64> must always be pre-interned");
        super::types::CompiledValue::owned(raw, types::I64, runtime_iter_vir)
    }

    /// Track an owned iterator in the current RC scope for cleanup.
    pub(crate) fn track_iter_in_rc_scope(&mut self, iter: &super::types::CompiledValue) {
        if iter.is_owned() && self.cached_rc_state_v(iter.type_id).needs_cleanup() {
            let tracked_var = self
                .builder
                .declare_var(self.cranelift_type_v(iter.type_id));
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
    /// returning a `RuntimeIterator` `CompiledValue` (VirTypeId-native).
    pub(crate) fn wrap_interface_iter_v(
        &mut self,
        mut iface: super::types::CompiledValue,
        elem_vir: VirTypeId,
    ) -> CodegenResult<super::types::CompiledValue> {
        let wrapped = self.call_runtime(RuntimeKey::InterfaceIter, &[iface.value])?;
        self.consume_rc_value(&mut iface)?;
        Ok(self.make_runtime_iter_value_v(wrapped, elem_vir))
    }

    /// Box a value as `Iterator<T>` interface and wrap via `InterfaceIter` into
    /// a `RuntimeIterator`.
    ///
    /// This is the unified path for creating `RuntimeIterator` values from
    /// custom iterators and coercion sites. Handles interface boxing, wrapping,
    /// and RC cleanup of the intermediate boxed interface.
    pub(crate) fn box_and_wrap_as_runtime_iterator(
        &mut self,
        obj: super::types::CompiledValue,
        interface_vir_ty: VirTypeId,
        elem_vir_ty: VirTypeId,
    ) -> CodegenResult<super::types::CompiledValue> {
        let resolved_interface = self.try_substitute_type_v(interface_vir_ty);
        let boxed = self.box_interface_value_v(obj, resolved_interface)?;
        let elem_vir = self.try_substitute_type_v(elem_vir_ty);
        self.wrap_interface_iter_v(boxed, elem_vir)
    }

    /// Convert a raw i64 value from iter_next to the element's Cranelift type (VirTypeId-native).
    pub(crate) fn convert_iter_elem_v(
        &mut self,
        raw_val: Value,
        elem_vir: VirTypeId,
        elem_cr_type: Type,
    ) -> CodegenResult<Value> {
        if let Some(wide) = self.vir_query_wide_type_v(elem_vir) {
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

    /// Convert a raw i64 value using a pre-computed [`VirElemConversion`].
    ///
    /// This is the annotation-driven path that replaces type-based branching
    /// in `convert_iter_elem_v` and `decode_scalar_array_elem`.  Falls back
    /// to `convert_iter_elem_v` for `Unresolved` (generic templates).
    pub(crate) fn convert_elem_by_hint(
        &mut self,
        raw_val: Value,
        elem_vir: VirTypeId,
        hint: VirElemConversion,
    ) -> CodegenResult<Value> {
        match hint {
            VirElemConversion::Identity => Ok(raw_val),
            VirElemConversion::BitcastF64 => {
                Ok(self
                    .builder
                    .ins()
                    .bitcast(types::F64, MemFlags::new(), raw_val))
            }
            VirElemConversion::BitcastF32 => {
                let i32_val = self.builder.ins().ireduce(types::I32, raw_val);
                Ok(self
                    .builder
                    .ins()
                    .bitcast(types::F32, MemFlags::new(), i32_val))
            }
            VirElemConversion::ReduceInt { bits } => {
                let target = match bits {
                    8 => types::I8,
                    16 => types::I16,
                    32 => types::I32,
                    _ => return Ok(raw_val),
                };
                Ok(self.builder.ins().ireduce(target, raw_val))
            }
            VirElemConversion::WideUnbox => {
                let wide = self
                    .vir_query_wide_type_v(elem_vir)
                    .expect("INTERNAL: WideUnbox hint but no wide type");
                let wide_bits = self.call_runtime(RuntimeKey::Wide128Unbox, &[raw_val])?;
                Ok(wide.reinterpret_i128(self.builder, wide_bits))
            }
            VirElemConversion::Unresolved => {
                // Resolve dynamically; the type should be concrete
                // post-monomorphization.  Delegate to the old type-branch
                // method as a safety net for any still-unresolved params.
                let elem_cr_type = self.cranelift_type_v(elem_vir);
                self.convert_iter_elem_v(raw_val, elem_vir, elem_cr_type)
            }
        }
    }

    /// Decode a raw array element value to the correct Cranelift type (VirTypeId-native).
    ///
    /// Dispatches on the pre-computed [`ArrayStoreStrategy`] when available,
    /// falling back to the `union_storage` hint and type queries.
    pub(crate) fn decode_array_elem_v(
        &mut self,
        elem_val: Value,
        elem_ptr: Value,
        elem_vir: VirTypeId,
        union_storage: Option<UnionStorageKind>,
    ) -> CodegenResult<Value> {
        // Compute the strategy from the existing annotations.
        let strategy = match union_storage {
            Some(UnionStorageKind::Inline) => ArrayStoreStrategy::UnionInline,
            Some(UnionStorageKind::Heap) => ArrayStoreStrategy::UnionBoxed,
            None => self.array_store_strategy_v(elem_vir),
        };
        self.decode_array_elem_by_strategy(elem_val, elem_ptr, elem_vir, strategy)
    }

    /// Decode a raw array element using both [`ArrayStoreStrategy`] and an
    /// optional [`VirElemConversion`] hint.
    ///
    /// For scalar strategies (`DirectScalar`, `HeapCopyStruct`, `Unresolved`),
    /// uses the hint to avoid type-branching.  Falls back to
    /// `decode_array_elem_by_strategy` when no hint is available.
    pub(crate) fn decode_array_elem_hinted(
        &mut self,
        elem_val: Value,
        elem_ptr: Value,
        elem_vir: VirTypeId,
        strategy: ArrayStoreStrategy,
        elem_conversion: Option<VirElemConversion>,
    ) -> CodegenResult<Value> {
        match strategy {
            ArrayStoreStrategy::DirectScalar
            | ArrayStoreStrategy::HeapCopyStruct
            | ArrayStoreStrategy::Unresolved => {
                let hint = elem_conversion.unwrap_or(VirElemConversion::Unresolved);
                self.convert_elem_by_hint(elem_val, elem_vir, hint)
            }
            _ => self.decode_array_elem_by_strategy(elem_val, elem_ptr, elem_vir, strategy),
        }
    }

    /// Decode a raw array element dispatching on an [`ArrayStoreStrategy`].
    pub(crate) fn decode_array_elem_by_strategy(
        &mut self,
        elem_val: Value,
        elem_ptr: Value,
        elem_vir: VirTypeId,
        strategy: ArrayStoreStrategy,
    ) -> CodegenResult<Value> {
        match strategy {
            ArrayStoreStrategy::Unknown => self.decode_unknown_array_elem(elem_val, elem_ptr),
            ArrayStoreStrategy::UnionInline => {
                let tag_offset = std::mem::offset_of!(vole_runtime::value::TaggedValue, tag) as i32;
                let elem_tag =
                    self.builder
                        .ins()
                        .load(types::I64, MemFlags::new(), elem_ptr, tag_offset);
                Ok(self
                    .decode_dynamic_array_union_element_v(elem_tag, elem_val, elem_vir)
                    .value)
            }
            ArrayStoreStrategy::UnionBoxed => {
                Ok(self.copy_union_heap_to_stack_v(elem_val, elem_vir).value)
            }
            ArrayStoreStrategy::WideBox => {
                let wide = self
                    .vir_query_wide_type_v(elem_vir)
                    .expect("INTERNAL: WideBox strategy but no wide type");
                let wide_bits = self.call_runtime(RuntimeKey::Wide128Unbox, &[elem_val])?;
                Ok(wide.reinterpret_i128(self.builder, wide_bits))
            }
            ArrayStoreStrategy::DirectScalar
            | ArrayStoreStrategy::HeapCopyStruct
            | ArrayStoreStrategy::Unresolved => self.decode_scalar_array_elem(elem_val, elem_vir),
        }
    }

    /// Decode an array element stored as `unknown` (tagged value pointer).
    fn decode_unknown_array_elem(
        &mut self,
        elem_val: Value,
        elem_ptr: Value,
    ) -> CodegenResult<Value> {
        let tag_offset = std::mem::offset_of!(vole_runtime::value::TaggedValue, tag) as i32;
        let elem_tag = self
            .builder
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
        Ok(self
            .builder
            .ins()
            .select(is_unknown_heap, elem_val, elem_ptr))
    }

    /// Decode a scalar array element (int, float, bool, nil, string, etc.).
    ///
    /// Delegates to `convert_elem_by_hint` with a dynamically computed hint.
    /// Prefer calling `convert_elem_by_hint` directly with a pre-computed
    /// `VirElemConversion` when available.
    fn decode_scalar_array_elem(
        &mut self,
        elem_val: Value,
        elem_vir: VirTypeId,
    ) -> CodegenResult<Value> {
        let hint = self.elem_conversion_v(elem_vir);
        self.convert_elem_by_hint(elem_val, elem_vir, hint)
    }
}
