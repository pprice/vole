// src/codegen/value_builders.rs
//
// Value construction and stack layout methods - impl Cg methods for creating
// CompiledValues, control flow helpers, and stack allocation.
//
// Handles primitive value constructors, tag operations, call argument
// compilation, control flow (switch/seal, loop body), stack allocation,
// struct return conventions, and union stack/heap copying. Split from context.rs.

use cranelift::prelude::{
    InstBuilder, IntCC, MemFlags, StackSlotData, StackSlotKind, Value, types,
};
use cranelift_codegen::ir::StackSlot;

use vole_identity::{TypeId, VirTypeId};

use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::union_layout;

use super::context::Cg;
use super::types::{CompiledValue, RcLifecycle};
use crate::ops::{sextend_const, uextend_const};

impl<'a, 'b, 'ctx> Cg<'a, 'b, 'ctx> {
    // ========== Void / zero defaults ==========

    /// Create a void return value.
    ///
    /// Reuses a single `iconst.i64 0` created in the entry block at `Cg`
    /// construction, avoiding thousands of dead iconst instructions that were
    /// previously emitted and never referenced.
    pub fn void_value(&self) -> CompiledValue {
        CompiledValue::new(self.cached_void_val, types::I64, VirTypeId::VOID)
    }

    /// Create a zero/default value of the given Cranelift type.
    ///
    /// Used for empty match arms, loop variable initialization, and other cases
    /// where a typed default is needed.
    ///
    /// Note: Cranelift's `iconst` does not support i128, so i128/f128 zeros are
    /// created by sign-extending an i64 zero.
    pub fn typed_zero(&mut self, ty: cranelift::prelude::Type) -> Value {
        if ty == types::F64 {
            self.builder.ins().f64const(0.0)
        } else if ty == types::F32 {
            self.builder.ins().f32const(0.0)
        } else if ty == types::I128 {
            let zero_i64 = self.iconst_cached(types::I64, 0);
            sextend_const(self.builder, types::I128, zero_i64)
        } else if ty == types::F128 {
            let zero_i64 = self.iconst_cached(types::I64, 0);
            let zero_i128 = sextend_const(self.builder, types::I128, zero_i64);
            self.builder
                .ins()
                .bitcast(types::F128, MemFlags::new(), zero_i128)
        } else {
            self.iconst_cached(ty, 0)
        }
    }

    // ========== CompiledValue constructors ==========

    /// Wrap a Cranelift value as a Bool CompiledValue
    pub fn bool_value(&self, value: Value) -> CompiledValue {
        CompiledValue::new(value, types::I8, VirTypeId::BOOL)
    }

    /// Create a boolean constant (true or false)
    pub fn bool_const(&mut self, b: bool) -> CompiledValue {
        let value = self.iconst_cached(types::I8, if b { 1 } else { 0 });
        self.bool_value(value)
    }

    /// Wrap a Cranelift value as an I64 CompiledValue
    pub fn i64_value(&self, value: Value) -> CompiledValue {
        CompiledValue::new(value, types::I64, VirTypeId::I64)
    }

    /// Create an integer constant with a specific Vole type
    pub fn int_const(&mut self, n: i64, type_id: TypeId) -> CompiledValue {
        let ty = self.cranelift_type(type_id);
        // If bidirectional inference produced a float type for an integer literal
        // (can happen in generic contexts where the type parameter resolves to f64
        // during sema but codegen uses i64 for the type param), fall back to i64.
        // Float conversion for `let x: f64 = 5` is handled by sema recording the
        // literal as a FloatLiteral, not through int_const.
        //
        // Likewise, if sema contextual typing labels an int literal as a union
        // element, keep the literal concrete here and let explicit union boxing
        // happen at coercion/assignment boundaries.
        let (ty, type_id) =
            if ty == types::F64 || ty == types::F32 || self.vir_query_is_union(type_id) {
                (types::I64, TypeId::I64)
            } else {
                (ty, type_id)
            };
        // Cranelift's iconst doesn't support I128 directly - we need to create
        // an i64 constant and sign-extend it to i128.
        // For f128, use the runtime software representation (f64 payload in low 64 bits).
        let value = if ty == types::I128 {
            let i64_val = self.iconst_cached(types::I64, n);
            sextend_const(self.builder, types::I128, i64_val)
        } else if ty == types::F128 {
            let low = self.iconst_cached(types::I64, (n as f64).to_bits() as i64);
            let wide = uextend_const(self.builder, types::I128, low);
            self.builder
                .ins()
                .bitcast(types::F128, MemFlags::new(), wide)
        } else {
            self.iconst_cached(ty, n)
        };
        self.compiled_with_ty(value, ty, type_id)
    }

    /// Create an integer constant using a VIR type ID.
    ///
    /// VIR-native version of `int_const` — queries VirTypeTable instead of
    /// TypeArena. Returns a `CompiledValue` with both `type_id` (derived via
    /// bridge for backward compat) and `vir_type_id` set.
    pub fn vir_int_const(&mut self, n: i64, vir_ty: VirTypeId) -> CompiledValue {
        let table = self.vir_type_table();
        let is_union = table.is_union(vir_ty);
        let cranelift_ty =
            crate::types::vir_conversions::vir_type_to_cranelift(vir_ty, table, self.ptr_type());
        // If the VIR type resolved to float or union, fall back to i64
        // (float conversion is handled by FloatLiteral, not int_const).
        let (cranelift_ty, vir_ty) =
            if cranelift_ty == types::F64 || cranelift_ty == types::F32 || is_union {
                (types::I64, VirTypeId::I64)
            } else {
                (cranelift_ty, vir_ty)
            };
        let value = if cranelift_ty == types::I128 {
            let i64_val = self.iconst_cached(types::I64, n);
            sextend_const(self.builder, types::I128, i64_val)
        } else if cranelift_ty == types::F128 {
            let low = self.iconst_cached(types::I64, (n as f64).to_bits() as i64);
            let wide = uextend_const(self.builder, types::I128, low);
            self.builder
                .ins()
                .bitcast(types::F128, MemFlags::new(), wide)
        } else {
            self.iconst_cached(cranelift_ty, n)
        };
        CompiledValue::new(value, cranelift_ty, vir_ty)
    }

    /// Create a wide (i128/f128) literal using a VIR type ID.
    pub fn vir_wide_literal_const(
        &mut self,
        low: u64,
        high: u64,
        vir_ty: VirTypeId,
    ) -> CompiledValue {
        let low_val = self.iconst_cached(types::I64, low as i64);
        let high_val = self.iconst_cached(types::I64, high as i64);
        let i128_val = crate::structs::reconstruct_i128(self.builder, low_val, high_val);
        if vir_ty == VirTypeId::F128 {
            let value = self
                .builder
                .ins()
                .bitcast(types::F128, MemFlags::new(), i128_val);
            CompiledValue::new(value, types::F128, vir_ty)
        } else {
            CompiledValue::new(i128_val, types::I128, vir_ty)
        }
    }

    /// Create a float constant with explicit type (for bidirectional inference)
    pub fn float_const(&mut self, n: f64, type_id: TypeId) -> CompiledValue {
        if self.vir_query_is_union(type_id) {
            let v = self.builder.ins().f64const(n);
            return CompiledValue::new(v, types::F64, VirTypeId::F64);
        }
        let (ty, value) = match type_id {
            TypeId::F32 => {
                let v = self.builder.ins().f32const(n as f32);
                (types::F32, v)
            }
            TypeId::F64 => {
                let v = self.builder.ins().f64const(n);
                (types::F64, v)
            }
            TypeId::F128 => {
                // Runtime f128 currently uses a compact software representation:
                // low 64 bits = f64 payload, high 64 bits = 0.
                let low = self.iconst_cached(types::I64, n.to_bits() as i64);
                let wide = uextend_const(self.builder, types::I128, low);
                let v = self
                    .builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), wide);
                (types::F128, v)
            }
            _ => unreachable!(
                "INTERNAL: float_const called with non-float type {:?}; \
                 float literals must have a float TypeId by the time codegen runs \
                 (union dispatch is handled above)",
                type_id
            ),
        };
        self.compiled_with_ty(value, ty, type_id)
    }

    /// Create a float constant using a VIR type ID.
    pub fn vir_float_const(&mut self, n: f64, vir_ty: VirTypeId) -> CompiledValue {
        let table = self.vir_type_table();
        if table.is_union(vir_ty) {
            let v = self.builder.ins().f64const(n);
            return CompiledValue::new(v, types::F64, VirTypeId::F64);
        }
        let (ty, value) = match vir_ty {
            VirTypeId::F32 => {
                let v = self.builder.ins().f32const(n as f32);
                (types::F32, v)
            }
            VirTypeId::F64 => {
                let v = self.builder.ins().f64const(n);
                (types::F64, v)
            }
            VirTypeId::F128 => {
                let low = self.iconst_cached(types::I64, n.to_bits() as i64);
                let wide = uextend_const(self.builder, types::I128, low);
                let v = self
                    .builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), wide);
                (types::F128, v)
            }
            _ => unreachable!(
                "INTERNAL: vir_float_const called with non-float VIR type {:?}",
                vir_ty
            ),
        };
        CompiledValue::new(value, ty, vir_ty)
    }

    // ========== Tag helpers ==========

    /// Load a tag byte from a union/optional pointer and compare to expected value.
    /// Returns an i8 value (1 if equal, 0 if not).
    pub fn tag_eq(&mut self, ptr: Value, expected_tag: i64) -> Value {
        let tag = self.builder.ins().load(types::I8, MemFlags::new(), ptr, 0);
        let expected = self.iconst_cached(types::I8, expected_tag);
        self.builder.ins().icmp(IntCC::Equal, tag, expected)
    }

    /// Load a tag byte from a union/optional pointer and compare for inequality.
    /// Returns an i8 value (1 if not equal, 0 if equal).
    pub fn tag_ne(&mut self, ptr: Value, expected_tag: i64) -> Value {
        let tag = self.builder.ins().load(types::I8, MemFlags::new(), ptr, 0);
        let expected = self.iconst_cached(types::I8, expected_tag);
        self.builder.ins().icmp(IntCC::NotEqual, tag, expected)
    }

    // ========== String / compiled helpers ==========

    /// Wrap a Cranelift value as a String CompiledValue marked as an RC temp
    pub fn string_temp(&self, value: Value) -> CompiledValue {
        CompiledValue::owned(value, self.ptr_type(), VirTypeId::STRING)
    }

    /// Create a CompiledValue from a value and TypeId, automatically computing the cranelift type
    pub fn compiled(&self, value: Value, type_id: TypeId) -> CompiledValue {
        CompiledValue::new(
            value,
            self.cranelift_type(type_id),
            self.to_vir_type(type_id),
        )
    }

    /// Create a CompiledValue from a value, pre-computed Cranelift type, and sema TypeId.
    ///
    /// Boundary bridge: converts TypeId to VirTypeId via `to_vir_type`.
    pub fn compiled_with_ty(
        &self,
        value: Value,
        cranelift_ty: cranelift::prelude::Type,
        type_id: TypeId,
    ) -> CompiledValue {
        CompiledValue::new(value, cranelift_ty, self.to_vir_type(type_id))
    }

    /// Create an RC-owned CompiledValue from a value, Cranelift type, and sema TypeId.
    ///
    /// Boundary bridge: converts TypeId to VirTypeId via `to_vir_type`.
    pub fn compiled_owned_with_ty(
        &self,
        value: Value,
        cranelift_ty: cranelift::prelude::Type,
        type_id: TypeId,
    ) -> CompiledValue {
        CompiledValue::owned(value, cranelift_ty, self.to_vir_type(type_id))
    }

    /// Convert a raw i64 field value to a CompiledValue with the proper type.
    /// Handles type narrowing for primitives (f64 bitcast, bool/int reduction).
    pub fn convert_field_value(&mut self, raw_value: Value, type_id: TypeId) -> CompiledValue {
        let (value, ty) = super::structs::convert_field_value_id(self.builder, raw_value, type_id);
        self.compiled_with_ty(value, ty, type_id)
    }

    /// Convert a raw i64 field value to a CompiledValue with the proper type (VirTypeId variant).
    /// Handles type narrowing for primitives (f64 bitcast, bool/int reduction).
    pub fn convert_field_value_v(&mut self, raw_value: Value, vir_ty: VirTypeId) -> CompiledValue {
        // Use env path to avoid borrow conflict with self.builder
        let table = &self.env.analyzed.type_table;
        let (value, ty) = crate::types::vir_struct_helpers::vir_convert_field_value(
            self.builder,
            raw_value,
            vir_ty,
            table,
        );
        CompiledValue::new(value, ty, vir_ty)
    }

    /// Extract a value from a TaggedValue (VirTypeId variant).
    pub fn extract_unknown_value_v(
        &mut self,
        raw_value: Value,
        vir_ty: VirTypeId,
    ) -> CompiledValue {
        self.convert_field_value_v(raw_value, vir_ty)
    }

    // ========== Control flow helpers ==========

    /// Emit a conditional branch, or a direct jump when the condition is a known constant.
    ///
    /// When `cond` is defined by an `iconst` instruction (known at compile time),
    /// this emits a `jump` to the taken block instead of a `brif`, eliminating
    /// dead branches from the generated code.
    pub fn emit_brif(
        &mut self,
        cond: Value,
        true_block: cranelift::prelude::Block,
        false_block: cranelift::prelude::Block,
    ) {
        if let Some(val) = crate::ops::try_constant_value(self.builder.func, cond) {
            if val != 0 {
                self.builder.ins().jump(true_block, &[]);
            } else {
                self.builder.ins().jump(false_block, &[]);
            }
        } else {
            self.builder
                .ins()
                .brif(cond, true_block, &[], false_block, &[]);
        }
    }

    /// Switch to a block and seal it (common pattern for sequential control flow)
    pub fn switch_and_seal(&mut self, block: cranelift::prelude::Block) {
        self.switch_to_block(block);
        self.builder.seal_block(block);
    }

    /// Compile the body of a VIR while loop, managing loop state and RC scopes.
    ///
    /// Mirrors [`compile_loop_body`] but operates on a `VirBody` instead of an
    /// AST `Block`.
    pub fn compile_vir_loop_body(
        &mut self,
        body: &vole_vir::VirBody,
        exit_block: cranelift::prelude::Block,
        continue_block: cranelift::prelude::Block,
    ) -> CodegenResult<bool> {
        let rc_depth = self.rc_scope_depth();
        self.cf.push_loop(exit_block, continue_block, rc_depth);
        self.push_rc_scope();
        // Save vars so that `let` bindings inside the loop body that shadow
        // outer variables do not leak into the outer scope after the loop.
        let saved_vars = self.vars.clone();
        let (terminated, _) = self.compile_vir_body(body)?;
        self.vars = saved_vars;
        self.cf.pop_loop();
        if !terminated {
            self.pop_rc_scope_with_cleanup(None)?;
            self.builder.ins().jump(continue_block, &[]);
        } else {
            self.rc_scopes.pop_scope();
        }
        Ok(terminated)
    }

    /// Finalize a for-loop by switching to exit_block and sealing internal blocks.
    ///
    /// Standard for-loop structure has 4 blocks: header, body, continue, exit.
    /// This must be called after compile_loop_body and any continue-block logic.
    ///
    /// Seals header, body, and continue blocks since their predecessors are now known.
    /// The exit block is NOT sealed - code following the loop may use variables
    /// defined before the loop (potentially in another loop), and sealing the exit
    /// block prematurely prevents Cranelift's SSA construction from properly
    /// threading those values through block parameters. The exit block will be
    /// sealed by seal_all_blocks() at function finalization.
    pub fn finalize_for_loop(
        &mut self,
        header: cranelift::prelude::Block,
        body_block: cranelift::prelude::Block,
        continue_block: cranelift::prelude::Block,
        exit_block: cranelift::prelude::Block,
    ) {
        self.switch_to_block(exit_block);
        self.builder.seal_block(header);
        self.builder.seal_block(body_block);
        self.builder.seal_block(continue_block);
        // exit_block left unsealed - see note above
    }

    // ========== Stack allocation ==========

    /// Allocate a stack slot of the given size in bytes
    pub fn alloc_stack(&mut self, size: u32) -> StackSlot {
        self.builder.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            size,
            0,
        ))
    }

    /// Copy a union heap buffer to a stack-allocated union slot (VirTypeId-native).
    ///
    /// Union heap layout: [tag:i8, is_rc:i8, pad(6), payload:i64] (16 bytes).
    /// Stack union layout: [tag:i8, pad(7), payload:i64] (16 bytes).
    /// This prevents use-after-free when reading union elements from dynamic arrays,
    /// since the array slot may be overwritten (e.g. by rehash) while the value is
    /// still in use.
    pub fn copy_union_heap_to_stack_v(
        &mut self,
        heap_ptr: Value,
        union_vir_ty: VirTypeId,
    ) -> CompiledValue {
        let union_size = self.type_size_v(union_vir_ty);
        let slot = self.alloc_stack(union_size);
        let tag = self
            .builder
            .ins()
            .load(types::I8, MemFlags::new(), heap_ptr, 0);
        self.builder.ins().stack_store(tag, slot, 0);
        let payload = self.builder.ins().load(
            types::I64,
            MemFlags::new(),
            heap_ptr,
            union_layout::PAYLOAD_OFFSET,
        );
        self.builder
            .ins()
            .stack_store(payload, slot, union_layout::PAYLOAD_OFFSET);
        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
        let mut cv = CompiledValue::new(ptr, ptr_type, union_vir_ty);
        cv.mark_borrowed();
        cv
    }

    // ========== Struct return conventions ==========

    /// Get the flat slot count for a struct (recursively counts leaf fields).
    /// This is the number of 8-byte slots needed to store the struct inline,
    /// accounting for nested struct fields.
    pub fn struct_flat_slot_count(&self, type_id: TypeId) -> Option<usize> {
        let vir_ty = self.vir_lookup(type_id);
        crate::types::vir_struct_helpers::vir_struct_flat_slot_count(
            vir_ty,
            self.vir_type_table(),
            self.analyzed(),
        )
    }

    /// Check if a struct type uses small return convention (1-2 flat slots).
    pub fn is_small_struct_return(&self, type_id: TypeId) -> bool {
        self.struct_flat_slot_count(type_id)
            .is_some_and(|count| count <= crate::MAX_SMALL_STRUCT_FIELDS)
    }

    /// Check if a struct type uses sret convention (3+ flat slots).
    pub fn is_sret_struct_return(&self, type_id: TypeId) -> bool {
        self.struct_flat_slot_count(type_id)
            .is_some_and(|count| count > crate::MAX_SMALL_STRUCT_FIELDS)
    }

    /// Check if a VIR struct type uses small return convention (1-2 flat slots).
    pub fn is_small_struct_return_v(&self, vir_ty: VirTypeId) -> bool {
        self.vir_struct_flat_slot_count(vir_ty)
            .is_some_and(|count| count <= crate::MAX_SMALL_STRUCT_FIELDS)
    }

    /// Check if a VIR struct type uses sret convention (3+ flat slots).
    pub fn is_sret_struct_return_v(&self, vir_ty: VirTypeId) -> bool {
        self.vir_struct_flat_slot_count(vir_ty)
            .is_some_and(|count| count > crate::MAX_SMALL_STRUCT_FIELDS)
    }

    /// If the return type uses sret convention (large struct), allocate a stack
    /// buffer for the return value and return a pointer to it. The caller should
    /// prepend this pointer to the call arguments.
    pub fn alloc_sret_ptr(&mut self, return_type_id: TypeId) -> CodegenResult<Option<Value>> {
        if !self.is_sret_struct_return(return_type_id) {
            return Ok(None);
        }
        let ptr_type = self.ptr_type();
        let flat_count = self
            .struct_flat_slot_count(return_type_id)
            .ok_or_else(|| CodegenError::internal("sret call: missing flat slot count"))?;
        let total_size = (flat_count as u32) * 8;
        let slot = self.alloc_stack(total_size);
        Ok(Some(self.builder.ins().stack_addr(ptr_type, slot, 0)))
    }

    /// Emit a return for a small struct (1-2 flat slots) via register passing (VIR variant).
    /// Loads flat slots into registers, pads to 2, and emits the return instruction.
    pub fn emit_small_struct_return_v(
        &mut self,
        struct_ptr: Value,
        ret_vir_ty: VirTypeId,
    ) -> CodegenResult<()> {
        let flat_count = self
            .vir_struct_flat_slot_count(ret_vir_ty)
            .ok_or_else(|| CodegenError::internal("struct return: missing flat slot count"))?;
        let mut return_vals = Vec::with_capacity(crate::MAX_SMALL_STRUCT_FIELDS);
        for i in 0..flat_count {
            let offset = (i as i32) * 8;
            let val = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), struct_ptr, offset);
            return_vals.push(val);
        }
        while return_vals.len() < crate::MAX_SMALL_STRUCT_FIELDS {
            return_vals.push(self.iconst_cached(types::I64, 0));
        }
        self.builder.ins().return_(&return_vals);
        Ok(())
    }

    /// Emit a return for a large struct (3+ flat slots) via sret convention (VIR variant).
    /// Copies flat slots into the sret buffer (first parameter) and returns the pointer.
    pub fn emit_sret_struct_return_v(
        &mut self,
        struct_ptr: Value,
        ret_vir_ty: VirTypeId,
    ) -> CodegenResult<()> {
        let entry_block =
            self.builder.func.layout.entry_block().ok_or_else(|| {
                CodegenError::internal("sret return: function has no entry block")
            })?;
        let sret_ptr = self.builder.block_params(entry_block)[0];
        let flat_count = self
            .vir_struct_flat_slot_count(ret_vir_ty)
            .ok_or_else(|| CodegenError::internal("sret return: missing flat slot count"))?;
        for i in 0..flat_count {
            let offset = (i as i32) * 8;
            let val = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), struct_ptr, offset);
            self.builder
                .ins()
                .store(MemFlags::new(), val, sret_ptr, offset);
        }
        self.builder.ins().return_(&[sret_ptr]);
        Ok(())
    }

    /// Reconstruct a struct from a multi-value return (two i64 registers).
    /// Allocates a stack slot and stores the register values as fields.
    pub fn reconstruct_struct_from_regs(
        &mut self,
        values: &[Value],
        type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let flat_count = self.struct_flat_slot_count(type_id).ok_or_else(|| {
            CodegenError::internal("reconstruct_struct_from_regs: expected struct type")
        })?;
        let total_size = (flat_count as u32) * 8;
        let slot = self.alloc_stack(total_size);

        for (i, &val) in values.iter().enumerate().take(flat_count) {
            let offset = (i as i32) * 8;
            self.builder.ins().stack_store(val, slot, offset);
        }

        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

        Ok(self.compiled_with_ty(ptr, ptr_type, type_id))
    }

    /// Copy a struct value to a new stack slot (value semantics).
    /// Copies all flat slots (8 bytes each), accounting for nested structs.
    pub fn copy_struct_value(&mut self, src: CompiledValue) -> CodegenResult<CompiledValue> {
        let flat_count = self
            .vir_struct_flat_slot_count(src.type_id)
            .ok_or_else(|| {
                CodegenError::type_mismatch("copy_struct_value", "struct type", "non-struct")
            })?;

        let total_size = (flat_count as u32) * 8;
        let dst_slot = self.alloc_stack(total_size);

        // Copy all flat slots (8 bytes each)
        for i in 0..flat_count {
            let offset = (i as i32) * 8;
            let val = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), src.value, offset);
            self.builder.ins().stack_store(val, dst_slot, offset);
        }

        let ptr_type = self.ptr_type();
        let dst_ptr = self.builder.ins().stack_addr(ptr_type, dst_slot, 0);

        Ok(CompiledValue::new(dst_ptr, ptr_type, src.type_id))
    }

    /// Copy a struct value to a heap allocation.
    /// Used when storing structs into arrays so the data survives the current stack frame.
    pub fn copy_struct_to_heap(&mut self, src: CompiledValue) -> CodegenResult<CompiledValue> {
        let flat_count = self
            .vir_struct_flat_slot_count(src.type_id)
            .ok_or_else(|| {
                CodegenError::type_mismatch("copy_struct_to_heap", "struct type", "non-struct")
            })?;

        let total_size = (flat_count as u32) * 8;
        let ptr_type = self.ptr_type();

        // Heap-allocate storage
        let heap_alloc_ref = self.runtime_func_ref(RuntimeKey::HeapAlloc)?;
        let size_val = self.iconst_cached(ptr_type, total_size as i64);
        let alloc_call = self.builder.ins().call(heap_alloc_ref, &[size_val]);
        let heap_ptr = self.builder.inst_results(alloc_call)[0];

        // Copy all flat slots (8 bytes each) from stack to heap
        for i in 0..flat_count {
            let offset = (i as i32) * 8;
            let val = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), src.value, offset);
            self.builder
                .ins()
                .store(MemFlags::new(), val, heap_ptr, offset);
        }

        Ok(CompiledValue::new(heap_ptr, ptr_type, src.type_id))
    }

    // ========== Call result & union helpers ==========

    /// Get the result of a call instruction as a CompiledValue.
    ///
    /// If the call has no results, returns void_value().
    /// For fallible returns with 2 results (tag, payload), packs them into a stack slot.
    /// Otherwise, wraps the first result with the given return_type_id.
    pub fn call_result(
        &mut self,
        call: cranelift_codegen::ir::Inst,
        return_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let results = self.builder.inst_results(call);
        if results.is_empty() {
            return Ok(self.void_value());
        }

        // Classify the return ABI to dispatch result reconstruction.
        let ret_vir = self.vir_lookup(return_type_id);
        let struct_slots = self.vir_struct_flat_slot_count(ret_vir);
        let ret_abi =
            vole_vir::func::ReturnAbi::classify(ret_vir, self.vir_type_table(), struct_slots);
        match ret_abi {
            vole_vir::func::ReturnAbi::WideFallible if results.len() == 3 => {
                let tag = results[0];
                let low = results[1];
                let high = results[2];
                let slot_size = 24u32;
                let slot = self.alloc_stack(slot_size);
                self.builder.ins().stack_store(tag, slot, 0);
                let i128_val = super::structs::reconstruct_i128(self.builder, low, high);
                super::structs::helpers::store_i128_to_stack(
                    self.builder,
                    i128_val,
                    slot,
                    union_layout::PAYLOAD_OFFSET,
                );
                let ptr_type = self.ptr_type();
                let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
                Ok(self.compiled_with_ty(ptr, ptr_type, return_type_id))
            }
            vole_vir::func::ReturnAbi::Fallible if results.len() == 2 => {
                let tag = results[0];
                let payload = results[1];
                let slot_size = union_layout::STANDARD_SIZE;
                let slot = self.alloc_stack(slot_size);
                self.builder.ins().stack_store(tag, slot, 0);
                self.builder
                    .ins()
                    .stack_store(payload, slot, union_layout::PAYLOAD_OFFSET);
                let ptr_type = self.ptr_type();
                let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
                Ok(self.compiled_with_ty(ptr, ptr_type, return_type_id))
            }
            vole_vir::func::ReturnAbi::SmallStruct { .. } => {
                let results_vec: Vec<Value> = results.to_vec();
                self.reconstruct_struct_from_regs(&results_vec, return_type_id)
            }
            vole_vir::func::ReturnAbi::UnionPtr => {
                let src_ptr = results[0];
                Ok(self.copy_union_ptr_to_local(src_ptr, return_type_id))
            }
            _ => {
                // SretStruct: result[0] is the sret pointer (handled by caller).
                // Single/Wide/Void: direct value return.
                Ok(self.compiled(results[0], return_type_id))
            }
        }
    }

    /// Copy a union value from a pointer (typically callee's stack) to a local stack slot.
    ///
    /// This prevents the returned union from being clobbered when the callee's
    /// stack frame is reused (e.g., by RC cleanup calls after a function return).
    pub fn copy_union_ptr_to_local(
        &mut self,
        src_ptr: Value,
        union_type_id: TypeId,
    ) -> CompiledValue {
        let union_size = self.type_size(union_type_id);
        let slot = self.alloc_stack(union_size);

        // Copy both tag (offset 0) and is_rc flag (offset 1) as a single i16 load.
        // The is_rc byte is required by copy_union_to_heap to decide whether to
        // rc_inc the payload when promoting the union to the heap.
        let tag_and_rc = self
            .builder
            .ins()
            .load(types::I16, MemFlags::new(), src_ptr, 0);
        self.builder.ins().stack_store(tag_and_rc, slot, 0);

        if union_size > union_layout::TAG_ONLY_SIZE {
            let payload = self.builder.ins().load(
                types::I64,
                MemFlags::new(),
                src_ptr,
                union_layout::PAYLOAD_OFFSET,
            );
            self.builder
                .ins()
                .stack_store(payload, slot, union_layout::PAYLOAD_OFFSET);
        }

        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
        let mut value = self.compiled(ptr, union_type_id);
        if self.rc_state(union_type_id).union_variants().is_some() {
            value.rc_lifecycle = RcLifecycle::Owned;
        }
        value
    }

    /// Load the payload from a union pointer using `VirTypeId` for size lookup.
    ///
    /// VirTypeId-native variant of [`load_union_payload`].
    pub fn load_union_payload_v(
        &mut self,
        union_ptr: Value,
        union_vir_ty: VirTypeId,
        payload_type: cranelift::prelude::Type,
    ) -> Value {
        let union_size = self.type_size_v(union_vir_ty);
        if union_size > union_layout::TAG_ONLY_SIZE {
            self.builder.ins().load(
                payload_type,
                MemFlags::new(),
                union_ptr,
                union_layout::PAYLOAD_OFFSET,
            )
        } else {
            self.iconst_cached(payload_type, 0)
        }
    }
}
