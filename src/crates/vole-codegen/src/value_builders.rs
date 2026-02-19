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

use vole_sema::PrimitiveType;
use vole_sema::type_arena::{SemaType as ArenaType, TypeId};

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
        CompiledValue::new(self.cached_void_val, types::I64, TypeId::VOID)
    }

    /// Create a zero/default value of the given Cranelift type.
    ///
    /// Used for empty match arms and other cases where a typed default is needed.
    pub fn typed_zero(&mut self, ty: cranelift::prelude::Type) -> Value {
        if ty == types::F64 {
            self.builder.ins().f64const(0.0)
        } else if ty == types::F32 {
            self.builder.ins().f32const(0.0)
        } else if ty == types::F128 {
            let zero_bits = self.builder.ins().iconst(types::I128, 0);
            self.builder
                .ins()
                .bitcast(types::F128, MemFlags::new(), zero_bits)
        } else {
            self.builder.ins().iconst(ty, 0)
        }
    }

    // ========== CompiledValue constructors ==========

    /// Wrap a Cranelift value as a Bool CompiledValue
    pub fn bool_value(&self, value: Value) -> CompiledValue {
        CompiledValue::new(value, types::I8, TypeId::BOOL)
    }

    /// Create a boolean constant (true or false)
    pub fn bool_const(&mut self, b: bool) -> CompiledValue {
        let value = self.builder.ins().iconst(types::I8, if b { 1 } else { 0 });
        self.bool_value(value)
    }

    /// Wrap a Cranelift value as an I64 CompiledValue
    pub fn i64_value(&self, value: Value) -> CompiledValue {
        CompiledValue::new(value, types::I64, TypeId::I64)
    }

    /// Create an integer constant with a specific Vole type
    pub fn int_const(&mut self, n: i64, type_id: TypeId) -> CompiledValue {
        let ty = self.cranelift_type(type_id);
        let arena = self.arena();
        // If bidirectional inference produced a float type for an integer literal
        // (can happen in generic contexts where the type parameter resolves to f64
        // during sema but codegen uses i64 for the type param), fall back to i64.
        // Float conversion for `let x: f64 = 5` is handled by sema recording the
        // literal as a FloatLiteral, not through int_const.
        //
        // Likewise, if sema contextual typing labels an int literal as a union
        // element, keep the literal concrete here and let explicit union boxing
        // happen at coercion/assignment boundaries.
        let (ty, type_id) = if ty == types::F64 || ty == types::F32 || arena.is_union(type_id) {
            (types::I64, TypeId::I64)
        } else {
            (ty, type_id)
        };
        // Cranelift's iconst doesn't support I128 directly - we need to create
        // an i64 constant and sign-extend it to i128.
        // For f128, use the runtime software representation (f64 payload in low 64 bits).
        let value = if ty == types::I128 {
            let i64_val = self.builder.ins().iconst(types::I64, n);
            sextend_const(self.builder, types::I128, i64_val)
        } else if ty == types::F128 {
            let low = self
                .builder
                .ins()
                .iconst(types::I64, (n as f64).to_bits() as i64);
            let wide = uextend_const(self.builder, types::I128, low);
            self.builder
                .ins()
                .bitcast(types::F128, MemFlags::new(), wide)
        } else {
            self.builder.ins().iconst(ty, n)
        };
        CompiledValue::new(value, ty, type_id)
    }

    /// Create a float constant with explicit type (for bidirectional inference)
    pub fn float_const(&mut self, n: f64, type_id: TypeId) -> CompiledValue {
        let arena = self.arena();
        if arena.is_union(type_id) {
            let v = self.builder.ins().f64const(n);
            return CompiledValue::new(v, types::F64, TypeId::F64);
        }
        let (ty, value) = match arena.get(type_id) {
            ArenaType::Primitive(PrimitiveType::F32) => {
                let v = self.builder.ins().f32const(n as f32);
                (types::F32, v)
            }
            ArenaType::Primitive(PrimitiveType::F128) => {
                // Runtime f128 currently uses a compact software representation:
                // low 64 bits = f64 payload, high 64 bits = 0.
                let low = self.builder.ins().iconst(types::I64, n.to_bits() as i64);
                let wide = uextend_const(self.builder, types::I128, low);
                let v = self
                    .builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), wide);
                (types::F128, v)
            }
            _ => {
                // Default to F64
                let v = self.builder.ins().f64const(n);
                (types::F64, v)
            }
        };
        CompiledValue::new(value, ty, type_id)
    }

    /// Create a nil value
    pub fn nil_value(&mut self) -> CompiledValue {
        let value = self.builder.ins().iconst(types::I8, 0);
        CompiledValue::new(value, types::I8, TypeId::NIL)
    }

    // ========== Tag helpers ==========

    /// Load a tag byte from a union/optional pointer and compare to expected value.
    /// Returns an i8 value (1 if equal, 0 if not).
    pub fn tag_eq(&mut self, ptr: Value, expected_tag: i64) -> Value {
        let tag = self.builder.ins().load(types::I8, MemFlags::new(), ptr, 0);
        let expected = self.builder.ins().iconst(types::I8, expected_tag);
        self.builder.ins().icmp(IntCC::Equal, tag, expected)
    }

    /// Load a tag byte from a union/optional pointer and compare for inequality.
    /// Returns an i8 value (1 if not equal, 0 if equal).
    pub fn tag_ne(&mut self, ptr: Value, expected_tag: i64) -> Value {
        let tag = self.builder.ins().load(types::I8, MemFlags::new(), ptr, 0);
        let expected = self.builder.ins().iconst(types::I8, expected_tag);
        self.builder.ins().icmp(IntCC::NotEqual, tag, expected)
    }

    // ========== String / compiled helpers ==========

    /// Wrap a Cranelift value as a String CompiledValue marked as an RC temp
    pub fn string_temp(&self, value: Value) -> CompiledValue {
        CompiledValue::owned(value, self.ptr_type(), TypeId::STRING)
    }

    /// Create a CompiledValue from a value and TypeId, automatically computing the cranelift type
    pub fn compiled(&self, value: Value, type_id: TypeId) -> CompiledValue {
        CompiledValue::new(value, self.cranelift_type(type_id), type_id)
    }

    /// Convert a raw i64 field value to a CompiledValue with the proper type.
    /// Handles type narrowing for primitives (f64 bitcast, bool/int reduction).
    pub fn convert_field_value(&mut self, raw_value: Value, type_id: TypeId) -> CompiledValue {
        // Use env.analyzed.type_arena() to avoid borrow conflict with builder
        let arena = self.env.analyzed.type_arena();
        let (value, ty) =
            super::structs::convert_field_value_id(self.builder, raw_value, type_id, arena);
        CompiledValue::new(value, ty, type_id)
    }

    /// Extract a value from a TaggedValue (unknown type) after type narrowing.
    /// The raw_value is the value field from the TaggedValue (already loaded from offset 8).
    /// This converts it to the appropriate Cranelift type based on the narrowed type.
    pub fn extract_unknown_value(&mut self, raw_value: Value, type_id: TypeId) -> CompiledValue {
        self.convert_field_value(raw_value, type_id)
    }

    // ========== Call argument compilation ==========

    /// Compile a list of expression arguments into Cranelift values.
    /// This is the common pattern for function/method calls.
    pub fn compile_call_args(&mut self, args: &[vole_frontend::Expr]) -> CodegenResult<Vec<Value>> {
        let (values, _) = self.compile_call_args_tracking_rc(args)?;
        Ok(values)
    }

    /// Compile call arguments, returning both Cranelift values for the call
    /// and owned `CompiledValue`s that need rc_dec after the call completes.
    pub fn compile_call_args_tracking_rc(
        &mut self,
        args: &[vole_frontend::Expr],
    ) -> CodegenResult<(Vec<Value>, Vec<CompiledValue>)> {
        let mut values = Vec::with_capacity(args.len());
        let mut rc_temps = Vec::new();
        for arg in args {
            let compiled = self.expr(arg)?;
            if compiled.is_owned() {
                rc_temps.push(compiled);
            }
            values.push(compiled.value);
        }
        Ok((values, rc_temps))
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
        self.builder.switch_to_block(block);
        self.builder.seal_block(block);
    }

    /// Compile a loop body with proper loop context setup.
    ///
    /// - Registers the loop with exit_block and continue_block
    /// - Compiles the body block
    /// - If not terminated, jumps to continue_block
    ///
    /// Returns true if the body terminated (return/break).
    pub fn compile_loop_body(
        &mut self,
        body: &vole_frontend::Block,
        exit_block: cranelift::prelude::Block,
        continue_block: cranelift::prelude::Block,
    ) -> CodegenResult<bool> {
        let rc_depth = self.rc_scope_depth();
        self.cf.push_loop(exit_block, continue_block, rc_depth);
        // Push a per-iteration RC scope so temps created in the loop body
        // get cleaned up at the end of each iteration, not just once at loop exit.
        self.push_rc_scope();
        let terminated = self.block(body)?;
        self.cf.pop_loop();
        if !terminated {
            // Emit per-iteration cleanup before jumping back to continue/header
            self.pop_rc_scope_with_cleanup(None)?;
            self.builder.ins().jump(continue_block, &[]);
        } else {
            // Body terminated (break/return) — scope already cleaned by those paths.
            // Still pop the scope to keep the stack balanced.
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
        self.builder.switch_to_block(exit_block);
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

    /// Copy a union heap buffer (16 bytes: [tag:i8, is_rc:i8, pad(6), payload:i64])
    /// to a stack-allocated union slot (16 bytes: [tag:i8, pad(7), payload:i64]).
    /// This prevents use-after-free when reading union elements from dynamic arrays,
    /// since the array slot may be overwritten (e.g. by rehash) while the value is
    /// still in use.
    pub fn copy_union_heap_to_stack(
        &mut self,
        heap_ptr: Value,
        union_type_id: TypeId,
    ) -> CompiledValue {
        let union_size = self.type_size(union_type_id);
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
        let mut cv = CompiledValue::new(ptr, ptr_type, union_type_id);
        cv.mark_borrowed();
        cv
    }

    // ========== Struct return conventions ==========

    /// Get the flat slot count for a struct (recursively counts leaf fields).
    /// This is the number of 8-byte slots needed to store the struct inline,
    /// accounting for nested struct fields.
    pub fn struct_flat_slot_count(&self, type_id: TypeId) -> Option<usize> {
        let arena = self.arena();
        let entities = self.registry();
        super::structs::struct_flat_slot_count(type_id, arena, entities)
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

    /// If the return type uses sret convention (large struct), allocate a stack
    /// buffer for the return value and return a pointer to it. The caller should
    /// prepend this pointer to the call arguments.
    pub fn alloc_sret_ptr(&mut self, return_type_id: TypeId) -> Option<Value> {
        if !self.is_sret_struct_return(return_type_id) {
            return None;
        }
        let ptr_type = self.ptr_type();
        let flat_count = self
            .struct_flat_slot_count(return_type_id)
            .expect("INTERNAL: sret call: missing flat slot count");
        let total_size = (flat_count as u32) * 8;
        let slot = self.alloc_stack(total_size);
        Some(self.builder.ins().stack_addr(ptr_type, slot, 0))
    }

    /// Emit a return for a small struct (1-2 flat slots) via register passing.
    /// Loads flat slots into registers, pads to 2, and emits the return instruction.
    pub fn emit_small_struct_return(&mut self, struct_ptr: Value, ret_type_id: TypeId) {
        let flat_count = self
            .struct_flat_slot_count(ret_type_id)
            .expect("INTERNAL: struct return: missing flat slot count");
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
            return_vals.push(self.builder.ins().iconst(types::I64, 0));
        }
        self.builder.ins().return_(&return_vals);
    }

    /// Emit a return for a large struct (3+ flat slots) via sret convention.
    /// Copies flat slots into the sret buffer (first parameter) and returns the pointer.
    pub fn emit_sret_struct_return(&mut self, struct_ptr: Value, ret_type_id: TypeId) {
        let entry_block = self
            .builder
            .func
            .layout
            .entry_block()
            .expect("INTERNAL: sret return: function has no entry block");
        let sret_ptr = self.builder.block_params(entry_block)[0];
        let flat_count = self
            .struct_flat_slot_count(ret_type_id)
            .expect("INTERNAL: sret return: missing flat slot count");
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
    }

    /// Reconstruct a struct from a multi-value return (two i64 registers).
    /// Allocates a stack slot and stores the register values as fields.
    pub fn reconstruct_struct_from_regs(
        &mut self,
        values: &[Value],
        type_id: TypeId,
    ) -> CompiledValue {
        let flat_count = self
            .struct_flat_slot_count(type_id)
            .expect("INTERNAL: reconstruct_struct_from_regs: expected struct type");
        let total_size = (flat_count as u32) * 8;
        let slot = self.alloc_stack(total_size);

        for (i, &val) in values.iter().enumerate().take(flat_count) {
            let offset = (i as i32) * 8;
            self.builder.ins().stack_store(val, slot, offset);
        }

        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

        CompiledValue::new(ptr, ptr_type, type_id)
    }

    /// Copy a struct value to a new stack slot (value semantics).
    /// Copies all flat slots (8 bytes each), accounting for nested structs.
    pub fn copy_struct_value(&mut self, src: CompiledValue) -> CodegenResult<CompiledValue> {
        let flat_count = self.struct_flat_slot_count(src.type_id).ok_or_else(|| {
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
        let flat_count = self.struct_flat_slot_count(src.type_id).ok_or_else(|| {
            CodegenError::type_mismatch("copy_struct_to_heap", "struct type", "non-struct")
        })?;

        let total_size = (flat_count as u32) * 8;
        let ptr_type = self.ptr_type();

        // Heap-allocate storage
        let heap_alloc_ref = self.runtime_func_ref(RuntimeKey::HeapAlloc)?;
        let size_val = self.builder.ins().iconst(ptr_type, total_size as i64);
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
    ) -> CompiledValue {
        let results = self.builder.inst_results(call);
        if results.is_empty() {
            return self.void_value();
        }

        // Check for wide fallible multi-value return (3 results: tag, low, high)
        // i128 success values are split across two i64 registers
        if results.len() == 3 && crate::types::is_wide_fallible(return_type_id, self.arena()) {
            let tag = results[0];
            let low = results[1];
            let high = results[2];

            // Allocate stack slot: 8 (tag) + 16 (i128 payload) = 24 bytes
            let slot_size = 24u32;
            let slot = self.alloc_stack(slot_size);

            // Store tag at offset 0
            self.builder.ins().stack_store(tag, slot, 0);
            // Reconstruct i128 from low/high and store at offset 8
            let i128_val = super::structs::reconstruct_i128(self.builder, low, high);
            super::structs::helpers::store_i128_to_stack(
                self.builder,
                i128_val,
                slot,
                union_layout::PAYLOAD_OFFSET,
            );

            let ptr_type = self.ptr_type();
            let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

            return CompiledValue::new(ptr, ptr_type, return_type_id);
        }

        // Check for fallible multi-value return (2 results: tag, payload)
        if results.len() == 2 && self.arena().unwrap_fallible(return_type_id).is_some() {
            let tag = results[0];
            let payload = results[1];

            // Allocate stack slot to store (tag, payload) for callers that expect a pointer
            let slot_size = union_layout::STANDARD_SIZE;
            let slot = self.alloc_stack(slot_size);

            // Store tag at offset 0
            self.builder.ins().stack_store(tag, slot, 0);
            // Store payload at offset 8
            self.builder
                .ins()
                .stack_store(payload, slot, union_layout::PAYLOAD_OFFSET);

            // Get pointer to stack slot
            let ptr_type = self.ptr_type();
            let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

            return CompiledValue::new(ptr, ptr_type, return_type_id);
        }

        // Check for small struct multi-value return (2 results: field0, field1)
        if results.len() == 2 && self.is_small_struct_return(return_type_id) {
            let results_vec: Vec<Value> = results.to_vec();
            return self.reconstruct_struct_from_regs(&results_vec, return_type_id);
        }

        // Large struct sret return: the result is already a pointer to the buffer
        // (handled by the caller passing the sret arg, result[0] is the sret pointer)
        // No special handling needed here since result[0] is already the pointer.

        // If the return type is a union, the returned value is a pointer to the callee's stack.
        // We must copy the union data to our own stack immediately, before any subsequent
        // calls (e.g. rc_dec for temporary args) can clobber the callee's stack frame.
        if self.arena().is_union(return_type_id) {
            let src_ptr = results[0];
            return self.copy_union_ptr_to_local(src_ptr, return_type_id);
        }

        self.compiled(results[0], return_type_id)
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

        let tag = self
            .builder
            .ins()
            .load(types::I8, MemFlags::new(), src_ptr, 0);
        self.builder.ins().stack_store(tag, slot, 0);

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

    /// Load the payload from a union pointer, returning zero if the union is tag-only.
    ///
    /// Sentinel-only unions have `union_size == TAG_ONLY_SIZE` (8 bytes, tag only)
    /// and carry no payload data, so this returns an `iconst 0` for those.
    pub fn load_union_payload(
        &mut self,
        union_ptr: Value,
        union_type_id: TypeId,
        payload_type: cranelift::prelude::Type,
    ) -> Value {
        let union_size = self.type_size(union_type_id);
        if union_size > union_layout::TAG_ONLY_SIZE {
            self.builder.ins().load(
                payload_type,
                MemFlags::new(),
                union_ptr,
                union_layout::PAYLOAD_OFFSET,
            )
        } else {
            self.builder.ins().iconst(payload_type, 0)
        }
    }
}
