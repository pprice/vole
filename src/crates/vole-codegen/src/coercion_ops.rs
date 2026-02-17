// src/codegen/coercion_ops.rs
//
// Type coercion methods - impl Cg methods for type-level coercions.
//
// Handles value coercion between types (union wrapping, interface boxing,
// unknown boxing), Cranelift IR value coercion (int/float widening/narrowing),
// call argument coercion, return value coercion, and default parameter
// compilation. Split from context.rs.

use cranelift::prelude::{InstBuilder, MemFlags, Type, Value, types};

use smallvec::SmallVec;
use vole_frontend::Expr;
use vole_sema::type_arena::TypeId;

use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::union_layout;

use super::context::{Cg, deref_expr_ptr};
use super::types::CompiledValue;

impl<'a, 'b, 'ctx> Cg<'a, 'b, 'ctx> {
    // ========== Cranelift IR value coercion ==========

    /// Coerce a single Cranelift IR value from one type to another.
    ///
    /// Handles int<->int (sextend/ireduce), float<->int (bitcast),
    /// int<->float (bitcast), and float<->float (fpromote/fdemote).
    /// Returns the value unchanged if no coercion applies.
    pub(crate) fn coerce_cranelift_value(
        &mut self,
        value: Value,
        actual_ty: Type,
        expected_ty: Type,
    ) -> Value {
        if actual_ty == expected_ty {
            return value;
        }
        if actual_ty.is_int() && expected_ty.is_int() {
            if expected_ty.bytes() > actual_ty.bytes() {
                self.builder.ins().sextend(expected_ty, value)
            } else {
                self.builder.ins().ireduce(expected_ty, value)
            }
        } else if actual_ty.is_float() && expected_ty.is_int() {
            // float -> int via bitcast (for generic contexts using i64 for type params)
            if actual_ty == types::F64 && expected_ty == types::I64 {
                self.builder
                    .ins()
                    .bitcast(types::I64, MemFlags::new(), value)
            } else if actual_ty == types::F32 && expected_ty == types::I64 {
                let f64_val = self.builder.ins().fpromote(types::F64, value);
                self.builder
                    .ins()
                    .bitcast(types::I64, MemFlags::new(), f64_val)
            } else if actual_ty == types::F128 && expected_ty == types::I128 {
                self.builder
                    .ins()
                    .bitcast(types::I128, MemFlags::new(), value)
            } else {
                value
            }
        } else if actual_ty.is_int() && expected_ty.is_float() {
            if actual_ty == types::I64 && expected_ty == types::F64 {
                self.builder
                    .ins()
                    .bitcast(types::F64, MemFlags::new(), value)
            } else if actual_ty == types::I128 && expected_ty == types::F128 {
                self.builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), value)
            } else {
                value
            }
        } else if actual_ty == types::F32 && expected_ty == types::F64 {
            self.builder.ins().fpromote(types::F64, value)
        } else if actual_ty == types::F64 && expected_ty == types::F32 {
            self.builder.ins().fdemote(types::F32, value)
        } else {
            value
        }
    }

    // ========== Call argument / return coercion ==========

    /// Coerce call arguments to match a function signature's expected parameter types.
    ///
    /// In generic contexts, expressions may produce narrow integer types (i8, i16, i32)
    /// while the callee expects i64 (or vice versa). This method inserts `sextend` or
    /// `ireduce` instructions as needed so the Cranelift verifier is satisfied.
    /// Float-to-int and int-to-float coercions are also handled via bitcast/fpromote.
    pub fn coerce_call_args(
        &mut self,
        func_ref: cranelift::codegen::ir::FuncRef,
        args: &[Value],
    ) -> SmallVec<[Value; 8]> {
        let sig_ref = self.builder.func.dfg.ext_funcs[func_ref].signature;
        let expected: SmallVec<[Type; 8]> = self.builder.func.dfg.signatures[sig_ref]
            .params
            .iter()
            .map(|p| p.value_type)
            .collect();

        let mut coerced: SmallVec<[Value; 8]> = SmallVec::with_capacity(args.len());
        for (i, &arg) in args.iter().enumerate() {
            let actual_ty = self.builder.func.dfg.value_type(arg);
            let val = match expected.get(i).copied() {
                Some(exp) if actual_ty != exp => self.coerce_cranelift_value(arg, actual_ty, exp),
                _ => arg,
            };
            coerced.push(val);
        }
        coerced
    }

    /// Coerce a return value to match the function's declared return type.
    ///
    /// In generic function contexts, sema may infer a specific type for an
    /// expression (e.g., i32 or f64) while the function signature uses i64
    /// for the generic type parameter. This method ensures the value type
    /// matches the function signature's return type.
    pub fn coerce_return_value(&mut self, value: Value) -> Value {
        let value_ty = self.builder.func.dfg.value_type(value);
        let ret_types = &self.builder.func.signature.returns;
        if ret_types.len() != 1 {
            return value;
        }
        let expected_ty = ret_types[0].value_type;
        self.coerce_cranelift_value(value, value_ty, expected_ty)
    }

    // ========== Type-level coercion ==========

    /// Coerce a value to match a target type if needed.
    ///
    /// Handles three cases:
    /// - If target is an interface and value is not, boxes the value
    /// - If target is a union and value is not, wraps the value in a union
    /// - If target is unknown, boxes the value with a type tag (TaggedValue)
    ///
    /// Returns the value unchanged if no coercion is needed.
    pub fn coerce_to_type(
        &mut self,
        value: CompiledValue,
        target_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Resolve generic type params in monomorphized contexts before coercion checks.
        // This keeps union/interface coercions from comparing concrete targets against
        // unresolved TypeParam values.
        let resolved_target_type_id = self.try_substitute_type(target_type_id);
        let resolved_value_type_id = self.try_substitute_type(value.type_id);
        let mut resolved_value = value;
        resolved_value.type_id = resolved_value_type_id;

        let (
            is_target_interface,
            is_value_interface,
            is_target_union,
            is_value_union,
            is_target_unknown,
            is_value_unknown,
            is_value_runtime_iterator,
            is_target_numeric,
            is_value_numeric,
        ) = {
            let arena = self.arena();
            (
                arena.is_interface(resolved_target_type_id),
                arena.is_interface(resolved_value_type_id),
                arena.is_union(resolved_target_type_id),
                arena.is_union(resolved_value_type_id),
                arena.is_unknown(resolved_target_type_id),
                arena.is_unknown(resolved_value_type_id),
                arena.is_runtime_iterator(resolved_value_type_id),
                arena.is_numeric(resolved_target_type_id),
                arena.is_numeric(resolved_value_type_id),
            )
        };

        if is_target_numeric
            && is_value_numeric
            && resolved_target_type_id != resolved_value_type_id
        {
            return self.coerce_numeric_to_type(resolved_value, resolved_target_type_id);
        }
        // RuntimeIterator is a concrete type that implements Iterator dispatch
        // directly via runtime_iterator_method; skip interface boxing.
        if is_target_interface && !is_value_interface && !is_value_runtime_iterator {
            self.box_interface_value(resolved_value, resolved_target_type_id)
        } else if is_target_union && !is_value_union {
            self.construct_union_id(resolved_value, resolved_target_type_id)
        } else if is_target_unknown && !is_value_unknown {
            self.box_to_unknown(resolved_value)
        } else {
            Ok(resolved_value)
        }
    }

    fn coerce_numeric_to_type(
        &mut self,
        value: CompiledValue,
        target_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let target_ty = self.cranelift_type(target_type_id);
        if value.ty == target_ty {
            return Ok(CompiledValue::new(value.value, target_ty, target_type_id));
        }

        let source_is_unsigned = self.arena().is_unsigned(value.type_id);
        let target_is_unsigned = self.arena().is_unsigned(target_type_id);

        let converted = if target_ty == types::F128 {
            match value.ty {
                ty if ty == types::F128 => value.value,
                ty if ty == types::F64 => {
                    let bits = self.call_runtime(RuntimeKey::F64ToF128, &[value.value])?;
                    self.builder
                        .ins()
                        .bitcast(types::F128, MemFlags::new(), bits)
                }
                ty if ty == types::F32 => {
                    let bits = self.call_runtime(RuntimeKey::F32ToF128, &[value.value])?;
                    self.builder
                        .ins()
                        .bitcast(types::F128, MemFlags::new(), bits)
                }
                ty if ty == types::I128 => {
                    let bits = self.call_runtime(RuntimeKey::I128ToF128, &[value.value])?;
                    self.builder
                        .ins()
                        .bitcast(types::F128, MemFlags::new(), bits)
                }
                ty if ty.is_int() => {
                    let i64_val = if ty == types::I64 {
                        value.value
                    } else if ty.bytes() < 8 {
                        if source_is_unsigned {
                            self.builder.ins().uextend(types::I64, value.value)
                        } else {
                            self.builder.ins().sextend(types::I64, value.value)
                        }
                    } else {
                        self.builder.ins().ireduce(types::I64, value.value)
                    };
                    let bits = self.call_runtime(RuntimeKey::I64ToF128, &[i64_val])?;
                    self.builder
                        .ins()
                        .bitcast(types::F128, MemFlags::new(), bits)
                }
                _ => value.value,
            }
        } else if value.ty == types::F128 {
            let f128_bits = self
                .builder
                .ins()
                .bitcast(types::I128, MemFlags::new(), value.value);
            match target_ty {
                ty if ty == types::F64 => self.call_runtime(RuntimeKey::F128ToF64, &[f128_bits])?,
                ty if ty == types::F32 => self.call_runtime(RuntimeKey::F128ToF32, &[f128_bits])?,
                ty if ty == types::I128 => {
                    self.call_runtime(RuntimeKey::F128ToI128, &[f128_bits])?
                }
                ty if ty.is_int() => {
                    let i64_val = self.call_runtime(RuntimeKey::F128ToI64, &[f128_bits])?;
                    if ty == types::I64 {
                        i64_val
                    } else if ty.bytes() < 8 {
                        self.builder.ins().ireduce(ty, i64_val)
                    } else {
                        // i128 path is handled above; keep for defensive completeness.
                        self.builder.ins().sextend(ty, i64_val)
                    }
                }
                _ => value.value,
            }
        } else if target_ty.is_int() && value.ty.is_int() {
            if target_ty.bytes() > value.ty.bytes() {
                if source_is_unsigned {
                    self.builder.ins().uextend(target_ty, value.value)
                } else {
                    self.builder.ins().sextend(target_ty, value.value)
                }
            } else {
                self.builder.ins().ireduce(target_ty, value.value)
            }
        } else if target_ty.is_float() && value.ty.is_float() {
            if value.ty == types::F32 && target_ty == types::F64 {
                self.builder.ins().fpromote(types::F64, value.value)
            } else if value.ty == types::F64 && target_ty == types::F32 {
                self.builder.ins().fdemote(types::F32, value.value)
            } else {
                value.value
            }
        } else if target_ty.is_float() && value.ty.is_int() {
            if source_is_unsigned {
                self.builder.ins().fcvt_from_uint(target_ty, value.value)
            } else {
                self.builder.ins().fcvt_from_sint(target_ty, value.value)
            }
        } else if target_ty.is_int() && value.ty.is_float() {
            if target_is_unsigned {
                self.builder.ins().fcvt_to_uint(target_ty, value.value)
            } else {
                self.builder.ins().fcvt_to_sint(target_ty, value.value)
            }
        } else {
            value.value
        };

        Ok(CompiledValue::new(converted, target_ty, target_type_id))
    }

    /// Box a value into the unknown type (TaggedValue representation).
    ///
    /// Creates a 16-byte stack slot containing:
    /// - Offset 0: tag (u64) - runtime type identifier
    /// - Offset 8: value (u64) - the actual value (or pointer for reference types)
    ///
    /// Returns a pointer to the TaggedValue.
    pub fn box_to_unknown(&mut self, value: CompiledValue) -> CodegenResult<CompiledValue> {
        use crate::types::unknown_type_tag;

        if value.ty == types::I128 || value.ty == types::F128 {
            return Err(CodegenError::type_mismatch(
                "unknown boxing",
                "a type that fits in 64 bits",
                "128-bit values (i128/f128 cannot be boxed as unknown)",
            ));
        }

        // Get the runtime tag for this type
        let tag = unknown_type_tag(value.type_id, self.arena());

        // Create a stack slot for TaggedValue
        let slot = self.alloc_stack(union_layout::STANDARD_SIZE);

        // Store the tag at offset 0
        let tag_val = self.builder.ins().iconst(types::I64, tag as i64);
        self.builder.ins().stack_store(tag_val, slot, 0);

        // Store the value at offset 8
        // Convert to i64 if needed (for smaller types)
        let value_as_i64 = if value.ty == types::I64 || value.ty == self.ptr_type() {
            value.value
        } else if value.ty == types::F64 {
            // F64 is stored as bits
            self.builder
                .ins()
                .bitcast(types::I64, MemFlags::new(), value.value)
        } else if value.ty == types::F32 {
            // F32 needs to be extended
            let i32_val = self
                .builder
                .ins()
                .bitcast(types::I32, MemFlags::new(), value.value);
            self.builder.ins().uextend(types::I64, i32_val)
        } else if value.ty.is_int() && value.ty.bytes() < 8 {
            // Extend smaller integers to i64
            if self.arena().is_unsigned(value.type_id) {
                self.builder.ins().uextend(types::I64, value.value)
            } else {
                self.builder.ins().sextend(types::I64, value.value)
            }
        } else {
            value.value
        };

        self.builder
            .ins()
            .stack_store(value_as_i64, slot, union_layout::PAYLOAD_OFFSET);

        // Return pointer to the TaggedValue
        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

        Ok(CompiledValue::new(ptr, ptr_type, TypeId::UNKNOWN))
    }

    /// Box a value as an interface type.
    ///
    /// This method avoids borrow issues by having exclusive access to self.
    /// If the value is already an interface or the type is not an interface,
    /// returns the value unchanged.
    pub fn box_interface_value(
        &mut self,
        value: CompiledValue,
        interface_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        crate::interfaces::box_interface_value_id(
            self.builder,
            self.codegen_ctx,
            self.env,
            value,
            interface_type_id,
        )
    }

    // ========== Default parameter compilation ==========

    /// Compile default expressions for omitted parameters.
    ///
    /// This is a unified helper used by function calls, method calls, and static method calls.
    /// It takes pre-extracted raw pointers to default expressions to avoid borrow checker issues.
    ///
    /// # Arguments
    /// - `default_ptrs`: Raw pointers to default expressions (indexed by parameter position)
    /// - `start_index`: Index of the first omitted parameter
    /// - `expected_type_ids`: Expected TypeIds for the omitted parameters (slice starting at start_index)
    /// - `is_generic_class`: Whether this is a generic class call (needs value_to_word conversion)
    ///
    /// # Safety
    /// The raw pointers must point to data in EntityRegistry which outlives compilation.
    pub fn compile_defaults_from_ptrs(
        &mut self,
        default_ptrs: &[Option<*const Expr>],
        start_index: usize,
        expected_type_ids: &[TypeId],
        is_generic_class: bool,
    ) -> CodegenResult<(Vec<Value>, Vec<CompiledValue>)> {
        use crate::types::value_to_word;

        let mut args = Vec::new();
        let mut rc_owned = Vec::new();
        for (i, &param_type_id) in expected_type_ids.iter().enumerate() {
            let param_idx = start_index + i;
            if let Some(Some(default_ptr)) = default_ptrs.get(param_idx) {
                let default_expr = deref_expr_ptr(*default_ptr);
                let compiled = self.expr_with_expected_type(default_expr, param_type_id)?;

                // Track owned RC values for cleanup after the call
                if compiled.is_owned() {
                    rc_owned.push(compiled);
                }

                // Coerce to the expected param type (handles interface boxing, union construction)
                let compiled = self.coerce_to_type(compiled, param_type_id)?;

                // Handle integer narrowing/widening if needed
                let expected_ty = self.cranelift_type(param_type_id);
                let compiled = if compiled.ty.is_int()
                    && expected_ty.is_int()
                    && expected_ty.bits() != compiled.ty.bits()
                {
                    let new_value = if expected_ty.bits() < compiled.ty.bits() {
                        self.builder.ins().ireduce(expected_ty, compiled.value)
                    } else {
                        self.builder.ins().sextend(expected_ty, compiled.value)
                    };
                    CompiledValue::new(new_value, expected_ty, param_type_id)
                } else {
                    compiled
                };

                // Generic class methods expect i64 for TypeParam, convert if needed
                let arg_value = if is_generic_class && compiled.ty != types::I64 {
                    let ptr_type = self.ptr_type();
                    let arena = self.env.analyzed.type_arena();
                    let registry = self.env.analyzed.entity_registry();
                    value_to_word(
                        self.builder,
                        &compiled,
                        ptr_type,
                        None, // No heap alloc needed for primitive conversions
                        arena,
                        registry,
                    )?
                } else {
                    compiled.value
                };
                args.push(arg_value);
            }
        }

        Ok((args, rc_owned))
    }
}
