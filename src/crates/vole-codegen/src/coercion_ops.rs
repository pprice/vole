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
use vole_identity::{FunctionId, MethodId, NodeId, TypeId, VirTypeId};
use vole_vir::numeric_model::{NumericCoercion, numeric_coercion_v};

use vole_vir::expr::CoerceKind;

use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};

use super::context::Cg;
use super::types::CompiledValue;
use crate::ops::{sextend_const, uextend_const};

/// Pre-computed type classification for a coercion source/target pair.
///
/// Groups the boolean type queries needed by `coerce_to_type_detected()` so
/// the dispatch logic reads as a match on properties rather than 9 separate
/// let bindings.
struct CoercionClassification {
    target_interface: bool,
    value_interface: bool,
    target_union: bool,
    value_union: bool,
    target_unknown: bool,
    value_unknown: bool,
    value_runtime_iterator: bool,
    target_numeric: bool,
    value_numeric: bool,
}

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
                sextend_const(self.builder, expected_ty, value)
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

        // Fast path: scan for the first type mismatch. Most calls need no
        // coercion so we avoid allocating a SmallVec of expected types and
        // the per-element push loop entirely.
        let first_mismatch = {
            let params = &self.builder.func.dfg.signatures[sig_ref].params;
            args.iter()
                .enumerate()
                .position(|(i, &arg)| match params.get(i) {
                    Some(p) => self.builder.func.dfg.value_type(arg) != p.value_type,
                    None => false,
                })
        };

        let Some(mismatch_idx) = first_mismatch else {
            // All types match — just copy the args.
            return SmallVec::from_slice(args);
        };

        // Slow path: snapshot expected types (releases immutable borrow on
        // self.builder so coerce_cranelift_value can take &mut self), copy
        // the already-matching prefix, then coerce from mismatch onward.
        let expected: SmallVec<[Type; 8]> = self.builder.func.dfg.signatures[sig_ref]
            .params
            .iter()
            .map(|p| p.value_type)
            .collect();

        let mut coerced: SmallVec<[Value; 8]> = SmallVec::with_capacity(args.len());
        coerced.extend_from_slice(&args[..mismatch_idx]);
        for (i, &arg) in args[mismatch_idx..].iter().enumerate() {
            let idx = mismatch_idx + i;
            let actual_ty = self.builder.func.dfg.value_type(arg);
            let val = match expected.get(idx).copied() {
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
    /// Coerce a value to the target type specified by a sema `TypeId`.
    ///
    /// Boundary bridge: converts `TypeId` to `VirTypeId` via `vir_lookup_or_compat`
    /// and delegates to [`coerce_to_type`](Self::coerce_to_type).
    /// Uses compat encoding so unmapped cross-module types survive round-tripping.
    pub fn coerce_to_type_id(
        &mut self,
        value: CompiledValue,
        target_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        self.coerce_to_type(value, self.vir_lookup_or_compat(target_type_id))
    }

    pub fn coerce_to_type(
        &mut self,
        value: CompiledValue,
        target_vir_ty: VirTypeId,
    ) -> CodegenResult<CompiledValue> {
        self.coerce_to_type_hinted(value, target_vir_ty, None)
    }

    /// Coerce a value to the target type, optionally using a pre-computed
    /// [`CoerceKind`] hint to skip the 6-way type detection.
    ///
    /// When `hint` is `Some`, dispatches directly to the appropriate coercion
    /// path. When `None`, falls back to runtime type queries.
    pub fn coerce_to_type_hinted(
        &mut self,
        value: CompiledValue,
        target_vir_ty: VirTypeId,
        hint: Option<&CoerceKind>,
    ) -> CodegenResult<CompiledValue> {
        // Resolve generic type params in monomorphized contexts before coercion checks.
        // This keeps union/interface coercions from comparing concrete targets against
        // unresolved TypeParam values.
        let resolved_target_vir = self.try_substitute_type_v(target_vir_ty);
        let resolved_value_vir = self.try_substitute_type_v(value.type_id);
        let mut resolved_value = value;
        resolved_value.type_id = resolved_value_vir;

        if let Some(kind) = hint {
            return self.compile_vir_coerce(
                resolved_value,
                resolved_target_vir,
                resolved_value_vir,
                resolved_target_vir,
                kind,
            );
        }

        self.coerce_to_type_detected(resolved_value, resolved_target_vir)
    }

    fn classify_coercion_types(
        &self,
        value_vir: VirTypeId,
        target_vir: VirTypeId,
    ) -> CoercionClassification {
        CoercionClassification {
            target_interface: self.vir_query_is_interface_v(target_vir),
            value_interface: self.vir_query_is_interface_v(value_vir),
            target_union: self.vir_query_is_union_v(target_vir),
            value_union: self.vir_query_is_union_v(value_vir),
            target_unknown: self.vir_query_is_unknown_v(target_vir),
            value_unknown: self.vir_query_is_unknown_v(value_vir),
            value_runtime_iterator: self.vir_query_is_runtime_iterator_v(value_vir),
            target_numeric: self.vir_query_is_numeric_v(target_vir),
            value_numeric: self.vir_query_is_numeric_v(value_vir),
        }
    }

    /// Fallback coercion path: queries types to determine the coercion kind.
    fn coerce_to_type_detected(
        &mut self,
        value: CompiledValue,
        target_vir_ty: VirTypeId,
    ) -> CodegenResult<CompiledValue> {
        let c = self.classify_coercion_types(value.type_id, target_vir_ty);

        if c.target_numeric && c.value_numeric && target_vir_ty != value.type_id {
            return self.coerce_numeric_to_type(value, target_vir_ty);
        }
        // RuntimeIterator is a concrete type that implements Iterator dispatch
        // directly via runtime_iterator_method; skip interface boxing.
        if c.target_interface && !c.value_interface && !c.value_runtime_iterator {
            self.box_interface_value_v(value, target_vir_ty)
        } else if c.target_union && !c.value_union {
            self.construct_union_id_v(value, target_vir_ty)
        } else if c.target_unknown && !c.value_unknown {
            self.box_to_unknown(value)
        } else {
            Ok(value)
        }
    }

    fn coerce_numeric_to_type(
        &mut self,
        value: CompiledValue,
        target_vir_ty: VirTypeId,
    ) -> CodegenResult<CompiledValue> {
        let target_ty = self.cranelift_type_v(target_vir_ty);
        // If the Cranelift representation is already the right type (e.g. u8 → i8,
        // u32 → i32), no IR instruction is needed — just re-tag the value.
        if value.ty == target_ty {
            return Ok(CompiledValue::new(value.value, target_ty, target_vir_ty));
        }
        let coercion = numeric_coercion_v(value.type_id, target_vir_ty);

        let converted = match coercion {
            NumericCoercion::Identity => {
                return Ok(CompiledValue::new(value.value, target_ty, target_vir_ty));
            }
            NumericCoercion::IntWiden { signed: true } => {
                sextend_const(self.builder, target_ty, value.value)
            }
            NumericCoercion::IntWiden { signed: false } => {
                uextend_const(self.builder, target_ty, value.value)
            }
            NumericCoercion::IntNarrow { .. } => self.builder.ins().ireduce(target_ty, value.value),
            NumericCoercion::FloatWiden => self.float_widen(value, target_vir_ty)?,
            NumericCoercion::FloatNarrow => self.float_narrow(value, target_vir_ty)?,
            NumericCoercion::IntToFloat { from_signed } => {
                self.int_to_float(value, target_vir_ty, from_signed)?
            }
            NumericCoercion::FloatToInt { to_signed } => {
                self.float_to_int(value, target_vir_ty, to_signed)?
            }
        };
        Ok(CompiledValue::new(converted, target_ty, target_vir_ty))
    }

    /// Bitcast an F128 value to I128 for passing to runtime conversion functions.
    ///
    /// Cranelift cannot operate on F128 directly; all F128 arithmetic routes
    /// through runtime calls that accept/return I128 bit patterns.
    #[inline]
    fn f128_to_i128_bits(&mut self, f128_val: Value) -> Value {
        self.builder
            .ins()
            .bitcast(types::I128, MemFlags::new(), f128_val)
    }

    /// Bitcast an I128 bit pattern (from a runtime call) back to F128.
    #[inline]
    fn i128_bits_to_f128(&mut self, i128_bits: Value) -> Value {
        self.builder
            .ins()
            .bitcast(types::F128, MemFlags::new(), i128_bits)
    }

    /// Float widening: F32→F64 (fpromote), or anything→F128 (runtime calls).
    fn float_widen(&mut self, value: CompiledValue, to: VirTypeId) -> CodegenResult<Value> {
        let target_ty = self.cranelift_type_v(to);
        if target_ty == types::F128 {
            // Anything→F128 goes through a runtime call, result is i128 bits → bitcast to f128.
            let bits = match value.ty {
                ty if ty == types::F64 => {
                    self.call_runtime(RuntimeKey::F64ToF128, &[value.value])?
                }
                ty if ty == types::F32 => {
                    self.call_runtime(RuntimeKey::F32ToF128, &[value.value])?
                }
                _ => unreachable!("float_widen to F128: unexpected source type"),
            };
            Ok(self.i128_bits_to_f128(bits))
        } else {
            // F32→F64: direct fpromote
            Ok(self.builder.ins().fpromote(target_ty, value.value))
        }
    }

    /// Float narrowing: F128→F64/F32 (runtime calls), F64→F32 (fdemote).
    fn float_narrow(&mut self, value: CompiledValue, to: VirTypeId) -> CodegenResult<Value> {
        let target_ty = self.cranelift_type_v(to);
        if value.ty == types::F128 {
            let f128_bits = self.f128_to_i128_bits(value.value);
            match target_ty {
                ty if ty == types::F64 => self.call_runtime(RuntimeKey::F128ToF64, &[f128_bits]),
                ty if ty == types::F32 => self.call_runtime(RuntimeKey::F128ToF32, &[f128_bits]),
                _ => unreachable!("float_narrow from F128: unexpected target type"),
            }
        } else {
            // F64→F32: direct fdemote
            Ok(self.builder.ins().fdemote(target_ty, value.value))
        }
    }

    /// Integer-to-float conversion.
    /// Handles →F128 (runtime calls with intermediate i64), otherwise fcvt_from_sint/uint.
    fn int_to_float(
        &mut self,
        value: CompiledValue,
        to: VirTypeId,
        from_signed: bool,
    ) -> CodegenResult<Value> {
        let target_ty = self.cranelift_type_v(to);
        if target_ty == types::F128 {
            // I128→F128 gets its own runtime call; all others route through i64.
            if value.ty == types::I128 {
                let bits = self.call_runtime(RuntimeKey::I128ToF128, &[value.value])?;
                return Ok(self.i128_bits_to_f128(bits));
            }
            // Narrow or widen the source integer to i64 first.
            let i64_val = if value.ty == types::I64 {
                value.value
            } else if value.ty.bytes() < 8 {
                if from_signed {
                    sextend_const(self.builder, types::I64, value.value)
                } else {
                    uextend_const(self.builder, types::I64, value.value)
                }
            } else {
                self.builder.ins().ireduce(types::I64, value.value)
            };
            let bits = self.call_runtime(RuntimeKey::I64ToF128, &[i64_val])?;
            Ok(self.i128_bits_to_f128(bits))
        } else if from_signed {
            Ok(self.builder.ins().fcvt_from_sint(target_ty, value.value))
        } else {
            Ok(self.builder.ins().fcvt_from_uint(target_ty, value.value))
        }
    }

    /// Float-to-integer conversion.
    /// Handles F128→ (runtime calls: F128ToI128, F128ToI64 + narrow), otherwise fcvt_to_sint/uint.
    fn float_to_int(
        &mut self,
        value: CompiledValue,
        to: VirTypeId,
        to_signed: bool,
    ) -> CodegenResult<Value> {
        let target_ty = self.cranelift_type_v(to);
        if value.ty == types::F128 {
            let f128_bits = self.f128_to_i128_bits(value.value);
            if target_ty == types::I128 {
                return self.call_runtime(RuntimeKey::F128ToI128, &[f128_bits]);
            }
            // All other integer targets go through i64 first, then narrow if needed.
            let i64_val = self.call_runtime(RuntimeKey::F128ToI64, &[f128_bits])?;
            if target_ty == types::I64 {
                Ok(i64_val)
            } else if target_ty.bytes() < 8 {
                Ok(self.builder.ins().ireduce(target_ty, i64_val))
            } else {
                // Defensive: i128 is handled above; keep for completeness.
                Ok(sextend_const(self.builder, target_ty, i64_val))
            }
        } else if to_signed {
            Ok(self.builder.ins().fcvt_to_sint(target_ty, value.value))
        } else {
            Ok(self.builder.ins().fcvt_to_uint(target_ty, value.value))
        }
    }

    /// Box a value into the unknown type (TaggedValue representation).
    ///
    /// Heap-allocates a 16-byte TaggedValue via `vole_tagged_value_new`:
    /// - Offset 0: tag (u64) - runtime type identifier
    /// - Offset 8: value (u64) - the actual value (or pointer for reference types)
    ///
    /// Returns a pointer to the heap-allocated TaggedValue. The buffer is freed
    /// by `unknown_heap_cleanup` which conditionally `rc_dec`'s the payload.
    ///
    /// If the inner value is borrowed and RC-managed, this method rc_inc's it
    /// so the TaggedValue owns its own reference. Callers that already handle
    /// rc_inc for the inner value should pass `skip_inner_rc_inc = true` via
    /// `box_to_unknown_no_inc`.
    pub fn box_to_unknown(&mut self, value: CompiledValue) -> CodegenResult<CompiledValue> {
        // RC-inc borrowed RC values so the TaggedValue owns its own reference.
        // unknown_heap_cleanup will rc_dec the inner value when the TaggedValue
        // is freed, so we need the extra reference to avoid use-after-free.
        if value.is_borrowed()
            && self.rc_scopes.has_active_scope()
            && self.cached_rc_state_v(value.type_id).needs_cleanup()
        {
            self.emit_rc_inc_for_type_v(value.value, value.type_id)?;
        }
        self.box_to_unknown_raw(value)
    }

    /// Box a value into the unknown type without rc_inc'ing the inner value.
    ///
    /// Use when the caller has already ensured the inner value has an extra
    /// reference (e.g., class literal field init which rc_inc's before coercion).
    pub fn box_to_unknown_no_inc(&mut self, value: CompiledValue) -> CodegenResult<CompiledValue> {
        self.box_to_unknown_raw(value)
    }

    /// Raw unknown boxing: heap-allocates a TaggedValue without RC adjustment.
    fn box_to_unknown_raw(&mut self, value: CompiledValue) -> CodegenResult<CompiledValue> {
        if value.ty == types::I128 || value.ty == types::F128 {
            return Err(CodegenError::type_mismatch(
                "unknown boxing",
                "a type that fits in 64 bits",
                "128-bit values (i128/f128 cannot be boxed as unknown)",
            ));
        }

        // Get the runtime tag for this type
        let tag = self.vir_query_unknown_type_tag_v(value.type_id);
        let tag_val = self.iconst_cached(types::I64, tag as i64);

        // Convert value to i64 for storage
        let value_as_i64 = if value.ty == types::I64 || value.ty == self.ptr_type() {
            value.value
        } else if value.ty == types::F64 {
            self.builder
                .ins()
                .bitcast(types::I64, MemFlags::new(), value.value)
        } else if value.ty == types::F32 {
            let i32_val = self
                .builder
                .ins()
                .bitcast(types::I32, MemFlags::new(), value.value);
            uextend_const(self.builder, types::I64, i32_val)
        } else if value.ty.is_int() && value.ty.bytes() < 8 {
            if self.vir_query_is_unsigned_v(value.type_id) {
                uextend_const(self.builder, types::I64, value.value)
            } else {
                sextend_const(self.builder, types::I64, value.value)
            }
        } else {
            value.value
        };

        // Heap-allocate the TaggedValue via runtime call
        let ptr = self.call_runtime(RuntimeKey::TaggedValueNew, &[tag_val, value_as_i64])?;

        Ok(CompiledValue::new(ptr, self.ptr_type(), VirTypeId::UNKNOWN))
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

    /// Box a value as an interface type using a VirTypeId.
    pub fn box_interface_value_v(
        &mut self,
        value: CompiledValue,
        interface_vir_ty: VirTypeId,
    ) -> CodegenResult<CompiledValue> {
        // Decompose the interface from VIR directly (VirTypeId-native path).
        if let Some((type_def_id, vir_type_args)) =
            self.vir_query_unwrap_interface_v(interface_vir_ty)
        {
            return crate::interfaces::box_interface_value_decomposed(
                self.builder,
                self.codegen_ctx,
                self.env,
                value,
                interface_vir_ty,
                type_def_id,
                &vir_type_args,
            );
        }

        // Fallback: try via TypeId lookup
        let interface_type_id = self
            .vir_type_table()
            .lookup_vir_type_id(interface_vir_ty)
            .unwrap_or(TypeId::UNKNOWN);
        self.box_interface_value(value, interface_type_id)
    }

    // ========== Integer width coercion ==========

    /// Narrow or widen an integer `CompiledValue` to match `expected_ty`.
    /// If both source and target are integers of different widths, emits
    /// `ireduce`, `uextend`, or `sextend` as appropriate. Otherwise returns
    /// the value unchanged.
    fn coerce_int_width(
        &mut self,
        compiled: CompiledValue,
        expected_ty: Type,
        param_type_id: TypeId,
        param_vir_ty: VirTypeId,
    ) -> CompiledValue {
        if compiled.ty.is_int() && expected_ty.is_int() && expected_ty.bits() != compiled.ty.bits()
        {
            let new_value = if expected_ty.bits() < compiled.ty.bits() {
                self.builder.ins().ireduce(expected_ty, compiled.value)
            } else if self.vir_query_is_unsigned(param_type_id) {
                uextend_const(self.builder, expected_ty, compiled.value)
            } else {
                sextend_const(self.builder, expected_ty, compiled.value)
            };
            CompiledValue::new(new_value, expected_ty, param_vir_ty)
        } else {
            compiled
        }
    }

    // ========== Default parameter compilation ==========

    /// Core loop for compiling default parameter values.
    ///
    /// `lookup_default` returns `Ok(Some(vir_expr))` for parameters with defaults,
    /// `Ok(None)` for parameters without (skipped), or `Err` when a default was
    /// expected but its VIR lowering is missing (internal error).
    ///
    /// `post_process` optionally transforms the final value (e.g., `emit_word`
    /// for generic class method defaults).
    fn compile_defaults_core(
        &mut self,
        start_index: usize,
        expected_type_ids: &[TypeId],
        mut lookup_default: impl FnMut(&mut Self, usize) -> CodegenResult<Option<vole_vir::VirExpr>>,
        mut post_process: impl FnMut(&mut Self, CompiledValue) -> CodegenResult<Value>,
    ) -> CodegenResult<(Vec<Value>, Vec<CompiledValue>)> {
        let mut args = Vec::new();
        let mut rc_owned = Vec::new();

        for (offset, &param_type_id) in expected_type_ids.iter().enumerate() {
            let slot = start_index + offset;
            let Some(default_vir) = lookup_default(self, slot)? else {
                continue;
            };

            let compiled = self.compile_vir_expr(&default_vir)?;
            if compiled.is_owned() {
                rc_owned.push(compiled);
            }

            let param_vir_ty = self.vir_lookup_or_compat(param_type_id);
            let compiled = self.coerce_to_type(compiled, param_vir_ty)?;
            let expected_ty = self.cranelift_type(param_type_id);
            let compiled =
                self.coerce_int_width(compiled, expected_ty, param_type_id, param_vir_ty);

            args.push(post_process(self, compiled)?);
        }

        Ok((args, rc_owned))
    }

    /// Compile default expressions for omitted parameters using typed function ID.
    pub fn compile_function_defaults(
        &mut self,
        func_id: FunctionId,
        start_index: usize,
        expected_type_ids: &[TypeId],
    ) -> CodegenResult<(Vec<Value>, Vec<CompiledValue>)> {
        self.compile_defaults_core(
            start_index,
            expected_type_ids,
            |cg, slot| match cg.function_default_vir_init(func_id, slot).cloned() {
                Some(vir) => Ok(Some(vir)),
                None if cg.analyzed().has_function_default_expr(func_id, slot) => {
                    Err(CodegenError::internal_with_context(
                        "missing VIR function default expression",
                        format!("{func_id:?} param {slot}"),
                    ))
                }
                None => Ok(None),
            },
            |_, cv| Ok(cv.value),
        )
    }

    /// Compile default expressions for omitted parameters using typed method ID.
    pub fn compile_method_defaults(
        &mut self,
        method_id: MethodId,
        start_index: usize,
        expected_type_ids: &[TypeId],
        is_generic_class: bool,
    ) -> CodegenResult<(Vec<Value>, Vec<CompiledValue>)> {
        self.compile_defaults_core(
            start_index,
            expected_type_ids,
            |cg, slot| match cg.method_default_vir_init(method_id, slot).cloned() {
                Some(vir) => Ok(Some(vir)),
                None if cg.analyzed().has_method_default_expr(method_id, slot) => {
                    Err(CodegenError::internal_with_context(
                        "missing VIR method default expression",
                        format!("{method_id:?} param {slot}"),
                    ))
                }
                None => Ok(None),
            },
            |cg, cv| {
                if is_generic_class && cv.ty != types::I64 {
                    cg.emit_word(&cv, None)
                } else {
                    Ok(cv.value)
                }
            },
        )
    }

    /// Compile default expressions for omitted lambda parameters from VIR.
    pub fn compile_lambda_defaults(
        &mut self,
        lambda_node_id: NodeId,
        start_index: usize,
        expected_type_ids: &[TypeId],
    ) -> CodegenResult<(Vec<Value>, Vec<CompiledValue>)> {
        self.compile_defaults_core(
            start_index,
            expected_type_ids,
            |cg, slot| match cg.lambda_default_vir_init(lambda_node_id, slot).cloned() {
                Some(vir) => Ok(Some(vir)),
                None => Err(CodegenError::internal_with_context(
                    "missing VIR lambda default expression",
                    format!("lambda={lambda_node_id:?} param {slot}"),
                )),
            },
            |_, cv| Ok(cv.value),
        )
    }
}
