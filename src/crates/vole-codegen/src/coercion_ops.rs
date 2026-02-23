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
use vole_identity::{FunctionId, MethodId};
use vole_sema::numeric_model::{NumericCoercion, numeric_coercion};
use vole_sema::type_arena::TypeId;

use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};

use super::context::Cg;
use super::types::CompiledValue;
use crate::ops::{sextend_const, uextend_const};

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
        // If the Cranelift representation is already the right type (e.g. u8 → i8,
        // u32 → i32), no IR instruction is needed — just re-tag the value.
        if value.ty == target_ty {
            return Ok(CompiledValue::new(value.value, target_ty, target_type_id));
        }
        let coercion = numeric_coercion(value.type_id, target_type_id);

        let converted = match coercion {
            NumericCoercion::Identity => {
                return Ok(CompiledValue::new(value.value, target_ty, target_type_id));
            }
            NumericCoercion::IntWiden { signed: true } => {
                sextend_const(self.builder, target_ty, value.value)
            }
            NumericCoercion::IntWiden { signed: false } => {
                uextend_const(self.builder, target_ty, value.value)
            }
            NumericCoercion::IntNarrow { .. } => self.builder.ins().ireduce(target_ty, value.value),
            NumericCoercion::FloatWiden => self.float_widen(value, target_type_id)?,
            NumericCoercion::FloatNarrow => self.float_narrow(value, target_type_id)?,
            NumericCoercion::IntToFloat { from_signed } => {
                self.int_to_float(value, target_type_id, from_signed)?
            }
            NumericCoercion::FloatToInt { to_signed } => {
                self.float_to_int(value, target_type_id, to_signed)?
            }
        };
        Ok(CompiledValue::new(converted, target_ty, target_type_id))
    }

    /// Float widening: F32→F64 (fpromote), or anything→F128 (runtime calls).
    fn float_widen(&mut self, value: CompiledValue, to: TypeId) -> CodegenResult<Value> {
        let target_ty = self.cranelift_type(to);
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
            Ok(self
                .builder
                .ins()
                .bitcast(types::F128, MemFlags::new(), bits))
        } else {
            // F32→F64: direct fpromote
            Ok(self.builder.ins().fpromote(target_ty, value.value))
        }
    }

    /// Float narrowing: F128→F64/F32 (runtime calls), F64→F32 (fdemote).
    fn float_narrow(&mut self, value: CompiledValue, to: TypeId) -> CodegenResult<Value> {
        let target_ty = self.cranelift_type(to);
        if value.ty == types::F128 {
            let f128_bits = self
                .builder
                .ins()
                .bitcast(types::I128, MemFlags::new(), value.value);
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
        to: TypeId,
        from_signed: bool,
    ) -> CodegenResult<Value> {
        let target_ty = self.cranelift_type(to);
        if target_ty == types::F128 {
            // I128→F128 gets its own runtime call; all others route through i64.
            if value.ty == types::I128 {
                let bits = self.call_runtime(RuntimeKey::I128ToF128, &[value.value])?;
                return Ok(self
                    .builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), bits));
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
            Ok(self
                .builder
                .ins()
                .bitcast(types::F128, MemFlags::new(), bits))
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
        to: TypeId,
        to_signed: bool,
    ) -> CodegenResult<Value> {
        let target_ty = self.cranelift_type(to);
        if value.ty == types::F128 {
            let f128_bits = self
                .builder
                .ins()
                .bitcast(types::I128, MemFlags::new(), value.value);
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
            && self.rc_state(value.type_id).needs_cleanup()
        {
            self.emit_rc_inc_for_type(value.value, value.type_id)?;
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
            if self.arena().is_unsigned(value.type_id) {
                uextend_const(self.builder, types::I64, value.value)
            } else {
                sextend_const(self.builder, types::I64, value.value)
            }
        } else {
            value.value
        };

        // Heap-allocate the TaggedValue via runtime call
        let ptr = self.call_runtime(RuntimeKey::TaggedValueNew, &[tag_val, value_as_i64])?;

        Ok(CompiledValue::new(ptr, self.ptr_type(), TypeId::UNKNOWN))
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

    /// Compile default expressions for omitted parameters using typed function ID.
    ///
    /// Looks up default expressions from `EntityRegistry` by `FunctionId` and parameter
    /// index. No raw pointers: the registry is accessed via `'ctx`-lifetime references
    /// that outlive `&mut self`.
    ///
    /// # Arguments
    /// - `func_id`: The sema `FunctionId` whose defaults to compile
    /// - `start_index`: Index of the first omitted parameter
    /// - `expected_type_ids`: TypeIds for parameters starting at `start_index`
    pub fn compile_function_defaults(
        &mut self,
        func_id: FunctionId,
        start_index: usize,
        expected_type_ids: &[TypeId],
    ) -> CodegenResult<(Vec<Value>, Vec<CompiledValue>)> {
        // Collect &'ctx Expr references before taking &mut self.
        // query() returns ProgramQuery<'ctx>, so default_refs lives as 'ctx.
        let default_refs: Vec<Option<&'ctx Expr>> = {
            let query = self.query();
            (start_index..start_index + expected_type_ids.len())
                .map(|idx| query.function_default_expr_by_id(func_id, idx))
                .collect()
        };
        self.compile_defaults_from_refs(&default_refs, expected_type_ids, false)
    }

    /// Compile default expressions for omitted parameters using typed method ID.
    ///
    /// Looks up default expressions from `EntityRegistry` by `MethodId` and parameter
    /// index. No raw pointers: the registry is accessed via `'ctx`-lifetime references.
    ///
    /// # Arguments
    /// - `method_id`: The sema `MethodId` whose defaults to compile
    /// - `start_index`: Index of the first omitted parameter
    /// - `expected_type_ids`: TypeIds for parameters starting at `start_index`
    /// - `is_generic_class`: Whether this is a generic class call (needs value_to_word)
    pub fn compile_method_defaults(
        &mut self,
        method_id: MethodId,
        start_index: usize,
        expected_type_ids: &[TypeId],
        is_generic_class: bool,
    ) -> CodegenResult<(Vec<Value>, Vec<CompiledValue>)> {
        let default_refs: Vec<Option<&'ctx Expr>> = {
            let query = self.query();
            (start_index..start_index + expected_type_ids.len())
                .map(|idx| query.method_default_expr_by_id(method_id, idx))
                .collect()
        };
        self.compile_defaults_from_refs(&default_refs, expected_type_ids, is_generic_class)
    }

    /// Compile default expressions for omitted lambda parameters.
    ///
    /// `default_refs` is a slice of `Option<&Expr>` for the omitted parameters
    /// (one entry per expected param, in order). Uses shared coercion logic.
    pub fn compile_lambda_defaults(
        &mut self,
        default_refs: &[Option<&'ctx Expr>],
        expected_type_ids: &[TypeId],
    ) -> CodegenResult<(Vec<Value>, Vec<CompiledValue>)> {
        self.compile_defaults_from_refs(default_refs, expected_type_ids, false)
    }

    /// Unified default-expression compilation kernel.
    ///
    /// Takes a slice of optional `&'ctx Expr` references (already resolved from the
    /// stable owning store) and compiles each present entry with coercion.
    ///
    /// # Arguments
    /// - `default_refs`: One entry per omitted parameter; `None` means no default available
    /// - `expected_type_ids`: TypeIds for each entry in `default_refs` (same length)
    /// - `is_generic_class`: Whether generic-class word-packing is needed
    fn compile_defaults_from_refs(
        &mut self,
        default_refs: &[Option<&'ctx Expr>],
        expected_type_ids: &[TypeId],
        is_generic_class: bool,
    ) -> CodegenResult<(Vec<Value>, Vec<CompiledValue>)> {
        let mut args = Vec::new();
        let mut rc_owned = Vec::new();

        for (default_ref, &param_type_id) in default_refs.iter().zip(expected_type_ids.iter()) {
            let Some(default_expr) = default_ref else {
                continue;
            };
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
                    sextend_const(self.builder, expected_ty, compiled.value)
                };
                CompiledValue::new(new_value, expected_ty, param_type_id)
            } else {
                compiled
            };

            // Generic class methods expect i64 for TypeParam, convert if needed
            let arg_value = if is_generic_class && compiled.ty != types::I64 {
                self.emit_word(&compiled, None)?
            } else {
                compiled.value
            };
            args.push(arg_value);
        }

        Ok((args, rc_owned))
    }
}
