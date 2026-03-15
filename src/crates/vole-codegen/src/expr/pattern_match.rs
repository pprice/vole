// src/codegen/expr/pattern_match.rs
//
// Match expressions, is-checks, and pattern matching compilation.

use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;
use rustc_hash::FxHashMap;

use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, FALLIBLE_SUCCESS_TAG, load_fallible_payload, load_fallible_tag};

use vole_identity::Symbol;
use vole_identity::{VirIsCheckResult, VirTypeId};

use super::super::context::Cg;
use super::super::control_flow::match_switch;

impl Cg<'_, '_, '_> {
    // =========================================================================
    // Is-check compilation
    // =========================================================================

    /// Compute IsCheckResult at codegen time for monomorphized generic functions.
    /// Sema skips generic function bodies, so `is` expressions inside them have no
    /// pre-computed result. This uses the substituted value type to compute it.
    pub(super) fn compute_is_check_result(
        &self,
        value_vir: VirTypeId,
        tested_vir: VirTypeId,
    ) -> VirIsCheckResult {
        if value_vir == VirTypeId::UNKNOWN {
            VirIsCheckResult::CheckUnknown(tested_vir, tested_vir)
        } else if let Some(variants) = self.vir_query_unwrap_union_v(value_vir) {
            if let Some(index) = variants.iter().position(|&v| v == tested_vir) {
                VirIsCheckResult::CheckTag(index as u32)
            } else {
                VirIsCheckResult::AlwaysFalse
            }
        } else if value_vir == tested_vir {
            VirIsCheckResult::AlwaysTrue
        } else {
            VirIsCheckResult::AlwaysFalse
        }
    }

    // =========================================================================
    // Unknown is-check helper
    // =========================================================================

    /// Compile an `is` check against an unknown value using VIR type metadata.
    ///
    /// Handles annotation types via two-level check (Instance tag + type_id),
    /// mirroring [`compile_unknown_is_check`].
    pub(super) fn compile_unknown_is_check_vir(
        &mut self,
        tagged_value_ptr: Value,
        tested_vir_type_id: VirTypeId,
    ) -> Value {
        let tag = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), tagged_value_ptr, 0);

        if let Some(ann_runtime_type_id) = self.get_annotation_runtime_type_id_v(tested_vir_type_id)
        {
            // Two-level annotation check:
            // 1. Tag must be Instance (7)
            let instance_tag = self.iconst_cached(
                types::I64,
                vole_runtime::value::RuntimeTypeId::Instance as i64,
            );
            let tag_match = self.builder.ins().icmp(IntCC::Equal, tag, instance_tag);

            // 2. Load the instance pointer from TaggedValue.value (offset 8)
            let instance_ptr =
                self.builder
                    .ins()
                    .load(types::I64, MemFlags::new(), tagged_value_ptr, 8);

            // 3. Load RcInstance.type_id (u32 at offset 16 = sizeof(RcHeader))
            let inst_type_id =
                self.builder
                    .ins()
                    .load(types::I32, MemFlags::new(), instance_ptr, 16);

            // 4. Compare against the expected annotation runtime type_id
            let expected_id = self.iconst_cached(types::I32, ann_runtime_type_id as i64);
            let id_match = self
                .builder
                .ins()
                .icmp(IntCC::Equal, inst_type_id, expected_id);

            // Both checks must pass
            self.builder.ins().band(tag_match, id_match)
        } else {
            // Standard single-level tag check
            let expected_tag = crate::types::vir_conversions::vir_unknown_type_tag(
                tested_vir_type_id,
                self.vir_type_table(),
            );
            let expected_val = self.iconst_cached(types::I64, expected_tag as i64);
            self.builder.ins().icmp(IntCC::Equal, tag, expected_val)
        }
    }

    /// Compile an equality check for two values, dispatching via
    /// [`ComparisonHint`] derived from the given `vir_ty`.
    ///
    /// Used by match-pattern literal and val comparisons.  Delegates to
    /// the same `emit_eq` / `string_eq` helpers that `binary_op` uses,
    /// so there is a single source of truth for comparison dispatch.
    fn compile_equality_check_v(
        &mut self,
        vir_ty: VirTypeId,
        left: Value,
        right: Value,
    ) -> CodegenResult<Value> {
        use vole_vir::ComparisonHint;

        let hint = self.classify_eq_hint_from_type(vir_ty);
        match hint {
            ComparisonHint::StringEq => self.string_eq(left, right),
            ComparisonHint::FloatCmp => Ok(self.builder.ins().fcmp(FloatCC::Equal, left, right)),
            ComparisonHint::F128Cmp => self.call_f128_cmp(crate::RuntimeKey::F128Eq, left, right),
            ComparisonHint::IntCmp | ComparisonHint::UnsignedIntCmp => {
                Ok(self.builder.ins().icmp(IntCC::Equal, left, right))
            }
            _ => Err(CodegenError::type_mismatch(
                "equality comparison",
                "string, float, integer, or bool",
                self.vir_query_display_basic_v(vir_ty),
            )),
        }
    }

    // =========================================================================
    // VIR Match expression compilation
    // =========================================================================

    /// Compile a VIR `Match` expression.
    ///
    /// Like [`match_expr`] but operates on VIR nodes: the scrutinee is a
    /// `VirRef`, arms carry concrete `VirPattern` variants, VIR guards, and
    /// `VirBody` bodies.  Pattern compilation dispatches on concrete VIR
    /// pattern variants (Wildcard, Binding, TypeCheck, Literal, Val, Success,
    /// Error, Tuple, Record).
    pub(crate) fn compile_vir_match(
        &mut self,
        scrutinee_expr: &vole_vir::VirExpr,
        arms: &[vole_vir::VirMatchArm],
        vir_result_type_id: VirTypeId,
        result_is_union: bool,
    ) -> CodegenResult<CompiledValue> {
        let scrutinee = self.compile_vir_expr(scrutinee_expr)?;
        let scrutinee_type_id = scrutinee.type_id;

        let mut effective_result_vir = self.try_substitute_type_v(vir_result_type_id);
        // Track whether effective_result_vir is a union.  Start with the
        // pre-computed annotation; updated when the repair heuristics below
        // change effective_result_vir.
        let mut is_result_union =
            result_is_union || self.vir_query_is_union_v(effective_result_vir);

        // Repair degraded match result metadata by inferring from arm result
        // types when they provide a consistent concrete shape.
        let mut arm_vir_types: Vec<VirTypeId> = Vec::new();
        for arm in arms {
            let arm_vir = self.try_substitute_type_v(arm.ty);
            if arm_vir != VirTypeId::UNKNOWN && !arm_vir_types.contains(&arm_vir) {
                arm_vir_types.push(arm_vir);
            }
        }
        if arm_vir_types.len() > 1
            && let Some(inferred_union) =
                self.vir_type_table().lookup_union_v(arm_vir_types.clone())
            && (!is_result_union
                || effective_result_vir == VirTypeId::UNKNOWN
                || self.vir_query_is_function_v(effective_result_vir))
        {
            effective_result_vir = inferred_union;
            is_result_union = true;
        } else if let [single] = arm_vir_types.as_slice()
            && (effective_result_vir == VirTypeId::UNKNOWN
                || self.vir_query_is_function_v(effective_result_vir))
        {
            effective_result_vir = *single;
            is_result_union = self.vir_query_is_union_v(effective_result_vir);
        }

        // Replicate the nil-arm union return type adjustment from match_expr.
        if !is_result_union {
            let has_nil_arm = arms.iter().any(|arm| {
                arm.ty != VirTypeId::UNKNOWN
                    && self.vir_query_is_nil_v(self.try_substitute_type_v(arm.ty))
            });
            if has_nil_arm && let Some(ret_vir_ty) = self.return_type {
                let ret_vir_ty = self.try_substitute_type_v(ret_vir_ty);
                if self.vir_query_is_union_v(ret_vir_ty) {
                    effective_result_vir = ret_vir_ty;
                    is_result_union = true;
                }
            }
        }

        let result_cranelift_type = self.cranelift_type_v(effective_result_vir);
        let is_void = effective_result_vir == VirTypeId::VOID;
        let result_vir_ty = effective_result_vir;

        // Try switch optimization for dense integer literal arms.
        if let Some(analysis) = match_switch::analyze_vir_switch(arms, scrutinee_type_id) {
            return self.emit_vir_switch_match(
                arms,
                analysis,
                scrutinee,
                result_vir_ty,
                result_cranelift_type,
                is_void,
                is_result_union,
            );
        }

        self.compile_vir_match_chain(
            arms,
            scrutinee,
            result_vir_ty,
            result_cranelift_type,
            is_void,
            scrutinee_type_id,
            is_result_union,
        )
    }

    /// Compile a VIR match using the standard chain of if-else blocks.
    #[expect(clippy::too_many_arguments)]
    fn compile_vir_match_chain(
        &mut self,
        arms: &[vole_vir::VirMatchArm],
        scrutinee: CompiledValue,
        result_vir_ty: VirTypeId,
        result_cranelift_type: Type,
        is_void: bool,
        scrutinee_type_id: VirTypeId,
        is_result_union: bool,
    ) -> CodegenResult<CompiledValue> {
        let merge_block = self.builder.create_block();
        if !is_void {
            self.builder
                .append_block_param(merge_block, result_cranelift_type);
        }

        let trap_block = self.builder.create_block();
        let arm_blocks: Vec<Block> = arms.iter().map(|_| self.builder.create_block()).collect();

        if !arm_blocks.is_empty() {
            self.builder.ins().jump(arm_blocks[0], &[]);
        } else if !is_void {
            let default_val = self.typed_zero(result_cranelift_type);
            let default_arg = BlockArg::from(default_val);
            self.builder.ins().jump(merge_block, &[default_arg]);
        } else {
            self.builder.ins().jump(merge_block, &[]);
        }

        for (i, arm) in arms.iter().enumerate() {
            let next_block = arm_blocks.get(i + 1).copied().unwrap_or(trap_block);
            self.compile_vir_match_arm(
                arm,
                &scrutinee,
                arm_blocks[i],
                next_block,
                merge_block,
                result_vir_ty,
                result_cranelift_type,
                is_void,
                is_result_union,
            )?;
        }

        self.switch_and_seal(trap_block);
        self.builder.ins().trap(crate::trap_codes::UNREACHABLE);

        self.switch_and_seal(merge_block);

        self.cleanup_fallible_scrutinee(&scrutinee, scrutinee_type_id)?;

        self.merge_block_result(merge_block, result_cranelift_type, result_vir_ty, is_void)
    }

    /// Compile a single VIR match arm: pattern check, guard, body, and jump to merge.
    #[expect(clippy::too_many_arguments)]
    fn compile_vir_match_arm(
        &mut self,
        arm: &vole_vir::VirMatchArm,
        scrutinee: &CompiledValue,
        arm_block: Block,
        next_block: Block,
        merge_block: Block,
        result_vir_ty: VirTypeId,
        result_cranelift_type: Type,
        is_void: bool,
        is_result_union: bool,
    ) -> CodegenResult<()> {
        self.switch_to_block(arm_block);

        let mut arm_variables = self.vars.clone();
        let mut effective_arm_block = arm_block;

        let pattern_matches = self.compile_vir_pattern(
            &arm.pattern,
            scrutinee,
            &mut arm_variables,
            arm_block,
            next_block,
            &mut effective_arm_block,
        )?;

        // Compile guard from VIR.
        let guard_result = if let Some(guard_expr) = &arm.guard {
            let saved_vars = std::mem::replace(&mut self.vars, arm_variables.clone());
            let guard_val = self.compile_vir_expr(guard_expr)?;
            arm_variables = std::mem::replace(&mut self.vars, saved_vars);
            Some(guard_val.value)
        } else {
            None
        };

        let should_execute = match (pattern_matches, guard_result) {
            (None, None) => None,
            (Some(p), None) => Some(p),
            (None, Some(g)) => Some(g),
            (Some(p), Some(g)) => Some(self.builder.ins().band(p, g)),
        };

        let body_block = self.builder.create_block();
        if let Some(cond) = should_execute {
            self.emit_brif(cond, body_block, next_block);
        } else {
            self.builder.ins().jump(body_block, &[]);
        }
        self.builder.seal_block(effective_arm_block);

        self.switch_to_block(body_block);
        let saved_vars = std::mem::replace(&mut self.vars, arm_variables);
        let body_result = self.compile_vir_arm_body_v(&arm.body, result_vir_ty, is_result_union)?;
        let _ = std::mem::replace(&mut self.vars, saved_vars);

        self.emit_match_arm_exit(
            body_result,
            result_vir_ty,
            result_cranelift_type,
            is_void,
            merge_block,
        )?;
        self.builder.seal_block(body_block);
        Ok(())
    }

    /// Compile a VIR pattern, returning the condition value (if any).
    ///
    /// Dispatches concrete VIR pattern variants to specialised helpers.
    fn compile_vir_pattern(
        &mut self,
        pattern: &vole_vir::VirPattern,
        scrutinee: &CompiledValue,
        arm_variables: &mut FxHashMap<Symbol, (Variable, VirTypeId)>,
        arm_block: Block,
        next_block: Block,
        effective_arm_block: &mut Block,
    ) -> CodegenResult<Option<Value>> {
        match pattern {
            vole_vir::VirPattern::Wildcard => Ok(None),

            vole_vir::VirPattern::Binding { name, ty: _, .. } => {
                let var = self.builder.declare_var(scrutinee.ty);
                self.builder.def_var(var, scrutinee.value);
                arm_variables.insert(*name, (var, self.try_substitute_type_v(scrutinee.type_id)));
                Ok(None)
            }

            vole_vir::VirPattern::TypeCheck {
                result,
                tested_type,
                binding,
                ..
            } => {
                // For monomorphized generics, recompute the IsCheckResult
                // using substituted types.
                let cond = if self.substitutions.is_some() {
                    let sub_tested = self.try_substitute_type_v(*tested_type);
                    let sub_scrutinee = self.try_substitute_type_v(scrutinee.type_id);
                    let effective_result = self.compute_is_check_result(sub_scrutinee, sub_tested);
                    self.compile_vir_is_check_result(&effective_result, scrutinee)?
                } else {
                    self.compile_vir_is_check_result(result, scrutinee)?
                };

                // If there's a binding, introduce the variable after the check.
                if let Some((name, bind_ty, _)) = binding {
                    let var = self.builder.declare_var(scrutinee.ty);
                    self.builder.def_var(var, scrutinee.value);
                    arm_variables.insert(*name, (var, self.try_substitute_type_v(*bind_ty)));
                }

                Ok(cond)
            }

            vole_vir::VirPattern::Literal {
                value: lit_expr,
                scrutinee_ty,
                ..
            } => {
                // Save and restore vars for pattern matching (literal may
                // reference arm-scoped variables in degenerate cases).
                let saved_vars = std::mem::replace(&mut self.vars, arm_variables.clone());
                let lit_val = self.compile_vir_expr(lit_expr)?;
                *arm_variables = std::mem::replace(&mut self.vars, saved_vars);

                let coerced_lit = self.convert_for_select(lit_val.value, scrutinee.ty);
                let cmp = self.compile_equality_check_v(
                    self.try_substitute_type_v(*scrutinee_ty),
                    scrutinee.value,
                    coerced_lit,
                )?;
                Ok(Some(cmp))
            }

            vole_vir::VirPattern::Val { name } => {
                let (var_val, var_vir_ty) =
                    if let Some(&(var, var_vir_ty)) = arm_variables.get(name) {
                        (self.builder.use_var(var), var_vir_ty)
                    } else if let Some(binding) = self.get_capture(name).copied() {
                        let captured = self.load_capture(&binding)?;
                        (captured.value, self.try_substitute_type_v(captured.type_id))
                    } else {
                        return Err(CodegenError::internal("undefined variable in val pattern"));
                    };

                let cmp = self.compile_equality_check_v(var_vir_ty, scrutinee.value, var_val)?;
                Ok(Some(cmp))
            }

            vole_vir::VirPattern::Success {
                inner,
                success_type,
                ..
            } => self.compile_vir_success_pattern(
                inner,
                scrutinee,
                self.try_substitute_type_v(*success_type),
                arm_variables,
            ),

            vole_vir::VirPattern::Error { kind } => {
                let tag = load_fallible_tag(self.builder, scrutinee.value);
                self.compile_vir_error_pattern(kind, scrutinee, tag, arm_variables)
            }

            vole_vir::VirPattern::Tuple { bindings } => {
                self.compile_vir_tuple_pattern(bindings, scrutinee, arm_variables)
            }

            vole_vir::VirPattern::Record {
                type_check,
                tested_type,
                fields,
                source_ty,
                is_union_payload,
                is_struct,
                ..
            } => self.compile_vir_record_pattern(
                type_check,
                tested_type,
                fields,
                *source_ty,
                *is_union_payload,
                *is_struct,
                scrutinee,
                arm_variables,
                arm_block,
                next_block,
                effective_arm_block,
            ),
        }
    }

    /// Compile a VIR success pattern: check tag == SUCCESS, optionally
    /// extract payload and match inner pattern.
    fn compile_vir_success_pattern(
        &mut self,
        inner: &Option<Box<vole_vir::VirPattern>>,
        scrutinee: &CompiledValue,
        success_vir: VirTypeId,
        arm_variables: &mut FxHashMap<Symbol, (Variable, VirTypeId)>,
    ) -> CodegenResult<Option<Value>> {
        let tag = load_fallible_tag(self.builder, scrutinee.value);
        let is_success = self
            .builder
            .ins()
            .icmp_imm(IntCC::Equal, tag, FALLIBLE_SUCCESS_TAG);

        if let Some(inner_pat) = inner {
            let payload_ty = self.cranelift_type_v(success_vir);
            let payload = load_fallible_payload(self.builder, scrutinee.value, payload_ty);

            // The inner pattern is a VIR pattern (e.g. Binding for `success x`).
            if let vole_vir::VirPattern::Binding { name, .. } = inner_pat.as_ref() {
                let var = self.builder.declare_var(payload_ty);
                self.builder.def_var(var, payload);
                arm_variables.insert(*name, (var, success_vir));
            }
        }
        Ok(Some(is_success))
    }

    /// Compile a VIR error pattern from the pre-resolved `VirErrorPatternKind`.
    fn compile_vir_error_pattern(
        &mut self,
        kind: &vole_vir::VirErrorPatternKind,
        scrutinee: &CompiledValue,
        tag: Value,
        arm_variables: &mut FxHashMap<Symbol, (Variable, VirTypeId)>,
    ) -> CodegenResult<Option<Value>> {
        match kind {
            vole_vir::VirErrorPatternKind::Bare => {
                let is_error =
                    self.builder
                        .ins()
                        .icmp_imm(IntCC::NotEqual, tag, FALLIBLE_SUCCESS_TAG);
                Ok(Some(is_error))
            }

            vole_vir::VirErrorPatternKind::CatchAll { name, error_ty, .. } => {
                let is_error =
                    self.builder
                        .ins()
                        .icmp_imm(IntCC::NotEqual, tag, FALLIBLE_SUCCESS_TAG);
                let error_vir_ty = self.try_substitute_type_v(*error_ty);
                let payload_ty = self.cranelift_type_v(error_vir_ty);
                let payload = load_fallible_payload(self.builder, scrutinee.value, payload_ty);
                let var = self.builder.declare_var(payload_ty);
                self.builder.def_var(var, payload);
                arm_variables.insert(*name, (var, error_vir_ty));
                Ok(Some(is_error))
            }

            vole_vir::VirErrorPatternKind::Specific { error_tag } => {
                let is_this_error = self.builder.ins().icmp_imm(IntCC::Equal, tag, *error_tag);
                Ok(Some(is_this_error))
            }

            vole_vir::VirErrorPatternKind::SpecificRecord {
                error_tag,
                type_def,
                fields,
            } => {
                let is_this_error = self.builder.ins().icmp_imm(IntCC::Equal, tag, *error_tag);
                self.extract_error_field_bindings(
                    *type_def,
                    scrutinee.value,
                    fields,
                    arm_variables,
                )?;
                Ok(Some(is_this_error))
            }
        }
    }

    /// Compile a VIR tuple destructuring pattern.
    ///
    /// Loads each element from the tuple's stack slot at the pre-computed byte
    /// offset and processes the nested pattern (typically `Binding` or
    /// `Wildcard`).  Element types are pre-resolved during VIR lowering;
    /// layout offsets and Cranelift types are computed here at instruction
    /// selection time via `tuple_layout()` and `cranelift_types()`.
    ///
    /// Tuple patterns always match (no condition), so this returns `Ok(None)`.
    fn compile_vir_tuple_pattern(
        &mut self,
        bindings: &[vole_vir::VirTupleBinding],
        scrutinee: &CompiledValue,
        arm_variables: &mut FxHashMap<Symbol, (Variable, VirTypeId)>,
    ) -> CodegenResult<Option<Value>> {
        let elem_vir_type_ids = self.vir_query_unwrap_tuple_v(scrutinee.type_id);
        if let Some(elem_vir_type_ids) = elem_vir_type_ids {
            let (_, offsets) = self.tuple_layout_v(&elem_vir_type_ids);
            for binding in bindings {
                let i = binding.element_index;
                let offset = offsets[i];
                let elem_vir_type_id = elem_vir_type_ids[i];
                let elem_cr_type = self.cranelift_type_v(elem_vir_type_id);

                if let vole_vir::VirPattern::Binding { name, .. } = &binding.pattern {
                    let value = self.builder.ins().load(
                        elem_cr_type,
                        MemFlags::new(),
                        scrutinee.value,
                        offset,
                    );
                    let var = self.builder.declare_var(elem_cr_type);
                    self.builder.def_var(var, value);
                    arm_variables
                        .insert(*name, (var, self.try_substitute_type_v(elem_vir_type_id)));
                }
                // Wildcard and other patterns: nothing to bind.
            }
        }
        Ok(None)
    }

    /// Compile a VIR record destructuring pattern.
    ///
    /// Handles both typed patterns (`Point { x, y }` in a union match) and
    /// anonymous patterns (`{ name, age }`).  For typed patterns in a union
    /// scrutinee, creates a conditional extraction block: branch on the type
    /// check, then extract fields in a separate block.
    ///
    /// Field extraction delegates to `extract_record_fields` which handles
    /// struct (flat layout) vs class (instance) field loading.
    #[expect(clippy::too_many_arguments)]
    fn compile_vir_record_pattern(
        &mut self,
        type_check: &Option<vole_vir::expr::IsCheckResult>,
        tested_type: &Option<VirTypeId>,
        fields: &[vole_vir::VirRecordFieldBinding],
        source_ty: VirTypeId,
        is_union_payload: bool,
        _is_struct: bool,
        scrutinee: &CompiledValue,
        arm_variables: &mut FxHashMap<Symbol, (Variable, VirTypeId)>,
        arm_block: Block,
        next_block: Block,
        effective_arm_block: &mut Block,
    ) -> CodegenResult<Option<Value>> {
        // Compute pattern check condition (if type check present)
        let pattern_check = if let Some(vir_result) = type_check {
            if self.substitutions.is_some() {
                if let Some(tested) = tested_type {
                    let sub_tested = self.try_substitute_type_v(*tested);
                    let sub_scrutinee = self.try_substitute_type_v(scrutinee.type_id);
                    let effective_result = self.compute_is_check_result(sub_scrutinee, sub_tested);
                    self.compile_vir_is_check_result(&effective_result, scrutinee)?
                } else {
                    self.compile_vir_is_check_result(vir_result, scrutinee)?
                }
            } else {
                self.compile_vir_is_check_result(vir_result, scrutinee)?
            }
        } else {
            None
        };

        // Resolve source type with substitutions for monomorphized generics
        let resolved_source_ty = self.try_substitute_type_v(source_ty);

        // Conditional extraction: when scrutinee is a union, branch on the type
        // check before extracting fields in a new block.
        let is_conditional = pattern_check.is_some() && is_union_payload;

        if is_conditional {
            let extract_block = self.builder.create_block();
            let cond =
                pattern_check.expect("INTERNAL: record pattern: missing pattern_check condition");
            self.emit_brif(cond, extract_block, next_block);
            self.builder.seal_block(arm_block);
            *effective_arm_block = extract_block;
            self.switch_to_block(extract_block);

            // Extract union payload at offset 8
            let payload = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), scrutinee.value, 8);
            self.extract_vir_record_fields(fields, payload, resolved_source_ty, arm_variables)?;
            Ok(None)
        } else {
            // Non-conditional: extract fields directly from scrutinee
            let (field_source, field_type) = if is_union_payload {
                // Union but no type check (anonymous record in union context)
                let payload =
                    self.builder
                        .ins()
                        .load(types::I64, MemFlags::new(), scrutinee.value, 8);
                (payload, resolved_source_ty)
            } else {
                (scrutinee.value, resolved_source_ty)
            };
            self.extract_vir_record_fields(fields, field_source, field_type, arm_variables)?;
            Ok(pattern_check)
        }
    }

    /// Extract and bind fields from a VIR record pattern.
    ///
    /// For class/instance types, uses `get_instance_field` runtime call.
    /// For struct types (auto-boxed in unions), uses `struct_field_load` since the
    /// source pointer is a raw heap pointer with flat offsets.
    fn extract_vir_record_fields(
        &mut self,
        fields: &[vole_vir::VirRecordFieldBinding],
        field_source: Value,
        field_source_type: VirTypeId,
        arm_variables: &mut FxHashMap<Symbol, (Variable, VirTypeId)>,
    ) -> CodegenResult<()> {
        let is_struct = self.vir_query_is_struct_v(field_source_type);
        for field in fields {
            let field_name = self.interner().resolve(field.field_name);
            let (slot, field_type_id) =
                self.vir_field_slot_and_type(field_source_type, field_name)?;

            let converted = if is_struct {
                self.struct_field_load(field_source, slot, field_type_id, field_source_type)?
            } else {
                self.get_instance_field(field_source, slot, field_type_id)?
            };
            let var = self.builder.declare_var(converted.ty);
            self.builder.def_var(var, converted.value);
            arm_variables.insert(field.binding_name, (var, self.to_vir_type(field_type_id)));
        }
        Ok(())
    }

    /// Compile a VIR `IsCheckResult` into a condition value (if runtime check needed).
    ///
    /// Like [`compile_is_check_result`] but operates directly on VIR's `IsCheckResult`,
    /// avoiding the `vir_to_sema_type_id_lossy` bridge in `CheckUnknown`.
    fn compile_vir_is_check_result(
        &mut self,
        result: &VirIsCheckResult,
        scrutinee: &CompiledValue,
    ) -> CodegenResult<Option<Value>> {
        match result {
            VirIsCheckResult::AlwaysTrue => Ok(None),
            VirIsCheckResult::AlwaysFalse => {
                let never_match = self.iconst_cached(types::I8, 0);
                Ok(Some(never_match))
            }
            VirIsCheckResult::CheckTag(tag_index) => {
                let cmp = self.tag_eq(scrutinee.value, *tag_index as i64);
                Ok(Some(cmp))
            }
            VirIsCheckResult::CheckUnknown(_, vir_tested_type_id) => {
                let cmp = self.compile_unknown_is_check_vir(scrutinee.value, *vir_tested_type_id);
                Ok(Some(cmp))
            }
        }
    }

    /// Compile a VIR match arm body, coercing the result to the match result type.
    fn compile_vir_arm_body_v(
        &mut self,
        body: &vole_vir::VirBody,
        result_vir_ty: VirTypeId,
        is_result_union: bool,
    ) -> CodegenResult<CompiledValue> {
        let body_result = if let Some(trailing) = &body.trailing {
            let mut terminated = false;
            for vir_stmt in &body.stmts {
                if terminated {
                    break;
                }
                terminated = self.compile_vir_stmt(vir_stmt)?;
            }
            if terminated {
                self.void_value()
            } else if is_result_union
                && matches!(trailing.as_ref(), vole_vir::VirExpr::ArrayLiteral { .. })
                && let Some(expected_variant) =
                    self.preferred_array_like_union_variant_v(result_vir_ty)
            {
                self.compile_vir_expr_with_expected_type(trailing, expected_variant)?
            } else {
                self.compile_vir_expr(trailing)?
            }
        } else {
            let (_, body_val) = self.compile_vir_body(body)?;
            body_val.unwrap_or_else(|| self.void_value())
        };
        if body_result.type_id == VirTypeId::NEVER {
            return Ok(body_result);
        }
        self.coerce_to_type(body_result, result_vir_ty)
    }

    /// Emit the exit jump for a match arm body to the merge block.
    fn emit_match_arm_exit(
        &mut self,
        body_result: CompiledValue,
        result_vir_ty: VirTypeId,
        result_cranelift_type: Type,
        is_void: bool,
        merge_block: Block,
    ) -> CodegenResult<()> {
        if body_result.type_id == VirTypeId::NEVER {
            self.builder.ins().trap(crate::trap_codes::UNREACHABLE);
        } else if !is_void {
            let result_needs_rc = self.cached_rc_state_v(result_vir_ty).needs_cleanup();
            self.jump_with_owned_result(
                body_result,
                result_vir_ty,
                result_cranelift_type,
                result_needs_rc,
                merge_block,
            )?;
        } else {
            self.builder.ins().jump(merge_block, &[]);
        }
        Ok(())
    }

    /// Emit a VIR match using Cranelift's Switch for O(1) dispatch.
    #[expect(clippy::too_many_arguments)]
    fn emit_vir_switch_match(
        &mut self,
        arms: &[vole_vir::VirMatchArm],
        analysis: match_switch::SwitchAnalysis,
        scrutinee: CompiledValue,
        result_vir_ty: VirTypeId,
        result_cranelift_type: Type,
        is_void: bool,
        is_result_union: bool,
    ) -> CodegenResult<CompiledValue> {
        use cranelift::frontend::Switch;

        let merge_block = self.builder.create_block();
        if !is_void {
            self.builder
                .append_block_param(merge_block, result_cranelift_type);
        }

        let body_blocks: Vec<Block> = arms.iter().map(|_| self.builder.create_block()).collect();

        let default_block = if let Some(wc_idx) = analysis.wildcard_idx {
            body_blocks[wc_idx]
        } else {
            self.builder.create_block()
        };

        let mut switch = Switch::new();
        for &(arm_idx, value) in &analysis.arm_values {
            let entry = value as u64 as u128;
            switch.set_entry(entry, body_blocks[arm_idx]);
        }
        switch.emit(self.builder, scrutinee.value, default_block);

        if analysis.wildcard_idx.is_none() {
            self.switch_and_seal(default_block);
            self.builder.ins().trap(crate::trap_codes::UNREACHABLE);
        }

        for (i, arm) in arms.iter().enumerate() {
            self.switch_to_block(body_blocks[i]);
            self.builder.seal_block(body_blocks[i]);

            let body_result =
                self.compile_vir_arm_body_v(&arm.body, result_vir_ty, is_result_union)?;
            self.emit_match_arm_exit(
                body_result,
                result_vir_ty,
                result_cranelift_type,
                is_void,
                merge_block,
            )?;
        }

        self.switch_and_seal(merge_block);

        self.merge_block_result(merge_block, result_cranelift_type, result_vir_ty, is_void)
    }
}
