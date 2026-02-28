// src/codegen/expr/pattern_match.rs
//
// Match expressions, is-checks, and pattern matching compilation.

use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;
use rustc_hash::FxHashMap;

use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, FALLIBLE_SUCCESS_TAG, load_fallible_payload, load_fallible_tag};

use vole_frontend::Symbol;
use vole_frontend::ast::RecordFieldPattern;
use vole_identity::{IsCheckResult, TypeId, VirTypeId};

use super::super::context::Cg;
use super::super::control_flow::match_switch;
use super::super::structs::get_field_slot_and_type_id_cg;

impl Cg<'_, '_, '_> {
    // =========================================================================
    // Is-check compilation
    // =========================================================================

    /// Compute IsCheckResult at codegen time for monomorphized generic functions.
    /// Sema skips generic function bodies, so `is` expressions inside them have no
    /// pre-computed result. This uses the substituted value type to compute it.
    pub(super) fn compute_is_check_result(
        &self,
        value_type_id: TypeId,
        tested_type_id: TypeId,
    ) -> IsCheckResult {
        if value_type_id.is_unknown() {
            IsCheckResult::CheckUnknown(tested_type_id)
        } else if let Some(variants) = self.vir_query_unwrap_union(value_type_id) {
            if let Some(index) = variants.iter().position(|&v| v == tested_type_id) {
                IsCheckResult::CheckTag(index as u32)
            } else {
                IsCheckResult::AlwaysFalse
            }
        } else if value_type_id == tested_type_id {
            IsCheckResult::AlwaysTrue
        } else {
            IsCheckResult::AlwaysFalse
        }
    }

    // =========================================================================
    // Unknown is-check helper
    // =========================================================================

    /// Compile an `is` check against an unknown-typed value.
    ///
    /// For non-annotation types, compares the TaggedValue's tag against the
    /// expected RuntimeTypeId.
    ///
    /// For annotation types (structs with `@annotation`), performs a two-level
    /// check: (1) tag == Instance, (2) the instance's `type_id` field matches
    /// the annotation type's registered runtime type_id. This distinguishes
    /// different annotation types that all share the Instance tag.
    pub(super) fn compile_unknown_is_check(
        &mut self,
        tagged_value_ptr: Value,
        tested_type_id: TypeId,
    ) -> Value {
        // TaggedValue layout: [tag: u64 at offset 0][value: u64 at offset 8]
        let tag = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), tagged_value_ptr, 0);

        if let Some(ann_runtime_type_id) = self.get_annotation_runtime_type_id(tested_type_id) {
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
            //    RcHeader: [ref_count: u32, header_type_id: u32, drop_fn: ptr] = 16 bytes
            //    RcInstance: [header: RcHeader, type_id: u32 @ offset 16, ...]
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
            let expected_tag = crate::types::unknown_type_tag(tested_type_id, self.arena());
            let expected_val = self.iconst_cached(types::I64, expected_tag as i64);
            self.builder.ins().icmp(IntCC::Equal, tag, expected_val)
        }
    }

    /// Compile an `is` check against an unknown value using VIR type metadata.
    ///
    /// TEMP(N279-C): bridge for VIR-native type checks where sema `TypeId`
    /// cannot be recovered losslessly.
    pub(super) fn compile_unknown_is_check_vir(
        &mut self,
        tagged_value_ptr: Value,
        tested_vir_type_id: VirTypeId,
    ) -> Value {
        let tag = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), tagged_value_ptr, 0);
        let expected_tag = crate::types::vir_conversions::vir_unknown_type_tag(
            tested_vir_type_id,
            self.vir_type_table(),
        );
        let expected_val = self.iconst_cached(types::I64, expected_tag as i64);
        self.builder.ins().icmp(IntCC::Equal, tag, expected_val)
    }

    /// Compile an equality check for two values based on their Vole type.
    /// Handles string comparison via runtime function, floats via fcmp, and integers via icmp.
    fn compile_equality_check(
        &mut self,
        type_id: TypeId,
        left: Value,
        right: Value,
    ) -> CodegenResult<Value> {
        use crate::RuntimeKey;
        use cranelift::prelude::FloatCC;

        if self.vir_query_is_string(type_id) {
            Ok(self.call_runtime(RuntimeKey::StringEq, &[left, right])?)
        } else if self.vir_query_is_float(type_id) {
            Ok(self.builder.ins().fcmp(FloatCC::Equal, left, right))
        } else if type_id.is_integer() || type_id.is_bool() {
            Ok(self.builder.ins().icmp(IntCC::Equal, left, right))
        } else {
            Err(CodegenError::type_mismatch(
                "equality comparison",
                "string, float, integer, or bool",
                format!("{type_id:?}"),
            ))
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
        result_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let scrutinee = self.compile_vir_expr(scrutinee_expr)?;
        let scrutinee_type_id = scrutinee.type_id;

        let mut effective_result_type = self.try_substitute_type(result_type_id);

        // Repair degraded match result metadata by inferring from arm result
        // types when they provide a consistent concrete shape.
        let mut arm_types: Vec<TypeId> = Vec::new();
        for arm in arms {
            let arm_ty = self.try_substitute_type(self.sema_type_from_vir(arm.ty));
            if arm_ty != TypeId::UNKNOWN && !arm_types.contains(&arm_ty) {
                arm_types.push(arm_ty);
            }
        }
        if arm_types.len() > 1
            && let Some(inferred_union) = self.vir_query_lookup_union(arm_types.clone().into())
            && (!self.vir_query_is_union(effective_result_type)
                || effective_result_type.is_unknown()
                || self.vir_query_is_function(effective_result_type))
        {
            effective_result_type = inferred_union;
        } else if let [single] = arm_types.as_slice()
            && (effective_result_type.is_unknown()
                || self.vir_query_is_function(effective_result_type))
        {
            effective_result_type = *single;
        }

        // Replicate the nil-arm union return type adjustment from match_expr.
        if !self.vir_query_is_union(effective_result_type) {
            let has_nil_arm = arms.iter().any(|arm| {
                arm.ty != VirTypeId::UNKNOWN
                    && self
                        .vir_query_is_nil(self.try_substitute_type(self.sema_type_from_vir(arm.ty)))
            });
            if has_nil_arm && let Some(ret_type_id) = self.return_type {
                let ret_type_id = self.try_substitute_type(ret_type_id);
                if self.vir_query_is_union(ret_type_id) {
                    effective_result_type = ret_type_id;
                }
            }
        }

        let result_cranelift_type = self.cranelift_type(effective_result_type);
        let is_void = effective_result_type.is_void();

        // Try switch optimization for dense integer literal arms.
        if let Some(analysis) = match_switch::analyze_vir_switch(arms, scrutinee_type_id) {
            return self.emit_vir_switch_match(
                arms,
                analysis,
                scrutinee,
                effective_result_type,
                result_cranelift_type,
                is_void,
            );
        }

        self.compile_vir_match_chain(
            arms,
            scrutinee,
            effective_result_type,
            result_cranelift_type,
            is_void,
            scrutinee_type_id,
        )
    }

    /// Compile a VIR match using the standard chain of if-else blocks.
    fn compile_vir_match_chain(
        &mut self,
        arms: &[vole_vir::VirMatchArm],
        scrutinee: CompiledValue,
        result_type_id: TypeId,
        result_cranelift_type: Type,
        is_void: bool,
        scrutinee_type_id: TypeId,
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
                result_type_id,
                result_cranelift_type,
                is_void,
            )?;
        }

        self.switch_and_seal(trap_block);
        self.builder.ins().trap(crate::trap_codes::UNREACHABLE);

        self.switch_and_seal(merge_block);

        self.cleanup_fallible_scrutinee(&scrutinee, scrutinee_type_id)?;

        self.merge_block_result(merge_block, result_cranelift_type, result_type_id, is_void)
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
        result_type_id: TypeId,
        result_cranelift_type: Type,
        is_void: bool,
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
        let body_result = self.compile_vir_arm_body(&arm.body, result_type_id)?;
        let _ = std::mem::replace(&mut self.vars, saved_vars);

        self.emit_match_arm_exit(
            body_result,
            result_type_id,
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
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
        arm_block: Block,
        next_block: Block,
        effective_arm_block: &mut Block,
    ) -> CodegenResult<Option<Value>> {
        match pattern {
            vole_vir::VirPattern::Wildcard => Ok(None),

            vole_vir::VirPattern::Binding { name, ty: _, .. } => {
                let var = self.builder.declare_var(scrutinee.ty);
                self.builder.def_var(var, scrutinee.value);
                arm_variables.insert(*name, (var, scrutinee.type_id));
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
                let effective_result = if self.substitutions.is_some() {
                    let sub_tested =
                        self.try_substitute_type(self.sema_type_from_vir(*tested_type));
                    let sub_scrutinee = self.try_substitute_type(scrutinee.type_id);
                    self.compute_is_check_result(sub_scrutinee, sub_tested)
                } else {
                    convert_vir_is_check(result)
                };

                let cond = self.compile_is_check_result(&effective_result, scrutinee)?;

                // If there's a binding, introduce the variable after the check.
                if let Some((name, bind_ty, _)) = binding {
                    let var = self.builder.declare_var(scrutinee.ty);
                    self.builder.def_var(var, scrutinee.value);
                    arm_variables.insert(*name, (var, self.sema_type_from_vir(*bind_ty)));
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
                let cmp = self.compile_equality_check(
                    self.sema_type_from_vir(*scrutinee_ty),
                    scrutinee.value,
                    coerced_lit,
                )?;
                Ok(Some(cmp))
            }

            vole_vir::VirPattern::Val { name } => {
                let (var_val, var_type_id) =
                    if let Some(&(var, var_type_id)) = arm_variables.get(name) {
                        (self.builder.use_var(var), var_type_id)
                    } else if let Some(binding) = self.get_capture(name).copied() {
                        let captured = self.load_capture(&binding)?;
                        (captured.value, captured.type_id)
                    } else {
                        return Err(CodegenError::internal("undefined variable in val pattern"));
                    };

                let cmp = self.compile_equality_check(var_type_id, scrutinee.value, var_val)?;
                Ok(Some(cmp))
            }

            vole_vir::VirPattern::Success {
                inner,
                success_type,
                ..
            } => self.compile_vir_success_pattern(
                inner,
                scrutinee,
                self.sema_type_from_vir(*success_type),
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
        success_type: TypeId,
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
    ) -> CodegenResult<Option<Value>> {
        let tag = load_fallible_tag(self.builder, scrutinee.value);
        let is_success = self
            .builder
            .ins()
            .icmp_imm(IntCC::Equal, tag, FALLIBLE_SUCCESS_TAG);

        if let Some(inner_pat) = inner {
            let success_type_id = self.try_substitute_type(success_type);
            let payload_ty = self.cranelift_type(success_type_id);
            let payload = load_fallible_payload(self.builder, scrutinee.value, payload_ty);

            // The inner pattern is a VIR pattern (e.g. Binding for `success x`).
            if let vole_vir::VirPattern::Binding { name, .. } = inner_pat.as_ref() {
                let var = self.builder.declare_var(payload_ty);
                self.builder.def_var(var, payload);
                arm_variables.insert(*name, (var, success_type_id));
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
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
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
                let error_type_id = self.try_substitute_type(self.sema_type_from_vir(*error_ty));
                let payload_ty = self.cranelift_type(error_type_id);
                let payload = load_fallible_payload(self.builder, scrutinee.value, payload_ty);
                let var = self.builder.declare_var(payload_ty);
                self.builder.def_var(var, payload);
                arm_variables.insert(*name, (var, error_type_id));
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
                let ast_fields: Vec<_> = fields
                    .iter()
                    .map(|f| RecordFieldPattern {
                        field_name: f.field_name,
                        binding: f.binding,
                        span: vole_identity::Span::default(),
                    })
                    .collect();
                self.extract_error_field_bindings(
                    *type_def,
                    scrutinee.value,
                    &ast_fields,
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
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
    ) -> CodegenResult<Option<Value>> {
        let elem_type_ids = self.vir_query_unwrap_tuple(scrutinee.type_id);
        if let Some(elem_type_ids) = elem_type_ids {
            let (_, offsets) = self.tuple_layout(&elem_type_ids);
            let elem_cr_types = self.cranelift_types(&elem_type_ids);
            for binding in bindings {
                let i = binding.element_index;
                let offset = offsets[i];
                let elem_type_id = elem_type_ids[i];
                let elem_cr_type = elem_cr_types[i];

                if let vole_vir::VirPattern::Binding { name, .. } = &binding.pattern {
                    let value = self.builder.ins().load(
                        elem_cr_type,
                        MemFlags::new(),
                        scrutinee.value,
                        offset,
                    );
                    let var = self.builder.declare_var(elem_cr_type);
                    self.builder.def_var(var, value);
                    arm_variables.insert(*name, (var, elem_type_id));
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
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
        arm_block: Block,
        next_block: Block,
        effective_arm_block: &mut Block,
    ) -> CodegenResult<Option<Value>> {
        // Compute pattern check condition (if type check present)
        let pattern_check = if let Some(vir_result) = type_check {
            let effective_result = if self.substitutions.is_some() {
                if let Some(tested) = tested_type {
                    let sub_tested = self.try_substitute_type(self.sema_type_from_vir(*tested));
                    let sub_scrutinee = self.try_substitute_type(scrutinee.type_id);
                    self.compute_is_check_result(sub_scrutinee, sub_tested)
                } else {
                    convert_vir_is_check(vir_result)
                }
            } else {
                convert_vir_is_check(vir_result)
            };
            self.compile_is_check_result(&effective_result, scrutinee)?
        } else {
            None
        };

        // Resolve source type with substitutions for monomorphized generics
        let resolved_source_ty = self.try_substitute_type(self.sema_type_from_vir(source_ty));

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
        field_source_type_id: TypeId,
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
    ) -> CodegenResult<()> {
        let is_struct = self.vir_query_is_struct(field_source_type_id);
        for field in fields {
            let field_name = self.interner().resolve(field.field_name);
            let (slot, field_type_id) =
                get_field_slot_and_type_id_cg(field_source_type_id, field_name, self)?;

            let converted = if is_struct {
                self.struct_field_load(field_source, slot, field_type_id, field_source_type_id)?
            } else {
                self.get_instance_field(field_source, slot, field_type_id)?
            };
            let var = self.builder.declare_var(converted.ty);
            self.builder.def_var(var, converted.value);
            arm_variables.insert(field.binding_name, (var, field_type_id));
        }
        Ok(())
    }

    /// Compile an IsCheckResult into a condition value (if runtime check needed).
    fn compile_is_check_result(
        &mut self,
        result: &IsCheckResult,
        scrutinee: &CompiledValue,
    ) -> CodegenResult<Option<Value>> {
        match result {
            IsCheckResult::AlwaysTrue => Ok(None),
            IsCheckResult::AlwaysFalse => {
                let never_match = self.iconst_cached(types::I8, 0);
                Ok(Some(never_match))
            }
            IsCheckResult::CheckTag(tag_index) => {
                let cmp = self.tag_eq(scrutinee.value, *tag_index as i64);
                Ok(Some(cmp))
            }
            IsCheckResult::CheckUnknown(tested_type_id) => {
                let cmp = self.compile_unknown_is_check(scrutinee.value, *tested_type_id);
                Ok(Some(cmp))
            }
        }
    }

    /// Compile a VIR match arm body, coercing the result to the match result type.
    fn compile_vir_arm_body(
        &mut self,
        body: &vole_vir::VirBody,
        result_type_id: TypeId,
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
            } else if self.vir_query_is_union(result_type_id)
                && matches!(trailing.as_ref(), vole_vir::VirExpr::ArrayLiteral { .. })
                && let Some(expected_variant) =
                    self.preferred_array_like_union_variant(result_type_id)
            {
                self.compile_vir_expr_with_expected_type(trailing, expected_variant)?
            } else {
                self.compile_vir_expr(trailing)?
            }
        } else {
            let (_, body_val) = self.compile_vir_body(body)?;
            body_val.unwrap_or_else(|| self.void_value())
        };
        if body_result.type_id == TypeId::NEVER {
            return Ok(body_result);
        }
        self.coerce_to_type(body_result, result_type_id)
    }

    /// Emit the exit jump for a match arm body to the merge block.
    fn emit_match_arm_exit(
        &mut self,
        body_result: CompiledValue,
        result_type_id: TypeId,
        result_cranelift_type: Type,
        is_void: bool,
        merge_block: Block,
    ) -> CodegenResult<()> {
        if body_result.type_id == TypeId::NEVER {
            self.builder.ins().trap(crate::trap_codes::UNREACHABLE);
        } else if !is_void {
            let result_needs_rc = self.rc_state(result_type_id).needs_cleanup();
            self.jump_with_owned_result(
                body_result,
                result_type_id,
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
    fn emit_vir_switch_match(
        &mut self,
        arms: &[vole_vir::VirMatchArm],
        analysis: match_switch::SwitchAnalysis,
        scrutinee: CompiledValue,
        result_type_id: TypeId,
        result_cranelift_type: Type,
        is_void: bool,
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

            let body_result = self.compile_vir_arm_body(&arm.body, result_type_id)?;
            self.emit_match_arm_exit(
                body_result,
                result_type_id,
                result_cranelift_type,
                is_void,
                merge_block,
            )?;
        }

        self.switch_and_seal(merge_block);

        self.merge_block_result(merge_block, result_cranelift_type, result_type_id, is_void)
    }
}

/// Convert VIR's `IsCheckResult` to sema's `IsCheckResult`.
///
/// VIR defines its own copy to avoid circular crate dependencies.
/// The variants are isomorphic so this is a mechanical mapping.
fn convert_vir_is_check(vir: &vole_vir::expr::IsCheckResult) -> IsCheckResult {
    match vir {
        vole_vir::expr::IsCheckResult::AlwaysTrue => IsCheckResult::AlwaysTrue,
        vole_vir::expr::IsCheckResult::AlwaysFalse => IsCheckResult::AlwaysFalse,
        vole_vir::expr::IsCheckResult::CheckTag(tag) => IsCheckResult::CheckTag(*tag),
        vole_vir::expr::IsCheckResult::CheckUnknown(ty, _) => IsCheckResult::CheckUnknown(
            crate::types::vir_conversions::vir_to_sema_type_id_lossy(*ty),
        ),
    }
}
