// src/codegen/expr/pattern_match.rs
//
// Match expressions, is-checks, and pattern matching compilation.

use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;
use rustc_hash::FxHashMap;

use crate::errors::{CodegenError, CodegenResult};
use crate::types::{
    CompiledValue, FALLIBLE_SUCCESS_TAG, load_fallible_payload, load_fallible_tag,
    type_id_to_cranelift,
};

use vole_frontend::ast::{MatchExpr, RecordFieldPattern};
use vole_frontend::{ExprKind, NodeId, Pattern, PatternKind, Symbol, TypeExpr, TypeExprKind};
use vole_sema::IsCheckResult;
use vole_sema::type_arena::TypeId;

use super::super::context::Cg;
use super::super::control_flow::match_switch;

impl Cg<'_, '_, '_> {
    // =========================================================================
    // Type resolution helpers
    // =========================================================================

    /// Resolve a simple TypeExpr to a TypeId (for monomorphized generic fallback).
    /// Handles primitive types, named types (nil, Done, etc.), never, unknown - enough
    /// for `is` checks in generic function bodies that sema didn't analyze.
    pub(super) fn resolve_simple_type_expr(&self, type_expr: &TypeExpr) -> Option<TypeId> {
        use vole_frontend::{PrimitiveType, TypeExprKind as TEK};
        let arena = self.arena();
        match &type_expr.kind {
            TEK::Never => Some(TypeId::NEVER),
            TEK::Unknown => Some(TypeId::UNKNOWN),
            TEK::Primitive(p) => Some(match p {
                PrimitiveType::Bool => TypeId::BOOL,
                PrimitiveType::I8 => arena.i8(),
                PrimitiveType::I16 => arena.i16(),
                PrimitiveType::I32 => arena.i32(),
                PrimitiveType::I64 => arena.i64(),
                PrimitiveType::I128 => arena.i128(),
                PrimitiveType::U8 => arena.u8(),
                PrimitiveType::U16 => arena.u16(),
                PrimitiveType::U32 => arena.u32(),
                PrimitiveType::U64 => arena.u64(),
                PrimitiveType::F32 => arena.f32(),
                PrimitiveType::F64 => arena.f64(),
                PrimitiveType::F128 => arena.f128(),
                PrimitiveType::String => arena.string(),
            }),
            TEK::Named(sym) => {
                // Resolve named types (sentinels, structs, classes, etc.) through the
                // name resolution system. Uses current module context or main module.
                let name = self.interner().resolve(*sym);
                let module_id = self.current_module.unwrap_or(self.env.analyzed.module_id);
                let query = self.query();
                if let Some(type_def_id) = query.resolve_type_def_by_str(module_id, name) {
                    return self.registry().get_type(type_def_id).base_type_id;
                }
                // If name resolution failed, check if this is a type parameter
                // that can be resolved via the current substitutions map.
                if let Some(subs) = self.substitutions {
                    let name_table = self.name_table();
                    for (&name_id, &type_id) in subs {
                        if name_table.last_segment_str(name_id).as_deref() == Some(name) {
                            return Some(type_id);
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Recover the concrete pattern type for a typed record arm.
    ///
    /// Prefer sema's `IsCheckResult` (which already includes generic inference),
    /// then fall back to simple type resolution for non-generic monomorph cases.
    fn pattern_type_id_for_record_arm(
        &self,
        scrutinee_type_id: TypeId,
        pattern_id: NodeId,
        type_expr: &TypeExpr,
    ) -> Option<TypeId> {
        let is_record_type = |ty: TypeId| {
            self.arena().unwrap_nominal(ty).is_some_and(|(_, _, kind)| {
                kind.is_class_or_struct()
                    || matches!(kind, vole_sema::type_arena::NominalKind::Error)
            })
        };

        if let Some(is_check_result) = self.get_is_check_result(pattern_id) {
            match is_check_result {
                IsCheckResult::CheckTag(tag) => {
                    let variants = self.arena().unwrap_union(scrutinee_type_id)?;
                    return variants
                        .get(tag as usize)
                        .copied()
                        .filter(|&ty| is_record_type(ty));
                }
                IsCheckResult::AlwaysTrue => {
                    if is_record_type(scrutinee_type_id) {
                        return Some(scrutinee_type_id);
                    }
                    return None;
                }
                IsCheckResult::AlwaysFalse => return None,
                IsCheckResult::CheckUnknown(_) => {}
            }
        }

        self.resolve_simple_type_expr(type_expr)
            .filter(|&ty| is_record_type(ty))
    }

    pub(super) fn type_expr_terminal_symbol(type_expr: &TypeExpr) -> Option<Symbol> {
        match &type_expr.kind {
            TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => Some(*sym),
            TypeExprKind::QualifiedPath { segments, .. } => segments.last().copied(),
            _ => None,
        }
    }

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
        let arena = self.arena();
        if value_type_id.is_unknown() {
            IsCheckResult::CheckUnknown(tested_type_id)
        } else if let Some(variants) = arena.unwrap_union(value_type_id) {
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

    /// Try to statically determine the result of an `is` check without compiling the value.
    /// Returns Some(IsCheckResult) if the result is known, None if compilation is needed.
    /// Used to eliminate dead branches in monomorphized generics.
    pub(crate) fn try_static_is_check(
        &self,
        is_expr: &vole_frontend::ast::IsExpr,
        expr_id: NodeId,
    ) -> Option<IsCheckResult> {
        // When substitutions are active (monomorphized module code), prefer
        // recomputation over sema's stored result: sema stored tag indices for
        // the generic union ordering which may differ from the substituted ordering.
        // Fall back to the sema result only when the tested type cannot be resolved.
        if self.substitutions.is_some() {
            if let Some(tested_type_id) = self.resolve_simple_type_expr(&is_expr.type_expr) {
                let value_type_id = match &is_expr.value.kind {
                    ExprKind::Identifier(sym) => self.vars.get(sym).map(|(_, tid)| *tid)?,
                    _ => return self.get_is_check_result(expr_id),
                };
                return Some(self.compute_is_check_result(value_type_id, tested_type_id));
            }
            // Cannot resolve tested type — fall through to sema's result
            return self.get_is_check_result(expr_id);
        }

        // Non-monomorphized path: trust sema's pre-computed result
        if let Some(result) = self.get_is_check_result(expr_id) {
            return Some(result);
        }

        // For monomorphized generics: compute from the value's variable type
        let tested_type_id = self.resolve_simple_type_expr(&is_expr.type_expr)?;

        // Get the value's type from the variable scope (for identifiers)
        let value_type_id = match &is_expr.value.kind {
            ExprKind::Identifier(sym) => self.vars.get(sym).map(|(_, tid)| *tid)?,
            _ => return None,
        };

        Some(self.compute_is_check_result(value_type_id, tested_type_id))
    }

    /// Compile an `is` type check expression
    pub(super) fn is_expr(
        &mut self,
        is_expr: &vole_frontend::ast::IsExpr,
        expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let value = self.expr(&is_expr.value)?;

        // Look up pre-computed type check result from sema (module-aware).
        // Falls back to computing it at codegen time for monomorphized generic functions,
        // since sema skips generic function bodies.
        //
        // When substitutions are active (monomorphized module code), prefer recomputation:
        // sema analyzed the module body with generic types (e.g. `T | Done`) and stored
        // tag indices based on that ordering.  After substitution the union variant order
        // may change (e.g. `i64 | Done` sorts differently), making stored CheckTag
        // indices stale.  Fall back to the sema result only when the tested type cannot
        // be resolved (complex type expressions that resolve_simple_type_expr doesn't handle).
        let is_check_result = if self.substitutions.is_some() {
            if let Some(tested_type_id) = self.resolve_simple_type_expr(&is_expr.type_expr) {
                self.compute_is_check_result(value.type_id, tested_type_id)
            } else if let Some(result) = self.get_is_check_result(expr_id) {
                result
            } else {
                return Err(CodegenError::internal(
                    "is expression in monomorphized generic: cannot resolve tested type",
                ));
            }
        } else {
            match self.get_is_check_result(expr_id) {
                Some(result) => result,
                None => {
                    // Monomorphized generic: compute from substituted types
                    let tested_type_id = self
                        .resolve_simple_type_expr(&is_expr.type_expr)
                        .ok_or_else(|| {
                            CodegenError::internal(
                                "is expression in monomorphized generic: cannot resolve tested type",
                            )
                        })?;
                    self.compute_is_check_result(value.type_id, tested_type_id)
                }
            }
        };
        match is_check_result {
            IsCheckResult::AlwaysTrue => Ok(self.bool_const(true)),
            IsCheckResult::AlwaysFalse => Ok(self.bool_const(false)),
            IsCheckResult::CheckTag(tag_index) => {
                let result = self.tag_eq(value.value, tag_index as i64);
                Ok(self.bool_value(result))
            }
            IsCheckResult::CheckUnknown(tested_type_id) => {
                // Check if the unknown value's tag matches the tested type
                // TaggedValue layout: [tag: u64 at offset 0][value: u64 at offset 8]
                let tag = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), value.value, 0);
                let expected_tag = crate::types::unknown_type_tag(tested_type_id, self.arena());
                let expected_val = self.builder.ins().iconst(types::I64, expected_tag as i64);
                let result = self.builder.ins().icmp(IntCC::Equal, tag, expected_val);
                Ok(self.bool_value(result))
            }
        }
    }

    // =========================================================================
    // Pattern compilation helpers
    // =========================================================================

    /// Compile a type pattern check for match expressions
    /// Returns Some(comparison_value) if a runtime check is needed, None if always matches
    fn compile_type_pattern_check(
        &mut self,
        scrutinee: &CompiledValue,
        pattern_id: NodeId,
    ) -> CodegenResult<Option<Value>> {
        // Look up pre-computed type check result from sema (module-aware)
        let is_check_result = self
            .get_is_check_result(pattern_id)
            .expect("INTERNAL: type pattern: missing IsCheckResult from sema");

        match is_check_result {
            IsCheckResult::AlwaysTrue => Ok(None), // Always matches
            IsCheckResult::AlwaysFalse => {
                // Never matches
                let never_match = self.builder.ins().iconst(types::I8, 0);
                Ok(Some(never_match))
            }
            IsCheckResult::CheckTag(tag_index) => {
                let result = self.tag_eq(scrutinee.value, tag_index as i64);
                Ok(Some(result))
            }
            IsCheckResult::CheckUnknown(tested_type_id) => {
                // Check if the unknown value's tag matches the tested type
                // TaggedValue layout: [tag: u64 at offset 0][value: u64 at offset 8]
                let tag = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), scrutinee.value, 0);
                let expected_tag = crate::types::unknown_type_tag(tested_type_id, self.arena());
                let expected_val = self.builder.ins().iconst(types::I64, expected_tag as i64);
                let result = self.builder.ins().icmp(IntCC::Equal, tag, expected_val);
                Ok(Some(result))
            }
        }
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

        let arena = self.arena();
        if arena.is_string(type_id) {
            Ok(self.call_runtime(RuntimeKey::StringEq, &[left, right])?)
        } else if arena.is_float(type_id) {
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

    /// Compile a single match arm's pattern, returning the condition value (if any).
    ///
    /// Updates `arm_variables` with any bindings introduced by the pattern and
    /// `effective_arm_block` if a conditional extraction block is created.
    fn compile_match_arm_pattern(
        &mut self,
        scrutinee: &CompiledValue,
        pattern: &Pattern,
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
        arm_block: Block,
        next_block: Block,
        effective_arm_block: &mut Block,
    ) -> CodegenResult<Option<Value>> {
        let scrutinee_type_id = scrutinee.type_id;
        match &pattern.kind {
            PatternKind::Wildcard => Ok(None),
            PatternKind::Identifier { name } => {
                // Check if sema recognized this as a type pattern by looking for
                // a pre-computed IsCheckResult. This handles all type patterns
                // including sentinel types (Done, nil) from prelude modules.
                if self.get_is_check_result(pattern.id).is_some() {
                    // Type pattern - compare against union variant tag
                    Ok(self.compile_type_pattern_check(scrutinee, pattern.id)?)
                } else {
                    // Regular identifier binding
                    let var = self.builder.declare_var(scrutinee.ty);
                    self.builder.def_var(var, scrutinee.value);
                    arm_variables.insert(*name, (var, scrutinee_type_id));
                    Ok(None)
                }
            }
            PatternKind::Type { type_expr: _ } => {
                Ok(self.compile_type_pattern_check(scrutinee, pattern.id)?)
            }
            PatternKind::Literal(lit_expr) => {
                // Save and restore vars for pattern matching
                let saved_vars = std::mem::replace(&mut self.vars, arm_variables.clone());
                let lit_val = self.expr(lit_expr)?;
                *arm_variables = std::mem::replace(&mut self.vars, saved_vars);

                // Coerce literal value to match scrutinee's Cranelift type.
                let coerced_lit = self.convert_for_select(lit_val.value, scrutinee.ty);

                let cmp =
                    self.compile_equality_check(scrutinee_type_id, scrutinee.value, coerced_lit)?;
                Ok(Some(cmp))
            }
            PatternKind::Val { name } => {
                // Val pattern - compare against existing variable's value.
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
            PatternKind::Success { inner } => {
                self.compile_success_pattern(inner, scrutinee, scrutinee_type_id, arm_variables)
            }
            PatternKind::Error { inner } => {
                let tag = load_fallible_tag(self.builder, scrutinee.value);
                Ok(self.compile_error_pattern(inner, scrutinee, tag, arm_variables)?)
            }
            PatternKind::Tuple { elements } => {
                self.compile_tuple_pattern(elements, scrutinee, arm_variables)
            }
            PatternKind::Record { type_name, fields } => self.compile_record_pattern(
                scrutinee,
                pattern,
                type_name.as_ref(),
                fields,
                arm_variables,
                arm_block,
                next_block,
                effective_arm_block,
            ),
        }
    }

    /// Compile a success pattern (Ok { inner }) inside a match arm.
    fn compile_success_pattern(
        &mut self,
        inner: &Option<Box<Pattern>>,
        scrutinee: &CompiledValue,
        scrutinee_type_id: TypeId,
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
    ) -> CodegenResult<Option<Value>> {
        let tag = load_fallible_tag(self.builder, scrutinee.value);
        let is_success = self
            .builder
            .ins()
            .icmp_imm(IntCC::Equal, tag, FALLIBLE_SUCCESS_TAG);

        if let Some(inner_pat) = inner {
            let fallible_types = self.arena().unwrap_fallible(scrutinee_type_id);
            if let Some((success_type_id, _error_type_id)) = fallible_types {
                let ptr_type = self.ptr_type();
                let payload_ty = {
                    let arena = self.arena();
                    type_id_to_cranelift(success_type_id, arena, ptr_type)
                };
                let payload = load_fallible_payload(self.builder, scrutinee.value, payload_ty);

                if let PatternKind::Identifier { name } = &inner_pat.kind {
                    let var = self.builder.declare_var(payload_ty);
                    self.builder.def_var(var, payload);
                    arm_variables.insert(*name, (var, success_type_id));
                }
            }
        }
        Ok(Some(is_success))
    }

    /// Compile a tuple destructure pattern.
    fn compile_tuple_pattern(
        &mut self,
        elements: &[Pattern],
        scrutinee: &CompiledValue,
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
    ) -> CodegenResult<Option<Value>> {
        use crate::types::tuple_layout_id;

        let elem_type_ids = self.arena().unwrap_tuple(scrutinee.type_id).cloned();
        if let Some(elem_type_ids) = elem_type_ids {
            let ptr_type = self.ptr_type();
            let offsets = {
                let arena = self.arena();
                let (_, offsets) =
                    tuple_layout_id(&elem_type_ids, ptr_type, self.registry(), arena);
                offsets
            };
            let elem_cr_types = self.cranelift_types(&elem_type_ids);
            for (i, pat) in elements.iter().enumerate() {
                if let PatternKind::Identifier { name } = &pat.kind {
                    let offset = offsets[i];
                    let elem_type_id = elem_type_ids[i];
                    let elem_cr_type = elem_cr_types[i];
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
            }
        }
        Ok(None)
    }

    #[expect(clippy::too_many_arguments)]
    fn compile_record_pattern(
        &mut self,
        scrutinee: &CompiledValue,
        pattern: &Pattern,
        type_name: Option<&TypeExpr>,
        fields: &[RecordFieldPattern],
        arm_variables: &mut FxHashMap<Symbol, (Variable, TypeId)>,
        arm_block: Block,
        next_block: Block,
        effective_arm_block: &mut Block,
    ) -> CodegenResult<Option<Value>> {
        let scrutinee_type_id = scrutinee.type_id;

        let (pattern_check, pattern_type_id) = if let Some(type_expr) = type_name {
            let pattern_check = self.compile_type_pattern_check(scrutinee, pattern.id)?;
            let pattern_type_id =
                self.pattern_type_id_for_record_arm(scrutinee_type_id, pattern.id, type_expr);
            (pattern_check, pattern_type_id)
        } else {
            (None, None)
        };

        let is_conditional_extract =
            pattern_check.is_some() && self.arena().is_union(scrutinee_type_id);

        if is_conditional_extract {
            let extract_block = self.builder.create_block();

            let cond =
                pattern_check.expect("INTERNAL: match pattern: missing pattern_check condition");
            self.builder
                .ins()
                .brif(cond, extract_block, &[], next_block, &[]);
            self.builder.seal_block(arm_block);
            *effective_arm_block = extract_block;

            self.builder.switch_to_block(extract_block);

            let (field_source, field_source_type_id) = if let Some(pt_id) = pattern_type_id {
                let payload =
                    self.builder
                        .ins()
                        .load(types::I64, MemFlags::new(), scrutinee.value, 8);
                (payload, pt_id)
            } else {
                (scrutinee.value, scrutinee_type_id)
            };

            self.extract_record_fields(fields, field_source, field_source_type_id, arm_variables)?;

            Ok(None)
        } else {
            let (field_source, field_source_type_id) = if self.arena().is_union(scrutinee_type_id) {
                if let Some(pt_id) = pattern_type_id {
                    let payload =
                        self.builder
                            .ins()
                            .load(types::I64, MemFlags::new(), scrutinee.value, 8);
                    (payload, pt_id)
                } else {
                    (scrutinee.value, scrutinee_type_id)
                }
            } else {
                (scrutinee.value, scrutinee_type_id)
            };

            self.extract_record_fields(fields, field_source, field_source_type_id, arm_variables)?;

            Ok(pattern_check)
        }
    }

    // =========================================================================
    // Match expression compilation
    // =========================================================================

    /// Compile a match expression
    #[tracing::instrument(skip(self, match_expr), fields(arms = match_expr.arms.len()))]
    pub fn match_expr(
        &mut self,
        match_expr: &MatchExpr,
        expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let scrutinee = self.expr(&match_expr.scrutinee)?;
        let scrutinee_type_id = scrutinee.type_id;
        let scrutinee_type_str = self.arena().display_basic(scrutinee_type_id);
        tracing::trace!(scrutinee_type = %scrutinee_type_str, "match scrutinee");

        // Get the result type from semantic analysis (same as when_expr / if_expr)
        let mut result_type_id = self
            .get_expr_type_substituted(&expr_id)
            .unwrap_or(TypeId::VOID);
        // Match expressions that mix a non-union value with `nil` can be inferred
        // as the non-union value in some monomorphized contexts, which erases nil
        // arms to zero values. If this function returns a union type, use that
        // union return type for the match result.
        if !self.arena().is_union(result_type_id) {
            let has_nil_arm = match_expr.arms.iter().any(|arm| {
                self.get_expr_type_substituted(&arm.body.id)
                    .is_some_and(|ty| self.arena().is_nil(ty))
            });
            if has_nil_arm && let Some(ret_type_id) = self.return_type {
                let ret_type_id = self.try_substitute_type(ret_type_id);
                if self.arena().is_union(ret_type_id) {
                    result_type_id = ret_type_id;
                }
            }
        }
        let result_cranelift_type = self.cranelift_type(result_type_id);
        let is_void = self.arena().is_void(result_type_id);

        // Try Switch optimization for dense integer literal arms (O(1) dispatch)
        if let Some(analysis) = match_switch::analyze_switch(match_expr, scrutinee_type_id) {
            tracing::trace!(arms = analysis.arm_values.len(), "using switch dispatch");
            return self.emit_switch_match(
                match_expr,
                analysis,
                scrutinee,
                result_type_id,
                result_cranelift_type,
                is_void,
            );
        }

        self.compile_match_chain(
            match_expr,
            scrutinee,
            result_type_id,
            result_cranelift_type,
            is_void,
            scrutinee_type_id,
        )
    }

    /// Compile a match expression using the standard chain of if-else blocks.
    fn compile_match_chain(
        &mut self,
        match_expr: &MatchExpr,
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

        // Create a trap block for non-exhaustive match (should be unreachable)
        let trap_block = self.builder.create_block();

        let arm_blocks: Vec<Block> = match_expr
            .arms
            .iter()
            .map(|_| self.builder.create_block())
            .collect();

        if !arm_blocks.is_empty() {
            self.builder.ins().jump(arm_blocks[0], &[]);
        } else if !is_void {
            let default_val = self.typed_zero(result_cranelift_type);
            let default_arg = BlockArg::from(default_val);
            self.builder.ins().jump(merge_block, &[default_arg]);
        } else {
            self.builder.ins().jump(merge_block, &[]);
        }

        for (i, arm) in match_expr.arms.iter().enumerate() {
            let arm_block = arm_blocks[i];
            // For the last arm, if pattern fails, go to trap (should be unreachable)
            let next_block = arm_blocks.get(i + 1).copied().unwrap_or(trap_block);

            self.builder.switch_to_block(arm_block);
            self.invalidate_value_caches();

            let mut arm_variables = self.vars.clone();
            // Track the effective arm block (may change for conditional extraction)
            let mut effective_arm_block = arm_block;

            let pattern_matches = self.compile_match_arm_pattern(
                &scrutinee,
                &arm.pattern,
                &mut arm_variables,
                arm_block,
                next_block,
                &mut effective_arm_block,
            )?;

            // Save and restore vars for guard evaluation
            let guard_result = if let Some(guard) = &arm.guard {
                let saved_vars = std::mem::replace(&mut self.vars, arm_variables.clone());
                let guard_val = self.expr(guard)?;
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
                self.builder
                    .ins()
                    .brif(cond, body_block, &[], next_block, &[]);
            } else {
                self.builder.ins().jump(body_block, &[]);
            }

            // Seal the effective arm block (may be extract_block for conditional patterns)
            self.builder.seal_block(effective_arm_block);

            self.builder.switch_to_block(body_block);

            // Compile body with the arm's variables
            let saved_vars = std::mem::replace(&mut self.vars, arm_variables);
            let mut body_val = self.expr(&arm.body)?;
            let _ = std::mem::replace(&mut self.vars, saved_vars);

            if body_val.type_id == TypeId::NEVER {
                // Divergent arm (unreachable/panic) — terminate with trap
                self.builder.ins().trap(crate::trap_codes::UNREACHABLE);
            } else if !is_void {
                body_val = self.coerce_to_type(body_val, result_type_id)?;
                // If the arm body produces a borrowed RC value, emit rc_inc so
                // the match result owns its reference (mirroring if_expr_blocks).
                // Without this, borrowed payloads extracted from unions would be
                // freed by both the union cleanup and the result variable cleanup.
                let result_needs_rc = self.rc_state(result_type_id).needs_cleanup();
                self.jump_with_owned_result(
                    body_val,
                    result_type_id,
                    result_cranelift_type,
                    result_needs_rc,
                    merge_block,
                )?;
            } else {
                self.builder.ins().jump(merge_block, &[]);
            }
            self.builder.seal_block(body_block);
        }

        // Fill in trap block (should be unreachable if match is exhaustive)
        self.switch_and_seal(trap_block);
        self.builder.ins().trap(crate::trap_codes::UNREACHABLE);

        self.switch_and_seal(merge_block);
        self.invalidate_value_caches();

        // Clean up fallible scrutinee payload.
        // Fallible structs are stack-allocated (tag + payload) and never RC-tracked,
        // so the RC payload inside them leaks unless we explicitly rc_dec it here.
        // Each match arm already rc_inc'd any borrowed payload it returns, so this
        // rc_dec balances the original reference from the callee.
        self.cleanup_fallible_scrutinee(&scrutinee, scrutinee_type_id)?;

        self.merge_block_result(merge_block, result_cranelift_type, result_type_id, is_void)
    }

    /// Emit a match expression using Cranelift's Switch for O(1) dispatch.
    ///
    /// Creates a body block for each arm plus a default block, wires up the Switch,
    /// then compiles each arm body and merges results.
    fn emit_switch_match(
        &mut self,
        match_expr: &MatchExpr,
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

        // Create body blocks for each arm
        let body_blocks: Vec<Block> = match_expr
            .arms
            .iter()
            .map(|_| self.builder.create_block())
            .collect();

        // Default block: wildcard arm or trap
        let default_block = if let Some(wc_idx) = analysis.wildcard_idx {
            body_blocks[wc_idx]
        } else {
            self.builder.create_block()
        };

        // Build and emit the Switch
        let mut switch = Switch::new();
        for &(arm_idx, value) in &analysis.arm_values {
            // Use two's complement representation so negative i64 values
            // map to the upper half of u64 range (fits within i64 type bounds)
            let entry = value as u64 as u128;
            switch.set_entry(entry, body_blocks[arm_idx]);
        }
        switch.emit(self.builder, scrutinee.value, default_block);

        // If there's no wildcard, the default block is a trap
        if analysis.wildcard_idx.is_none() {
            self.switch_and_seal(default_block);
            self.builder.ins().trap(crate::trap_codes::UNREACHABLE);
        }

        // Whether the result type needs RC cleanup
        let result_needs_rc = !is_void && self.rc_state(result_type_id).needs_cleanup();

        // Compile each arm body
        for (i, arm) in match_expr.arms.iter().enumerate() {
            self.builder.switch_to_block(body_blocks[i]);
            self.builder.seal_block(body_blocks[i]);
            self.invalidate_value_caches();

            let mut body_val = self.expr(&arm.body)?;

            if body_val.type_id == TypeId::NEVER {
                // Divergent arm (unreachable/panic) — terminate with trap
                self.builder.ins().trap(crate::trap_codes::UNREACHABLE);
            } else if !is_void {
                body_val = self.coerce_to_type(body_val, result_type_id)?;
                self.jump_with_owned_result(
                    body_val,
                    result_type_id,
                    result_cranelift_type,
                    result_needs_rc,
                    merge_block,
                )?;
            } else {
                self.builder.ins().jump(merge_block, &[]);
            }
        }

        self.switch_and_seal(merge_block);
        self.invalidate_value_caches();

        self.merge_block_result(merge_block, result_cranelift_type, result_type_id, is_void)
    }
}
