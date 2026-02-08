// src/sema/analyzer/patterns.rs

use super::*;
use crate::analysis_cache::IsCheckResult;
use crate::type_arena::TypeId as ArenaTypeId;
use crate::type_arena::TypeIdVec;
use crate::types::StructFieldId;
use rustc_hash::FxHashMap;
use vole_frontend::{PatternKind, Symbol, TypeExpr};

impl Analyzer {
    /// Check pattern and return TypeId directly.
    pub(crate) fn check_pattern_id(
        &mut self,
        pattern: &Pattern,
        scrutinee_type_id: ArenaTypeId,
        interner: &Interner,
    ) -> Option<ArenaTypeId> {
        match &pattern.kind {
            PatternKind::Wildcard => {
                // Wildcard always matches, nothing to check, no narrowing
                None
            }
            PatternKind::Literal(expr) => {
                // Check literal type matches scrutinee type, using bidirectional type
                // inference so integer literals get the scrutinee's type (e.g. i32, not i64).
                if let Ok(lit_type_id) =
                    self.check_expr_expecting_id(expr, Some(scrutinee_type_id), interner)
                    && !self.types_compatible_id(lit_type_id, scrutinee_type_id, interner)
                    && !self.types_compatible_id(scrutinee_type_id, lit_type_id, interner)
                {
                    let expected = self.type_display_id(scrutinee_type_id);
                    let found = self.type_display_id(lit_type_id);
                    self.add_error(
                        SemanticError::PatternTypeMismatch {
                            expected,
                            found,
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                }
                None
            }
            PatternKind::Identifier { name } => {
                let span = pattern.span;
                if let Some(pattern_type_id) =
                    self.resolve_identifier_pattern_type_id(*name, scrutinee_type_id, interner)
                {
                    self.check_type_pattern_compatibility_id(
                        pattern_type_id,
                        scrutinee_type_id,
                        span,
                        interner,
                    );

                    // Compute IsCheckResult for codegen
                    let is_check_result =
                        self.compute_type_pattern_check_result(pattern_type_id, scrutinee_type_id);
                    self.record_is_check_result(pattern.id, is_check_result);

                    Some(pattern_type_id)
                } else {
                    // Regular identifier binding pattern
                    self.scope.define(
                        *name,
                        Variable {
                            ty: scrutinee_type_id,
                            mutable: false,
                            declaration_span: pattern.span,
                        },
                    );
                    None
                }
            }
            PatternKind::Type { type_expr } => {
                let span = pattern.span;
                let pattern_type_id =
                    self.resolve_pattern_type_expr_id(type_expr, scrutinee_type_id, interner);
                self.check_type_pattern_compatibility_id(
                    pattern_type_id,
                    scrutinee_type_id,
                    span,
                    interner,
                );

                // Compute IsCheckResult for codegen
                let is_check_result =
                    self.compute_type_pattern_check_result(pattern_type_id, scrutinee_type_id);
                self.record_is_check_result(pattern.id, is_check_result);

                Some(pattern_type_id)
            }
            PatternKind::Val { name } => {
                let span = pattern.span;
                // Val pattern compares against existing variable's value
                let var_ty_id = self.scope.get(*name).map(|v| v.ty);
                if let Some(var_ty_id) = var_ty_id {
                    // Check type compatibility using TypeId
                    if !self.types_compatible_id(var_ty_id, scrutinee_type_id, interner)
                        && !self.types_compatible_id(scrutinee_type_id, var_ty_id, interner)
                    {
                        let expected = self.type_display_id(scrutinee_type_id);
                        let found = self.type_display_id(var_ty_id);
                        self.add_error(
                            SemanticError::PatternTypeMismatch {
                                expected,
                                found,
                                span: span.into(),
                            },
                            span,
                        );
                    }
                } else {
                    self.add_error(
                        SemanticError::UndefinedVariable {
                            name: interner.resolve(*name).to_string(),
                            span: span.into(),
                        },
                        span,
                    );
                }
                // Val patterns don't narrow types
                None
            }
            PatternKind::Success { inner } => {
                let span = pattern.span;
                // Success pattern only valid when matching on fallible type
                let fallible_info = self.type_arena().unwrap_fallible(scrutinee_type_id);
                let Some((success_type_id, _error_type_id)) = fallible_info else {
                    let found = self.type_display_id(scrutinee_type_id);
                    self.add_error(
                        SemanticError::SuccessPatternOnNonFallible {
                            found,
                            span: span.into(),
                        },
                        span,
                    );
                    return None;
                };

                // If there's an inner pattern, check it against success type
                if let Some(inner_pattern) = inner {
                    self.check_pattern_id(inner_pattern, success_type_id, interner)
                } else {
                    // Bare success - no narrowing
                    None
                }
            }
            PatternKind::Error { inner } => {
                let span = pattern.span;
                // Error pattern only valid when matching on fallible type
                let fallible_info = self.type_arena().unwrap_fallible(scrutinee_type_id);
                let Some((_success_type_id, error_type_id)) = fallible_info else {
                    let found = self.type_display_id(scrutinee_type_id);
                    self.add_error(
                        SemanticError::ErrorPatternOnNonFallible {
                            found,
                            span: span.into(),
                        },
                        span,
                    );
                    return None;
                };

                // If there's an inner pattern, check it against error type
                if let Some(inner_pattern) = inner {
                    self.check_error_inner_pattern(inner_pattern, error_type_id, interner)
                } else {
                    // Bare error - no narrowing
                    None
                }
            }
            PatternKind::Tuple { elements } => {
                let span = pattern.span;
                // Skip if scrutinee type is INVALID (prior error)
                if scrutinee_type_id.is_invalid() {
                    return None;
                }
                // Tuple pattern - check against tuple type
                let tuple_elements = self
                    .type_arena()
                    .unwrap_tuple(scrutinee_type_id)
                    .map(|v| v.to_vec());
                if let Some(elem_type_ids) = tuple_elements {
                    if elements.len() != elem_type_ids.len() {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: format!("tuple of {} elements", elem_type_ids.len()),
                                found: format!("tuple pattern with {} elements", elements.len()),
                                span: span.into(),
                            },
                            span,
                        );
                        return None;
                    }
                    // Check each element pattern against its type
                    for (pat, elem_type_id) in elements.iter().zip(elem_type_ids.iter()) {
                        self.check_pattern_id(pat, *elem_type_id, interner);
                    }
                    None // No type narrowing for tuple patterns
                } else {
                    self.type_error_id("tuple", scrutinee_type_id, span);
                    None
                }
            }
            PatternKind::Record { type_name, fields } => {
                let span = pattern.span;
                // Typed record pattern: TypeName { x, y }
                if let Some(type_expr) = type_name {
                    let pattern_type_id =
                        self.resolve_pattern_type_expr_id(type_expr, scrutinee_type_id, interner);

                    if pattern_type_id.is_invalid() {
                        if let Some(name) = Self::named_type_symbol(type_expr) {
                            let type_name = interner.resolve(name);
                            self.add_error(
                                SemanticError::UnknownType {
                                    name: type_name.to_string(),
                                    hint: unknown_type_hint(type_name),
                                    span: span.into(),
                                },
                                span,
                            );
                        }
                        return None;
                    }

                    let Some(type_fields) = self.record_pattern_fields_for_type_id(pattern_type_id)
                    else {
                        let found = self.type_display_id(pattern_type_id);
                        self.add_error(
                            SemanticError::PatternTypeMismatch {
                                expected: "class, struct, or error".to_string(),
                                found,
                                span: span.into(),
                            },
                            span,
                        );
                        return None;
                    };

                    // Check pattern fields
                    self.check_record_pattern_fields_id(fields, &type_fields, span, interner);

                    // Check compatibility with scrutinee
                    self.check_type_pattern_compatibility_id(
                        pattern_type_id,
                        scrutinee_type_id,
                        span,
                        interner,
                    );

                    // Compute IsCheckResult for codegen
                    let is_check_result =
                        self.compute_type_pattern_check_result(pattern_type_id, scrutinee_type_id);
                    self.record_is_check_result(pattern.id, is_check_result);

                    Some(pattern_type_id)
                } else {
                    // Anonymous record pattern - check against scrutinee's fields
                    self.check_anonymous_record_pattern_id(
                        fields,
                        scrutinee_type_id,
                        span,
                        interner,
                    );
                    None
                }
            }
        }
    }

    fn named_type_symbol(type_expr: &TypeExpr) -> Option<Symbol> {
        match type_expr {
            TypeExpr::Named(sym) | TypeExpr::Generic { name: sym, .. } => Some(*sym),
            _ => None,
        }
    }

    fn terminal_type_symbol(type_expr: &TypeExpr) -> Option<Symbol> {
        match type_expr {
            TypeExpr::Named(sym) | TypeExpr::Generic { name: sym, .. } => Some(*sym),
            TypeExpr::QualifiedPath { segments, .. } => segments.last().copied(),
            _ => None,
        }
    }

    fn infer_pattern_type_args_for_def(
        &self,
        type_def_id: TypeDefId,
        scrutinee_type_id: ArenaTypeId,
    ) -> TypeIdVec {
        let arena = self.type_arena();

        if let Some((scrutinee_def_id, type_args, _)) = arena.unwrap_nominal(scrutinee_type_id)
            && scrutinee_def_id == type_def_id
        {
            return type_args.clone();
        }

        if let Some(variants) = arena.unwrap_union(scrutinee_type_id) {
            for &variant_type_id in variants {
                if let Some((variant_def_id, type_args, _)) = arena.unwrap_nominal(variant_type_id)
                    && variant_def_id == type_def_id
                {
                    return type_args.clone();
                }
            }
        }

        TypeIdVec::new()
    }

    fn resolve_identifier_pattern_type_id(
        &mut self,
        name: Symbol,
        scrutinee_type_id: ArenaTypeId,
        interner: &Interner,
    ) -> Option<ArenaTypeId> {
        let type_def_id = self
            .resolver(interner)
            .resolve_type(name, &self.entity_registry())?;
        let type_kind = self.entity_registry().type_kind(type_def_id);
        match type_kind {
            TypeDefKind::Class => {
                let type_args =
                    self.infer_pattern_type_args_for_def(type_def_id, scrutinee_type_id);
                Some(self.type_arena_mut().class(type_def_id, type_args))
            }
            TypeDefKind::Struct | TypeDefKind::Sentinel => {
                let type_args =
                    self.infer_pattern_type_args_for_def(type_def_id, scrutinee_type_id);
                Some(self.type_arena_mut().struct_type(type_def_id, type_args))
            }
            _ => None,
        }
    }

    fn resolve_pattern_type_expr_id(
        &mut self,
        type_expr: &TypeExpr,
        scrutinee_type_id: ArenaTypeId,
        interner: &Interner,
    ) -> ArenaTypeId {
        if let TypeExpr::Named(name) = type_expr
            && let Some(pattern_type_id) =
                self.resolve_identifier_pattern_type_id(*name, scrutinee_type_id, interner)
        {
            return pattern_type_id;
        }
        self.resolve_type_id(type_expr, interner)
    }

    fn instantiate_nominal_pattern_fields(
        &mut self,
        type_def_id: TypeDefId,
        type_args: &[ArenaTypeId],
    ) -> Vec<StructFieldId> {
        let Some(generic_info) = self.entity_registry().type_generic_info(type_def_id) else {
            return vec![];
        };

        let substitutions: FxHashMap<_, _> = generic_info
            .type_params
            .iter()
            .zip(type_args.iter())
            .map(|(param, &arg)| (param.name_id, arg))
            .collect();

        generic_info
            .field_names
            .iter()
            .zip(generic_info.field_types.iter())
            .enumerate()
            .map(|(slot, (&name_id, &field_type_id))| {
                let ty = if substitutions.is_empty() {
                    field_type_id
                } else {
                    self.type_arena_mut()
                        .substitute(field_type_id, &substitutions)
                };
                StructFieldId { name_id, ty, slot }
            })
            .collect()
    }

    fn record_pattern_fields_for_type_id(
        &mut self,
        pattern_type_id: ArenaTypeId,
    ) -> Option<Vec<StructFieldId>> {
        let class_info = {
            let arena = self.type_arena();
            arena
                .unwrap_class(pattern_type_id)
                .map(|(type_def_id, type_args)| (type_def_id, type_args.clone()))
        };
        if let Some((type_def_id, type_args)) = class_info {
            return Some(self.instantiate_nominal_pattern_fields(type_def_id, &type_args));
        }

        let struct_info = {
            let arena = self.type_arena();
            arena
                .unwrap_struct(pattern_type_id)
                .map(|(type_def_id, type_args)| (type_def_id, type_args.clone()))
        };
        if let Some((type_def_id, type_args)) = struct_info {
            return Some(self.instantiate_nominal_pattern_fields(type_def_id, &type_args));
        }

        if let Some(type_def_id) = self.type_arena().unwrap_error(pattern_type_id) {
            let field_ids = self.entity_registry().type_fields(type_def_id);
            let fields_ref: Vec<StructFieldId> = field_ids
                .into_iter()
                .map(|field_id| {
                    let (name_id, ty) = self.entity_registry().field_name_and_type(field_id);
                    let slot = self.entity_registry().get_field(field_id).slot;
                    StructFieldId { name_id, ty, slot }
                })
                .collect();
            return Some(fields_ref);
        }

        None
    }

    /// Check type pattern compatibility (TypeId version)
    fn check_type_pattern_compatibility_id(
        &mut self,
        pattern_type_id: ArenaTypeId,
        scrutinee_type_id: ArenaTypeId,
        span: Span,
        interner: &Interner,
    ) {
        // Check if pattern type is compatible with scrutinee
        if !self.types_compatible_id(pattern_type_id, scrutinee_type_id, interner)
            && !self.types_compatible_id(scrutinee_type_id, pattern_type_id, interner)
        {
            let expected = self.type_display_id(scrutinee_type_id);
            let found = self.type_display_id(pattern_type_id);
            self.add_error(
                SemanticError::PatternTypeMismatch {
                    expected,
                    found,
                    span: span.into(),
                },
                span,
            );
        }
    }

    /// Compute IsCheckResult for a type pattern.
    /// Determines whether the check can be resolved at compile time or needs a runtime tag check.
    fn compute_type_pattern_check_result(
        &self,
        pattern_type_id: ArenaTypeId,
        scrutinee_type_id: ArenaTypeId,
    ) -> IsCheckResult {
        let union_variants = self.type_arena().unwrap_union(scrutinee_type_id).cloned();
        if let Some(variants) = union_variants {
            // Union type: find which variant the pattern type matches
            if let Some(index) = variants.iter().position(|&v| v == pattern_type_id) {
                IsCheckResult::CheckTag(index as u32)
            } else {
                // Pattern type is not a variant - always false
                IsCheckResult::AlwaysFalse
            }
        } else {
            // Non-union type: check direct type equality
            if scrutinee_type_id == pattern_type_id {
                IsCheckResult::AlwaysTrue
            } else {
                IsCheckResult::AlwaysFalse
            }
        }
    }

    /// Check record pattern fields against type fields (TypeId version)
    fn check_record_pattern_fields_id(
        &mut self,
        pattern_fields: &[RecordFieldPattern],
        type_fields: &[StructFieldId],
        span: Span,
        interner: &Interner,
    ) {
        for field_pat in pattern_fields {
            let field_name_str = interner.resolve(field_pat.field_name);
            // Find field in type
            let field_type_id = type_fields.iter().find_map(|f| {
                self.name_table()
                    .last_segment_str(f.name_id)
                    .filter(|s| *s == field_name_str)
                    .map(|_| f.ty)
            });
            if let Some(field_type_id) = field_type_id {
                // Bind the variable (binding may be different from field_name if renamed)
                self.scope.define(
                    field_pat.binding,
                    Variable {
                        ty: field_type_id,
                        mutable: false,
                        declaration_span: field_pat.span,
                    },
                );
            } else {
                // Unknown field in pattern
                self.add_error(
                    SemanticError::UnknownField {
                        ty: "class".to_string(),
                        field: field_name_str.to_string(),
                        span: span.into(),
                    },
                    span,
                );
            }
        }
    }

    /// Check anonymous record pattern against scrutinee's fields (TypeId version)
    fn check_anonymous_record_pattern_id(
        &mut self,
        pattern_fields: &[RecordFieldPattern],
        scrutinee_type_id: ArenaTypeId,
        span: Span,
        interner: &Interner,
    ) {
        // Try to get fields from the scrutinee type (class or struct)
        let type_def_info = {
            use crate::type_arena::NominalKind;
            let arena = self.type_arena();
            arena
                .unwrap_nominal(scrutinee_type_id)
                .filter(|(_, _, kind)| matches!(kind, NominalKind::Class | NominalKind::Struct))
                .map(|(id, _, _)| id)
        };

        if let Some(type_def_id) = type_def_info {
            // Clone generic_info to avoid holding borrow
            let generic_info = self.entity_registry().type_generic_info(type_def_id);
            // Get fields from generic_info
            let type_fields: Vec<StructFieldId> = generic_info
                .as_ref()
                .map(|gi| {
                    gi.field_names
                        .iter()
                        .zip(gi.field_types.iter())
                        .enumerate()
                        .map(|(i, (&name_id, &ty))| StructFieldId {
                            name_id,
                            ty,
                            slot: i,
                        })
                        .collect()
                })
                .unwrap_or_default();

            self.check_record_pattern_fields_id(pattern_fields, &type_fields, span, interner);
        } else {
            // Not a class/struct type
            let found = self.type_display_id(scrutinee_type_id);
            self.add_error(
                SemanticError::PatternTypeMismatch {
                    expected: "class or struct".to_string(),
                    found,
                    span: span.into(),
                },
                span,
            );
        }
    }

    /// Check an inner pattern within an `error` pattern.
    ///
    /// For identifier patterns (e.g., `error NotFound`), resolves the error type
    /// from the fallible's error union rather than from scope. This allows matching
    /// error types from imported modules without requiring them to be in scope.
    ///
    /// For record patterns (e.g., `error NotFound { path: p }`), similarly resolves
    /// the type name from the error union.
    fn check_error_inner_pattern(
        &mut self,
        pattern: &Pattern,
        error_type_id: ArenaTypeId,
        interner: &Interner,
    ) -> Option<ArenaTypeId> {
        let span = pattern.span;

        match &pattern.kind {
            PatternKind::Identifier { name } => {
                // Try to resolve as error type from the error union first
                if let Some(type_def_id) =
                    self.resolve_error_type_from_union(*name, error_type_id, interner)
                {
                    let pattern_type_id = self.type_arena_mut().error_type(type_def_id);
                    self.check_type_pattern_compatibility_id(
                        pattern_type_id,
                        error_type_id,
                        span,
                        interner,
                    );
                    let is_check_result =
                        self.compute_type_pattern_check_result(pattern_type_id, error_type_id);
                    self.record_is_check_result(pattern.id, is_check_result);
                    return Some(pattern_type_id);
                }
                // Fall through to regular pattern checking (e.g., variable binding)
                self.check_pattern_id(pattern, error_type_id, interner)
            }
            PatternKind::Record {
                type_name: Some(type_expr),
                ..
            } => {
                // Try to resolve the record type name from the error union
                if let Some(name) = Self::terminal_type_symbol(type_expr)
                    && let Some(type_def_id) =
                        self.resolve_error_type_from_union(name, error_type_id, interner)
                {
                    // Resolve using the found TypeDefId
                    let kind = self.entity_registry().type_kind(type_def_id);
                    if kind == TypeDefKind::ErrorType {
                        let field_ids = self.entity_registry().type_fields(type_def_id);
                        let fields_ref: Vec<StructFieldId> = field_ids
                            .into_iter()
                            .map(|field_id| {
                                let (name_id, ty) =
                                    self.entity_registry().field_name_and_type(field_id);
                                let slot = self.entity_registry().get_field(field_id).slot;
                                StructFieldId { name_id, ty, slot }
                            })
                            .collect();
                        let pattern_type_id = self.type_arena_mut().error_type(type_def_id);

                        // Check pattern fields
                        if let PatternKind::Record { fields, .. } = &pattern.kind {
                            self.check_record_pattern_fields_id(
                                fields,
                                &fields_ref,
                                span,
                                interner,
                            );
                        }

                        self.check_type_pattern_compatibility_id(
                            pattern_type_id,
                            error_type_id,
                            span,
                            interner,
                        );
                        let is_check_result =
                            self.compute_type_pattern_check_result(pattern_type_id, error_type_id);
                        self.record_is_check_result(pattern.id, is_check_result);
                        return Some(pattern_type_id);
                    }
                }
                // Fall through to regular pattern checking
                self.check_pattern_id(pattern, error_type_id, interner)
            }
            _ => {
                // For other patterns (wildcard, binding, etc.), use regular checking
                self.check_pattern_id(pattern, error_type_id, interner)
            }
        }
    }

    /// Resolve an error type name from a fallible's error union type.
    ///
    /// When matching `error NotFound { ... }`, the `NotFound` needs to be resolved
    /// from the error union's variants, not from the consumer's scope. This is necessary
    /// because error types defined in imported modules aren't in the consumer's scope.
    fn resolve_error_type_from_union(
        &self,
        name: Symbol,
        error_type_id: ArenaTypeId,
        interner: &Interner,
    ) -> Option<TypeDefId> {
        let name_str = interner.resolve(name);
        let name_table = self.name_table();
        let entity_reg = self.entity_registry();

        // Helper to check if a TypeDefId's last name segment matches the target name
        let check_variant = |type_def_id: TypeDefId| -> bool {
            name_table
                .last_segment_str(entity_reg.name_id(type_def_id))
                .is_some_and(|seg| seg == name_str)
        };

        // Check if error_type_id is a single error type
        if let Some(type_def_id) = self.type_arena().unwrap_error(error_type_id)
            && check_variant(type_def_id)
        {
            return Some(type_def_id);
        }

        // Check union variants
        if let Some(variants) = self.type_arena().unwrap_union(error_type_id) {
            for &variant in variants {
                if let Some(type_def_id) = self.type_arena().unwrap_error(variant)
                    && check_variant(type_def_id)
                {
                    return Some(type_def_id);
                }
            }
        }

        None
    }

    /// Check if a match expression is exhaustive (TypeId version)
    pub(crate) fn check_match_exhaustiveness_id(
        &mut self,
        arms: &[MatchArm],
        scrutinee_type_id: ArenaTypeId,
        _span: Span,
        interner: &Interner,
    ) -> bool {
        // Check for catch-all patterns (wildcard or identifier binding)
        let has_catch_all = arms.iter().any(|arm| {
            match &arm.pattern.kind {
                PatternKind::Wildcard => true,
                PatternKind::Identifier { name } => {
                    // Only a catch-all if NOT a known type name
                    let is_type = self
                        .resolver(interner)
                        .resolve_type(*name, &self.entity_registry())
                        .is_some();
                    !is_type
                }
                _ => false,
            }
        });

        if has_catch_all {
            return true;
        }

        // For union types, check if all variants are covered by type patterns
        let union_variants: Option<Vec<ArenaTypeId>> = {
            let arena = self.type_arena();
            arena.unwrap_union(scrutinee_type_id).map(|v| v.to_vec())
        };

        if let Some(variants) = union_variants {
            let mut covered: Vec<bool> = vec![false; variants.len()];

            for arm in arms {
                let pattern_type_id =
                    self.get_pattern_type_id(&arm.pattern, scrutinee_type_id, interner);

                if let Some(pt_id) = pattern_type_id {
                    for (i, &variant_id) in variants.iter().enumerate() {
                        if variant_id == pt_id {
                            covered[i] = true;
                        }
                    }
                }
            }

            return covered.iter().all(|&c| c);
        }

        // For non-union types, check if any pattern covers the exact type
        for arm in arms {
            let pattern_type_id =
                self.get_pattern_type_id(&arm.pattern, scrutinee_type_id, interner);
            if let Some(pt_id) = pattern_type_id
                && pt_id == scrutinee_type_id
            {
                return true;
            }
        }

        false
    }

    /// Extract the TypeId that a pattern matches against, if it's a type pattern
    fn get_pattern_type_id(
        &mut self,
        pattern: &Pattern,
        scrutinee_type_id: ArenaTypeId,
        interner: &Interner,
    ) -> Option<ArenaTypeId> {
        match &pattern.kind {
            PatternKind::Type { type_expr } => {
                Some(self.resolve_pattern_type_expr_id(type_expr, scrutinee_type_id, interner))
            }
            PatternKind::Identifier { name } => {
                // Well-known sentinel values resolve directly to their reserved TypeIds
                let name_str = interner.resolve(*name);
                if name_str == "nil" {
                    return Some(ArenaTypeId::NIL);
                }
                if name_str == "Done" {
                    return Some(ArenaTypeId::DONE);
                }

                self.resolve_identifier_pattern_type_id(*name, scrutinee_type_id, interner)
            }
            PatternKind::Record {
                type_name: Some(type_expr),
                ..
            } => Some(self.resolve_pattern_type_expr_id(type_expr, scrutinee_type_id, interner)),
            _ => None,
        }
    }
}
