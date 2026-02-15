// src/sema/analyzer/stmt/error_handling.rs
//
// Error handling statement analysis:
// - raise statement checking (type validation, field initializers)
// - try expression analysis (fallible unwrapping, error propagation)
// - Error type compatibility checking

use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;

impl Analyzer {
    /// Analyze a raise statement
    pub(super) fn analyze_raise_stmt(
        &mut self,
        stmt: &RaiseStmt,
        interner: &Interner,
    ) -> ArenaTypeId {
        // Check we're in a fallible function
        let Some(error_type) = self.env.current_function_error_type else {
            self.add_error(
                SemanticError::RaiseOutsideFallible {
                    span: stmt.span.into(),
                },
                stmt.span,
            );
            return self.ty_invalid_id();
        };

        // Look up the error type via resolver
        let type_id_opt = self
            .resolver(interner)
            .resolve_type(stmt.error_name, &self.entity_registry());

        let Some(type_id) = type_id_opt else {
            self.add_error(
                SemanticError::UndefinedError {
                    name: interner.resolve(stmt.error_name).to_string(),
                    span: stmt.span.into(),
                },
                stmt.span,
            );
            return self.ty_invalid_id();
        };

        let has_error_info = self
            .entity_registry()
            .get_type(type_id)
            .error_info
            .is_some();
        if !has_error_info {
            // Type exists but is not an error type
            self.add_error(
                SemanticError::UndefinedError {
                    name: interner.resolve(stmt.error_name).to_string(),
                    span: stmt.span.into(),
                },
                stmt.span,
            );
            return self.ty_invalid_id();
        }

        // Get the error type name for error messages
        let error_type_name = {
            let name_id = self.entity_registry().name_id(type_id);
            self.name_table()
                .last_segment_str(name_id)
                .unwrap_or_else(|| "error".to_string())
        };

        // Collect field IDs first to avoid borrow conflicts in the loop
        let field_ids = self.entity_registry().type_fields(type_id);
        let error_fields: Vec<(String, ArenaTypeId)> = field_ids
            .into_iter()
            .filter_map(|field_id| {
                let (name_id, ty) = self.entity_registry().field_name_and_type(field_id);
                let name = self.name_table().last_segment_str(name_id)?;
                Some((name, ty))
            })
            .collect();

        self.check_raise_field_initializers(stmt, &error_fields, &error_type_name, interner);

        self.check_raise_error_compatibility(stmt, error_type, type_id, interner);

        self.ty_void_id() // raise doesn't produce a value - it transfers control
    }

    /// Verify that raised error type is compatible with declared error type.
    fn check_raise_error_compatibility(
        &mut self,
        stmt: &RaiseStmt,
        error_type: ArenaTypeId,
        type_id: TypeDefId,
        interner: &Interner,
    ) {
        let stmt_error_name = interner.resolve(stmt.error_name);
        let is_compatible = {
            let arena = self.type_arena();
            if let Some(declared_type_def_id) = arena.unwrap_error(error_type) {
                // Single error type - must match exactly
                let name = self
                    .name_table()
                    .last_segment_str(self.entity_registry().name_id(declared_type_def_id));
                name.as_deref() == Some(stmt_error_name)
            } else if let Some(variants) = arena.unwrap_union(error_type) {
                // Union of error types - raised error must be one of the variants
                variants.iter().any(|&variant_id| {
                    if let Some(variant_type_def_id) = arena.unwrap_error(variant_id) {
                        let name = self
                            .name_table()
                            .last_segment_str(self.entity_registry().name_id(variant_type_def_id));
                        name.as_deref() == Some(stmt_error_name)
                    } else {
                        false
                    }
                })
            } else {
                false // Should not happen if we got past the fallible check
            }
        };

        if !is_compatible {
            // Extract types before calling type_display_id to avoid borrow conflict
            let raised_type_id = self.type_arena_mut().error_type(type_id);
            let declared_str = self.type_display_id(error_type);
            let raised_str = self.type_display_id(raised_type_id);

            self.add_error(
                SemanticError::IncompatibleRaiseError {
                    raised: raised_str,
                    declared: declared_str,
                    span: stmt.span.into(),
                },
                stmt.span,
            );
        }
    }

    /// Validate raise statement field initializers: check for missing fields,
    /// unknown fields, and type compatibility.
    fn check_raise_field_initializers(
        &mut self,
        stmt: &RaiseStmt,
        error_fields: &[(String, ArenaTypeId)],
        error_type_name: &str,
        interner: &Interner,
    ) {
        // Check for missing fields (fields in error type but not provided in raise)
        let provided_fields: HashSet<String> = stmt
            .fields
            .iter()
            .map(|f| interner.resolve(f.name).to_string())
            .collect();
        for (field_name, _) in error_fields {
            if !provided_fields.contains(field_name) {
                self.add_error(
                    SemanticError::MissingField {
                        ty: error_type_name.to_string(),
                        field: field_name.clone(),
                        span: stmt.span.into(),
                    },
                    stmt.span,
                );
            }
        }

        // Type check field initializers and check for unknown fields
        for field_init in &stmt.fields {
            let value_type_id = match self.check_expr(&field_init.value, interner) {
                Ok(ty_id) => ty_id,
                Err(_) => ArenaTypeId::INVALID,
            };
            let field_init_name = interner.resolve(field_init.name);
            if let Some((_, field_ty_id)) = error_fields
                .iter()
                .find(|(name, _)| name == field_init_name)
            {
                // Known field - check type compatibility using TypeId
                if !self.types_compatible_id(value_type_id, *field_ty_id, interner) {
                    self.add_type_mismatch_id(*field_ty_id, value_type_id, field_init.span);
                }
            } else {
                // Unknown field
                self.add_error(
                    SemanticError::UnknownField {
                        ty: error_type_name.to_string(),
                        field: interner.resolve(field_init.name).to_string(),
                        span: field_init.span.into(),
                    },
                    field_init.span,
                );
            }
        }
    }

    /// Analyze a try expression (propagation)
    ///
    /// try unwraps a fallible type:
    /// - On success: returns the success value
    /// - On error: propagates the error to the caller (early return)
    pub(crate) fn analyze_try(
        &mut self,
        inner_expr: &Expr,
        _interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // Check the inner expression - must be fallible
        let inner_type_id = self.check_expr(inner_expr, _interner)?;

        let fallible_info = self.type_arena().unwrap_fallible(inner_type_id);
        let Some((success_type_id, error_type_id)) = fallible_info else {
            let found = self.type_display_id(inner_type_id);
            self.add_error(
                SemanticError::TryOnNonFallible {
                    found,
                    span: inner_expr.span.into(),
                },
                inner_expr.span,
            );
            return Ok(ArenaTypeId::INVALID);
        };

        // Check that we're in a fallible function context
        let Some(current_error_id) = self.env.current_function_error_type else {
            self.add_error(
                SemanticError::TryOutsideFallible {
                    span: inner_expr.span.into(),
                },
                inner_expr.span,
            );
            return Ok(success_type_id);
        };

        // Check that the error type is compatible with the function's error type (TypeId version)
        if !self.error_type_compatible_id(error_type_id, current_error_id) {
            let try_error = self.type_display_id(error_type_id);
            let func_error = self.type_display_id(current_error_id);
            self.add_error(
                SemanticError::IncompatibleTryError {
                    try_error,
                    func_error,
                    span: inner_expr.span.into(),
                },
                inner_expr.span,
            );
        }

        // try unwraps - returns the success type
        Ok(success_type_id)
    }

    /// Check if error type is compatible with function's declared error type (TypeId version)
    fn error_type_compatible_id(
        &self,
        error_type_id: ArenaTypeId,
        func_error_id: ArenaTypeId,
    ) -> bool {
        // Same type (O(1) via TypeId equality)
        if error_type_id == func_error_id {
            return true;
        }

        // Check if func_error is a union and error_type is a member
        let arena = self.type_arena();
        if let Some(func_variants) = arena.unwrap_union(func_error_id) {
            if func_variants.contains(&error_type_id) {
                return true;
            }
            // Also check if error_type is a union whose members are all in func_error
            if let Some(error_variants) = arena.unwrap_union(error_type_id) {
                return error_variants.iter().all(|ev| func_variants.contains(ev));
            }
        }

        false
    }
}
