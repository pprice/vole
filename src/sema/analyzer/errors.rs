//! Error and warning reporting helpers for the analyzer.

use super::{TypeError, TypeWarning};
use crate::errors::{SemanticError, SemanticWarning};
use crate::frontend::Span;
use crate::sema::type_arena::TypeId as ArenaTypeId;
use crate::sema::types::StructuralType;
use crate::sema::{LegacyType, TypeKey};

use super::Analyzer;

impl Analyzer {
    /// Helper to add a type error
    pub(super) fn add_error(&mut self, error: SemanticError, span: Span) {
        self.errors.push(TypeError::new(error, span));
    }

    /// Helper to add a type warning
    #[allow(dead_code)] // Infrastructure for future warnings
    pub(super) fn add_warning(&mut self, warning: SemanticWarning, span: Span) {
        self.warnings.push(TypeWarning::new(warning, span));
    }

    pub(super) fn type_key_for(&mut self, ty: &LegacyType) -> TypeKey {
        self.entity_registry.type_table.key_for_type(ty)
    }

    #[allow(dead_code)]
    pub(super) fn type_key_for_id(&mut self, id: ArenaTypeId) -> TypeKey {
        self.entity_registry
            .type_table
            .key_for_type_id(id, &self.type_arena.borrow())
    }

    pub(super) fn type_display(&self, ty: &LegacyType) -> String {
        self.entity_registry
            .type_table
            .display_type(ty, &self.name_table, &self.entity_registry)
    }

    /// Display a type from TypeId (directly from SemaType, no LegacyType materialization)
    pub(super) fn type_display_id(&self, id: ArenaTypeId) -> String {
        self.entity_registry
            .type_table
            .display_type_id_direct(id, &self.type_arena.borrow(), &self.name_table, &self.entity_registry)
    }

    pub(super) fn type_display_pair_id(&self, left: ArenaTypeId, right: ArenaTypeId) -> String {
        format!(
            "{} and {}",
            self.type_display_id(left),
            self.type_display_id(right)
        )
    }

    /// Format a structural type for warning messages
    #[allow(dead_code)] // Infrastructure for future warnings
    pub(super) fn format_structural_type(&mut self, structural: &StructuralType) -> String {
        let mut parts = Vec::new();

        for field in &structural.fields {
            let name = self
                .name_table
                .last_segment_str(field.name)
                .unwrap_or_else(|| "<unknown>".to_string());
            let ty = self.type_display(&field.ty);
            parts.push(format!("{}: {}", name, ty));
        }

        for method in &structural.methods {
            let name = self
                .name_table
                .last_segment_str(method.name)
                .unwrap_or_else(|| "<unknown>".to_string());
            let params: Vec<String> = method.params.iter().map(|p| self.type_display(p)).collect();
            let ret = self.type_display(&method.return_type);
            parts.push(format!("func {}({}) -> {}", name, params.join(", "), ret));
        }

        parts.join(", ")
    }

    /// Helper to add a type mismatch error (string version)
    #[allow(dead_code)]
    pub(super) fn type_mismatch(&mut self, expected: &str, found: &str, span: Span) {
        self.add_error(
            SemanticError::TypeMismatch {
                expected: expected.to_string(),
                found: found.to_string(),
                span: span.into(),
            },
            span,
        );
    }

    /// Helper to add a type mismatch error with automatic type display
    pub(crate) fn type_error(&mut self, expected: &str, found: &LegacyType, span: Span) {
        let found_str = self.type_display(found);
        self.add_error(
            SemanticError::TypeMismatch {
                expected: expected.to_string(),
                found: found_str,
                span: span.into(),
            },
            span,
        );
    }

    /// Helper to add a type mismatch error with TypeId
    pub(crate) fn type_error_id(&mut self, expected: &str, found: ArenaTypeId, span: Span) {
        let found_str = self.type_display_id(found);
        self.add_error(
            SemanticError::TypeMismatch {
                expected: expected.to_string(),
                found: found_str,
                span: span.into(),
            },
            span,
        );
    }

    /// Helper to add a type mismatch error for binary operations with TypeId
    pub(crate) fn type_error_pair_id(
        &mut self,
        expected: &str,
        left: ArenaTypeId,
        right: ArenaTypeId,
        span: Span,
    ) {
        let found = self.type_display_pair_id(left, right);
        self.add_error(
            SemanticError::TypeMismatch {
                expected: expected.to_string(),
                found,
                span: span.into(),
            },
            span,
        );
    }

    /// Helper to add a type mismatch error with TypeId arguments
    pub(crate) fn add_type_mismatch_id(
        &mut self,
        expected: ArenaTypeId,
        found: ArenaTypeId,
        span: Span,
    ) {
        let expected_str = self.type_display_id(expected);
        let found_str = self.type_display_id(found);
        self.add_error(
            SemanticError::TypeMismatch {
                expected: expected_str,
                found: found_str,
                span: span.into(),
            },
            span,
        );
    }

    /// Helper to add a wrong argument count error
    pub(crate) fn add_wrong_arg_count(&mut self, expected: usize, found: usize, span: Span) {
        self.add_error(
            SemanticError::WrongArgumentCount {
                expected,
                found,
                span: span.into(),
            },
            span,
        );
    }
}
