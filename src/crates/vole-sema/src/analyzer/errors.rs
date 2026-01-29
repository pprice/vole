//! Error and warning reporting helpers for the analyzer.

use super::{TypeError, TypeWarning};
use crate::errors::{SemanticError, SemanticWarning};
use crate::type_arena::{InternedStructural, TypeId as ArenaTypeId};
use crate::type_display::{display_structural_constraint, display_type_id};
use vole_frontend::Span;
use vole_frontend::ast::TypeExpr;

use super::Analyzer;

impl Analyzer {
    /// Helper to add a type error
    pub(super) fn add_error(&mut self, error: SemanticError, span: Span) {
        self.errors.push(TypeError::new(error, span));
    }

    /// Helper to add a type warning
    pub(super) fn add_warning(&mut self, warning: SemanticWarning, span: Span) {
        self.warnings.push(TypeWarning::new(warning, span));
    }

    /// Display a type from TypeId.
    pub(super) fn type_display_id(&self, id: ArenaTypeId) -> String {
        display_type_id(
            id,
            &self.type_arena(),
            &self.name_table(),
            &self.entity_registry(),
        )
    }

    /// Display a structural constraint for error messages.
    pub(super) fn structural_display(&self, structural: &InternedStructural) -> String {
        display_structural_constraint(
            structural,
            &self.type_arena(),
            &self.name_table(),
            &self.entity_registry(),
        )
    }

    pub(super) fn type_display_pair_id(&self, left: ArenaTypeId, right: ArenaTypeId) -> String {
        format!(
            "{} and {}",
            self.type_display_id(left),
            self.type_display_id(right)
        )
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

    /// Helper to add a wrong argument count error with a range (min to max)
    pub(crate) fn add_wrong_arg_count_range(
        &mut self,
        min: usize,
        max: usize,
        found: usize,
        span: Span,
    ) {
        if min == max {
            // If they're equal, use the simpler error
            self.add_wrong_arg_count(min, found, span);
        } else {
            self.add_error(
                SemanticError::WrongArgumentCountRange {
                    min,
                    max,
                    found,
                    span: span.into(),
                },
                span,
            );
        }
    }

    /// Check if a resolved type is `never` and emit an error if so.
    /// This should be called for types in non-return-type positions
    /// (e.g., variable declarations, parameters, fields).
    pub(crate) fn check_never_not_allowed(&mut self, type_id: ArenaTypeId, span: Span) {
        if type_id.is_never() {
            self.add_error(SemanticError::NeverNotAllowed { span: span.into() }, span);
        }
    }

    /// Check if a type expression contains a union with `never` or `unknown` and emit W3004.
    /// This walks the type expression tree to catch nested unions like `[i32 | never]`.
    pub(crate) fn check_union_simplification(&mut self, ty: &TypeExpr, span: Span) {
        match ty {
            TypeExpr::Union(variants) => {
                for variant in variants {
                    match variant {
                        TypeExpr::Never => {
                            self.add_warning(
                                SemanticWarning::UnionSimplification {
                                    ty: "never".to_string(),
                                    simplification_hint: "`never` is the bottom type and is automatically removed from unions; `T | never` simplifies to `T`".to_string(),
                                    span: span.into(),
                                    label: "`never` in union will be removed".to_string(),
                                },
                                span,
                            );
                        }
                        TypeExpr::Unknown => {
                            self.add_warning(
                                SemanticWarning::UnionSimplification {
                                    ty: "unknown".to_string(),
                                    simplification_hint: "`unknown` is the top type and absorbs all other types; `T | unknown` simplifies to `unknown`".to_string(),
                                    span: span.into(),
                                    label: "`unknown` in union absorbs all other types".to_string(),
                                },
                                span,
                            );
                        }
                        _ => {}
                    }
                    // Recurse into variant to catch nested unions
                    self.check_union_simplification(variant, span);
                }
            }
            // Recurse into container types
            TypeExpr::Array(inner) | TypeExpr::Optional(inner) => {
                self.check_union_simplification(inner, span);
            }
            TypeExpr::FixedArray { element, .. } => {
                self.check_union_simplification(element, span);
            }
            TypeExpr::Tuple(elements) => {
                for elem in elements {
                    self.check_union_simplification(elem, span);
                }
            }
            TypeExpr::Function {
                params,
                return_type,
            } => {
                for param in params {
                    self.check_union_simplification(param, span);
                }
                self.check_union_simplification(return_type, span);
            }
            TypeExpr::Fallible {
                success_type,
                error_type,
            } => {
                self.check_union_simplification(success_type, span);
                self.check_union_simplification(error_type, span);
            }
            TypeExpr::Generic { args, .. } => {
                for arg in args {
                    self.check_union_simplification(arg, span);
                }
            }
            _ => {}
        }
    }
}
