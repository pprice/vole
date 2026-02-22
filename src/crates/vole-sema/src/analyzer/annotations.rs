//! Annotation validation for declarations.
//!
//! Annotations are metadata attached to declarations using the `@Name` syntax.
//! Only types marked with `@annotation` can be used as annotations.
//! The `annotation` type itself is bootstrapped: it is special-cased to allow
//! the self-referential `@annotation struct annotation {}`.

use super::Analyzer;
use crate::errors::SemanticError;
use vole_frontend::Interner;
use vole_frontend::ast::{Annotation, Decl, Program, TypeParam};

impl Analyzer {
    /// Pass 1.5: Process annotations on all declarations.
    ///
    /// First pass: mark types that have `@annotation` as annotation types.
    /// Second pass: validate that all annotations reference annotation types.
    pub(super) fn process_annotations(&mut self, program: &Program, interner: &Interner) {
        // First pass: register annotation types.
        // A type is an annotation type if it has @annotation in its annotations list.
        for decl in &program.declarations {
            let (name_sym, annotations, type_params) = match decl {
                Decl::Struct(s) => (s.name, &s.annotations, s.type_params.as_slice()),
                Decl::Class(c) => (c.name, &c.annotations, c.type_params.as_slice()),
                Decl::Interface(i) => (i.name, &i.annotations, i.type_params.as_slice()),
                Decl::Function(_) => continue, // functions can't be annotation types
                _ => continue,
            };

            if annotations.is_empty() {
                continue;
            }

            let annotation_ann = annotations.iter().find(|ann| {
                let ann_name = interner.resolve(ann.name);
                ann_name == "annotation"
            });

            if let Some(ann) = annotation_ann {
                self.validate_annotation_type_decl(name_sym, type_params, ann, interner);
                self.mark_as_annotation_type(name_sym, interner);
            }
        }

        // Second pass: validate all annotations reference annotation types.
        for decl in &program.declarations {
            let annotations = match decl {
                Decl::Struct(s) => &s.annotations,
                Decl::Class(c) => &c.annotations,
                Decl::Interface(i) => &i.annotations,
                Decl::Function(f) => &f.annotations,
                _ => continue,
            };

            for ann in annotations {
                self.validate_annotation(ann, interner);
            }
        }
    }

    /// Validate that a type declaration is suitable as an annotation type.
    /// Annotation types cannot be generic (no type parameters).
    fn validate_annotation_type_decl(
        &mut self,
        name_sym: vole_frontend::Symbol,
        type_params: &[TypeParam],
        ann: &Annotation,
        interner: &Interner,
    ) {
        if !type_params.is_empty() {
            let name = interner.resolve(name_sym).to_string();
            self.add_error(
                SemanticError::GenericAnnotationType {
                    name,
                    span: ann.span.into(),
                },
                ann.span,
            );
        }
    }

    /// Mark a type as an annotation type in the entity registry.
    fn mark_as_annotation_type(&mut self, name_sym: vole_frontend::Symbol, interner: &Interner) {
        let name_str = interner.resolve(name_sym);
        let type_def_id = self
            .resolver(interner)
            .resolve_type_str_or_interface(name_str, &self.entity_registry());

        if let Some(type_def_id) = type_def_id {
            self.entity_registry_mut()
                .get_type_mut(type_def_id)
                .is_annotation = true;
        }
    }

    /// Validate a single annotation: the referenced type must exist and be
    /// an annotation type (decorated with @annotation).
    fn validate_annotation(&mut self, ann: &Annotation, interner: &Interner) {
        let ann_name = interner.resolve(ann.name);

        // Bootstrap: @annotation on annotation itself is always valid
        if ann_name == "annotation" {
            // Check that the annotation type exists (it should, from the prelude)
            let type_def_id = self
                .resolver(interner)
                .resolve_type_str_or_interface(ann_name, &self.entity_registry());

            if type_def_id.is_none() {
                // annotation type not found — this is fine during prelude loading
                // because annotation.vole hasn't been loaded yet
                return;
            }
            return;
        }

        // Look up the annotation type
        let type_def_id = self
            .resolver(interner)
            .resolve_type_str_or_interface(ann_name, &self.entity_registry());

        let Some(type_def_id) = type_def_id else {
            self.add_error(
                SemanticError::UnknownAnnotation {
                    name: ann_name.to_string(),
                    span: ann.span.into(),
                },
                ann.span,
            );
            return;
        };

        // Check that the type is an annotation type
        let is_annotation = self.entity_registry().get_type(type_def_id).is_annotation;
        if !is_annotation {
            self.add_error(
                SemanticError::NotAnAnnotationType {
                    name: ann_name.to_string(),
                    span: ann.span.into(),
                },
                ann.span,
            );
        }
    }
}
