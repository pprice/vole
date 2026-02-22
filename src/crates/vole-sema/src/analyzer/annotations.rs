//! Annotation validation for declarations.
//!
//! Annotations are metadata attached to declarations using the `@Name` syntax.
//! Only types marked with `@annotation` can be used as annotations.
//! The `annotation` type itself is bootstrapped: it is special-cased to allow
//! the self-referential `@annotation struct annotation {}`.

use super::Analyzer;
use crate::entity_defs::ValidatedAnnotation;
use crate::errors::SemanticError;
use vole_frontend::Interner;
use vole_frontend::ast::{
    Annotation, CallArg, Decl, FieldDef, FuncDecl, Program, TestsDecl, TypeParam,
};
use vole_identity::TypeDefId;

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
        // Visits annotations on declarations and their nested items (fields, params, etc.).
        for decl in &program.declarations {
            self.validate_decl_annotations(decl, interner);
        }
    }

    /// Validate annotations on a declaration and all its nested annotatable items.
    fn validate_decl_annotations(&mut self, decl: &Decl, interner: &Interner) {
        match decl {
            Decl::Struct(s) => {
                self.validate_annotations(&s.annotations, interner);
                self.validate_and_store_field_annotations(s.name, &s.fields, interner);
                self.validate_method_annotations(&s.methods, interner);
            }
            Decl::Class(c) => {
                self.validate_annotations(&c.annotations, interner);
                self.validate_and_store_field_annotations(c.name, &c.fields, interner);
                self.validate_method_annotations(&c.methods, interner);
            }
            Decl::Interface(i) => {
                self.validate_annotations(&i.annotations, interner);
                self.validate_and_store_field_annotations(i.name, &i.fields, interner);
            }
            Decl::Function(f) => {
                self.validate_annotations(&f.annotations, interner);
                self.validate_param_annotations(f, interner);
            }
            Decl::Implement(i) => {
                self.validate_annotations(&i.annotations, interner);
                self.validate_method_annotations(&i.methods, interner);
            }
            Decl::Tests(t) => {
                self.validate_tests_annotations(t, interner);
            }
            _ => {}
        }
    }

    /// Validate annotations on a tests block and its nested test cases and declarations.
    fn validate_tests_annotations(&mut self, tests: &TestsDecl, interner: &Interner) {
        self.validate_annotations(&tests.annotations, interner);
        for test in &tests.tests {
            self.validate_annotations(&test.annotations, interner);
        }
        for decl in &tests.decls {
            self.validate_decl_annotations(decl, interner);
        }
    }

    /// Validate and store annotations on field definitions.
    ///
    /// For each field, validates each annotation (type, args) and stores the
    /// validated result in the entity registry's FieldDef so codegen can read it.
    fn validate_and_store_field_annotations(
        &mut self,
        type_name: vole_frontend::Symbol,
        fields: &[FieldDef],
        interner: &Interner,
    ) {
        // Resolve the owning type to find FieldIds in the entity registry
        let type_name_str = interner.resolve(type_name);
        let type_def_id = self
            .resolver(interner)
            .resolve_type_str_or_interface(type_name_str, &self.entity_registry());

        for field in fields {
            let mut validated = Vec::new();
            for ann in &field.annotations {
                if let Some(v) = self.validate_annotation_with_args(ann, interner) {
                    validated.push(v);
                }
            }

            // Store validated annotations on the entity FieldDef if we have any
            if !validated.is_empty()
                && let Some(td_id) = type_def_id
            {
                self.store_field_annotations(td_id, field, &validated, interner);
            }
        }
    }

    /// Store validated annotations on the entity registry's FieldDef.
    fn store_field_annotations(
        &mut self,
        type_def_id: TypeDefId,
        ast_field: &FieldDef,
        validated: &[ValidatedAnnotation],
        interner: &Interner,
    ) {
        let field_name_str = interner.resolve(ast_field.name);
        let names = self.name_table();
        let entities = self.entity_registry();
        let field_id = entities.fields_on_type(type_def_id).find(|&fid| {
            let fd = entities.get_field(fid);
            names.last_segment_str(fd.name_id).as_deref() == Some(field_name_str)
        });
        drop(names);
        drop(entities);

        if let Some(field_id) = field_id {
            self.entity_registry_mut()
                .get_field_mut(field_id)
                .annotations = validated.to_vec();
        }
    }

    /// Validate annotations on methods and their parameters.
    fn validate_method_annotations(&mut self, methods: &[FuncDecl], interner: &Interner) {
        for method in methods {
            self.validate_annotations(&method.annotations, interner);
            self.validate_param_annotations(method, interner);
        }
    }

    /// Validate annotations on function parameters.
    fn validate_param_annotations(&mut self, func: &FuncDecl, interner: &Interner) {
        for param in &func.params {
            self.validate_annotations(&param.annotations, interner);
        }
    }

    /// Validate a slice of annotations (without storing results).
    fn validate_annotations(&mut self, annotations: &[Annotation], interner: &Interner) {
        for ann in annotations {
            self.validate_annotation_with_args(ann, interner);
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
    /// an annotation type (decorated with @annotation). Also validates args.
    ///
    /// Returns `Some(ValidatedAnnotation)` if the annotation is valid,
    /// `None` if there were errors.
    fn validate_annotation_with_args(
        &mut self,
        ann: &Annotation,
        interner: &Interner,
    ) -> Option<ValidatedAnnotation> {
        let ann_name = interner.resolve(ann.name);

        // Bootstrap: @annotation on annotation itself is always valid
        if ann_name == "annotation" {
            let type_def_id = self
                .resolver(interner)
                .resolve_type_str_or_interface(ann_name, &self.entity_registry());

            if let Some(type_def_id) = type_def_id {
                return Some(ValidatedAnnotation {
                    type_def_id,
                    args: Vec::new(),
                });
            }
            // annotation type not found — fine during prelude loading
            return None;
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
            return None;
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
            return None;
        }

        // Validate args against the annotation struct's fields
        self.validate_annotation_args(ann, type_def_id, interner)
    }

    /// Validate annotation arguments against the annotation struct's fields.
    ///
    /// Returns `Some(ValidatedAnnotation)` with resolved field-to-node mappings
    /// if validation passes, `None` if errors were found.
    fn validate_annotation_args(
        &mut self,
        ann: &Annotation,
        type_def_id: TypeDefId,
        interner: &Interner,
    ) -> Option<ValidatedAnnotation> {
        let ann_name = interner.resolve(ann.name);

        // Collect the annotation struct's fields (name_id, in order)
        let field_ids: Vec<_> = self.entity_registry().fields_on_type(type_def_id).collect();

        let expected_count = field_ids.len();
        let found_count = ann.args.len();

        // Zero-field annotation: no args expected
        if expected_count == 0 {
            if found_count > 0 {
                self.add_error(
                    SemanticError::AnnotationWrongArgCount {
                        name: ann_name.to_string(),
                        expected: 0,
                        found: found_count,
                        span: ann.span.into(),
                    },
                    ann.span,
                );
                return None;
            }
            return Some(ValidatedAnnotation {
                type_def_id,
                args: Vec::new(),
            });
        }

        // Build field name lookup for the annotation struct
        let names = self.name_table();
        let entities = self.entity_registry();
        let field_names: Vec<(vole_identity::NameId, String)> = field_ids
            .iter()
            .map(|&fid| {
                let fd = entities.get_field(fid);
                let name = names
                    .last_segment_str(fd.name_id)
                    .unwrap_or_else(|| "?".to_string());
                (fd.name_id, name)
            })
            .collect();
        drop(names);
        drop(entities);

        // Check arg count matches field count
        if found_count != expected_count {
            self.add_error(
                SemanticError::AnnotationWrongArgCount {
                    name: ann_name.to_string(),
                    expected: expected_count,
                    found: found_count,
                    span: ann.span.into(),
                },
                ann.span,
            );
            return None;
        }

        // Match args to fields
        self.match_annotation_args_to_fields(ann, type_def_id, &field_names, interner)
    }

    /// Match annotation arguments (positional or named) to struct fields.
    fn match_annotation_args_to_fields(
        &mut self,
        ann: &Annotation,
        type_def_id: TypeDefId,
        field_names: &[(vole_identity::NameId, String)],
        interner: &Interner,
    ) -> Option<ValidatedAnnotation> {
        let ann_name = interner.resolve(ann.name);
        let mut result_args = Vec::with_capacity(field_names.len());
        let mut seen_fields = vec![false; field_names.len()];
        let mut has_error = false;

        for (i, arg) in ann.args.iter().enumerate() {
            match arg {
                CallArg::Positional(expr) => {
                    // Positional arg maps to field by index
                    let (name_id, _) = &field_names[i];
                    result_args.push((*name_id, Box::new(expr.clone())));
                    seen_fields[i] = true;
                }
                CallArg::Named { name, value, span } => {
                    let arg_name = interner.resolve(*name);
                    // Find field by name
                    if let Some(idx) = field_names.iter().position(|(_, fname)| fname == arg_name) {
                        if seen_fields[idx] {
                            self.add_error(
                                SemanticError::AnnotationDuplicateArg {
                                    annotation: ann_name.to_string(),
                                    field: arg_name.to_string(),
                                    span: (*span).into(),
                                },
                                *span,
                            );
                            has_error = true;
                        } else {
                            let (name_id, _) = &field_names[idx];
                            result_args.push((*name_id, Box::new(value.clone())));
                            seen_fields[idx] = true;
                        }
                    } else {
                        self.add_error(
                            SemanticError::AnnotationUnknownArg {
                                annotation: ann_name.to_string(),
                                arg_name: arg_name.to_string(),
                                span: (*span).into(),
                            },
                            *span,
                        );
                        has_error = true;
                    }
                }
            }
        }

        if has_error {
            return None;
        }

        Some(ValidatedAnnotation {
            type_def_id,
            args: result_args,
        })
    }
}
