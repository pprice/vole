// src/sema/analyzer/stmt/destructuring.rs
//
// Destructuring logic for let/let-tuple statements:
// - Tuple destructuring
// - Record destructuring (class/struct fields)
// - Module destructuring (import bindings)
// - Type binding registration for imported types

use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;
use vole_frontend::PatternKind;

impl Analyzer {
    /// Recursively check a destructuring pattern against a type.
    pub(crate) fn check_destructure_pattern_id(
        &mut self,
        pattern: &Pattern,
        ty_id: ArenaTypeId,
        mutable: bool,
        init_span: Span,
        interner: &Interner,
    ) {
        match &pattern.kind {
            PatternKind::Identifier { name } => {
                self.env.scope.define(
                    *name,
                    Variable {
                        ty: ty_id,
                        mutable,
                        declaration_span: pattern.span,
                    },
                );
                self.add_lambda_local(*name);
            }
            PatternKind::Wildcard => {
                // Wildcard - nothing to bind
            }
            PatternKind::Tuple { elements } => {
                self.check_tuple_destructure(
                    pattern, elements, ty_id, mutable, init_span, interner,
                );
            }
            PatternKind::Record { fields, .. } => {
                let span = pattern.span;
                self.check_record_destructuring_id(
                    ty_id, fields, mutable, span, init_span, interner,
                );
            }
            _ => {
                // Other patterns not supported in let destructuring
            }
        }
    }

    /// Check tuple or fixed-array destructuring.
    fn check_tuple_destructure(
        &mut self,
        pattern: &Pattern,
        elements: &[Pattern],
        ty_id: ArenaTypeId,
        mutable: bool,
        init_span: Span,
        interner: &Interner,
    ) {
        let span = pattern.span;
        // Skip if type is INVALID (prior error)
        if ty_id.is_invalid() {
            return;
        }
        // Check for tuple or fixed array using arena (extract info first to avoid borrow conflicts)
        enum TupleOrArray {
            Tuple(crate::type_arena::TypeIdVec),
            FixedArray(ArenaTypeId, usize),
            Neither,
        }
        let type_info = {
            let arena = self.type_arena();
            if let Some(elem_ids) = arena.unwrap_tuple(ty_id) {
                TupleOrArray::Tuple(elem_ids.clone())
            } else if let Some((elem_id, size)) = arena.unwrap_fixed_array(ty_id) {
                TupleOrArray::FixedArray(elem_id, size)
            } else {
                TupleOrArray::Neither
            }
        };

        match type_info {
            TupleOrArray::Tuple(elem_type_ids) => {
                if elements.len() != elem_type_ids.len() {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: format!("tuple of {} elements", elem_type_ids.len()),
                            found: format!(
                                "destructuring pattern with {} elements",
                                elements.len()
                            ),
                            span: span.into(),
                        },
                        span,
                    );
                } else {
                    for (elem_pattern, &elem_type_id) in elements.iter().zip(elem_type_ids.iter()) {
                        self.check_destructure_pattern_id(
                            elem_pattern,
                            elem_type_id,
                            mutable,
                            init_span,
                            interner,
                        );
                    }
                }
            }
            TupleOrArray::FixedArray(elem_id, size) => {
                if elements.len() != size {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: format!("array of {} elements", size),
                            found: format!(
                                "destructuring pattern with {} elements",
                                elements.len()
                            ),
                            span: span.into(),
                        },
                        span,
                    );
                } else {
                    for elem_pattern in elements {
                        self.check_destructure_pattern_id(
                            elem_pattern,
                            elem_id,
                            mutable,
                            init_span,
                            interner,
                        );
                    }
                }
            }
            TupleOrArray::Neither => {
                self.type_error_id("tuple or fixed array", ty_id, init_span);
            }
        }
    }

    /// Check destructuring and bind variables (TypeId version)
    fn check_record_destructuring_id(
        &mut self,
        ty_id: ArenaTypeId,
        fields: &[RecordFieldPattern],
        mutable: bool,
        _pattern_span: Span,
        init_span: Span,
        interner: &Interner,
    ) {
        // First check if this is a module type - if so, use module destructuring
        // Clone to avoid borrow conflicts with the mutable method call
        let module_info = self.type_arena().unwrap_module(ty_id).cloned();
        if let Some(module_info) = module_info {
            self.check_module_destructuring(&module_info, fields, mutable, init_span, interner);
            return;
        }

        // Get type_def_id from the type using arena (class only)
        let type_def_id = {
            use crate::type_arena::NominalKind;
            let arena = self.type_arena();
            arena.unwrap_nominal(ty_id).and_then(|(id, _, kind)| {
                matches!(kind, NominalKind::Class | NominalKind::Struct).then_some(id)
            })
        };

        let Some(type_def_id) = type_def_id else {
            self.type_error_id("class, struct, or module", ty_id, init_span);
            return;
        };

        // Look up fields from entity_registry - clone to avoid borrow conflicts
        let generic_info_opt = self.entity_registry().type_generic_info(type_def_id);
        let Some(generic_info) = generic_info_opt else {
            self.type_error_id("class or struct with fields", ty_id, init_span);
            return;
        };

        // Check each destructured field
        for field_pattern in fields {
            let field_name_str = interner.resolve(field_pattern.field_name);

            // Find the field by name in generic_info
            let found = generic_info
                .field_names
                .iter()
                .enumerate()
                .find(|(_, name_id)| {
                    self.name_table().last_segment_str(**name_id).as_deref() == Some(field_name_str)
                });

            if let Some((slot, _)) = found {
                let field_type_id = generic_info.field_types[slot];
                // Bind the field to the binding name
                self.env.scope.define(
                    field_pattern.binding,
                    Variable {
                        ty: field_type_id,
                        mutable,
                        declaration_span: field_pattern.span,
                    },
                );
                self.add_lambda_local(field_pattern.binding);
            } else {
                // Get the type name for the error message
                let type_name = self.type_display_id(ty_id);
                self.add_error(
                    SemanticError::UnknownField {
                        ty: type_name,
                        field: field_name_str.to_string(),
                        span: field_pattern.span.into(),
                    },
                    field_pattern.span,
                );
            }
        }
    }

    /// Check module destructuring and bind variables.
    /// Handles `let { A, B as C } = import "..."`.
    fn check_module_destructuring(
        &mut self,
        module_info: &crate::type_arena::InternedModule,
        fields: &[RecordFieldPattern],
        mutable: bool,
        init_span: Span,
        interner: &Interner,
    ) {
        // Get the module path for error messages
        let module_path = self
            .name_table()
            .module_path(module_info.module_id)
            .to_string();

        // Check each destructured field against module exports
        for field_pattern in fields {
            self.check_module_field_binding(
                field_pattern,
                module_info,
                &module_path,
                mutable,
                interner,
            );
        }

        // Emit a warning if mutable is used with module destructuring
        if mutable {
            self.add_warning(
                SemanticWarning::MutableModuleBinding {
                    span: init_span.into(),
                },
                init_span,
            );
        }
    }

    /// Check a single field binding in module destructuring.
    fn check_module_field_binding(
        &mut self,
        field_pattern: &RecordFieldPattern,
        module_info: &crate::type_arena::InternedModule,
        module_path: &str,
        mutable: bool,
        interner: &Interner,
    ) {
        let export_name_str = interner.resolve(field_pattern.field_name);

        // Find the export by name in module_info.exports
        let found = module_info.exports.iter().find(|(name_id, _)| {
            self.name_table().last_segment_str(*name_id).as_deref() == Some(export_name_str)
        });

        let Some((export_name_id, export_type_id)) = found else {
            // Export not found
            self.add_error(
                SemanticError::ModuleNoExport {
                    module: module_path.to_string(),
                    name: export_name_str.to_string(),
                    span: field_pattern.span.into(),
                },
                field_pattern.span,
            );
            return;
        };

        // Check if this is a generic function that needs special registration
        self.maybe_register_generic_function_binding(field_pattern, *export_name_id, interner);

        // Check if the export type is a class or interface type
        // If so, register a type alias so it's usable as a type name
        self.maybe_register_type_binding(field_pattern.binding, *export_type_id, interner);

        // Bind the export to the binding name
        self.env.scope.define(
            field_pattern.binding,
            Variable {
                ty: *export_type_id,
                mutable,
                declaration_span: field_pattern.span,
            },
        );
        self.add_lambda_local(field_pattern.binding);
    }

    /// If the export is a generic function, register it in the current module
    /// under the binding name so call analysis can find it.
    fn maybe_register_generic_function_binding(
        &mut self,
        field_pattern: &RecordFieldPattern,
        export_name_id: NameId,
        interner: &Interner,
    ) {
        let source_func_id = self.entity_registry().function_by_name(export_name_id);
        let generic_func_data = source_func_id.and_then(|func_id| {
            let registry = self.entity_registry();
            let func_def = registry.get_function(func_id);
            func_def.generic_info.clone().map(|gi| {
                (
                    gi,
                    func_def.signature.clone(),
                    func_def.required_params,
                    func_def.param_defaults.clone(),
                    func_def.param_names.clone(),
                    func_def.is_external,
                )
            })
        });
        if let Some((
            generic_info,
            signature,
            required_params,
            param_defaults,
            param_names,
            is_external,
        )) = generic_func_data
        {
            let binding_name_id = self.name_table_mut().intern(
                self.module.current_module,
                &[field_pattern.binding],
                interner,
            );

            // Register a copy of the function in the current module's namespace
            let new_func_id = self.entity_registry_mut().register_function_full(
                binding_name_id,
                export_name_id, // Keep original name for codegen lookup
                self.module.current_module,
                signature,
                required_params,
                param_defaults,
                param_names,
                is_external,
            );
            self.entity_registry_mut()
                .set_function_generic_info(new_func_id, generic_info);
        }
    }

    /// Check if a type is a class or interface type and if so,
    /// register a type alias so it's usable as a type name in the current module.
    ///
    /// This enables patterns like:
    /// ```vole
    /// let { Duration } = import "std:time"
    /// let d = Duration { nanos: 1000 }  // Works as type name
    /// func foo(d: Duration) -> Duration { d }  // Works in type annotations
    /// ```
    fn maybe_register_type_binding(
        &mut self,
        binding_name: Symbol,
        type_id: ArenaTypeId,
        interner: &Interner,
    ) {
        use crate::entity_defs::TypeDefKind;

        // Check if the type is a class or interface
        let type_def_id = {
            let arena = self.type_arena();
            arena
                .unwrap_nominal(type_id)
                .map(|(def_id, _, _kind)| def_id)
        };

        let Some(original_type_def_id) = type_def_id else {
            return; // Not a class/interface type, nothing to register
        };

        // Don't create type aliases for generic types - they need proper handling
        // Generic types like Iterator<T> or MapLike<K, V> can't be aliased simply
        // because the alias wouldn't carry the type parameters
        let is_generic = !self
            .entity_registry()
            .get_type(original_type_def_id)
            .type_params
            .is_empty();
        if is_generic {
            return; // Skip generic types
        }

        // Create a type alias in the current module pointing to the original type
        // First, intern the binding name in the current module's namespace
        let binding_name_id =
            self.name_table_mut()
                .intern(self.module.current_module, &[binding_name], interner);

        // Check if a type with this name already exists in the current module
        if self
            .entity_registry()
            .type_by_name(binding_name_id)
            .is_some()
        {
            // Type already exists (possibly from a previous import or local definition)
            // Don't create a duplicate
            return;
        }

        // Register a new type alias that points to the original type
        let is_annotation = self
            .entity_registry()
            .get_type(original_type_def_id)
            .is_annotation;
        let alias_type_def_id = self.entity_registry_mut().register_type(
            binding_name_id,
            TypeDefKind::Alias,
            self.module.current_module,
        );

        // Set the aliased type to the original class/interface type
        self.entity_registry_mut()
            .set_aliased_type(alias_type_def_id, type_id);

        // Propagate the is_annotation flag from the original type
        if is_annotation {
            self.entity_registry_mut()
                .get_type_mut(alias_type_def_id)
                .is_annotation = true;
        }
    }
}
