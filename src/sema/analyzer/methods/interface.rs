use crate::identity::{NameId, TypeDefId};
use crate::sema::entity_defs::TypeDefKind;
use crate::sema::types::StructuralType;

use super::super::*;

impl Analyzer {
    /// Check if a type structurally satisfies an interface by TypeDefId
    ///
    /// This is the EntityRegistry-based version of interface satisfaction checking.
    /// Uses TypeDefId and MethodId instead of string-based lookups.
    pub fn satisfies_interface_by_type_def_id(
        &self,
        ty: &Type,
        interface_id: TypeDefId,
        interner: &Interner,
    ) -> bool {
        let interface = self.entity_registry.get_type(interface_id);

        // Verify this is actually an interface
        if interface.kind != TypeDefKind::Interface {
            return false;
        }

        // Check required fields
        for field_id in &interface.fields {
            let field = self.entity_registry.get_field(*field_id);
            let field_name_str = self
                .name_table
                .last_segment_str(field.name_id)
                .unwrap_or_default();
            if !self.type_has_field_by_str(ty, &field_name_str, &field.ty, interner) {
                return false;
            }
        }

        // Check required methods (skip those with defaults)
        for method_id in &interface.methods {
            let method = self.entity_registry.get_method(*method_id);
            if method.has_default {
                continue;
            }

            let method_name_str = self
                .name_table
                .last_segment_str(method.name_id)
                .unwrap_or_default();
            if !self.type_has_method_by_str(ty, &method_name_str, &method.signature, interner) {
                return false;
            }
        }

        // Check parent interfaces (extends)
        for parent_id in &interface.extends.clone() {
            if !self.satisfies_interface_by_type_def_id(ty, *parent_id, interner) {
                return false;
            }
        }

        true
    }

    /// Check if a type structurally satisfies an interface by NameId
    /// (EntityRegistry-first version with fallback)
    ///
    /// Tries EntityRegistry lookup first for better performance,
    /// falling back to the traditional approach if EntityRegistry
    /// doesn't have the interface registered.
    pub fn satisfies_interface_via_entity_registry(
        &self,
        ty: &Type,
        interface_name_id: NameId,
        interner: &Interner,
    ) -> bool {
        // Try EntityRegistry first
        if let Some(type_def_id) = self.entity_registry.type_by_name(interface_name_id) {
            return self.satisfies_interface_by_type_def_id(ty, type_def_id, interner);
        }

        // Fall back to traditional approach
        self.satisfies_interface_by_name_id(ty, interface_name_id, interner)
    }

    /// Check if a type has a field with the given name (string) and compatible type
    fn type_has_field_by_str(
        &self,
        ty: &Type,
        field_name: &str,
        expected_type: &Type,
        interner: &Interner,
    ) -> bool {
        match ty {
            Type::Record(r) => r.fields.iter().any(|f| {
                f.name == field_name && self.types_compatible(&f.ty, expected_type, interner)
            }),
            Type::Class(c) => c.fields.iter().any(|f| {
                f.name == field_name && self.types_compatible(&f.ty, expected_type, interner)
            }),
            _ => false,
        }
    }

    /// Check if a type has a method matching the given name and signature
    fn type_has_method_by_str(
        &self,
        ty: &Type,
        method_name: &str,
        expected_sig: &FunctionType,
        interner: &Interner,
    ) -> bool {
        // Get type name_id for method lookup
        let type_name_id = match ty {
            Type::Record(r) => Some(r.name_id),
            Type::Class(c) => Some(c.name_id),
            _ => None,
        };

        // For primitives/arrays, check implement registry
        if type_name_id.is_none() {
            if let Some(type_id) = TypeId::from_type(ty, &self.entity_registry.type_table)
                && let Some(method_id) = self.method_name_id_by_str(method_name, interner)
            {
                return self
                    .implement_registry
                    .get_method(&type_id, method_id)
                    .is_some();
            }
            return false;
        }

        let type_name_id =
            type_name_id.expect("checked is_none above and returned early");

        // Check direct methods on the type via EntityRegistry
        if let Some(type_def_id) = self.entity_registry.type_by_name(type_name_id)
            && let Some(method_name_id) = self.method_name_id_by_str(method_name, interner)
            && let Some(method_id) = self
                .entity_registry
                .find_method_on_type(type_def_id, method_name_id)
        {
            let method_def = self.entity_registry.get_method(method_id);
            if self.signatures_compatible(expected_sig, &method_def.signature, ty) {
                return true;
            }
        }

        // Check implement registry
        if let Some(type_id) = TypeId::from_type(ty, &self.entity_registry.type_table)
            && let Some(method_id) = self.method_name_id_by_str(method_name, interner)
            && self
                .implement_registry
                .get_method(&type_id, method_id)
                .is_some()
        {
            return true;
        }

        false
    }

    /// Check if two function signatures are compatible (for interface satisfaction)
    fn signatures_compatible(
        &self,
        expected: &FunctionType,
        found: &FunctionType,
        _implementing_type: &Type,
    ) -> bool {
        // Check param count
        if expected.params.len() != found.params.len() {
            return false;
        }

        // For now, just check that params and return type match
        // TODO: Handle Self type substitution properly
        expected.params == found.params && *expected.return_type == *found.return_type
    }

    /// Check if a type structurally satisfies an interface by NameId
    ///
    /// This implements duck typing: a type satisfies an interface if it has
    /// all required fields and methods, regardless of explicit `implements`.
    pub fn satisfies_interface_by_name_id(
        &self,
        ty: &Type,
        interface_name_id: NameId,
        interner: &Interner,
    ) -> bool {
        // Use EntityRegistry for interface lookup
        let Some(type_def_id) = self.entity_registry.type_by_name(interface_name_id) else {
            return false;
        };
        self.satisfies_interface_by_type_def_id(ty, type_def_id, interner)
    }

    /// Check if a type implements Stringable (has to_string() -> string method)
    pub fn satisfies_stringable(&self, ty: &Type, interner: &Interner) -> bool {
        // Use the well-known Stringable NameId if available
        if let Some(stringable_id) = self.name_table.well_known.stringable {
            return self.satisfies_interface_via_entity_registry(ty, stringable_id, interner);
        }
        // Fallback: try to find "Stringable" via Resolver with interface fallback
        let type_def_id = self
            .resolver(interner)
            .resolve_type_str_or_interface("Stringable", &self.entity_registry);
        if let Some(type_def_id) = type_def_id {
            let interface = self.entity_registry.get_type(type_def_id);
            return self.satisfies_interface_via_entity_registry(ty, interface.name_id, interner);
        }
        false
    }

    /// Check if a type structurally satisfies an interface
    ///
    /// This implements duck typing: a type satisfies an interface if it has
    /// all required fields and methods, regardless of explicit `implements`.
    pub fn satisfies_interface(
        &self,
        ty: &Type,
        interface_name: Symbol,
        interner: &Interner,
    ) -> bool {
        // Look up interface via Resolver with interface fallback
        let type_def_id = self
            .resolver(interner)
            .resolve_type_or_interface(interface_name, &self.entity_registry);

        let Some(type_def_id) = type_def_id else {
            return false;
        };

        self.satisfies_interface_by_type_def_id(ty, type_def_id, interner)
    }

    /// Validate that a type satisfies an interface by having all required methods with correct signatures
    pub(crate) fn validate_interface_satisfaction(
        &mut self,
        type_name: Symbol,
        iface_name: Symbol,
        type_methods: &HashMap<String, FunctionType>,
        span: Span,
        interner: &Interner,
    ) {
        // Get the implementing type for Self substitution via Resolver
        let type_id_opt = self
            .resolver(interner)
            .resolve_type(type_name, &self.entity_registry);
        let implementing_type = if let Some(type_id) = type_id_opt {
            let type_def = self.entity_registry.get_type(type_id);
            match type_def.kind {
                TypeDefKind::Class => self
                    .entity_registry
                    .build_class_type(type_id, &self.name_table)
                    .map(Type::Class),
                TypeDefKind::Record => self
                    .entity_registry
                    .build_record_type(type_id, &self.name_table)
                    .map(Type::Record),
                _ => None,
            }
        } else {
            None
        };
        let implementing_type = match implementing_type {
            Some(t) => t,
            None => return, // Unknown type, can't validate
        };

        // Look up interface via Resolver with interface fallback
        let type_def_id = self
            .resolver(interner)
            .resolve_type_or_interface(iface_name, &self.entity_registry);

        if let Some(type_def_id) = type_def_id {
            // Clone the data we need to avoid borrow conflicts
            let iface = self.entity_registry.get_type(type_def_id);
            let method_ids = iface.methods.clone();
            let extends = iface.extends.clone();

            // Collect method info upfront (name_str, has_default, signature)
            let method_infos: Vec<(String, bool, FunctionType)> = method_ids
                .iter()
                .map(|&method_id| {
                    let method = self.entity_registry.get_method(method_id);
                    let name = self
                        .name_table
                        .last_segment_str(method.name_id)
                        .unwrap_or_default();
                    (name, method.has_default, method.signature.clone())
                })
                .collect();

            // Collect parent names upfront
            let parent_names: Vec<Option<String>> = extends
                .iter()
                .map(|&parent_id| {
                    let parent_def = self.entity_registry.get_type(parent_id);
                    self.name_table.last_segment_str(parent_def.name_id)
                })
                .collect();

            // Check methods required by this interface
            for (required_name, has_default, signature) in &method_infos {
                if *has_default {
                    continue;
                }
                match type_methods.get(required_name) {
                    None => {
                        // Method is missing entirely
                        self.add_error(
                            SemanticError::InterfaceNotSatisfied {
                                type_name: interner.resolve(type_name).to_string(),
                                interface_name: interner.resolve(iface_name).to_string(),
                                method: required_name.clone(),
                                span: span.into(),
                            },
                            span,
                        );
                    }
                    Some(found_sig) => {
                        // Method exists, check signature (substituting Self with implementing type)
                        if !Self::signatures_match_entity(
                            &signature.params,
                            &signature.return_type,
                            found_sig,
                            &implementing_type,
                        ) {
                            // Use interface-specific formatter to show "Self" properly
                            let expected = self.format_interface_method_signature(
                                &signature.params,
                                &signature.return_type,
                            );
                            let found = self.format_method_signature(
                                &found_sig.params,
                                &found_sig.return_type,
                                interner,
                            );

                            // Generate detailed mismatch information
                            let details = self.describe_signature_mismatch(
                                &signature.params,
                                &signature.return_type,
                                found_sig,
                                &implementing_type,
                            );

                            self.add_error(
                                SemanticError::InterfaceSignatureMismatch {
                                    interface_name: interner.resolve(iface_name).to_string(),
                                    method: required_name.to_string(),
                                    expected,
                                    found,
                                    details,
                                    span: span.into(),
                                },
                                span,
                            );
                        }
                    }
                }
            }

            // Check parent interfaces (extends) - get their Symbols from entity registry
            for parent_name_str in parent_names.into_iter().flatten() {
                if let Some(parent_sym) = interner.lookup(&parent_name_str) {
                    self.validate_interface_satisfaction(
                        type_name,
                        parent_sym,
                        type_methods,
                        span,
                        interner,
                    );
                }
            }
        }
    }

    /// Check if method signature matches (EntityRegistry version)
    fn signatures_match_entity(
        required_params: &[Type],
        required_return: &Type,
        found: &FunctionType,
        implementing_type: &Type,
    ) -> bool {
        // Check parameter count
        if required_params.len() != found.params.len() {
            return false;
        }
        // Check parameter types, substituting Self (Type::Error) with implementing_type
        for (req_param, found_param) in required_params.iter().zip(found.params.iter()) {
            let effective_req = if matches!(req_param, Type::Error) {
                implementing_type
            } else {
                req_param
            };
            if effective_req != found_param {
                return false;
            }
        }
        // Check return type, substituting Self (Type::Error) with implementing_type
        let effective_return = if matches!(required_return, Type::Error) {
            implementing_type
        } else {
            required_return
        };
        effective_return == &*found.return_type
    }

    /// Describe what specifically mismatches between required and found signatures.
    /// Returns a human-readable description of the differences.
    fn describe_signature_mismatch(
        &mut self,
        required_params: &[Type],
        required_return: &Type,
        found: &FunctionType,
        implementing_type: &Type,
    ) -> String {
        let mut mismatches = Vec::new();

        // Check parameter count
        if required_params.len() != found.params.len() {
            mismatches.push(format!(
                "parameter count: expected {}, found {}",
                required_params.len(),
                found.params.len()
            ));
        } else {
            // Check each parameter type
            for (i, (req_param, found_param)) in
                required_params.iter().zip(found.params.iter()).enumerate()
            {
                let effective_req = if matches!(req_param, Type::Error) {
                    implementing_type
                } else {
                    req_param
                };
                if effective_req != found_param {
                    let expected_str = if matches!(req_param, Type::Error) {
                        "Self".to_string()
                    } else {
                        self.type_display(req_param)
                    };
                    let found_str = self.type_display(found_param);
                    mismatches.push(format!(
                        "parameter {}: expected '{}', found '{}'",
                        i + 1,
                        expected_str,
                        found_str
                    ));
                }
            }
        }

        // Check return type
        let effective_return = if matches!(required_return, Type::Error) {
            implementing_type
        } else {
            required_return
        };
        if effective_return != &*found.return_type {
            let expected_str = if matches!(required_return, Type::Error) {
                "Self".to_string()
            } else {
                self.type_display(required_return)
            };
            let found_str = self.type_display(&found.return_type);
            mismatches.push(format!(
                "return type: expected '{}', found '{}'",
                expected_str, found_str
            ));
        }

        if mismatches.is_empty() {
            "signature mismatch".to_string()
        } else {
            mismatches.join("\n")
        }
    }

    /// Get all method signatures for a type (from direct methods + implement blocks)
    pub(crate) fn get_type_method_signatures(
        &self,
        type_name: Symbol,
        interner: &Interner,
    ) -> HashMap<String, FunctionType> {
        let mut method_sigs = HashMap::new();

        let method_name_str = |method_id: NameId| {
            self.name_table
                .last_segment_str(method_id)
                .unwrap_or_default()
        };

        // Methods defined directly on the type via Resolver
        let type_def_id_opt = self
            .resolver(interner)
            .resolve_type(type_name, &self.entity_registry);
        if let Some(type_def_id) = type_def_id_opt {
            for method_id in self.entity_registry.methods_on_type(type_def_id) {
                let method = self.entity_registry.get_method(method_id);
                method_sigs.insert(method_name_str(method.name_id), method.signature.clone());
            }

            // Methods from implement blocks
            let name_id = self.entity_registry.get_type(type_def_id).name_id;
            let type_id = TypeId::from_name_id(name_id);
            for (method_name, method_impl) in self.implement_registry.get_methods_for_type(&type_id)
            {
                method_sigs.insert(method_name_str(method_name), method_impl.func_type.clone());
            }
        }

        method_sigs
    }

    /// Check if a type satisfies a structural constraint.
    /// Returns None if satisfied, or Some(mismatch_description) if not.
    pub fn check_structural_constraint(
        &self,
        ty: &Type,
        structural: &StructuralType,
        interner: &Interner,
    ) -> Option<String> {
        let mut mismatches = Vec::new();

        // Check required fields
        for field in &structural.fields {
            let field_name_str = self
                .name_table
                .last_segment_str(field.name)
                .unwrap_or_default();

            if !self.type_has_field_with_type(ty, &field_name_str, &field.ty, interner) {
                let type_str = self
                    .entity_registry
                    .type_table
                    .clone()
                    .display_type(&field.ty, &mut self.name_table.clone());
                mismatches.push(format!(
                    "missing field '{}' of type '{}'",
                    field_name_str, type_str
                ));
            }
        }

        // Check required methods
        for method in &structural.methods {
            let method_name_str = self
                .name_table
                .last_segment_str(method.name)
                .unwrap_or_default();

            if !self.type_has_structural_method(
                ty,
                &method_name_str,
                &method.params,
                &method.return_type,
                interner,
            ) {
                let params_str = method
                    .params
                    .iter()
                    .map(|p| {
                        self.entity_registry
                            .type_table
                            .clone()
                            .display_type(p, &mut self.name_table.clone())
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                let ret_str = self
                    .entity_registry
                    .type_table
                    .clone()
                    .display_type(&method.return_type, &mut self.name_table.clone());
                mismatches.push(format!(
                    "missing method '{}({}) -> {}'",
                    method_name_str, params_str, ret_str
                ));
            }
        }

        if mismatches.is_empty() {
            None
        } else {
            Some(mismatches.join(", "))
        }
    }

    /// Check if a type has a field with compatible type
    fn type_has_field_with_type(
        &self,
        ty: &Type,
        field_name: &str,
        expected_type: &Type,
        interner: &Interner,
    ) -> bool {
        match ty {
            Type::Record(r) => r.fields.iter().any(|f| {
                f.name == field_name && self.types_compatible(&f.ty, expected_type, interner)
            }),
            Type::Class(c) => c.fields.iter().any(|f| {
                f.name == field_name && self.types_compatible(&f.ty, expected_type, interner)
            }),
            _ => false,
        }
    }

    /// Check if a type has a method with compatible signature for structural constraints
    /// Uses covariant return types and contravariant parameter types
    fn type_has_structural_method(
        &self,
        ty: &Type,
        method_name: &str,
        expected_params: &[Type],
        expected_return: &Type,
        interner: &Interner,
    ) -> bool {
        // Get type name_id for method lookup
        let type_name_id = match ty {
            Type::Record(r) => Some(r.name_id),
            Type::Class(c) => Some(c.name_id),
            _ => None,
        };

        // For primitives/arrays, check implement registry
        if type_name_id.is_none() {
            if let Some(type_id) = TypeId::from_type(ty, &self.entity_registry.type_table)
                && let Some(method_id) = self.method_name_id_by_str(method_name, interner)
                && let Some(method_impl) = self.implement_registry.get_method(&type_id, method_id)
            {
                return self.check_structural_method_signature(
                    expected_params,
                    expected_return,
                    &method_impl.func_type,
                    interner,
                );
            }
            return false;
        }

        let type_name_id =
            type_name_id.expect("checked is_none above and returned early");

        // Check direct methods on the type via EntityRegistry
        if let Some(type_def_id) = self.entity_registry.type_by_name(type_name_id)
            && let Some(method_name_id) = self.method_name_id_by_str(method_name, interner)
            && let Some(method_id) = self
                .entity_registry
                .find_method_on_type(type_def_id, method_name_id)
        {
            let method_def = self.entity_registry.get_method(method_id);
            if self.check_structural_method_signature(
                expected_params,
                expected_return,
                &method_def.signature,
                interner,
            ) {
                return true;
            }
        }

        // Check implement registry
        if let Some(type_id) = TypeId::from_type(ty, &self.entity_registry.type_table)
            && let Some(method_id) = self.method_name_id_by_str(method_name, interner)
            && let Some(method_impl) = self.implement_registry.get_method(&type_id, method_id)
        {
            return self.check_structural_method_signature(
                expected_params,
                expected_return,
                &method_impl.func_type,
                interner,
            );
        }

        false
    }

    /// Check if a method signature satisfies structural constraints.
    /// Uses covariant return types (actual can be narrower) and
    /// contravariant parameter types (actual can be wider).
    fn check_structural_method_signature(
        &self,
        expected_params: &[Type],
        expected_return: &Type,
        actual: &FunctionType,
        interner: &Interner,
    ) -> bool {
        // Check parameter count
        if expected_params.len() != actual.params.len() {
            return false;
        }

        // Contravariant parameters: actual param types must be same or wider than expected
        // For now, use exact matching (full contravariance requires more complex subtyping)
        for (expected_param, actual_param) in expected_params.iter().zip(actual.params.iter()) {
            if !self.types_compatible(actual_param, expected_param, interner) {
                return false;
            }
        }

        // Covariant return: actual return type must be same or narrower than expected
        // For now, use exact matching (full covariance requires more complex subtyping)
        self.types_compatible(&actual.return_type, expected_return, interner)
    }
}
