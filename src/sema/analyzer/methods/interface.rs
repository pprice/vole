use super::super::*;

impl Analyzer {
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
        let Some(interface) = self.interface_registry.get(interface_name, interner) else {
            return false;
        };

        // Check required fields
        for field in &interface.fields {
            if !self.type_has_field(ty, field.name, &field.ty, interner) {
                return false;
            }
        }

        // Check required methods (skip those with defaults)
        for method in &interface.methods {
            if method.has_default {
                continue;
            }

            if !self.type_has_method(ty, method, interner) {
                return false;
            }
        }

        // Check parent interfaces (extends)
        for parent in &interface.extends {
            if !self.satisfies_interface(ty, *parent, interner) {
                return false;
            }
        }

        true
    }

    /// Check if a type has a field with the given name and compatible type
    pub(crate) fn type_has_field(
        &self,
        ty: &Type,
        field_name: Symbol,
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

    /// Check if a type has a method that matches the interface method signature
    pub(crate) fn type_has_method(
        &self,
        ty: &Type,
        interface_method: &InterfaceMethodDef,
        interner: &Interner,
    ) -> bool {
        // Get type symbol for method lookup
        let type_sym = match ty {
            Type::Record(r) => r.name,
            Type::Class(c) => c.name,
            _ => {
                // For primitives/arrays, check implement registry
                if let Some(type_id) = TypeId::from_type(ty, &self.type_table)
                    && let Some(method_id) =
                        self.method_name_id_lookup(interface_method.name, interner)
                {
                    return self
                        .implement_registry
                        .get_method(&type_id, method_id)
                        .is_some();
                }
                return false;
            }
        };

        // Check direct methods on the type
        if let Some(type_id) = self
            .records
            .get(&type_sym)
            .map(|record| record.name_id)
            .or_else(|| self.classes.get(&type_sym).map(|class| class.name_id))
            && let Some(method_id) = self.method_name_id_lookup(interface_method.name, interner)
        {
            let method_key = (type_id, method_id);
            if self.methods.contains_key(&method_key) {
                return true;
            }
        }

        // Check implement registry
        if let Some(type_id) = TypeId::from_type(ty, &self.type_table)
            && let Some(method_id) = self.method_name_id_lookup(interface_method.name, interner)
            && self
                .implement_registry
                .get_method(&type_id, method_id)
                .is_some()
        {
            return true;
        }

        false
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
        if let Some(iface) = self.interface_registry.get(iface_name, interner).cloned() {
            // Check methods required by this interface
            for required in &iface.methods {
                if required.has_default {
                    continue;
                }
                let required_name = interner.resolve(required.name);
                match type_methods.get(required_name) {
                    None => {
                        // Method is missing entirely
                        self.add_error(
                            SemanticError::InterfaceNotSatisfied {
                                type_name: interner.resolve(type_name).to_string(),
                                interface_name: interner.resolve(iface_name).to_string(),
                                method: required_name.to_string(),
                                span: span.into(),
                            },
                            span,
                        );
                    }
                    Some(found_sig) => {
                        // Method exists, check signature
                        if !Self::signatures_match(required, found_sig) {
                            let expected = self.format_method_signature(
                                &required.params,
                                &required.return_type,
                                interner,
                            );
                            let found = self.format_method_signature(
                                &found_sig.params,
                                &found_sig.return_type,
                                interner,
                            );
                            self.add_error(
                                SemanticError::InterfaceSignatureMismatch {
                                    interface_name: interner.resolve(iface_name).to_string(),
                                    method: required_name.to_string(),
                                    expected,
                                    found,
                                    span: span.into(),
                                },
                                span,
                            );
                        }
                    }
                }
            }
            // Check parent interfaces (extends)
            for parent_iface in &iface.extends {
                self.validate_interface_satisfaction(
                    type_name,
                    *parent_iface,
                    type_methods,
                    span,
                    interner,
                );
            }
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
                .last_segment_str(method_id, interner)
                .unwrap_or_default()
        };

        // Methods defined directly on the type
        let type_id = self
            .records
            .get(&type_name)
            .map(|record| record.name_id)
            .or_else(|| self.classes.get(&type_name).map(|class| class.name_id));
        if let Some(type_id) = type_id {
            for ((ty, method_name), func_type) in &self.methods {
                if *ty == type_id {
                    method_sigs.insert(method_name_str(*method_name), func_type.clone());
                }
            }
        }

        // Methods from implement blocks
        if let Some(type_id) = self
            .records
            .get(&type_name)
            .map(|record| TypeId::from_name_id(record.name_id))
            .or_else(|| {
                self.classes
                    .get(&type_name)
                    .map(|class| TypeId::from_name_id(class.name_id))
            })
        {
            for (method_name, method_impl) in self.implement_registry.get_methods_for_type(&type_id)
            {
                method_sigs.insert(method_name_str(method_name), method_impl.func_type.clone());
            }
        }

        method_sigs
    }
}
