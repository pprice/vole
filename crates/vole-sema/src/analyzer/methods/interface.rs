use crate::entity_defs::TypeDefKind;
use crate::implement_registry::ImplTypeId;
use crate::type_arena::TypeId as ArenaTypeId;
use vole_identity::{NameId, TypeDefId};

use super::super::*;

impl Analyzer {
    /// Check if a type implements Stringable (TypeId version)
    pub fn satisfies_stringable_id(&mut self, ty_id: ArenaTypeId, interner: &Interner) -> bool {
        // Look up Stringable interface
        let type_def_id = self
            .resolver(interner)
            .resolve_type_str_or_interface("Stringable", &self.entity_registry());
        if let Some(type_def_id) = type_def_id {
            return self.satisfies_interface_by_type_def_id_typeid(ty_id, type_def_id, interner);
        }
        false
    }

    /// Check if a type structurally satisfies an interface by TypeDefId.
    pub(crate) fn satisfies_interface_by_type_def_id_typeid(
        &mut self,
        ty_id: ArenaTypeId,
        interface_id: TypeDefId,
        interner: &Interner,
    ) -> bool {
        // Extract all data we need from the interface upfront to avoid borrow conflicts
        let (is_interface, field_ids, method_ids, extends) = {
            let registry = self.entity_registry();
            let interface = registry.get_type(interface_id);
            (
                interface.kind == TypeDefKind::Interface,
                interface.fields.clone(),
                interface.methods.clone(),
                interface.extends.clone(),
            )
        };

        if !is_interface {
            return false;
        }

        // Check required fields
        for field_id in field_ids {
            // Get field data first
            let (name_id, field_type_id) = {
                let registry = self.entity_registry();
                let field = registry.get_field(field_id);
                (field.name_id, field.ty)
            };
            // Then look up the name
            let field_name_str = self
                .name_table()
                .last_segment_str(name_id)
                .unwrap_or_default();
            if !self.type_has_field_by_str_id(ty_id, &field_name_str, field_type_id, interner) {
                return false;
            }
        }

        // Check required methods (skip those with defaults)
        for method_id in method_ids {
            // Step 1: Get method data from registry
            let (has_default, name_id, signature_id) = {
                let registry = self.entity_registry();
                let method = registry.get_method(method_id);
                (method.has_default, method.name_id, method.signature_id)
            };
            if has_default {
                continue;
            }
            // Step 2: Get signature from arena
            let signature = {
                let arena = self.type_arena();
                let (params, ret, is_closure) = arena
                    .unwrap_function(signature_id)
                    .expect("method signature must be a function type");
                FunctionType {
                    is_closure,
                    params_id: params.clone(),
                    return_type_id: ret,
                }
            };
            // Step 3: Get method name from name table
            let method_name_str = self
                .name_table()
                .last_segment_str(name_id)
                .unwrap_or_default();
            // Use TypeId-based method checking
            if !self.type_has_method_by_str_id(ty_id, &method_name_str, &signature, interner) {
                return false;
            }
        }

        // Check parent interfaces (extends)
        for parent_id in extends {
            if !self.satisfies_interface_by_type_def_id_typeid(ty_id, parent_id, interner) {
                return false;
            }
        }

        true
    }

    /// Check if a type has a field with the given name (string) and compatible type (TypeId version)
    fn type_has_field_by_str_id(
        &mut self,
        ty_id: ArenaTypeId,
        field_name: &str,
        expected_type_id: ArenaTypeId,
        interner: &Interner,
    ) -> bool {
        // Get type_def_id and type_args from TypeId using arena queries
        let (type_def_id, type_args_id) = {
            let arena = self.type_arena();
            if let Some((id, args)) = arena.unwrap_class(ty_id) {
                (id, args.clone())
            } else if let Some((id, args)) = arena.unwrap_record(ty_id) {
                (id, args.clone())
            } else {
                return false;
            }
        };

        // Clone generic_info to avoid holding borrow during subsequent operations
        let generic_info = {
            let registry = self.entity_registry();
            let type_def = registry.get_type(type_def_id);
            match type_def.generic_info.clone() {
                Some(info) => info,
                None => return false,
            }
        };

        // Build type substitutions directly using TypeId
        let substitutions: hashbrown::HashMap<_, _> = generic_info
            .type_params
            .iter()
            .zip(type_args_id.iter())
            .map(|(tp, &arg_id)| (tp.name_id, arg_id))
            .collect();

        // Find field and check type compatibility using arena substitution
        for (i, name_id) in generic_info.field_names.iter().enumerate() {
            if self.name_table().last_segment_str(*name_id).as_deref() == Some(field_name) {
                let field_type_id = generic_info.field_types[i];
                let substituted_field_type_id = self
                    .type_arena_mut()
                    .substitute(field_type_id, &substitutions);
                return self.types_compatible_id(
                    substituted_field_type_id,
                    expected_type_id,
                    interner,
                );
            }
        }
        false
    }

    /// Check if a type has a method matching the given name and signature (TypeId version)
    fn type_has_method_by_str_id(
        &mut self,
        ty_id: ArenaTypeId,
        method_name: &str,
        expected_sig: &FunctionType,
        interner: &Interner,
    ) -> bool {
        // Get type_def_id from TypeId using arena queries
        let type_def_id = {
            let arena = self.type_arena();
            if let Some((id, _)) = arena.unwrap_class(ty_id) {
                Some(id)
            } else if let Some((id, _)) = arena.unwrap_record(ty_id) {
                Some(id)
            } else {
                None
            }
        };

        // For primitives/arrays, check implement registry (using TypeId)
        if type_def_id.is_none() {
            let impl_type_id = {
                let arena = self.type_arena();
                ImplTypeId::from_type_id(ty_id, &arena, &self.entity_registry())
            };
            if let Some(impl_type_id) = impl_type_id
                && let Some(method_id) = self.method_name_id_by_str(method_name, interner)
            {
                return self
                    .implement_registry()
                    .get_method(&impl_type_id, method_id)
                    .is_some();
            }
            return false;
        }

        let type_def_id = type_def_id.expect("checked is_none above");

        // Check direct methods on the type via EntityRegistry
        let maybe_method_id = {
            if let Some(method_name_id) = self.method_name_id_by_str(method_name, interner) {
                let registry = self.entity_registry();
                registry.find_method_on_type(type_def_id, method_name_id)
            } else {
                None
            }
        };
        if let Some(method_id) = maybe_method_id {
            let signature_id = {
                let registry = self.entity_registry();
                registry.get_method(method_id).signature_id
            };
            let found_sig = {
                let arena = self.type_arena();
                let (params, ret, is_closure) = arena
                    .unwrap_function(signature_id)
                    .expect("method signature must be a function type");
                FunctionType {
                    is_closure,
                    params_id: params.clone(),
                    return_type_id: ret,
                }
            };
            if self.signatures_compatible_id(expected_sig, &found_sig) {
                return true;
            }
        }

        // Check implement registry (using TypeId)
        let impl_type_id = {
            let arena = self.type_arena();
            ImplTypeId::from_type_id(ty_id, &arena, &self.entity_registry())
        };
        if let Some(impl_type_id) = impl_type_id
            && let Some(method_id) = self.method_name_id_by_str(method_name, interner)
            && self
                .implement_registry()
                .get_method(&impl_type_id, method_id)
                .is_some()
        {
            return true;
        }

        false
    }

    /// Check if two function signatures are compatible using TypeId fields
    fn signatures_compatible_id(&self, expected: &FunctionType, found: &FunctionType) -> bool {
        // Compare TypeId fields directly
        expected.params_id.as_slice() == found.params_id.as_slice()
            && expected.return_type_id == found.return_type_id
    }

    /// Check if a TypeId satisfies an interface (TypeId version)
    pub(crate) fn satisfies_interface_id(
        &mut self,
        ty_id: ArenaTypeId,
        interface_name: Symbol,
        interner: &Interner,
    ) -> bool {
        // Look up interface via Resolver with interface fallback
        let type_def_id = self
            .resolver(interner)
            .resolve_type_or_interface(interface_name, &self.entity_registry());

        let Some(type_def_id) = type_def_id else {
            return false;
        };

        self.satisfies_interface_by_type_def_id_typeid(ty_id, type_def_id, interner)
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
            .resolve_type(type_name, &self.entity_registry());
        // Build implementing type directly as TypeId
        let implementing_type_id = if let Some(type_id) = type_id_opt {
            let kind = {
                let registry = self.entity_registry();
                registry.get_type(type_id).kind
            };
            match kind {
                TypeDefKind::Class => Some(
                    self.type_arena_mut()
                        .class(type_id, crate::type_arena::TypeIdVec::new()),
                ),
                TypeDefKind::Record => Some(
                    self.type_arena_mut()
                        .record(type_id, crate::type_arena::TypeIdVec::new()),
                ),
                _ => None,
            }
        } else {
            None
        };
        let implementing_type_id = match implementing_type_id {
            Some(t) => t,
            None => return, // Unknown type, can't validate
        };

        // Look up interface via Resolver with interface fallback
        let type_def_id = self
            .resolver(interner)
            .resolve_type_or_interface(iface_name, &self.entity_registry());

        if let Some(interface_type_id) = type_def_id {
            // Clone the data we need to avoid borrow conflicts
            let (method_ids, extends, interface_type_params) = {
                let registry = self.entity_registry();
                let iface = registry.get_type(interface_type_id);
                (
                    iface.methods.clone(),
                    iface.extends.clone(),
                    iface.type_params.clone(),
                )
            };

            // Build substitution map for generic interface type parameters (TypeId-based)
            // E.g., MapLike<K, V> implemented as MapLike<i64, i64> → {K: i64, V: i64}
            let substitutions: hashbrown::HashMap<NameId, ArenaTypeId> =
                if let Some(impl_type_id) = type_id_opt {
                    let type_args: Vec<_> = {
                        let registry = self.entity_registry();
                        registry
                            .get_implementation_type_args(impl_type_id, interface_type_id)
                            .to_vec()
                    };
                    interface_type_params
                        .iter()
                        .zip(type_args.iter())
                        .map(|(param, arg)| (*param, *arg))
                        .collect()
                } else {
                    hashbrown::HashMap::new()
                };

            // Collect method info upfront (name_str, has_default, signature with substitutions applied)
            let method_infos: Vec<(String, bool, FunctionType)> = method_ids
                .iter()
                .map(|&method_id| {
                    let (name_id, signature_id, has_default) = {
                        let registry = self.entity_registry();
                        let method = registry.get_method(method_id);
                        (method.name_id, method.signature_id, method.has_default)
                    };
                    let name = self
                        .name_table()
                        .last_segment_str(name_id)
                        .unwrap_or_default();

                    // Get original signature from arena
                    let (param_ids, return_id, is_closure) = {
                        let arena = self.type_arena();
                        let (params, ret, is_closure) = arena
                            .unwrap_function(signature_id)
                            .expect("method signature must be a function type");
                        (params.to_vec(), ret, is_closure)
                    };

                    // Apply type parameter substitution using TypeId-based arena substitution
                    let subst_sig = if substitutions.is_empty() {
                        FunctionType {
                            is_closure,
                            params_id: param_ids.into(),
                            return_type_id: return_id,
                        }
                    } else {
                        // Substitute using arena
                        let (subst_params, subst_ret) = {
                            let mut arena = self.type_arena_mut();
                            let params: Vec<ArenaTypeId> = param_ids
                                .iter()
                                .map(|&p| arena.substitute(p, &substitutions))
                                .collect();
                            let ret = arena.substitute(return_id, &substitutions);
                            (params, ret)
                        };

                        // Build FunctionType from substituted TypeIds
                        FunctionType::from_ids(&subst_params, subst_ret, is_closure)
                    };
                    (name, has_default, subst_sig)
                })
                .collect();

            // Collect parent names upfront
            let parent_names: Vec<Option<String>> = extends
                .iter()
                .map(|&parent_id| {
                    let name_id = {
                        let registry = self.entity_registry();
                        registry.get_type(parent_id).name_id
                    };
                    self.name_table().last_segment_str(name_id)
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
                        if !Self::signatures_match_entity_id(
                            &signature.params_id,
                            signature.return_type_id,
                            found_sig,
                            implementing_type_id,
                        ) {
                            // Use interface-specific formatter to show "Self" properly
                            let expected = self.format_interface_method_signature_id(
                                &signature.params_id,
                                signature.return_type_id,
                            );
                            let found = self.format_method_signature_id(
                                &found_sig.params_id,
                                found_sig.return_type_id,
                            );

                            // Generate detailed mismatch information
                            let details = self.describe_signature_mismatch_id(
                                &signature.params_id,
                                signature.return_type_id,
                                found_sig,
                                implementing_type_id,
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

    /// Check if method signature matches.
    fn signatures_match_entity_id(
        required_params_id: &[ArenaTypeId],
        required_return_id: ArenaTypeId,
        found: &FunctionType,
        implementing_type_id: ArenaTypeId,
    ) -> bool {
        // Check parameter count
        if required_params_id.len() != found.params_id.len() {
            return false;
        }
        // Check parameter types, substituting Self (TypeId::INVALID) with implementing_type_id
        for (&req_param_id, &found_param_id) in
            required_params_id.iter().zip(found.params_id.iter())
        {
            let effective_req = if req_param_id.is_invalid() {
                implementing_type_id
            } else {
                req_param_id
            };
            if effective_req != found_param_id {
                return false;
            }
        }
        // Check return type, substituting Self (TypeId::INVALID) with implementing_type_id
        let effective_return = if required_return_id.is_invalid() {
            implementing_type_id
        } else {
            required_return_id
        };
        effective_return == found.return_type_id
    }

    /// Describe what specifically mismatches between required and found signatures (TypeId version).
    /// Returns a human-readable description of the differences.
    fn describe_signature_mismatch_id(
        &mut self,
        required_params: &[ArenaTypeId],
        required_return: ArenaTypeId,
        found: &FunctionType,
        implementing_type_id: ArenaTypeId,
    ) -> String {
        let mut mismatches = Vec::new();

        // Check parameter count
        if required_params.len() != found.params_id.len() {
            mismatches.push(format!(
                "parameter count: expected {}, found {}",
                required_params.len(),
                found.params_id.len()
            ));
        } else {
            // Check each parameter type
            for (i, (&req_param, &found_param)) in required_params
                .iter()
                .zip(found.params_id.iter())
                .enumerate()
            {
                let req_is_invalid = self.type_arena().is_invalid(req_param);
                let effective_req = if req_is_invalid {
                    implementing_type_id
                } else {
                    req_param
                };
                if effective_req != found_param {
                    let expected_str = if req_is_invalid {
                        "Self".to_string()
                    } else {
                        self.type_display_id(req_param)
                    };
                    let found_str = self.type_display_id(found_param);
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
        let return_is_invalid = self.type_arena().is_invalid(required_return);
        let effective_return = if return_is_invalid {
            implementing_type_id
        } else {
            required_return
        };
        if effective_return != found.return_type_id {
            let expected_str = if return_is_invalid {
                "Self".to_string()
            } else {
                self.type_display_id(required_return)
            };
            let found_str = self.type_display_id(found.return_type_id);
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
            self.name_table()
                .last_segment_str(method_id)
                .unwrap_or_default()
        };

        // Methods defined directly on the type via Resolver
        let type_def_id_opt = self
            .resolver(interner)
            .resolve_type(type_name, &self.entity_registry());
        if let Some(type_def_id) = type_def_id_opt {
            let method_ids: Vec<_> = self
                .entity_registry()
                .methods_on_type(type_def_id)
                .collect();
            for method_id in method_ids {
                let (signature_id, name_id) = {
                    let registry = self.entity_registry();
                    let method = registry.get_method(method_id);
                    (method.signature_id, method.name_id)
                };
                let sig = {
                    let arena = self.type_arena();
                    let (params, ret, is_closure) = arena
                        .unwrap_function(signature_id)
                        .expect("method signature must be a function type");
                    FunctionType {
                        is_closure,
                        params_id: params.clone(),
                        return_type_id: ret,
                    }
                };
                method_sigs.insert(method_name_str(name_id), sig);
            }

            // Methods from implement blocks
            let name_id = self.entity_registry().get_type(type_def_id).name_id;
            let type_id = ImplTypeId::from_name_id(name_id);
            for (method_name, method_impl) in
                self.implement_registry().get_methods_for_type(&type_id)
            {
                method_sigs.insert(method_name_str(method_name), method_impl.func_type.clone());
            }
        }

        method_sigs
    }

    /// Check if a TypeId satisfies a structural constraint (TypeId version).
    /// Returns None if satisfied, or Some(mismatch_description) if not.
    pub(crate) fn check_structural_constraint_id(
        &mut self,
        ty_id: ArenaTypeId,
        structural: &crate::type_arena::InternedStructural,
        interner: &Interner,
    ) -> Option<String> {
        let mut mismatches = Vec::new();

        // Check required fields - InternedStructural uses (NameId, TypeId) pairs
        for (field_name, field_type_id) in &structural.fields {
            let field_name_str = self
                .name_table()
                .last_segment_str(*field_name)
                .unwrap_or_default();

            if !self.type_has_field_by_str_id(ty_id, &field_name_str, *field_type_id, interner) {
                let type_str = self.type_display_id(*field_type_id);
                mismatches.push(format!(
                    "missing field '{}' of type '{}'",
                    field_name_str, type_str
                ));
            }
        }

        // Check required methods - InternedStructuralMethod uses TypeId directly
        for method in &structural.methods {
            let method_name_str = self
                .name_table()
                .last_segment_str(method.name)
                .unwrap_or_default();

            // Create a FunctionType from the structural method signature (TypeId-based)
            let expected_sig = FunctionType::from_ids(&method.params, method.return_type, false);

            if !self.type_has_method_by_str_id(ty_id, &method_name_str, &expected_sig, interner) {
                let params_str = method
                    .params
                    .iter()
                    .map(|&p| self.type_display_id(p))
                    .collect::<Vec<_>>()
                    .join(", ");
                let ret_str = self.type_display_id(method.return_type);
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
}
