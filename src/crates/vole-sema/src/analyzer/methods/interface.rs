use crate::entity_defs::TypeDefKind;
use crate::implement_registry::ImplTypeId;
use crate::type_arena::TypeId as ArenaTypeId;
use rustc_hash::FxHashMap;
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
        let (is_interface, field_ids, method_ids, extends) =
            self.entity_registry().interface_info(interface_id);

        if !is_interface {
            return false;
        }

        // Check required fields
        for field_id in field_ids {
            let (name_id, field_type_id) = self.entity_registry().field_name_and_type(field_id);
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
            let (has_default, name_id, signature_id) =
                self.entity_registry().method_default_name_sig(method_id);
            if has_default {
                continue;
            }
            // Step 2: Get signature from arena
            let signature = {
                let arena = self.type_arena();
                // Skip methods with invalid signatures (unknown types) - error reported elsewhere
                let Some((params, ret, is_closure)) = arena.unwrap_function(signature_id) else {
                    continue;
                };
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
        // Get type_def_id and type_args from TypeId using arena queries (class only)
        let (type_def_id, type_args_id) = {
            let arena = self.type_arena();
            let Some((id, args, _)) = arena.unwrap_class_or_struct(ty_id) else {
                return false;
            };
            (id, args.clone())
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
        let substitutions: FxHashMap<_, _> = generic_info
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
        // Get type_def_id from TypeId using arena queries (class only)
        let type_def_id = {
            let arena = self.type_arena();
            arena.unwrap_class_or_struct(ty_id).map(|(id, _, _)| id)
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
        let maybe_method_id =
            self.method_name_id_by_str(method_name, interner)
                .and_then(|name_id| {
                    self.entity_registry()
                        .find_method_on_type(type_def_id, name_id)
                });

        if let Some(method_id) = maybe_method_id {
            let signature_id = self.entity_registry().method_signature(method_id);
            let found_sig = {
                let arena = self.type_arena();
                // If signature is invalid (unknown type), treat as not having the method
                let Some((params, ret, is_closure)) = arena.unwrap_function(signature_id) else {
                    return false;
                };
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

    /// Check if a TypeId satisfies an interface by Symbol (used in tests).
    #[cfg(test)]
    pub(crate) fn satisfies_interface_id(
        &mut self,
        ty_id: ArenaTypeId,
        interface_name: Symbol,
        interner: &Interner,
    ) -> bool {
        let type_def_id = self
            .resolver(interner)
            .resolve_type_or_interface(interface_name, &self.entity_registry());

        let Some(type_def_id) = type_def_id else {
            return false;
        };

        self.satisfies_interface_by_type_def_id_typeid(ty_id, type_def_id, interner)
    }

    /// Check if a type satisfies an interface, looked up by string name.
    /// Used for cross-interner constraint checking (e.g., prelude generic functions).
    pub(crate) fn satisfies_interface_by_name(
        &mut self,
        ty_id: ArenaTypeId,
        interface_name_str: &str,
        interner: &Interner,
    ) -> bool {
        let interface_type_def_id = self
            .resolver(interner)
            .resolve_type_str_or_interface(interface_name_str, &self.entity_registry());

        let Some(interface_type_def_id) = interface_type_def_id else {
            return false;
        };

        if !self.satisfies_interface_by_type_def_id_typeid(ty_id, interface_type_def_id, interner) {
            return false;
        }

        // Check specialization: if the implementation targets a specific generic
        // specialization (e.g., `implement Describable for Box<i64>`), verify
        // that the actual type args match the implementation's target type args.
        self.check_specialization_match(ty_id, interface_type_def_id)
    }

    /// Verify that a type's specialization matches any specialization-specific
    /// implementation. Returns true if there's no specialization constraint or
    /// if the type args match. Returns false if the implementation targets a
    /// different specialization than the value's actual type args.
    fn check_specialization_match(
        &self,
        ty_id: ArenaTypeId,
        interface_type_def_id: TypeDefId,
    ) -> bool {
        // Get the base TypeDefId and actual type args from the value's type
        let (base_type_def_id, actual_type_args) = {
            let arena = self.type_arena();
            match arena.unwrap_nominal(ty_id) {
                Some((td, args, _)) => (td, args.to_vec()),
                None => return true, // Non-nominal types: no specialization to check
            }
        };

        // Look up the implementation's target type args
        let registry = self.entity_registry();
        let target_type_args =
            registry.get_implementation_target_type_args(base_type_def_id, interface_type_def_id);

        // If no target type args, the implementation applies to all specializations
        if target_type_args.is_empty() {
            return true;
        }

        // Compare: the actual type args must match the implementation's target
        if actual_type_args.len() != target_type_args.len() {
            return false;
        }

        actual_type_args
            .iter()
            .zip(target_type_args.iter())
            .all(|(&actual, &target)| actual == target)
    }

    /// Check if a type satisfies a parameterized interface with specific type args.
    /// E.g., does IntProducer satisfy Producer<i64>?
    /// Resolves the interface, finds the type's implementation, and checks type arg compatibility.
    pub(crate) fn satisfies_parameterized_interface(
        &mut self,
        ty_id: ArenaTypeId,
        interface_name_str: &str,
        required_type_args: &[ArenaTypeId],
        interner: &Interner,
    ) -> bool {
        // First, the type must structurally satisfy the base interface
        let interface_type_def_id = self
            .resolver(interner)
            .resolve_type_str_or_interface(interface_name_str, &self.entity_registry());

        let Some(interface_type_def_id) = interface_type_def_id else {
            return false;
        };

        // Get the type def id for the concrete type to look up implementations
        let type_def_id = {
            let arena = self.type_arena();
            arena.unwrap_class_or_struct(ty_id).map(|(id, _, _)| id)
        };

        let Some(type_def_id) = type_def_id else {
            // For non-nominal types, fall back to structural check
            return self.satisfies_interface_by_type_def_id_typeid(
                ty_id,
                interface_type_def_id,
                interner,
            );
        };

        // Check if this type has an implementation for this interface with matching type args
        let impl_type_args = self
            .entity_registry()
            .get_implementation_type_args(type_def_id, interface_type_def_id)
            .to_vec();

        if impl_type_args.is_empty() {
            // No explicit implementation found; do structural check with type arg substitution
            return self.satisfies_substituted_interface(
                ty_id,
                interface_type_def_id,
                required_type_args,
                interner,
            );
        }

        // Check that the implementation's type args match the required ones
        if impl_type_args.len() != required_type_args.len() {
            return false;
        }

        impl_type_args
            .iter()
            .zip(required_type_args.iter())
            .all(|(&impl_arg, &req_arg)| {
                // If the required arg is still a type param, accept any impl arg
                let arena = self.type_arena();
                if arena.unwrap_type_param(req_arg).is_some()
                    || arena.unwrap_type_param_ref(req_arg).is_some()
                {
                    return true;
                }
                impl_arg == req_arg
            })
    }

    /// Check if a type structurally satisfies a parameterized interface by substituting
    /// interface type params with concrete args before comparing method signatures.
    fn satisfies_substituted_interface(
        &mut self,
        ty_id: ArenaTypeId,
        interface_id: TypeDefId,
        type_args: &[ArenaTypeId],
        interner: &Interner,
    ) -> bool {
        // Get interface type params for building substitution map
        let interface_type_params = self.entity_registry().type_params(interface_id);
        if interface_type_params.len() != type_args.len() {
            // Mismatched type arg count; fall back to basic structural check
            return self.satisfies_interface_by_type_def_id_typeid(ty_id, interface_id, interner);
        }

        // Build substitution map: interface type param NameId -> concrete TypeId
        let substitutions: FxHashMap<NameId, ArenaTypeId> = interface_type_params
            .iter()
            .zip(type_args.iter())
            .map(|(&param, &arg)| (param, arg))
            .collect();

        let (is_interface, _field_ids, method_ids, extends) =
            self.entity_registry().interface_info(interface_id);

        if !is_interface {
            return false;
        }

        // Check required methods with substituted signatures
        for method_id in method_ids {
            let (has_default, name_id, signature_id) =
                self.entity_registry().method_default_name_sig(method_id);
            if has_default {
                continue;
            }
            let signature = {
                let arena = self.type_arena();
                let Some((params, ret, is_closure)) = arena.unwrap_function(signature_id) else {
                    continue;
                };
                FunctionType {
                    is_closure,
                    params_id: params.clone(),
                    return_type_id: ret,
                }
            };

            // Apply type arg substitution to the interface method signature
            let subst_sig = if substitutions.is_empty() {
                signature
            } else {
                let (subst_params, subst_ret) = {
                    let mut arena = self.type_arena_mut();
                    let params: crate::type_arena::TypeIdVec = signature
                        .params_id
                        .iter()
                        .map(|&p| arena.substitute(p, &substitutions))
                        .collect();
                    let ret = arena.substitute(signature.return_type_id, &substitutions);
                    (params, ret)
                };
                FunctionType {
                    is_closure: signature.is_closure,
                    params_id: subst_params,
                    return_type_id: subst_ret,
                }
            };

            let method_name_str = self
                .name_table()
                .last_segment_str(name_id)
                .unwrap_or_default();

            if !self.type_has_method_by_str_id(ty_id, &method_name_str, &subst_sig, interner) {
                return false;
            }
        }

        // Check parent interfaces
        for parent_id in extends {
            if !self.satisfies_interface_by_type_def_id_typeid(ty_id, parent_id, interner) {
                return false;
            }
        }

        true
    }

    /// Collect interface method info with type parameter substitutions applied.
    /// Returns (method_name, has_default, substituted_signature) for each valid method.
    fn collect_substituted_method_infos(
        &mut self,
        method_ids: &[MethodId],
        substitutions: &FxHashMap<NameId, ArenaTypeId>,
    ) -> Vec<(String, bool, FunctionType)> {
        method_ids
            .iter()
            .filter_map(|&method_id| {
                let (has_default, name_id, signature_id) =
                    self.entity_registry().method_default_name_sig(method_id);
                let name = self
                    .name_table()
                    .last_segment_str(name_id)
                    .unwrap_or_default();

                // Get original signature from arena - skip if invalid
                let (param_ids, return_id, is_closure) = {
                    let arena = self.type_arena();
                    let (params, ret, is_closure) = arena.unwrap_function(signature_id)?;
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
                            .map(|&p| arena.substitute(p, substitutions))
                            .collect();
                        let ret = arena.substitute(return_id, substitutions);
                        (params, ret)
                    };

                    // Build FunctionType from substituted TypeIds
                    FunctionType::from_ids(&subst_params, subst_ret, is_closure)
                };
                Some((name, has_default, subst_sig))
            })
            .collect()
    }

    /// Validate that a type satisfies an interface by having all required methods with correct signatures
    pub(crate) fn validate_interface_satisfaction(
        &mut self,
        type_name: Symbol,
        iface_name: Symbol,
        type_methods: &FxHashMap<String, FunctionType>,
        span: Span,
        interner: &Interner,
    ) {
        // Get the implementing type for Self substitution via Resolver
        let type_id_opt = self
            .resolver(interner)
            .resolve_type(type_name, &self.entity_registry());
        // Build implementing type directly as TypeId
        let implementing_type_id = if let Some(type_id) = type_id_opt {
            let kind = self.entity_registry().type_kind(type_id);
            match kind {
                TypeDefKind::Class => Some(
                    self.type_arena_mut()
                        .class(type_id, crate::type_arena::TypeIdVec::new()),
                ),
                TypeDefKind::Interface
                | TypeDefKind::Struct
                | TypeDefKind::ErrorType
                | TypeDefKind::Primitive
                | TypeDefKind::Alias
                | TypeDefKind::Sentinel => None,
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
            let registry = self.entity_registry();
            let method_ids = registry.type_methods(interface_type_id);
            let extends = registry.type_extends_list(interface_type_id);
            let interface_type_params = registry.type_params(interface_type_id);
            drop(registry);

            // Build substitution map for generic interface type parameters (TypeId-based)
            // E.g., MapLike<K, V> implemented as MapLike<i64, i64> → {K: i64, V: i64}
            let substitutions: FxHashMap<NameId, ArenaTypeId> =
                if let Some(impl_type_id) = type_id_opt {
                    let type_args: Vec<_> = self
                        .entity_registry()
                        .get_implementation_type_args(impl_type_id, interface_type_id)
                        .to_vec();
                    interface_type_params
                        .iter()
                        .zip(type_args.iter())
                        .map(|(param, arg)| (*param, *arg))
                        .collect()
                } else {
                    FxHashMap::default()
                };

            let method_infos = self.collect_substituted_method_infos(&method_ids, &substitutions);

            // Collect parent names upfront
            let parent_names: Vec<Option<String>> = extends
                .iter()
                .map(|&parent_id| {
                    let name_id = self.entity_registry().name_id(parent_id);
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
                        if !self.signatures_match_entity_id(
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
        &self,
        required_params_id: &[ArenaTypeId],
        required_return_id: ArenaTypeId,
        found: &FunctionType,
        implementing_type_id: ArenaTypeId,
    ) -> bool {
        // Check parameter count
        if required_params_id.len() != found.params_id.len() {
            return false;
        }
        // Check parameter types, substituting Self (SelfType placeholder) with implementing_type_id
        for (&req_param_id, &found_param_id) in
            required_params_id.iter().zip(found.params_id.iter())
        {
            let effective_req = if self.type_arena().is_self_type(req_param_id) {
                implementing_type_id
            } else {
                req_param_id
            };
            if effective_req != found_param_id {
                return false;
            }
        }
        // Check return type, substituting Self (SelfType placeholder) with implementing_type_id
        let effective_return = if self.type_arena().is_self_type(required_return_id) {
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
                let req_is_self = self.type_arena().is_self_type(req_param);
                let effective_req = if req_is_self {
                    implementing_type_id
                } else {
                    req_param
                };
                if effective_req != found_param {
                    let expected_str = if req_is_self {
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
        let return_is_self = self.type_arena().is_self_type(required_return);
        let effective_return = if return_is_self {
            implementing_type_id
        } else {
            required_return
        };
        if effective_return != found.return_type_id {
            let expected_str = if return_is_self {
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
    ) -> FxHashMap<String, FunctionType> {
        let mut method_sigs = FxHashMap::default();

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
                // Skip methods with invalid signatures (e.g., unknown types)
                let sig_opt = {
                    let arena = self.type_arena();
                    arena
                        .unwrap_function(signature_id)
                        .map(|(params, ret, is_closure)| FunctionType {
                            is_closure,
                            params_id: params.clone(),
                            return_type_id: ret,
                        })
                };
                if let Some(sig) = sig_opt {
                    method_sigs.insert(method_name_str(name_id), sig);
                }
            }

            // Methods from implement blocks
            let name_id = self.entity_registry().name_id(type_def_id);
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
