use super::super::*;
use crate::entity_defs::TypeDefKind;
use crate::implement_registry::{ExternalMethodInfo, ImplTypeId, MethodImpl};
use crate::type_arena::TypeId as ArenaTypeId;
use rustc_hash::FxHashMap;
use vole_identity::{NameId, TypeDefId, TypeParamId};

impl Analyzer {
    /// Resolve a method on a type using EntityRegistry (TypeDefId-based)
    ///
    /// This is the EntityRegistry-based version of method resolution.
    /// Returns the MethodId if found on the type or its parent interfaces.
    pub fn find_method_via_entity_registry(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId> {
        // Use EntityRegistry's resolve_method which handles inheritance
        self.entity_registry_mut()
            .resolve_method(type_def_id, method_name_id)
    }

    /// Resolve a method call using TypeId directly
    #[tracing::instrument(skip(self, interner), fields(method = %interner.resolve(method_name)))]
    pub fn resolve_method_via_entity_registry_id(
        &mut self,
        object_type_id: ArenaTypeId,
        method_name: Symbol,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        // Step 1: Check for type parameters first
        if let Some(resolved) =
            self.try_resolve_type_param_method(object_type_id, method_name, interner)
        {
            return Some(resolved);
        }

        // Step 2: Try to get TypeDefId and type_args from nominal type
        let (type_def_id, type_args_id) = self.extract_nominal_type_info(object_type_id);

        // Step 3: Try primitives if no nominal type matched
        if type_def_id.is_none()
            && object_type_id.is_primitive()
            && let Some(resolved) =
                self.resolve_method_on_primitive_type(object_type_id, method_name, interner)
        {
            return Some(resolved);
        }

        // Step 4: Try nominal type resolution
        if let Some(type_def_id) = type_def_id
            && let Some(resolved) = self.resolve_method_on_nominal_type(
                object_type_id,
                type_def_id,
                &type_args_id,
                method_name,
                interner,
            )
        {
            return Some(resolved);
        }

        // Step 5: Fallback to implement_registry for builtins
        let method_name_id = self.method_name_id(method_name, interner);
        self.resolve_method_via_implement_registry(
            object_type_id,
            method_name,
            method_name_id,
            interner,
        )
    }

    /// Try to resolve a method on a type parameter
    fn try_resolve_type_param_method(
        &mut self,
        object_type_id: ArenaTypeId,
        method_name: Symbol,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        enum TypeParamResult {
            TypeParam(NameId),
            TypeParamRef(TypeParamId),
            None,
        }

        let type_param_result = {
            let arena = self.type_arena();
            if let Some(param_name_id) = arena.unwrap_type_param(object_type_id) {
                TypeParamResult::TypeParam(param_name_id)
            } else if let Some(type_param_id) = arena.unwrap_type_param_ref(object_type_id) {
                TypeParamResult::TypeParamRef(type_param_id)
            } else {
                TypeParamResult::None
            }
        };

        match type_param_result {
            TypeParamResult::TypeParam(param_name_id) => {
                self.resolve_method_on_type_param(param_name_id, method_name, interner)
            }
            TypeParamResult::TypeParamRef(type_param_id) => {
                let info = self.type_param_stack.get_by_type_param_id(type_param_id)?;
                self.resolve_method_on_type_param(info.name_id, method_name, interner)
            }
            TypeParamResult::None => None,
        }
    }

    /// Extract TypeDefId and type arguments from a nominal type
    fn extract_nominal_type_info(
        &self,
        object_type_id: ArenaTypeId,
    ) -> (Option<TypeDefId>, Vec<ArenaTypeId>) {
        let arena = self.type_arena();
        if let Some((id, args, _kind)) = arena.unwrap_nominal(object_type_id) {
            (Some(id), args.to_vec())
        } else {
            (None, vec![])
        }
    }

    /// Build substitution map using TypeId for arena-based substitution
    fn build_substitutions_id(
        &self,
        type_def_id: TypeDefId,
        type_args_id: &[crate::type_arena::TypeId],
    ) -> FxHashMap<NameId, crate::type_arena::TypeId> {
        self.entity_registry_mut()
            .substitution_map_id(type_def_id, type_args_id)
    }

    /// Apply TypeId substitutions to a function type using arena-based substitution
    fn apply_substitutions_id(
        &self,
        func_type: &FunctionType,
        substitutions: &FxHashMap<NameId, crate::type_arena::TypeId>,
    ) -> FunctionType {
        if substitutions.is_empty() {
            return func_type.clone();
        }

        // Substitute using arena
        let (new_params_id, new_return_type_id) = {
            let mut arena = self.type_arena_mut();
            let params: crate::type_arena::TypeIdVec = func_type
                .params_id
                .iter()
                .map(|&p| arena.substitute(p, substitutions))
                .collect();
            let ret = arena.substitute(func_type.return_type_id, substitutions);
            (params, ret)
        };

        // Build FunctionType from substituted TypeIds
        FunctionType::from_ids(&new_params_id, new_return_type_id, func_type.is_closure)
    }

    /// Map primitive TypeId to NameId for method binding lookup
    fn name_id_for_primitive_type_id(&self, type_id: ArenaTypeId) -> Option<NameId> {
        let primitives = &self.name_table().primitives;
        match type_id {
            ArenaTypeId::I8 => Some(primitives.i8),
            ArenaTypeId::I16 => Some(primitives.i16),
            ArenaTypeId::I32 => Some(primitives.i32),
            ArenaTypeId::I64 => Some(primitives.i64),
            ArenaTypeId::I128 => Some(primitives.i128),
            ArenaTypeId::U8 => Some(primitives.u8),
            ArenaTypeId::U16 => Some(primitives.u16),
            ArenaTypeId::U32 => Some(primitives.u32),
            ArenaTypeId::U64 => Some(primitives.u64),
            ArenaTypeId::F32 => Some(primitives.f32),
            ArenaTypeId::F64 => Some(primitives.f64),
            ArenaTypeId::BOOL => Some(primitives.bool),
            ArenaTypeId::STRING => Some(primitives.string),
            _ => None,
        }
    }

    /// Get the Symbol for a type by its NameId
    fn get_type_symbol_by_name_id(&self, name_id: NameId, interner: &Interner) -> Option<Symbol> {
        // Get the name string from name_table and look up Symbol via interner
        if let Some(name_str) = self.name_table().last_segment_str(name_id) {
            interner.lookup(&name_str)
        } else {
            None
        }
    }

    /// Resolve a method on a type parameter by looking up its constraint interfaces.
    /// Returns an InterfaceMethod resolution since the actual concrete type will be
    /// substituted at monomorphization time.
    fn resolve_method_on_type_param(
        &mut self,
        param_name_id: NameId,
        method_name: Symbol,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        let method_name_id = self.method_name_id(method_name, interner);
        let method_name_str = interner.resolve(method_name);
        tracing::trace!(
            ?param_name_id,
            method = %method_name_str,
            "resolve_method_on_type_param: starting"
        );

        // Look up the type parameter in type_param_stack
        let type_param_scope = self.type_param_stack.current()?;

        // Find the type parameter by name_id
        let type_param = type_param_scope
            .params()
            .iter()
            .find(|tp| tp.name_id == param_name_id);

        let type_param = match type_param {
            Some(tp) => tp,
            None => {
                tracing::trace!(?param_name_id, "type param not found in scope");
                return None;
            }
        };

        // Get the constraint (must be an interface constraint for method calls)
        let constraint = match type_param.constraint.as_ref() {
            Some(c) => c,
            None => {
                tracing::trace!(?param_name_id, "type param has no constraint");
                return None;
            }
        };

        let constraint_interfaces: Vec<Symbol> = match constraint {
            crate::generic::TypeConstraint::Interface(symbols) => symbols.clone(),
            other => {
                tracing::trace!(?param_name_id, constraint = ?other, "constraint is not interface-based");
                return None; // Union/Structural constraints don't support method calls this way
            }
        };

        tracing::trace!(
            num_constraints = constraint_interfaces.len(),
            "searching constraint interfaces"
        );

        // Try to find the method in one of the constraint interfaces
        for interface_sym in &constraint_interfaces {
            let interface_name = interner.resolve(*interface_sym);
            tracing::trace!(%interface_name, "checking interface");

            // Use resolve_type_or_interface to handle prelude interfaces like Hashable
            // Get interface_type_id first to drop the ResolverGuard before type_arena_mut
            let interface_type_id = self
                .resolver(interner)
                .resolve_type_or_interface(*interface_sym, &self.entity_registry());

            let Some(interface_type_id) = interface_type_id else {
                tracing::trace!(%interface_name, "could not resolve interface");
                continue;
            };

            if let Some(resolved) = self.find_method_in_constraint_interface(
                interface_type_id,
                *interface_sym,
                method_name,
                method_name_id,
                param_name_id,
                method_name_str,
            ) {
                return Some(resolved);
            }
        }

        tracing::trace!(
            method = %method_name_str,
            ?param_name_id,
            "method not found on any constraint interface"
        );
        None
    }

    /// Find a method in a constraint interface for type parameter resolution
    fn find_method_in_constraint_interface(
        &mut self,
        interface_type_id: TypeDefId,
        interface_sym: Symbol,
        method_name: Symbol,
        method_name_id: NameId,
        param_name_id: NameId,
        method_name_str: &str,
    ) -> Option<ResolvedMethod> {
        let method_ids = {
            let registry = self.entity_registry();
            let interface_def = registry.get_type(interface_type_id);
            tracing::trace!(
                ?interface_type_id,
                num_methods = interface_def.methods.len(),
                "found interface def"
            );
            interface_def.methods.clone()
        };

        for method_id in method_ids {
            let (def_method_name_id, method_signature_id) = {
                let registry = self.entity_registry();
                let method_def = registry.get_method(method_id);
                (method_def.name_id, method_def.signature_id)
            };
            let method_def_name = self
                .name_table()
                .last_segment_str(def_method_name_id)
                .unwrap_or_default();

            tracing::trace!(
                ?method_id,
                found_method = %method_def_name,
                looking_for = %method_name_str,
                "checking method"
            );

            if method_def_name != method_name_str {
                continue;
            }

            let interface_name_str = self
                .name_table()
                .last_segment_str(self.entity_registry().get_type(interface_type_id).name_id)
                .unwrap_or_default();
            tracing::trace!(
                ?method_id,
                %interface_name_str,
                "found method on constraint interface"
            );

            return Some(self.build_interface_method_resolution(
                interface_type_id,
                interface_sym,
                method_name,
                method_name_id,
                param_name_id,
                method_signature_id,
            ));
        }

        None
    }

    /// Build the ResolvedMethod::InterfaceMethod for a type parameter constraint
    fn build_interface_method_resolution(
        &mut self,
        interface_type_id: TypeDefId,
        interface_sym: Symbol,
        method_name: Symbol,
        method_name_id: NameId,
        param_name_id: NameId,
        method_signature_id: ArenaTypeId,
    ) -> ResolvedMethod {
        // Substitute SelfType placeholders with the type parameter.
        // The interface signature has Self as placeholder, but when
        // called through a constraint T: Interface, Self should be T.
        let self_type_id = self.type_arena_mut().type_param(param_name_id);
        let (params, ret, is_closure) = {
            let arena = self.type_arena();
            let (params, ret, is_closure) = arena
                .unwrap_function(method_signature_id)
                .expect("method signature must be a function type");
            (params.clone(), ret, is_closure)
        };

        // Substitute SelfType in params and return type
        let substituted_params: smallvec::SmallVec<[_; 4]> = params
            .iter()
            .map(|&p| self.type_arena_mut().substitute_self(p, self_type_id))
            .collect();
        let substituted_ret = self.type_arena_mut().substitute_self(ret, self_type_id);
        let func_type = FunctionType {
            is_closure,
            params_id: substituted_params,
            return_type_id: substituted_ret,
        };
        let return_type_id = func_type.return_type_id;
        let func_type_id = func_type.intern(&mut self.type_arena_mut());

        // Compute vtable slot index for direct dispatch
        let method_index = self
            .entity_registry()
            .interface_method_slot(interface_type_id, method_name_id)
            .unwrap_or(0);

        ResolvedMethod::InterfaceMethod {
            method_name_id,
            interface_name: interface_sym,
            method_name,
            func_type_id,
            return_type_id,
            interface_type_def_id: interface_type_id,
            method_index,
        }
    }

    /// Get the function type for a functional interface by TypeDefId
    pub(crate) fn get_functional_interface_type_by_type_def_id(
        &self,
        type_def_id: TypeDefId,
    ) -> Option<FunctionType> {
        let method_id = self.entity_registry().is_functional(type_def_id)?;
        let signature_id = {
            let registry = self.entity_registry();
            registry.get_method(method_id).signature_id
        };
        // Build from arena - get params and return type from signature_id
        let arena = self.type_arena();
        let (params, ret, _) = arena
            .unwrap_function(signature_id)
            .expect("method signature must be a function type");
        Some(FunctionType::from_ids(params, ret, true)) // is_closure for functional interface
    }

    /// Resolve a method on a primitive type (i64, f64, bool, string, etc.)
    fn resolve_method_on_primitive_type(
        &mut self,
        object_type_id: ArenaTypeId,
        method_name: Symbol,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        let primitive_name_id = self.name_id_for_primitive_type_id(object_type_id)?;
        let tdef_id = {
            let registry = self.entity_registry();
            registry.type_by_name(primitive_name_id)?
        };

        let method_name_id = self.method_name_id(method_name, interner);
        // Clone binding data to drop EntityRegistry borrow before using name_table
        let binding_result = self
            .entity_registry_mut()
            .find_method_binding_with_interface(tdef_id, method_name_id)
            .map(|(interface_id, binding)| (interface_id, binding.clone()));

        let (interface_id, binding) = binding_result?;
        let interface_name_id = self.entity_registry().get_type(interface_id).name_id;
        let trait_name = self
            .name_table()
            .last_segment_str(interface_name_id)
            .and_then(|s| interner.lookup(&s));

        // Substitute Self placeholder with the concrete primitive type.
        // Interface methods like `equals(other: Self)` need Self -> i64, etc.
        let substituted_params: smallvec::SmallVec<[_; 4]> = binding
            .func_type
            .params_id
            .iter()
            .map(|&p| self.type_arena_mut().substitute_self(p, object_type_id))
            .collect();
        let substituted_ret = self
            .type_arena_mut()
            .substitute_self(binding.func_type.return_type_id, object_type_id);

        let func_type = FunctionType {
            is_closure: binding.func_type.is_closure,
            params_id: substituted_params,
            return_type_id: substituted_ret,
        };
        let return_type_id = func_type.return_type_id;
        let func_type_id = func_type.intern(&mut self.type_arena_mut());

        Some(ResolvedMethod::Implemented {
            type_def_id: Some(tdef_id),
            method_name_id,
            trait_name,
            func_type_id,
            return_type_id,
            is_builtin: binding.is_builtin,
            external_info: binding.external_info,
            concrete_return_hint: None,
        })
    }

    /// Resolve a method on a nominal type (class, record, or interface)
    fn resolve_method_on_nominal_type(
        &mut self,
        object_type_id: ArenaTypeId,
        type_def_id: TypeDefId,
        type_args_id: &[ArenaTypeId],
        method_name: Symbol,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        let method_name_id = self.method_name_id(method_name, interner);

        // Try to find the method via EntityRegistry
        if let Some(method_id) = self.find_method_via_entity_registry(type_def_id, method_name_id)
            && let Some(resolved) = self.resolve_found_method(
                object_type_id,
                type_def_id,
                type_args_id,
                method_id,
                method_name_id,
                method_name,
                interner,
            )
        {
            return Some(resolved);
        }

        // Check interface method bindings (for default methods on classes/records)
        if let Some(resolved) =
            self.resolve_method_from_binding(type_def_id, method_name_id, interner)
        {
            return Some(resolved);
        }

        // Check default methods from implemented interfaces
        self.resolve_default_method_from_interfaces(
            type_def_id,
            method_name,
            method_name_id,
            interner,
        )
    }

    /// Resolve a method that was found via EntityRegistry
    #[allow(clippy::too_many_arguments)]
    fn resolve_found_method(
        &mut self,
        object_type_id: ArenaTypeId,
        type_def_id: TypeDefId,
        type_args_id: &[ArenaTypeId],
        method_id: MethodId,
        method_name_id: NameId,
        method_name: Symbol,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        // Extract all needed method data upfront
        let (
            method_defining_type_id,
            method_signature_id,
            method_has_default,
            method_external_binding,
        ) = {
            let registry = self.entity_registry();
            let method_def = registry.get_method(method_id);
            (
                method_def.defining_type,
                method_def.signature_id,
                method_def.has_default,
                method_def.external_binding,
            )
        };
        let (defining_type_kind, defining_type_name_id) = {
            let registry = self.entity_registry();
            let defining_type = registry.get_type(method_defining_type_id);
            (defining_type.kind, defining_type.name_id)
        };

        // Build substitutions for generic types
        let substitutions = if !type_args_id.is_empty() {
            self.build_substitutions_id(type_def_id, type_args_id)
        } else {
            FxHashMap::default()
        };

        // Get signature from arena
        let method_sig = {
            let arena = self.type_arena();
            let (params, ret, is_closure) = arena
                .unwrap_function(method_signature_id)
                .expect("method signature must be a function type");
            FunctionType {
                is_closure,
                params_id: params.clone(),
                return_type_id: ret,
            }
        };
        let func_type = self.apply_substitutions_id(&method_sig, &substitutions);
        let return_type_id = func_type.return_type_id;
        let func_type_id = func_type.intern(&mut self.type_arena_mut());

        // Determine the resolution type based on the defining type's kind
        match defining_type_kind {
            TypeDefKind::Interface => self.resolve_interface_method(
                object_type_id,
                type_def_id,
                method_defining_type_id,
                defining_type_name_id,
                method_name_id,
                method_name,
                method_has_default,
                method_external_binding,
                func_type_id,
                return_type_id,
                interner,
            ),
            TypeDefKind::Class | TypeDefKind::Record => {
                // Direct method on class/record
                Some(ResolvedMethod::Direct {
                    type_def_id: Some(type_def_id),
                    method_name_id,
                    func_type_id,
                    return_type_id,
                    method_id: Some(method_id),
                })
            }
            _ => None,
        }
    }

    /// Resolve a method defined on an interface
    #[allow(clippy::too_many_arguments)]
    fn resolve_interface_method(
        &mut self,
        object_type_id: ArenaTypeId,
        type_def_id: TypeDefId,
        method_defining_type_id: TypeDefId,
        defining_type_name_id: NameId,
        method_name_id: NameId,
        method_name: Symbol,
        method_has_default: bool,
        method_external_binding: Option<ExternalMethodInfo>,
        func_type_id: ArenaTypeId,
        return_type_id: ArenaTypeId,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        use crate::type_arena::NominalKind;

        // Check if object_type is a nominal type and what kind
        let nominal_kind = {
            let arena = self.type_arena();
            arena
                .unwrap_nominal(object_type_id)
                .map(|(_, _, kind)| kind)
        };
        let is_interface_type = nominal_kind == Some(NominalKind::Interface);
        let is_class_or_record = matches!(
            nominal_kind,
            Some(NominalKind::Class) | Some(NominalKind::Record)
        );

        // For external default methods on CONCRETE types (not interface types)
        if method_has_default
            && method_external_binding.is_some()
            && !is_interface_type
            && let Some(resolved) = self.resolve_external_default_method(
                type_def_id,
                defining_type_name_id,
                method_name_id,
                method_name,
                func_type_id,
                return_type_id,
                method_external_binding,
                interner,
            )
        {
            return Some(resolved);
        }

        // For non-external default methods on concrete types (Class/Record)
        if method_has_default
            && is_class_or_record
            && let Some(resolved) = self.resolve_non_external_default_method(
                type_def_id,
                defining_type_name_id,
                method_name_id,
                method_name,
                func_type_id,
                return_type_id,
                interner,
            )
        {
            return Some(resolved);
        }

        // For interface types and non-default methods, use vtable dispatch
        let interface_sym = self.get_type_symbol_by_name_id(defining_type_name_id, interner)?;
        // Compute vtable slot index for direct dispatch
        let method_index = self
            .entity_registry()
            .interface_method_slot(method_defining_type_id, method_name_id)
            .unwrap_or(0);
        Some(ResolvedMethod::InterfaceMethod {
            method_name_id,
            interface_name: interface_sym,
            method_name,
            func_type_id,
            return_type_id,
            interface_type_def_id: method_defining_type_id,
            method_index,
        })
    }

    /// Resolve an external default method (has `external` binding)
    #[allow(clippy::too_many_arguments)]
    fn resolve_external_default_method(
        &self,
        type_def_id: TypeDefId,
        defining_type_name_id: NameId,
        method_name_id: NameId,
        method_name: Symbol,
        func_type_id: ArenaTypeId,
        return_type_id: ArenaTypeId,
        method_external_binding: Option<ExternalMethodInfo>,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        let type_name_id = {
            let registry = self.entity_registry();
            registry.get_type(type_def_id).name_id
        };
        let type_sym = self.get_type_symbol_by_name_id(type_name_id, interner)?;
        let interface_sym = self.get_type_symbol_by_name_id(defining_type_name_id, interner)?;
        Some(ResolvedMethod::DefaultMethod {
            type_def_id: Some(type_def_id),
            method_name_id,
            interface_name: interface_sym,
            type_name: type_sym,
            method_name,
            func_type_id,
            return_type_id,
            external_info: method_external_binding,
        })
    }

    /// Resolve a non-external default method on a class or record
    #[allow(clippy::too_many_arguments)]
    fn resolve_non_external_default_method(
        &self,
        type_def_id: TypeDefId,
        defining_type_name_id: NameId,
        method_name_id: NameId,
        method_name: Symbol,
        func_type_id: ArenaTypeId,
        return_type_id: ArenaTypeId,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        let type_name_id = {
            let registry = self.entity_registry();
            registry.get_type(type_def_id).name_id
        };
        let type_sym = self.get_type_symbol_by_name_id(type_name_id, interner)?;
        let interface_sym = self.get_type_symbol_by_name_id(defining_type_name_id, interner)?;
        Some(ResolvedMethod::DefaultMethod {
            type_def_id: Some(type_def_id),
            method_name_id,
            interface_name: interface_sym,
            type_name: type_sym,
            method_name,
            func_type_id,
            return_type_id,
            external_info: None,
        })
    }

    /// Resolve a method from interface method bindings
    fn resolve_method_from_binding(
        &mut self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        // Extract binding data first to drop entity_registry_mut borrow
        let binding_result = self
            .entity_registry_mut()
            .find_method_binding_with_interface(type_def_id, method_name_id)
            .map(|(interface_id, binding)| (interface_id, binding.clone()));

        let (interface_id, binding) = binding_result?;
        let interface_name_id = self.entity_registry().get_type(interface_id).name_id;
        let trait_name = self
            .name_table()
            .last_segment_str(interface_name_id)
            .and_then(|s| interner.lookup(&s));
        let return_type_id = binding.func_type.return_type_id;
        let func_type_id = binding.func_type.intern(&mut self.type_arena_mut());

        Some(ResolvedMethod::Implemented {
            type_def_id: Some(type_def_id),
            method_name_id,
            trait_name,
            func_type_id,
            return_type_id,
            is_builtin: binding.is_builtin,
            external_info: binding.external_info,
            concrete_return_hint: None,
        })
    }

    /// Resolve a default method from implemented interfaces
    fn resolve_default_method_from_interfaces(
        &mut self,
        type_def_id: TypeDefId,
        method_name: Symbol,
        method_name_id: NameId,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        let type_name_id = {
            let registry = self.entity_registry();
            registry.get_type(type_def_id).name_id
        };
        let type_sym = self.get_type_symbol_by_name_id(type_name_id, interner)?;
        let method_name_str = interner.resolve(method_name);
        let interface_ids = self
            .entity_registry()
            .get_implemented_interfaces(type_def_id);

        for interface_id in interface_ids {
            if let Some(resolved) = self.find_default_method_in_interface(
                type_def_id,
                interface_id,
                method_name,
                method_name_id,
                type_sym,
                method_name_str,
                interner,
            ) {
                return Some(resolved);
            }
        }

        None
    }

    /// Find a default method in an implemented interface
    #[allow(clippy::too_many_arguments)]
    fn find_default_method_in_interface(
        &mut self,
        type_def_id: TypeDefId,
        interface_id: TypeDefId,
        method_name: Symbol,
        method_name_id: NameId,
        type_sym: Symbol,
        method_name_str: &str,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        let (interface_name_id, method_ids) = {
            let registry = self.entity_registry();
            let interface_def = registry.get_type(interface_id);
            (interface_def.name_id, interface_def.methods.clone())
        };

        for method_id in method_ids {
            let (
                def_method_name_id,
                method_has_default,
                method_signature_id,
                method_external_binding,
            ) = {
                let registry = self.entity_registry();
                let method = registry.get_method(method_id);
                (
                    method.name_id,
                    method.has_default,
                    method.signature_id,
                    method.external_binding,
                )
            };

            let def_method_name = self
                .name_table()
                .last_segment_str(def_method_name_id)
                .unwrap_or_default();

            if def_method_name != method_name_str || !method_has_default {
                continue;
            }

            // Get interface name Symbol
            let interface_name = self
                .name_table()
                .last_segment_str(interface_name_id)
                .and_then(|s| interner.lookup(&s))
                .unwrap_or(Symbol(0));

            let func_type = {
                let arena = self.type_arena();
                let (params, ret, is_closure) = arena
                    .unwrap_function(method_signature_id)
                    .expect("method signature must be a function type");
                FunctionType {
                    is_closure,
                    params_id: params.clone(),
                    return_type_id: ret,
                }
            };
            let return_type_id = func_type.return_type_id;
            let func_type_id = func_type.intern(&mut self.type_arena_mut());

            return Some(ResolvedMethod::DefaultMethod {
                type_def_id: Some(type_def_id),
                method_name_id,
                interface_name,
                type_name: type_sym,
                method_name,
                func_type_id,
                return_type_id,
                external_info: method_external_binding,
            });
        }

        None
    }

    /// Fallback to implement_registry for builtins (Array.length, String.length, etc.)
    fn resolve_method_via_implement_registry(
        &mut self,
        object_type_id: ArenaTypeId,
        method_name: Symbol,
        method_name_id: NameId,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        let impl_type_id = {
            let arena = self.type_arena();
            ImplTypeId::from_type_id(object_type_id, &arena, &self.entity_registry())
        };

        // Clone method impl data first to drop the registry borrow before calling type_arena_mut
        let method_impl = impl_type_id.and_then(|impl_type_id| {
            self.implement_registry()
                .get_method(&impl_type_id, method_name_id)
                .cloned()
        })?;

        let return_type_id = method_impl.func_type.return_type_id;
        let func_type_id = method_impl.func_type.intern(&mut self.type_arena_mut());

        // Compute concrete_return_hint for builtin iterator methods.
        let concrete_return_hint =
            self.compute_iterator_return_hint(object_type_id, method_name, &method_impl, interner);

        Some(ResolvedMethod::Implemented {
            type_def_id: None, // Builtins don't have a TypeDefId
            method_name_id,
            trait_name: method_impl.trait_name,
            func_type_id,
            return_type_id,
            is_builtin: method_impl.is_builtin,
            external_info: method_impl.external_info,
            concrete_return_hint,
        })
    }

    /// Compute concrete_return_hint for builtin iterator methods
    fn compute_iterator_return_hint(
        &mut self,
        object_type_id: ArenaTypeId,
        method_name: Symbol,
        method_impl: &MethodImpl,
        interner: &Interner,
    ) -> Option<ArenaTypeId> {
        method_impl.external_info?;

        let method_name_str = interner.resolve(method_name);
        if method_name_str != "iter" {
            return None;
        }

        // Determine the iterator element type based on the object type
        let element_type = {
            let arena = self.type_arena();
            if let Some(elem) = arena.unwrap_array(object_type_id) {
                // array.iter() -> RuntimeIterator(element)
                Some(elem)
            } else if object_type_id == arena.string() {
                // string.iter() -> RuntimeIterator(string) for char iteration
                Some(arena.string())
            } else if object_type_id == arena.range() {
                // range.iter() -> RuntimeIterator(i64)
                Some(arena.i64())
            } else {
                None
            }
        };

        element_type.map(|elem| self.type_arena_mut().runtime_iterator(elem))
    }
}
