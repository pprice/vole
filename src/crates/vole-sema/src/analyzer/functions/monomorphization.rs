// src/sema/analyzer/functions/monomorphization.rs
//! Monomorphization: propagation and derivation of concrete monomorph
//! instances for class/static/implement-block methods.
//!
//! Free-function monomorphization is handled by the VIR monomorph pass
//! (see `vole_vir::monomorph`).  Generic body analysis for Pass 2a lives
//! in `functions/generic_vir.rs`.  This module handles class/static
//! method propagation/derivation and implement-block method registration.

use super::super::*;
use crate::generic::{ImplementMethodMonomorphInstance, ImplementMethodMonomorphKey};

impl Analyzer {
    /// Propagate concrete type substitutions to class method monomorphs created
    /// from self-method calls inside generic class methods.
    ///
    /// When sema analyzes method bodies, `self` has abstract type params (e.g., `Box<T>`).
    /// A call like `self.inner()` records a monomorph with identity substitutions
    /// `{T: TypeParam(T)}`. When a concrete monomorph exists for `outer()` with `{T: i64}`,
    /// this pass creates a matching concrete monomorph for `inner()` with `{T: i64}`.
    ///
    /// Iterates to fixpoint to handle transitive chains: a() -> self.b() -> self.c().
    pub(in crate::analyzer) fn propagate_class_method_monomorphs(&mut self) {
        loop {
            let new_instances = self.derive_concrete_class_method_monomorphs();
            if new_instances.is_empty() {
                break;
            }

            for (key, instance) in new_instances {
                self.entity_registry_mut()
                    .class_method_monomorph_cache
                    .insert(key, instance);
            }
        }
    }

    /// Propagate concrete substitutions to static method monomorphs created
    /// from static calls inside generic class static methods.
    ///
    /// Example: `Map.new<K, V>()` calls `Map.with_capacity<K, V>(8)` and records
    /// an identity monomorph for `with_capacity`. When a concrete caller exists
    /// (e.g., `Map.new<i64, string>`), derive `Map.with_capacity<i64, string>`.
    pub(in crate::analyzer) fn propagate_static_method_monomorphs(&mut self) {
        loop {
            let new_instances = self.derive_concrete_static_method_monomorphs();
            if new_instances.is_empty() {
                break;
            }

            for (key, instance) in new_instances {
                self.entity_registry_mut()
                    .static_method_monomorph_cache
                    .insert(key, instance);
            }
        }
    }

    /// Single iteration: derive concrete static monomorphs from identity-substituted ones.
    ///
    /// Collects concrete substitutions from ALL classes and matches them against
    /// identity instances by TypeParam name, enabling cross-class propagation
    /// (e.g., Task.state<i64> calling Channel.buffered<T>).
    fn derive_concrete_static_method_monomorphs(
        &mut self,
    ) -> Vec<(
        StaticMethodMonomorphKey,
        crate::generic::StaticMethodMonomorphInstance,
    )> {
        let all_instances: Vec<crate::generic::StaticMethodMonomorphInstance> = self
            .entity_registry()
            .static_method_monomorph_cache
            .collect_instances();

        let mut all_concrete_subs: Vec<FxHashMap<NameId, ArenaTypeId>> = Vec::new();
        let mut identity_instances: Vec<&crate::generic::StaticMethodMonomorphInstance> =
            Vec::new();

        {
            let arena = self.type_arena();
            for inst in &all_instances {
                let has_type_param_value = inst
                    .substitutions
                    .values()
                    .any(|&v| arena.unwrap_type_param(v).is_some());
                if has_type_param_value {
                    identity_instances.push(inst);
                } else if !inst.substitutions.is_empty() {
                    all_concrete_subs.push(inst.substitutions.clone());
                }
            }
        }

        all_concrete_subs.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
        all_concrete_subs.dedup();

        let mut new_instances = Vec::new();

        for identity_inst in &identity_instances {
            for concrete_subs in &all_concrete_subs {
                let composed_subs =
                    self.compose_substitutions(&identity_inst.substitutions, concrete_subs);

                // Skip if composition still contains type params (incomplete match).
                {
                    let arena = self.type_arena();
                    if composed_subs
                        .values()
                        .any(|&v| arena.unwrap_type_param(v).is_some())
                    {
                        continue;
                    }
                }

                let Some(key) = self.build_static_method_monomorph_key(
                    identity_inst.class_name,
                    identity_inst.method_name,
                    &composed_subs,
                ) else {
                    continue;
                };

                if self
                    .entity_registry()
                    .static_method_monomorph_cache
                    .contains(&key)
                {
                    continue;
                }

                if new_instances
                    .iter()
                    .any(|(existing_key, _)| *existing_key == key)
                {
                    continue;
                }

                let Some(instance) =
                    self.create_derived_static_method_monomorph(identity_inst, &composed_subs)
                else {
                    continue;
                };

                tracing::debug!(
                    class = ?identity_inst.class_name,
                    method = ?identity_inst.method_name,
                    subs = ?composed_subs,
                    "propagated concrete static method monomorph"
                );

                new_instances.push((key, instance));
            }
        }

        new_instances
    }

    /// Single iteration: derive concrete monomorphs from identity-substituted ones.
    ///
    /// Collects concrete substitutions from ALL classes and matches them against
    /// identity instances by TypeParam name, enabling cross-class propagation.
    /// Returns a list of (key, instance) pairs to insert into the cache.
    fn derive_concrete_class_method_monomorphs(
        &mut self,
    ) -> Vec<(
        ClassMethodMonomorphKey,
        crate::generic::ClassMethodMonomorphInstance,
    )> {
        let all_instances: Vec<crate::generic::ClassMethodMonomorphInstance> = self
            .entity_registry()
            .class_method_monomorph_cache
            .collect_instances();

        // Partition into concrete and identity substitutions.
        let mut all_concrete_subs: Vec<FxHashMap<NameId, ArenaTypeId>> = Vec::new();
        let mut identity_instances: Vec<&crate::generic::ClassMethodMonomorphInstance> = Vec::new();

        {
            let arena = self.type_arena();
            for inst in &all_instances {
                let has_type_param_value = inst
                    .substitutions
                    .values()
                    .any(|&v| arena.unwrap_type_param(v).is_some());
                if has_type_param_value {
                    identity_instances.push(inst);
                } else if !inst.substitutions.is_empty() {
                    all_concrete_subs.push(inst.substitutions.clone());
                }
            }
        }

        all_concrete_subs.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
        all_concrete_subs.dedup();

        let mut new_instances = Vec::new();

        for identity_inst in &identity_instances {
            for concrete_subs in &all_concrete_subs {
                let composed_subs =
                    self.compose_substitutions(&identity_inst.substitutions, concrete_subs);

                // Skip if composition still contains type params (incomplete match).
                {
                    let arena = self.type_arena();
                    if composed_subs
                        .values()
                        .any(|&v| arena.unwrap_type_param(v).is_some())
                    {
                        continue;
                    }
                }

                let Some(key) = self.build_class_method_monomorph_key(
                    identity_inst.class_name,
                    identity_inst.method_name,
                    &composed_subs,
                ) else {
                    continue;
                };

                if self
                    .entity_registry()
                    .class_method_monomorph_cache
                    .contains(&key)
                {
                    continue;
                }

                if new_instances
                    .iter()
                    .any(|(existing_key, _)| *existing_key == key)
                {
                    continue;
                }

                let type_keys = key.type_keys.clone();
                let Some(instance) = self.create_derived_class_method_monomorph(
                    identity_inst,
                    &composed_subs,
                    &type_keys,
                ) else {
                    continue;
                };

                tracing::debug!(
                    class = ?identity_inst.class_name,
                    method = ?identity_inst.method_name,
                    subs = ?composed_subs,
                    "propagated concrete class method monomorph"
                );

                new_instances.push((key, instance));
            }
        }

        new_instances
    }

    /// Compose two substitution maps: apply `concrete` to the values of `identity`.
    ///
    /// Example:
    /// identity = {T: TypeParam(T)}, concrete = {T: i64} => {T: i64}
    fn compose_substitutions(
        &self,
        identity: &FxHashMap<NameId, ArenaTypeId>,
        concrete: &FxHashMap<NameId, ArenaTypeId>,
    ) -> FxHashMap<NameId, ArenaTypeId> {
        let arena = self.type_arena();
        let mut composed = FxHashMap::default();

        for (&name_id, &type_id) in identity {
            if let Some(param_name_id) = arena.unwrap_type_param(type_id)
                && let Some(&concrete_type_id) = concrete.get(&param_name_id)
            {
                composed.insert(name_id, concrete_type_id);
                continue;
            }
            composed.insert(name_id, type_id);
        }

        composed
    }

    /// Build a class-method monomorph key using the class's declared type param order.
    fn build_class_method_monomorph_key(
        &self,
        class_name: NameId,
        method_name: NameId,
        substitutions: &FxHashMap<NameId, ArenaTypeId>,
    ) -> Option<ClassMethodMonomorphKey> {
        let registry = self.entity_registry();
        let type_def_id = registry.type_by_name(class_name)?;
        let generic_info = registry.type_generic_info(type_def_id)?;
        let type_keys: Vec<VirTypeId> = generic_info
            .type_params
            .iter()
            .filter_map(|tp| substitutions.get(&tp.name_id).copied())
            .map(VirTypeId::from_type_id)
            .collect();
        Some(ClassMethodMonomorphKey::new(
            class_name,
            method_name,
            type_keys,
        ))
    }

    /// Build a static-method monomorph key using class and method type param order.
    fn build_static_method_monomorph_key(
        &self,
        class_name: NameId,
        method_name: NameId,
        substitutions: &FxHashMap<NameId, ArenaTypeId>,
    ) -> Option<StaticMethodMonomorphKey> {
        let registry = self.entity_registry();
        let type_def_id = registry.type_by_name(class_name)?;
        let class_type_keys: Vec<VirTypeId> = registry
            .type_generic_info(type_def_id)
            .map(|generic_info| {
                generic_info
                    .type_params
                    .iter()
                    .filter_map(|tp| substitutions.get(&tp.name_id).copied())
                    .map(VirTypeId::from_type_id)
                    .collect()
            })
            .unwrap_or_default();

        let method_id = registry.find_static_method_on_type(type_def_id, method_name)?;
        let method = registry.get_method(method_id);
        let method_type_keys: Vec<VirTypeId> = method
            .method_type_params
            .iter()
            .filter_map(|tp| substitutions.get(&tp.name_id).copied())
            .map(VirTypeId::from_type_id)
            .collect();

        Some(StaticMethodMonomorphKey::new(
            class_name,
            method_name,
            class_type_keys,
            method_type_keys,
        ))
    }

    /// Create a derived concrete class-method monomorph instance.
    fn create_derived_class_method_monomorph(
        &mut self,
        identity_inst: &crate::generic::ClassMethodMonomorphInstance,
        concrete_subs: &FxHashMap<NameId, ArenaTypeId>,
        type_keys: &[VirTypeId],
    ) -> Option<crate::generic::ClassMethodMonomorphInstance> {
        let type_def_id = self
            .entity_registry()
            .type_by_name(identity_inst.class_name)?;
        let method_id = self
            .entity_registry()
            .find_method_on_type(type_def_id, identity_inst.method_name)?;
        let signature_id = self.entity_registry().method_signature(method_id);

        let (params, ret, is_closure) = {
            let arena = self.type_arena();
            let (params, ret, is_closure) = arena.unwrap_function(signature_id)?;
            (params.to_vec(), ret, is_closure)
        };

        let (subst_params, subst_ret) = {
            let mut arena = self.type_arena_mut();
            let subst_params = params
                .iter()
                .map(|&param_type_id| arena.substitute(param_type_id, concrete_subs))
                .collect::<Vec<_>>();
            let subst_ret = arena.substitute(ret, concrete_subs);
            (subst_params, subst_ret)
        };
        let func_type = FunctionType::from_ids(&subst_params, subst_ret, is_closure);

        // Eagerly substitute field types so codegen can do immutable lookup_substitute.
        let generic_info = { self.entity_registry().type_generic_info(type_def_id) };
        if let Some(generic_info) = generic_info {
            let field_types = generic_info.field_types;
            let mut arena = self.type_arena_mut();
            for field_type_id in field_types {
                arena.substitute(field_type_id, concrete_subs);
            }
        }

        let kind = { self.entity_registry().get_type(type_def_id).kind };
        let type_args: crate::type_arena::TypeIdVec = type_keys
            .iter()
            .map(|&v| ArenaTypeId::from_raw(v.raw()))
            .collect();
        let self_type = match kind {
            TypeDefKind::Class => self.type_arena_mut().class(type_def_id, type_args),
            TypeDefKind::Struct | TypeDefKind::Sentinel => {
                self.type_arena_mut().struct_type(type_def_id, type_args)
            }
            TypeDefKind::Interface
            | TypeDefKind::ErrorType
            | TypeDefKind::Primitive
            | TypeDefKind::Alias => return None,
        };

        let instance_id = self
            .entity_registry_mut()
            .class_method_monomorph_cache
            .next_unique_id();
        let class_name_str = self
            .name_table()
            .last_segment_str(identity_inst.class_name)
            .unwrap_or_else(|| "class".to_string());
        let method_name_str = self
            .name_table()
            .last_segment_str(identity_inst.method_name)
            .unwrap_or_else(|| "method".to_string());
        let mangled_name_str = format!(
            "{}__method_{}__mono_{}",
            class_name_str, method_name_str, instance_id
        );
        let mangled_name = self
            .name_table_mut()
            .intern_raw(self.module.current_module, &[&mangled_name_str]);

        Some(crate::generic::ClassMethodMonomorphInstance {
            class_name: identity_inst.class_name,
            method_name: identity_inst.method_name,
            mangled_name,
            instance_id,
            func_type,
            substitutions: concrete_subs.clone(),
            external_info: identity_inst.external_info,
            self_type,
        })
    }

    /// Create a derived concrete static-method monomorph instance.
    fn create_derived_static_method_monomorph(
        &mut self,
        identity_inst: &crate::generic::StaticMethodMonomorphInstance,
        concrete_subs: &FxHashMap<NameId, ArenaTypeId>,
    ) -> Option<crate::generic::StaticMethodMonomorphInstance> {
        let type_def_id = self
            .entity_registry()
            .type_by_name(identity_inst.class_name)?;
        let method_id = self
            .entity_registry()
            .find_static_method_on_type(type_def_id, identity_inst.method_name)?;
        let signature_id = self.entity_registry().method_signature(method_id);

        let (params, ret, is_closure) = {
            let arena = self.type_arena();
            let (params, ret, is_closure) = arena.unwrap_function(signature_id)?;
            (params.to_vec(), ret, is_closure)
        };

        let (subst_params, subst_ret) = {
            let mut arena = self.type_arena_mut();
            let subst_params = params
                .iter()
                .map(|&param_type_id| arena.substitute(param_type_id, concrete_subs))
                .collect::<Vec<_>>();
            let subst_ret = arena.substitute(ret, concrete_subs);
            (subst_params, subst_ret)
        };
        let func_type = FunctionType::from_ids(&subst_params, subst_ret, is_closure);

        // Eagerly substitute field types so codegen can do immutable lookup_substitute.
        let generic_info = { self.entity_registry().type_generic_info(type_def_id) };
        if let Some(generic_info) = generic_info {
            let field_types = generic_info.field_types;
            let mut arena = self.type_arena_mut();
            for field_type_id in field_types {
                arena.substitute(field_type_id, concrete_subs);
            }
        }

        let instance_id = self
            .entity_registry_mut()
            .static_method_monomorph_cache
            .next_unique_id();
        let class_name_str = self
            .name_table()
            .last_segment_str(identity_inst.class_name)
            .unwrap_or_else(|| "class".to_string());
        let method_name_str = self
            .name_table()
            .last_segment_str(identity_inst.method_name)
            .unwrap_or_else(|| "method".to_string());
        let mangled_name_str = format!(
            "{}__static_{}__mono_{}",
            class_name_str, method_name_str, instance_id
        );
        let mangled_name = self
            .name_table_mut()
            .intern_raw(self.module.current_module, &[&mangled_name_str]);

        Some(crate::generic::StaticMethodMonomorphInstance {
            class_name: identity_inst.class_name,
            method_name: identity_inst.method_name,
            mangled_name,
            instance_id,
            func_type,
            substitutions: concrete_subs.clone(),
        })
    }

    /// Register implement-block method monomorph instances for all concrete
    /// element types known in the type arena.
    ///
    /// Scans the type arena for all concrete `Iterator<T>` element
    /// types and, for each (element_type, default_method) pair on the array's
    /// `Iterable<T>` implementation, registers an
    /// `ImplementMethodMonomorphInstance` in the entity registry cache.
    ///
    /// Records the instances in sema so that VIR lowering can later create
    /// concrete functions from them. Codegen resolves calls via VIR metadata
    /// in `VirProgram.implement_method_monomorphs`.
    pub(in crate::analyzer) fn register_implement_method_monomorphs(&mut self) {
        // Get array TypeDefId
        let array_tdef_id = {
            let registry = self.entity_registry();
            let array_name_id = match registry.array_name_id() {
                Some(id) => id,
                None => return,
            };
            match registry.type_by_name(array_name_id) {
                Some(id) => id,
                None => return,
            }
        };

        // Find Iterable TypeDefId (the interface array implements)
        let iterable_tdef_id = {
            let registry = self.entity_registry();
            let interfaces = registry.get_implemented_interfaces(array_tdef_id);
            if interfaces.is_empty() {
                return;
            }
            interfaces[0] // array implements exactly one interface: Iterable<T>
        };

        // Find T's NameId from the abstract substitution {T_name_id -> TypeParam(T)}
        let t_name_id: NameId = {
            let registry = self.entity_registry();
            let type_params = registry.type_params(iterable_tdef_id);
            let type_args = registry.get_implementation_type_args(array_tdef_id, iterable_tdef_id);
            let subs: FxHashMap<NameId, ArenaTypeId> = type_params
                .into_iter()
                .zip(type_args.iter().copied())
                .collect();
            match subs.into_keys().next() {
                Some(name_id) => name_id,
                None => return,
            }
        };

        // Collect non-external Iterable default methods on the array type
        let default_methods: Vec<(MethodId, NameId)> = {
            let registry = self.entity_registry();
            let mut results = Vec::new();
            for iface_method_id in registry.methods_on_type(iterable_tdef_id) {
                let method_def = registry.get_method(iface_method_id);
                if !method_def.has_default || method_def.external_binding.is_some() {
                    continue;
                }
                if let Some(array_method_id) =
                    registry.find_method_on_type(array_tdef_id, method_def.name_id)
                {
                    results.push((array_method_id, method_def.name_id));
                }
            }
            results
        };

        if default_methods.is_empty() {
            return;
        }

        // Get all concrete element types from the type arena
        let elem_types: Vec<ArenaTypeId> = {
            let arena = self.type_arena();
            arena.all_concrete_runtime_iterator_elem_types()
        };

        // Skip re-registration if element types haven't grown since last time.
        // The implement_method_monomorph_cache is not cleared between files (its
        // entries are arena-derived and stable), so if no new element types appeared,
        // the cache already contains all needed instances.
        let current_count = elem_types.len();
        let last_count = self.entity_registry().last_implement_elem_type_count;
        if current_count == last_count {
            return;
        }

        let mut count = 0u32;

        for elem_type in &elem_types {
            let mut concrete_subs: FxHashMap<NameId, ArenaTypeId> = FxHashMap::default();
            concrete_subs.insert(t_name_id, *elem_type);

            for &(method_id, method_name_id) in &default_methods {
                let key = ImplementMethodMonomorphKey::new(
                    iterable_tdef_id,
                    array_tdef_id,
                    method_name_id,
                    vec![VirTypeId::from_type_id(*elem_type)],
                );

                // Skip if already registered
                if self
                    .entity_registry()
                    .implement_method_monomorph_cache
                    .contains(&key)
                {
                    continue;
                }

                // Substitute the method signature with concrete types
                let signature_id = self.entity_registry().method_signature(method_id);
                let (params, ret, is_closure) = {
                    let arena = self.type_arena();
                    match arena.unwrap_function(signature_id) {
                        Some((p, r, c)) => (p.to_vec(), r, c),
                        None => continue,
                    }
                };

                let (subst_params, subst_ret) = {
                    let mut arena = self.type_arena_mut();
                    let sp = params
                        .iter()
                        .map(|&pt| arena.substitute(pt, &concrete_subs))
                        .collect::<Vec<_>>();
                    let sr = arena.substitute(ret, &concrete_subs);
                    (sp, sr)
                };
                let func_type = FunctionType::from_ids(&subst_params, subst_ret, is_closure);

                let instance_id = self
                    .entity_registry_mut()
                    .implement_method_monomorph_cache
                    .next_unique_id();

                let method_name_str = self
                    .name_table()
                    .last_segment_str(method_name_id)
                    .unwrap_or_else(|| "method".to_string());
                let mangled_name_str =
                    format!("__array_iterable_{}_{}", elem_type.index(), method_name_str);
                let mangled_name = self
                    .name_table_mut()
                    .intern_raw(self.module.current_module, &[&mangled_name_str]);

                let instance = ImplementMethodMonomorphInstance {
                    interface_type_def_id: iterable_tdef_id,
                    implementing_type_def_id: array_tdef_id,
                    method_id,
                    method_name: method_name_id,
                    mangled_name,
                    instance_id,
                    func_type,
                    substitutions: concrete_subs.clone(),
                };

                self.entity_registry_mut()
                    .implement_method_monomorph_cache
                    .insert(key, instance);
                count += 1;
            }
        }

        // Record how many element types we've now covered so subsequent calls
        // with the same count can skip the scan entirely.
        self.entity_registry_mut().last_implement_elem_type_count = current_count;

        if count > 0 {
            tracing::debug!(
                count,
                elem_types = elem_types.len(),
                methods = default_methods.len(),
                "registered implement method monomorph instances"
            );
        }
    }
}
