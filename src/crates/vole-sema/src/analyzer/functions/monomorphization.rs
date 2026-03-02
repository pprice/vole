// src/sema/analyzer/functions/monomorphization.rs
//! Monomorphization: propagation and derivation of concrete monomorph
//! instances for class/static methods.
//!
//! Free-function monomorphization is handled by the VIR monomorph pass
//! (see `vole_vir::monomorph`).  Generic body analysis for Pass 2a lives
//! in `functions/generic_vir.rs`.  This module handles only class/static
//! method propagation and derivation.

use super::super::*;

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
}
