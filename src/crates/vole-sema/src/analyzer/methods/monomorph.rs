use super::super::*;
use crate::generic::{
    ClassMethodMonomorphInstance, ClassMethodMonomorphKey, StaticMethodMonomorphInstance,
    StaticMethodMonomorphKey, TypeParamInfo,
};
use crate::implement_registry::ExternalMethodInfo;
use crate::type_arena::TypeId as ArenaTypeId;
use rustc_hash::FxHashMap;
use vole_identity::{NameId, TypeDefId};

/// Generic context for recording method monomorphizations.
pub(crate) struct GenericContext<'a> {
    pub(crate) class_type_params: &'a [TypeParamInfo],
    pub(crate) method_type_params: &'a [TypeParamInfo],
    pub(crate) inferred: &'a FxHashMap<NameId, ArenaTypeId>,
}

/// Bundled context for creating a class method monomorph instance.
struct ClassMonomorphCtx<'a> {
    key: &'a ClassMethodMonomorphKey,
    class_type_def_id: TypeDefId,
    class_name_id: NameId,
    method_name_id: NameId,
    type_args_id: &'a [ArenaTypeId],
    method_sym: Symbol,
    func_type: &'a FunctionType,
    external_info: Option<ExternalMethodInfo>,
    object_type_id: ArenaTypeId,
}

/// Bundled context for creating a static method monomorph instance.
struct StaticMonomorphCtx<'a> {
    key: &'a StaticMethodMonomorphKey,
    type_def_id: TypeDefId,
    class_name_id: NameId,
    method_name_id: NameId,
    method_sym: Symbol,
    func_type: &'a FunctionType,
    generic_ctx: &'a GenericContext<'a>,
}

impl Analyzer {
    /// Record a class method monomorphization for generic class method calls.
    /// Creates or retrieves a monomorphized instance and records the call site.
    pub(crate) fn record_class_method_monomorph(
        &mut self,
        expr: &Expr,
        object_type_id: ArenaTypeId,
        method_sym: Symbol,
        func_type: &FunctionType,
        external_info: Option<ExternalMethodInfo>,
        interner: &Interner,
    ) {
        // Extract type_def_id and type_args_id using arena queries
        // Note: We only record monomorphs for concrete types (Class) that have
        // method bodies to compile. Interface types use vtable dispatch and don't need monomorphs.
        tracing::debug!(object_type_id = ?object_type_id, "record_class_method_monomorph called");
        let generic_info = {
            let arena = self.type_arena();
            arena
                .unwrap_class_or_struct(object_type_id)
                .filter(|(_, args, _)| !args.is_empty())
                .map(|(id, args, _)| (id, args.clone()))
        };
        let Some((class_type_def_id, type_args_id)) = generic_info else {
            tracing::debug!("returning early - not a generic class");
            return;
        };

        let class_name_id = self.entity_registry().get_type(class_type_def_id).name_id;
        tracing::debug!(
            class_name_id = ?class_name_id,
            type_args_id = ?type_args_id,
            "extracted generic type info"
        );

        // Get the method name_id
        let method_name_id = self.method_name_id(method_sym, interner);

        // Use TypeIds directly as keys
        let type_keys: Vec<_> = type_args_id.iter().copied().collect();

        // Create the monomorph key
        let key = ClassMethodMonomorphKey::new(class_name_id, method_name_id, type_keys);

        // Create/cache the monomorph instance
        if !self
            .entity_registry_mut()
            .class_method_monomorph_cache
            .contains(&key)
        {
            let ctx = ClassMonomorphCtx {
                key: &key,
                class_type_def_id,
                class_name_id,
                method_name_id,
                type_args_id: &type_args_id,
                method_sym,
                func_type,
                external_info,
                object_type_id,
            };
            self.create_class_method_monomorph_instance(&ctx, interner);
        }

        // Record the call site -> key mapping
        tracing::debug!(expr_id = ?expr.id, key = ?key, "recording call site");
        self.results.node_map.set_class_method_generic(expr.id, key);
    }

    /// Create and cache a class method monomorph instance.
    fn create_class_method_monomorph_instance(
        &mut self,
        ctx: &ClassMonomorphCtx<'_>,
        interner: &Interner,
    ) {
        // Get the generic type definition for substitution info
        let generic_info = self
            .entity_registry()
            .type_generic_info(ctx.class_type_def_id);
        let substitutions = if let Some(generic_info) = &generic_info {
            let mut subs = FxHashMap::default();
            for (param, &arg_id) in generic_info.type_params.iter().zip(ctx.type_args_id.iter()) {
                subs.insert(param.name_id, arg_id);
            }

            // Eagerly substitute all field types into the arena so that codegen's
            // read-only lookup_substitute can find them later.
            if !subs.is_empty() {
                let field_types = generic_info.field_types.clone();
                let mut arena = self.type_arena_mut();
                for field_type in field_types {
                    arena.substitute(field_type, &subs);
                }
            }

            subs
        } else {
            FxHashMap::default()
        };

        // Generate unique mangled name
        let instance_id = self
            .entity_registry_mut()
            .class_method_monomorph_cache
            .next_unique_id();
        let class_name = self
            .name_table()
            .last_segment_str(ctx.class_name_id)
            .unwrap_or_else(|| "class".to_string());
        let method_name = interner.resolve(ctx.method_sym);
        let mangled_name_str = format!(
            "{}__method_{}__mono_{}",
            class_name, method_name, instance_id
        );
        let mangled_name = self
            .name_table_mut()
            .intern_raw(self.module.current_module, &[&mangled_name_str]);

        // Class method monomorphs must carry a concrete signature.
        let substituted_func_type = if substitutions.is_empty() {
            ctx.func_type.clone()
        } else {
            let param_type_ids: Vec<ArenaTypeId> =
                ctx.func_type.params_id.iter().copied().collect();
            let return_type_id: ArenaTypeId = ctx.func_type.return_type_id;
            let (subst_param_ids, subst_return_id) = {
                let mut arena = self.type_arena_mut();
                let params: Vec<ArenaTypeId> = param_type_ids
                    .iter()
                    .map(|&param_id| arena.substitute(param_id, &substitutions))
                    .collect();
                let ret = arena.substitute(return_type_id, &substitutions);
                (params, ret)
            };
            FunctionType::from_ids(&subst_param_ids, subst_return_id, ctx.func_type.is_closure)
        };

        let instance = ClassMethodMonomorphInstance {
            class_name: ctx.class_name_id,
            method_name: ctx.method_name_id,
            mangled_name,
            instance_id,
            func_type: substituted_func_type,
            substitutions,
            external_info: ctx.external_info,
            self_type: ctx.object_type_id,
        };

        tracing::debug!(
            mangled_name = %mangled_name_str,
            "inserting class method monomorph instance"
        );
        self.entity_registry_mut()
            .class_method_monomorph_cache
            .insert(ctx.key.clone(), instance);
    }

    /// Record a static method monomorphization for generic class static method calls.
    pub(crate) fn record_static_method_monomorph(
        &mut self,
        expr: &Expr,
        type_def_id: TypeDefId,
        method_sym: Symbol,
        func_type: &FunctionType,
        generic_ctx: &GenericContext<'_>,
        interner: &Interner,
    ) {
        // Get the type def to extract name and type args
        let class_name_id = self.entity_registry().name_id(type_def_id);

        // Get the method name_id
        let method_name_id = self.method_name_id(method_sym, interner);

        // Use TypeIds directly as keys for class type params
        let class_type_keys: Vec<_> = generic_ctx
            .class_type_params
            .iter()
            .filter_map(|tp| generic_ctx.inferred.get(&tp.name_id).copied())
            .collect();

        // Use TypeIds directly as keys for method type params
        let method_type_keys: Vec<_> = generic_ctx
            .method_type_params
            .iter()
            .filter_map(|tp| generic_ctx.inferred.get(&tp.name_id).copied())
            .collect();

        // Create the monomorph key with separate class and method type keys
        let key = StaticMethodMonomorphKey::new(
            class_name_id,
            method_name_id,
            class_type_keys,
            method_type_keys,
        );

        // Create/cache the monomorph instance
        if !self
            .entity_registry_mut()
            .static_method_monomorph_cache
            .contains(&key)
        {
            let ctx = StaticMonomorphCtx {
                key: &key,
                type_def_id,
                class_name_id,
                method_name_id,
                method_sym,
                func_type,
                generic_ctx,
            };
            self.create_static_method_monomorph_instance(&ctx, interner);
        }

        // Record the call site -> key mapping
        tracing::debug!(expr_id = ?expr.id, key = ?key, "recording static method call site");
        self.results
            .node_map
            .set_static_method_generic(expr.id, key);
    }

    /// Create and cache a static method monomorph instance.
    fn create_static_method_monomorph_instance(
        &mut self,
        ctx: &StaticMonomorphCtx<'_>,
        interner: &Interner,
    ) {
        // Generate unique mangled name
        let instance_id = self
            .entity_registry_mut()
            .static_method_monomorph_cache
            .next_unique_id();
        let class_name = self
            .name_table()
            .last_segment_str(ctx.class_name_id)
            .unwrap_or_else(|| "class".to_string());
        let method_name = interner.resolve(ctx.method_sym);
        let mangled_name_str = format!(
            "{}__static_{}__mono_{}",
            class_name, method_name, instance_id
        );
        let mangled_name = self
            .name_table_mut()
            .intern_raw(self.module.current_module, &[&mangled_name_str]);

        // Get param TypeIds from func_type
        let param_type_ids: Vec<ArenaTypeId> = ctx.func_type.params_id.iter().copied().collect();
        let return_type_id: ArenaTypeId = ctx.func_type.return_type_id;

        // Create the substituted function type using arena substitution (TypeId-based)
        let inferred_hb: FxHashMap<NameId, ArenaTypeId> = ctx
            .generic_ctx
            .inferred
            .iter()
            .map(|(&k, &v)| (k, v))
            .collect();

        // Eagerly substitute all field types into the arena so that codegen's
        // read-only lookup_substitute can find them later.
        {
            let generic_info = self.entity_registry().type_generic_info(ctx.type_def_id);
            if let Some(generic_info) = generic_info {
                let field_types = generic_info.field_types;
                let mut arena = self.type_arena_mut();
                for field_type in field_types {
                    arena.substitute(field_type, &inferred_hb);
                }
            }
        }

        let (subst_param_ids, subst_return_id) = {
            let mut arena = self.type_arena_mut();
            let params: Vec<ArenaTypeId> = param_type_ids
                .iter()
                .map(|&p| arena.substitute(p, &inferred_hb))
                .collect();
            let ret = arena.substitute(return_type_id, &inferred_hb);
            (params, ret)
        };

        // Build substituted FunctionType from TypeIds
        let substituted_func_type =
            FunctionType::from_ids(&subst_param_ids, subst_return_id, ctx.func_type.is_closure);

        // Convert back to FxHashMap for storage
        let substitutions: FxHashMap<NameId, ArenaTypeId> =
            inferred_hb.iter().map(|(&k, &v)| (k, v)).collect();

        let instance = StaticMethodMonomorphInstance {
            class_name: ctx.class_name_id,
            method_name: ctx.method_name_id,
            mangled_name,
            instance_id,
            func_type: substituted_func_type,
            substitutions,
        };

        tracing::debug!(
            mangled_name = %mangled_name_str,
            "inserting static method monomorph instance"
        );
        self.entity_registry_mut()
            .static_method_monomorph_cache
            .insert(ctx.key.clone(), instance);
    }
}
