//! Declaration signature collection — type parameter helpers.

use super::*;

impl Analyzer {
    /// Build type parameters with resolved constraints.
    ///
    /// This performs the two-pass type parameter resolution pattern:
    /// 1. First pass: Create a name scope with all type params (constraint=None) for constraint resolution
    /// 2. Second pass: Resolve constraints using that scope, building the final TypeParamInfo list
    ///
    /// Returns a TypeParamScope containing the fully resolved type parameters.
    /// Use `scope.to_params()` to get a cloned Vec, or `scope.into_params()` to consume and get owned Vec.
    pub(super) fn build_type_params_with_constraints(
        &mut self,
        ast_type_params: &[TypeParam],
        interner: &Interner,
    ) -> TypeParamScope {
        // First pass: create name_scope for constraint resolution
        // Type param constraints may reference other type params (e.g., T: Container<U>),
        // so we need all type param names available before resolving constraints.
        let name_scope = self.build_unconstrained_scope(ast_type_params, interner);

        // Second pass: resolve constraints with name_scope available, building final scope
        let type_params: Vec<TypeParamInfo> = ast_type_params
            .iter()
            .map(|tp| {
                let mut info = self.intern_type_param(tp, interner);
                info.constraint = tp.constraint.as_ref().and_then(|c| {
                    self.resolve_type_param_constraint(c, &name_scope, interner, tp.span)
                });
                info
            })
            .collect();

        TypeParamScope::from_params(type_params)
    }

    /// Create an unconstrained TypeParamInfo from an AST TypeParam.
    /// Interns the type param name as a NameId under the builtin module.
    pub(super) fn intern_type_param(
        &mut self,
        tp: &TypeParam,
        interner: &Interner,
    ) -> TypeParamInfo {
        let builtin_mod = self.name_table_mut().builtin_module();
        let tp_name_str = interner.resolve(tp.name);
        let tp_name_id = self
            .name_table_mut()
            .intern_raw(builtin_mod, &[tp_name_str]);
        TypeParamInfo {
            name: tp.name,
            name_id: tp_name_id,
            constraint: None,
            type_param_id: None,
            variance: TypeParamVariance::default(),
        }
    }

    /// Build a TypeParamScope with unconstrained entries from AST type params.
    /// This is the first pass of type param resolution - names only, no constraints.
    /// Used when constraints aren't needed (e.g., building a name scope for structural type resolution).
    pub(super) fn build_unconstrained_scope(
        &mut self,
        ast_type_params: &[TypeParam],
        interner: &Interner,
    ) -> TypeParamScope {
        let mut scope = TypeParamScope::new();
        for tp in ast_type_params {
            scope.add(self.intern_type_param(tp, interner));
        }
        scope
    }

    /// Extract type param NameIds from a scope and register them on an entity type.
    pub(super) fn register_type_params_on_entity(
        &mut self,
        entity_type_id: TypeDefId,
        scope: &TypeParamScope,
    ) {
        let name_ids: Vec<NameId> = scope.params().iter().map(|tp| tp.name_id).collect();
        self.entity_registry_mut()
            .set_type_params(entity_type_id, name_ids);
    }

    /// Build type argument placeholder TypeIds from a type param scope.
    /// Each type param gets a `type_param(name_id)` entry in the arena.
    pub(super) fn build_type_arg_placeholders(
        &mut self,
        scope: &TypeParamScope,
    ) -> Vec<ArenaTypeId> {
        scope
            .params()
            .iter()
            .map(|tp| self.type_arena_mut().type_param(tp.name_id))
            .collect()
    }

    /// Register a type shell (name and kind only, no fields/methods yet).
    /// This enables forward references - types can reference each other regardless of declaration order.
    ///
    /// If the type already exists in the registry (e.g., from a previous analysis of the same module
    /// in a shared cache scenario), returns the existing TypeDefId instead of creating a duplicate.
    pub(super) fn register_type_shell(
        &mut self,
        name: Symbol,
        kind: TypeDefKind,
        interner: &Interner,
    ) -> TypeDefId {
        let name_id = self
            .name_table_mut()
            .intern(self.module.current_module, &[name], interner);

        // Check if type already exists (important for shared cache across test files)
        if let Some(existing_id) = self.entity_registry().type_by_name(name_id) {
            return existing_id;
        }

        self.entity_registry_mut()
            .register_type(name_id, kind, self.module.current_module)
    }
}
