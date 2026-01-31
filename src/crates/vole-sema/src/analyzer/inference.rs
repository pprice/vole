//! Type parameter inference for generic function and method calls.

use super::Analyzer;
use crate::generic::TypeParamInfo;
use crate::type_arena::{InternedStructural, TypeId as ArenaTypeId};
use rustc_hash::FxHashMap;
use vole_identity::NameId;

impl Analyzer {
    /// Infer type parameters from argument types.
    /// Returns a map from type parameter NameId to inferred TypeId.
    pub(crate) fn infer_type_params_id(
        &self,
        type_params: &[TypeParamInfo],
        param_type_ids: &[ArenaTypeId],
        arg_type_ids: &[ArenaTypeId],
    ) -> FxHashMap<NameId, ArenaTypeId> {
        let mut inferred = FxHashMap::default();

        // For each parameter, try to match its type against the argument type
        for (&param_type_id, &arg_type_id) in param_type_ids.iter().zip(arg_type_ids.iter()) {
            self.unify_types_id(param_type_id, arg_type_id, type_params, &mut inferred);
        }

        inferred
    }

    /// Unify a parameter type pattern with an argument type (TypeId version).
    fn unify_types_id(
        &self,
        pattern_id: ArenaTypeId,
        actual_id: ArenaTypeId,
        type_params: &[TypeParamInfo],
        inferred: &mut FxHashMap<NameId, ArenaTypeId>,
    ) {
        let arena = self.type_arena();

        // If the pattern is a type param, bind it
        if let Some(name_id) = arena.unwrap_type_param(pattern_id) {
            drop(arena); // Release borrow before calling unify_type_param_id
            self.unify_type_param_id(name_id, actual_id, type_params, inferred);
            return;
        }

        // If the pattern is a type param ref, resolve to name_id and bind
        if let Some(type_param_id) = arena.unwrap_type_param_ref(pattern_id) {
            if let Some(info) = self.type_param_stack.get_by_type_param_id(type_param_id) {
                drop(arena);
                self.unify_type_param_id(info.name_id, actual_id, type_params, inferred);
            }
            return;
        }

        // Array: unify element types
        if let (Some(p_elem), Some(a_elem)) = (
            arena.unwrap_array(pattern_id),
            arena.unwrap_array(actual_id),
        ) {
            drop(arena);
            self.unify_types_id(p_elem, a_elem, type_params, inferred);
            return;
        }

        // Nominal types (class/interface): unify type args if same definition and kind
        if let (Some((p_def_id, p_args, p_kind)), Some((a_def_id, a_args, a_kind))) = (
            arena.unwrap_nominal(pattern_id),
            arena.unwrap_nominal(actual_id),
        ) {
            // Only unify if same kind and same type definition
            if p_kind == a_kind && p_def_id == a_def_id {
                let args: Vec<_> = p_args
                    .iter()
                    .zip(a_args.iter())
                    .map(|(&p, &a)| (p, a))
                    .collect();
                drop(arena);
                for (p_arg, a_arg) in args {
                    self.unify_types_id(p_arg, a_arg, type_params, inferred);
                }
            }
            return;
        }

        // Union: try to match each pattern variant
        if let (Some(p_variants), Some(a_variants)) = (
            arena.unwrap_union(pattern_id),
            arena.unwrap_union(actual_id),
        ) {
            let pairs: Vec<_> = p_variants
                .iter()
                .zip(a_variants.iter())
                .map(|(&p, &a)| (p, a))
                .collect();
            drop(arena);
            for (p, a) in pairs {
                self.unify_types_id(p, a, type_params, inferred);
            }
            return;
        }

        // Function types: unify params and return
        if let (Some((p_params, p_ret, _)), Some((a_params, a_ret, _))) = (
            arena.unwrap_function(pattern_id),
            arena.unwrap_function(actual_id),
        ) {
            let param_pairs: Vec<_> = p_params
                .iter()
                .zip(a_params.iter())
                .map(|(&p, &a)| (p, a))
                .collect();
            let (p_ret, a_ret) = (p_ret, a_ret);
            drop(arena);
            for (p, a) in param_pairs {
                self.unify_types_id(p, a, type_params, inferred);
            }
            self.unify_types_id(p_ret, a_ret, type_params, inferred);
            return;
        }

        // Structural type: unify field types from the pattern with the actual type's fields
        // This handles cases like `func foo<T>(a: { name: T })` where T should be inferred
        // from the actual argument's `name` field type.
        if let Some(structural) = arena.unwrap_structural(pattern_id) {
            let structural = structural.clone();
            drop(arena);
            self.unify_structural_type(&structural, actual_id, type_params, inferred);
        }

        // Everything else: no type params to extract
    }

    /// Unify a structural type pattern with an actual type by matching field types.
    /// For each field in the structural pattern, find the corresponding field in the
    /// actual type and unify their types. This allows inferring type parameters like
    /// `T` from `{ name: T }` when passed a class with a `name: string` field.
    fn unify_structural_type(
        &self,
        structural: &InternedStructural,
        actual_id: ArenaTypeId,
        type_params: &[TypeParamInfo],
        inferred: &mut FxHashMap<NameId, ArenaTypeId>,
    ) {
        // For each field in the structural type, try to find it in the actual type
        for (field_name_id, field_type_id) in &structural.fields {
            if let Some(actual_field_type_id) =
                self.get_field_type_by_name_id(actual_id, *field_name_id)
            {
                // Unify the structural field's type with the actual field's type
                self.unify_types_id(*field_type_id, actual_field_type_id, type_params, inferred);
            }
        }

        // For structural methods, we could also unify their signatures,
        // but method type params in structural types are less common.
        // For now, we only handle fields.
    }

    /// Get the type of a field from a class type by NameId.
    /// Returns None if the type doesn't have such a field.
    fn get_field_type_by_name_id(
        &self,
        ty_id: ArenaTypeId,
        field_name_id: NameId,
    ) -> Option<ArenaTypeId> {
        // Get type_def_id and type_args from TypeId using arena queries (class only)
        let (type_def_id, type_args_id) = {
            use crate::type_arena::NominalKind;
            let arena = self.type_arena();
            let (id, args, kind) = arena.unwrap_nominal(ty_id)?;
            if !matches!(kind, NominalKind::Class | NominalKind::Struct) {
                return None;
            }
            (id, args.to_vec())
        };

        // Clone generic_info to avoid holding borrow during subsequent operations
        let generic_info = self.entity_registry().type_generic_info(type_def_id)?;

        // Get the field name string for comparison
        let field_name_str = self.name_table().last_segment_str(field_name_id)?;

        // Build type substitutions directly using TypeId
        let substitutions: FxHashMap<_, _> = generic_info
            .type_params
            .iter()
            .zip(type_args_id.iter())
            .map(|(tp, &arg_id)| (tp.name_id, arg_id))
            .collect();

        // Find the field by name and get the substituted type
        for (i, name_id) in generic_info.field_names.iter().enumerate() {
            if self.name_table().last_segment_str(*name_id).as_deref() == Some(&field_name_str) {
                let field_type_id = generic_info.field_types[i];
                // Substitute any type params in the field type
                return Some(
                    self.type_arena_mut()
                        .substitute(field_type_id, &substitutions),
                );
            }
        }

        None
    }

    /// Helper to unify a type parameter with an actual type (TypeId version)
    fn unify_type_param_id(
        &self,
        name_id: NameId,
        actual_id: ArenaTypeId,
        type_params: &[TypeParamInfo],
        inferred: &mut FxHashMap<NameId, ArenaTypeId>,
    ) {
        // Only bind if it's one of our type params
        let type_param_info = type_params.iter().find(|tp| tp.name_id == name_id);
        if let Some(type_param_info) = type_param_info {
            // Compute actual_to_bind in a separate scope to release the arena borrow early
            let actual_to_bind = {
                let arena = self.type_arena();

                // Special case: if actual is Nil, check if the type param is already in
                // scope with the same name_id. If so, bind to the type param instead of Nil.
                if actual_id == ArenaTypeId::NIL {
                    // Check if this type param is in our current scope - if so, preserve it
                    if let Some(scope) = self.type_param_stack.current()
                        && scope.get_by_name_id(name_id).is_some()
                    {
                        // Preserve the type param - create a TypeParam TypeId
                        drop(arena);
                        self.type_arena_mut().type_param(name_id)
                    } else {
                        actual_id
                    }
                } else if let Some(actual_name_id) = arena.unwrap_type_param(actual_id) {
                    // If actual is also a type param, check if it's in our scope
                    if let Some(scope) = self.type_param_stack.current()
                        && scope.get_by_name_id(actual_name_id).is_some()
                    {
                        // Preserve the actual type param
                        actual_id
                    } else {
                        actual_id
                    }
                } else if arena.unwrap_type_param_ref(actual_id).is_some() {
                    // If actual is a type param ref, preserve it
                    actual_id
                } else {
                    actual_id
                }
            };

            // Only bind if not already bound (first binding wins)
            inferred.entry(name_id).or_insert(actual_to_bind);

            // If this type param has a structural constraint, also try to infer
            // type params from the constraint. This handles cases like:
            // func identity<T, __T0: { name: T }>(a: __T0) where we need to infer T
            // from the actual argument's field types.
            if let Some(crate::generic::TypeConstraint::Structural(structural)) =
                &type_param_info.constraint
            {
                let structural = structural.clone();
                self.unify_structural_type(&structural, actual_id, type_params, inferred);
            }
        }
    }
}
