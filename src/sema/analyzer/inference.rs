//! Type parameter inference for generic function and method calls.

use super::Analyzer;
use crate::identity::NameId;
use crate::sema::generic::TypeParamInfo;
use crate::sema::type_arena::TypeId as ArenaTypeId;
use std::collections::HashMap;

impl Analyzer {
    /// Infer type parameters from argument types.
    /// Returns a map from type parameter NameId to inferred TypeId.
    pub(crate) fn infer_type_params_id(
        &self,
        type_params: &[TypeParamInfo],
        param_type_ids: &[ArenaTypeId],
        arg_type_ids: &[ArenaTypeId],
    ) -> HashMap<NameId, ArenaTypeId> {
        let mut inferred = HashMap::new();

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
        inferred: &mut HashMap<NameId, ArenaTypeId>,
    ) {
        let arena = self.type_arena.borrow();

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

        // Interface types: unify type args for the same interface
        if let (Some((p_def_id, p_args)), Some((a_def_id, a_args))) = (
            arena.unwrap_interface(pattern_id),
            arena.unwrap_interface(actual_id),
        ) {
            if p_def_id == a_def_id {
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

        // Class: unify type args
        if let (Some((p_def_id, p_args)), Some((a_def_id, a_args))) = (
            arena.unwrap_class(pattern_id),
            arena.unwrap_class(actual_id),
        ) {
            if p_def_id == a_def_id {
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

        // Record: unify type args
        if let (Some((p_def_id, p_args)), Some((a_def_id, a_args))) = (
            arena.unwrap_record(pattern_id),
            arena.unwrap_record(actual_id),
        ) && p_def_id == a_def_id
        {
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

        // Everything else: no type params to extract
    }

    /// Helper to unify a type parameter with an actual type (TypeId version)
    fn unify_type_param_id(
        &self,
        name_id: NameId,
        actual_id: ArenaTypeId,
        type_params: &[TypeParamInfo],
        inferred: &mut HashMap<NameId, ArenaTypeId>,
    ) {
        // Only bind if it's one of our type params
        if type_params.iter().any(|tp| tp.name_id == name_id) {
            let arena = self.type_arena.borrow();

            // Special case: if actual is Nil, check if the type param is already in
            // scope with the same name_id. If so, bind to the type param instead of Nil.
            let actual_to_bind = if actual_id == ArenaTypeId::NIL {
                // Check if this type param is in our current scope - if so, preserve it
                if let Some(scope) = self.type_param_stack.current()
                    && scope.get_by_name_id(name_id).is_some()
                {
                    // Preserve the type param - create a TypeParam TypeId
                    drop(arena);
                    self.type_arena.borrow_mut().type_param(name_id)
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
            };

            // Only bind if not already bound (first binding wins)
            inferred.entry(name_id).or_insert(actual_to_bind);
        }
    }
}
