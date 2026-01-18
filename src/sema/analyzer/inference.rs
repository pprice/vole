//! Type parameter inference for generic function and method calls.

use super::Analyzer;
use crate::identity::NameId;
use crate::sema::generic::TypeParamInfo;
use crate::sema::type_arena::TypeId as ArenaTypeId;
use crate::sema::types::{LegacyType, NominalType};
use std::collections::HashMap;

impl Analyzer {
    /// Infer type parameters from argument types.
    /// Given type params like [T, U], param types like [T, [U]], and arg types like [i64, [string]],
    /// returns a map {NameId -> LegacyType} for substitution.
    pub(crate) fn infer_type_params(
        &self,
        type_params: &[TypeParamInfo],
        param_types: &[LegacyType],
        arg_types: &[LegacyType],
    ) -> HashMap<NameId, LegacyType> {
        let mut inferred = HashMap::new();

        // For each parameter, try to match its type against the argument type
        for (param_type, arg_type) in param_types.iter().zip(arg_types.iter()) {
            self.unify_types(param_type, arg_type, type_params, &mut inferred);
        }

        inferred
    }

    /// Unify a parameter type pattern with an argument type, extracting type param bindings.
    pub(super) fn unify_types(
        &self,
        pattern: &LegacyType,
        actual: &LegacyType,
        type_params: &[TypeParamInfo],
        inferred: &mut HashMap<NameId, LegacyType>,
    ) {
        match (pattern, actual) {
            // If the pattern is a type param, bind it
            (LegacyType::TypeParam(name_id), actual) => {
                self.unify_type_param(*name_id, actual, type_params, inferred);
            }
            // If the pattern is a type param ref, resolve to name_id and bind
            (LegacyType::TypeParamRef(type_param_id), actual) => {
                if let Some(info) = self.type_param_stack.get_by_type_param_id(*type_param_id) {
                    self.unify_type_param(info.name_id, actual, type_params, inferred);
                }
            }
            // Array: unify element types
            (LegacyType::Array(p_elem), LegacyType::Array(a_elem)) => {
                self.unify_types(p_elem, a_elem, type_params, inferred);
            }
            // Interface types: unify type args for the same interface
            (
                LegacyType::Nominal(NominalType::Interface(p_iface)),
                LegacyType::Nominal(NominalType::Interface(a_iface)),
            ) if p_iface.type_def_id == a_iface.type_def_id => {
                // Convert all type args to LegacyType first to avoid borrow issues
                let args: Vec<_> = {
                    let arena = self.type_arena.borrow();
                    p_iface
                        .type_args_id
                        .iter()
                        .zip(a_iface.type_args_id.iter())
                        .map(|(&p, &a)| (arena.to_type(p), arena.to_type(a)))
                        .collect()
                };
                for (p_arg, a_arg) in args {
                    self.unify_types(&p_arg, &a_arg, type_params, inferred);
                }
            }
            // Union: try to match each pattern variant
            (LegacyType::Union(p_types), LegacyType::Union(a_types)) => {
                for (p, a) in p_types.iter().zip(a_types.iter()) {
                    self.unify_types(p, a, type_params, inferred);
                }
            }
            // Function types: unify params and return
            (LegacyType::Function(p_ft), LegacyType::Function(a_ft)) => {
                for (p, a) in p_ft.params.iter().zip(a_ft.params.iter()) {
                    self.unify_types(p, a, type_params, inferred);
                }
                self.unify_types(&p_ft.return_type, &a_ft.return_type, type_params, inferred);
            }
            // Class: unify type args (for generic class parameters)
            (
                LegacyType::Nominal(NominalType::Class(p_class)),
                LegacyType::Nominal(NominalType::Class(a_class)),
            ) if p_class.type_def_id == a_class.type_def_id => {
                // Convert all type args to LegacyType first to avoid borrow issues
                let args: Vec<_> = {
                    let arena = self.type_arena.borrow();
                    p_class
                        .type_args_id
                        .iter()
                        .zip(a_class.type_args_id.iter())
                        .map(|(&p, &a)| (arena.to_type(p), arena.to_type(a)))
                        .collect()
                };
                for (p_arg, a_arg) in args {
                    self.unify_types(&p_arg, &a_arg, type_params, inferred);
                }
            }
            // Record: unify type args (for generic record parameters)
            (
                LegacyType::Nominal(NominalType::Record(p_rec)),
                LegacyType::Nominal(NominalType::Record(a_rec)),
            ) if p_rec.type_def_id == a_rec.type_def_id => {
                // Convert all type args to LegacyType first to avoid borrow issues
                let args: Vec<_> = {
                    let arena = self.type_arena.borrow();
                    p_rec
                        .type_args_id
                        .iter()
                        .zip(a_rec.type_args_id.iter())
                        .map(|(&p, &a)| (arena.to_type(p), arena.to_type(a)))
                        .collect()
                };
                for (p_arg, a_arg) in args {
                    self.unify_types(&p_arg, &a_arg, type_params, inferred);
                }
            }
            // Everything else: no type params to extract
            _ => {}
        }
    }

    /// Helper to unify a type parameter with an actual type
    fn unify_type_param(
        &self,
        name_id: NameId,
        actual: &LegacyType,
        type_params: &[TypeParamInfo],
        inferred: &mut HashMap<NameId, LegacyType>,
    ) {
        // Only bind if it's one of our type params
        if type_params.iter().any(|tp| tp.name_id == name_id) {
            // Special case: if actual is Nil, check if the type param is already in
            // scope with the same name_id. If so, bind to the type param instead of Nil.
            // This preserves type params in generic contexts (e.g., Box { value: nil }).
            let actual_to_bind = if matches!(actual, LegacyType::Nil) {
                // Check if this type param is in our current scope - if so, preserve it
                if let Some(scope) = self.type_param_stack.current()
                    && scope.get_by_name_id(name_id).is_some()
                {
                    // Preserve the type param
                    LegacyType::TypeParam(name_id)
                } else {
                    actual.clone()
                }
            } else if let LegacyType::TypeParam(actual_name_id) = actual {
                // If actual is also a type param, check if it's in our scope
                if let Some(scope) = self.type_param_stack.current()
                    && scope.get_by_name_id(*actual_name_id).is_some()
                {
                    // Preserve the actual type param
                    actual.clone()
                } else {
                    actual.clone()
                }
            } else if matches!(actual, LegacyType::TypeParamRef(_)) {
                // If actual is a type param ref, preserve it
                actual.clone()
            } else {
                actual.clone()
            };

            // Only bind if not already bound (first binding wins)
            inferred.entry(name_id).or_insert(actual_to_bind);
        }
    }

    // ========== TypeId-based inference ==========
    //
    // These versions work directly with TypeId, avoiding LegacyType conversion.

    /// Infer type parameters from argument types (TypeId version).
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
        if let (Some(p_elem), Some(a_elem)) =
            (arena.unwrap_array(pattern_id), arena.unwrap_array(actual_id))
        {
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
                let args: Vec<_> = p_args.iter().zip(a_args.iter()).map(|(&p, &a)| (p, a)).collect();
                drop(arena);
                for (p_arg, a_arg) in args {
                    self.unify_types_id(p_arg, a_arg, type_params, inferred);
                }
            }
            return;
        }

        // Union: try to match each pattern variant
        if let (Some(p_variants), Some(a_variants)) =
            (arena.unwrap_union(pattern_id), arena.unwrap_union(actual_id))
        {
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
        if let (Some((p_def_id, p_args)), Some((a_def_id, a_args))) =
            (arena.unwrap_class(pattern_id), arena.unwrap_class(actual_id))
        {
            if p_def_id == a_def_id {
                let args: Vec<_> = p_args.iter().zip(a_args.iter()).map(|(&p, &a)| (p, a)).collect();
                drop(arena);
                for (p_arg, a_arg) in args {
                    self.unify_types_id(p_arg, a_arg, type_params, inferred);
                }
            }
            return;
        }

        // Record: unify type args
        if let (Some((p_def_id, p_args)), Some((a_def_id, a_args))) =
            (arena.unwrap_record(pattern_id), arena.unwrap_record(actual_id))
        {
            if p_def_id == a_def_id {
                let args: Vec<_> = p_args.iter().zip(a_args.iter()).map(|(&p, &a)| (p, a)).collect();
                drop(arena);
                for (p_arg, a_arg) in args {
                    self.unify_types_id(p_arg, a_arg, type_params, inferred);
                }
            }
            return;
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
