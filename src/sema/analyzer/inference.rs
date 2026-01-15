//! Type parameter inference for generic function and method calls.

use super::Analyzer;
use crate::identity::NameId;
use crate::sema::Type;
use crate::sema::generic::TypeParamInfo;
use crate::sema::types::{LegacyType, NominalType};
use std::collections::HashMap;

impl Analyzer {
    /// Infer type parameters from argument types.
    /// Given type params like [T, U], param types like [T, [U]], and arg types like [i64, [string]],
    /// returns a map {NameId -> Type} for substitution.
    pub(crate) fn infer_type_params(
        &self,
        type_params: &[TypeParamInfo],
        param_types: &[Type],
        arg_types: &[Type],
    ) -> HashMap<NameId, Type> {
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
        pattern: &Type,
        actual: &Type,
        type_params: &[TypeParamInfo],
        inferred: &mut HashMap<NameId, Type>,
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
                for (p_arg, a_arg) in p_iface.type_args.iter().zip(a_iface.type_args.iter()) {
                    self.unify_types(p_arg, a_arg, type_params, inferred);
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
                for (p, a) in p_class.type_args.iter().zip(a_class.type_args.iter()) {
                    self.unify_types(p, a, type_params, inferred);
                }
            }
            // Record: unify type args (for generic record parameters)
            (
                LegacyType::Nominal(NominalType::Record(p_rec)),
                LegacyType::Nominal(NominalType::Record(a_rec)),
            ) if p_rec.type_def_id == a_rec.type_def_id => {
                for (p, a) in p_rec.type_args.iter().zip(a_rec.type_args.iter()) {
                    self.unify_types(p, a, type_params, inferred);
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
        actual: &Type,
        type_params: &[TypeParamInfo],
        inferred: &mut HashMap<NameId, Type>,
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
}
