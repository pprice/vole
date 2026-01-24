use super::super::*;
use crate::compatibility::types_compatible_core_id;
use crate::type_arena::TypeId as ArenaTypeId;
use std::collections::HashSet;
use vole_identity::TypeDefId;

impl Analyzer {
    /// Check type compatibility using TypeId.
    /// Uses TypeId-based interface checks where possible.
    pub(crate) fn types_compatible_id(
        &mut self,
        from: ArenaTypeId,
        to: ArenaTypeId,
        interner: &Interner,
    ) -> bool {
        // Use the core TypeId-based compatibility check
        if types_compatible_core_id(from, to, &self.type_arena()) {
            return true;
        }

        // Check structural type compatibility (duck typing)
        // If `to` is a structural type, check if `from` satisfies those constraints
        let structural_opt = self.type_arena().unwrap_structural(to).cloned();
        if let Some(structural) = structural_opt {
            // check_structural_constraint_id returns None if satisfied
            return self
                .check_structural_constraint_id(from, &structural, interner)
                .is_none();
        }

        // Check interface compatibility using TypeId
        self.types_compatible_interface_id(from, to, interner)
    }

    /// Interface-related compatibility checks using TypeId
    fn types_compatible_interface_id(
        &mut self,
        from: ArenaTypeId,
        to: ArenaTypeId,
        interner: &Interner,
    ) -> bool {
        // Extract interface info using TypeId (type_def_id and type_args)
        let (to_iface_id, to_type_args) = {
            let arena = self.type_arena();
            match arena.unwrap_interface(to) {
                Some((id, args)) => (id, args.to_vec()),
                None => return false,
            }
        };

        // Check interface extension
        let from_iface_id = {
            let arena = self.type_arena();
            arena.unwrap_interface(from).map(|(id, _)| id)
        };
        if let Some(from_iface_id) = from_iface_id
            && self.interface_extends_by_type_def_id(from_iface_id, to_iface_id)
        {
            return true;
        }

        // Check structural compatibility using TypeId
        if self.satisfies_interface_by_type_def_id_typeid(from, to_iface_id, interner) {
            // Pre-compute substituted method signatures for codegen's lookup_substitute
            // This is the interface boxing case: `from` is assigned to interface `to`
            self.precompute_interface_method_substitutions(to_iface_id, &to_type_args);
            return true;
        }

        // Check function type compatibility with functional interface
        let fn_info = {
            let arena = self.type_arena();
            arena
                .unwrap_function(from)
                .map(|(params, ret, _)| (params.to_vec(), ret))
        };

        if let Some((fn_param_ids, fn_ret)) = fn_info
            && let Some(iface_fn) = self.get_functional_interface_type_by_type_def_id(to_iface_id)
            && fn_param_ids.len() == iface_fn.params_id.len()
        {
            // Use TypeId fields directly
            let arena = self.type_arena();
            let params_match = fn_param_ids
                .iter()
                .zip(iface_fn.params_id.iter())
                .all(|(&p, &ip)| types_compatible_core_id(p, ip, &arena));

            if params_match && types_compatible_core_id(fn_ret, iface_fn.return_type_id, &arena) {
                // Pre-compute substituted method signatures for codegen's lookup_substitute
                // This is the functional interface boxing case
                self.precompute_interface_method_substitutions(to_iface_id, &to_type_args);
                return true;
            }
        }

        false
    }

    fn interface_extends_by_type_def_id(&self, derived: TypeDefId, base: TypeDefId) -> bool {
        if derived == base {
            return true;
        }

        let mut stack = vec![derived];
        let mut seen = HashSet::new();
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            let extends = {
                let registry = self.entity_registry();
                registry.get_type(current).extends.clone()
            };
            for parent_id in extends {
                if parent_id == base {
                    return true;
                }
                stack.push(parent_id);
            }
        }

        false
    }

    /// Format a method signature for error messages (TypeId-based)
    pub(crate) fn format_method_signature_id(
        &mut self,
        params: &[ArenaTypeId],
        return_type: ArenaTypeId,
    ) -> String {
        let params_str: Vec<String> = params.iter().map(|&t| self.type_display_id(t)).collect();
        format!(
            "({}) -> {}",
            params_str.join(", "),
            self.type_display_id(return_type)
        )
    }

    /// Format a method signature for interface requirement messages (TypeId-based).
    /// Shows "Self" for TypeId::INVALID (which represents Self in interfaces).
    pub(crate) fn format_interface_method_signature_id(
        &mut self,
        params: &[ArenaTypeId],
        return_type: ArenaTypeId,
    ) -> String {
        // Collect invalid status first
        let invalid_params: Vec<bool> = params
            .iter()
            .map(|&t| self.type_arena().is_invalid(t))
            .collect();
        let return_is_invalid = self.type_arena().is_invalid(return_type);

        // Now format
        let params_str: Vec<String> = params
            .iter()
            .zip(invalid_params.iter())
            .map(|(&t, &is_invalid)| {
                if is_invalid {
                    "Self".to_string()
                } else {
                    self.type_display_id(t)
                }
            })
            .collect();
        let return_str = if return_is_invalid {
            "Self".to_string()
        } else {
            self.type_display_id(return_type)
        };
        format!("({}) -> {}", params_str.join(", "), return_str)
    }
}
