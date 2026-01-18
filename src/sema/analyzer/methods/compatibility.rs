use super::super::*;
use crate::identity::TypeDefId;
use crate::sema::compatibility::{TypeCompatibility, types_compatible_core_id};
use crate::sema::type_arena::TypeId as ArenaTypeId;
use crate::sema::types::{LegacyType, NominalType};
use std::collections::HashSet;

#[allow(dead_code)]
impl Analyzer {
    /// Check type compatibility using TypeId (Phase 3 version).
    /// Uses TypeId-based interface checks where possible.
    #[allow(unused)] // Phase 3 infrastructure
    pub(crate) fn types_compatible_id(
        &mut self,
        from: ArenaTypeId,
        to: ArenaTypeId,
        interner: &Interner,
    ) -> bool {
        // Use the core TypeId-based compatibility check
        if types_compatible_core_id(from, to, &self.type_arena.borrow()) {
            return true;
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
        // Extract interface info using TypeId
        let to_iface_id = {
            let arena = self.type_arena.borrow();
            arena.unwrap_interface(to).map(|(id, _)| id)
        };

        let Some(to_iface_id) = to_iface_id else {
            return false;
        };

        // Check interface extension
        let from_iface_id = {
            let arena = self.type_arena.borrow();
            arena.unwrap_interface(from).map(|(id, _)| id)
        };
        if let Some(from_iface_id) = from_iface_id
            && self.interface_extends_by_type_def_id(from_iface_id, to_iface_id)
        {
            return true;
        }

        // Check structural compatibility using TypeId
        if self.satisfies_interface_by_type_def_id_typeid(from, to_iface_id, interner) {
            return true;
        }

        // Check function type compatibility with functional interface
        let fn_info = {
            let arena = self.type_arena.borrow();
            arena.unwrap_function(from).map(|(params, ret, _)| {
                (params.to_vec(), ret)
            })
        };

        if let Some((fn_param_ids, fn_ret)) = fn_info
            && let Some(iface_fn) = self.get_functional_interface_type_by_type_def_id(to_iface_id)
            && fn_param_ids.len() == iface_fn.params.len()
        {
            // Pre-compute interface param TypeIds
            let iface_param_ids: Vec<ArenaTypeId> = iface_fn
                .params
                .iter()
                .map(|p| self.type_to_id(p))
                .collect();
            let iface_ret_id = self.type_to_id(&iface_fn.return_type);

            // Now check compatibility
            let arena = self.type_arena.borrow();
            let params_match = fn_param_ids
                .iter()
                .zip(iface_param_ids.iter())
                .all(|(&p, &ip)| types_compatible_core_id(p, ip, &arena));

            if params_match && types_compatible_core_id(fn_ret, iface_ret_id, &arena) {
                return true;
            }
        }

        false
    }

    /// Interface-related compatibility checks (extracted for reuse)
    fn types_compatible_legacy_interface(
        &self,
        from: &LegacyType,
        to: &LegacyType,
        interner: &Interner,
    ) -> bool {
        // Non-functional interface compatibility
        if let LegacyType::Nominal(NominalType::Interface(iface)) = to {
            if let LegacyType::Nominal(NominalType::Interface(from_iface)) = from
                && self.interface_extends_by_type_def_id(from_iface.type_def_id, iface.type_def_id)
            {
                return true;
            }

            if self.satisfies_interface_via_entity_registry(from, iface.type_def_id, interner) {
                return true;
            }
        }

        // Function type is compatible with functional interface if signatures match
        if let LegacyType::Function(fn_type) = from
            && let LegacyType::Nominal(NominalType::Interface(iface)) = to
            && let Some(iface_fn) =
                self.get_functional_interface_type_by_type_def_id(iface.type_def_id)
            && fn_type.is_compatible_with_interface(&iface_fn)
        {
            return true;
        }

        false
    }

    pub(crate) fn types_compatible(
        &self,
        from: &LegacyType,
        to: &LegacyType,
        interner: &Interner,
    ) -> bool {
        // Use the core compatibility check for most cases
        if from.is_compatible(to) {
            return true;
        }

        // Non-functional interface compatibility
        if let LegacyType::Nominal(NominalType::Interface(iface)) = to {
            if let LegacyType::Nominal(NominalType::Interface(from_iface)) = from
                && self.interface_extends_by_type_def_id(from_iface.type_def_id, iface.type_def_id)
            {
                return true;
            }

            if self.satisfies_interface_via_entity_registry(from, iface.type_def_id, interner) {
                return true;
            }
        }

        // Function type is compatible with functional interface if signatures match
        if let LegacyType::Function(fn_type) = from
            && let LegacyType::Nominal(NominalType::Interface(iface)) = to
            && let Some(iface_fn) =
                self.get_functional_interface_type_by_type_def_id(iface.type_def_id)
            && fn_type.is_compatible_with_interface(&iface_fn)
        {
            return true;
        }

        false
    }

    #[allow(dead_code)]
    fn interface_extends(&self, derived: Symbol, base: Symbol, interner: &Interner) -> bool {
        if derived == base {
            return true;
        }

        // Look up both interfaces via EntityRegistry
        let derived_str = interner.resolve(derived);
        let base_str = interner.resolve(base);
        let resolver = self.resolver(interner);

        let derived_id = resolver.resolve_type_str_or_interface(derived_str, &self.entity_registry);

        let base_id = resolver.resolve_type_str_or_interface(base_str, &self.entity_registry);

        let (Some(derived_id), Some(base_id)) = (derived_id, base_id) else {
            return false;
        };

        self.interface_extends_by_type_def_id(derived_id, base_id)
    }

    fn interface_extends_by_name_id(
        &self,
        derived: NameId,
        base: NameId,
        _interner: &Interner,
    ) -> bool {
        if derived == base {
            return true;
        }

        // Look up TypeDefIds via EntityRegistry
        let derived_id = self.entity_registry.type_by_name(derived);
        let base_id = self.entity_registry.type_by_name(base);

        let (Some(derived_id), Some(base_id)) = (derived_id, base_id) else {
            return false;
        };

        self.interface_extends_by_type_def_id(derived_id, base_id)
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
            let def = self.entity_registry.get_type(current);
            for &parent_id in &def.extends {
                if parent_id == base {
                    return true;
                }
                stack.push(parent_id);
            }
        }

        false
    }

    /// Format a method signature for error messages
    pub(crate) fn format_method_signature(
        &mut self,
        params: &[LegacyType],
        return_type: &LegacyType,
        _interner: &Interner,
    ) -> String {
        let params_str: Vec<String> = params.iter().map(|t| self.type_display(t)).collect();
        format!(
            "({}) -> {}",
            params_str.join(", "),
            self.type_display(return_type)
        )
    }

    /// Format a method signature for interface requirement messages.
    /// Shows "Self" instead of "error" for LegacyType::Error (which represents Self in interfaces).
    pub(crate) fn format_interface_method_signature(
        &mut self,
        params: &[LegacyType],
        return_type: &LegacyType,
    ) -> String {
        let params_str: Vec<String> = params
            .iter()
            .map(|t| {
                if t.is_invalid() {
                    "Self".to_string()
                } else {
                    self.type_display(t)
                }
            })
            .collect();
        let return_str = if return_type.is_invalid() {
            "Self".to_string()
        } else {
            self.type_display(return_type)
        };
        format!("({}) -> {}", params_str.join(", "), return_str)
    }
}
