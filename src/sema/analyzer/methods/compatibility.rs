use super::super::*;
use crate::identity::TypeDefId;
use std::collections::HashSet;

#[allow(dead_code)]
impl Analyzer {
    pub(crate) fn types_compatible(&self, from: &Type, to: &Type, interner: &Interner) -> bool {
        // Use the core compatibility check for most cases
        if types_compatible_core(from, to) {
            return true;
        }

        // Non-functional interface compatibility
        if let Type::Interface(iface) = to {
            if let Type::Interface(from_iface) = from
                && self.interface_extends_by_name_id(from_iface.name_id, iface.name_id, interner)
            {
                return true;
            }

            if self.satisfies_interface_via_entity_registry(from, iface.name_id, interner) {
                return true;
            }
        }

        // Function type is compatible with functional interface if signatures match
        if let Type::Function(fn_type) = from
            && let Type::Interface(iface) = to
            && let Some(iface_fn) = self.get_functional_interface_type_by_name_id(iface.name_id)
            && function_compatible_with_interface(fn_type, &iface_fn)
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

        let derived_id = self
            .name_table
            .name_id_raw(self.current_module, &[derived_str])
            .and_then(|name_id| self.entity_registry.type_by_name(name_id))
            .or_else(|| {
                self.entity_registry
                    .interface_by_short_name(derived_str, &self.name_table)
            });

        let base_id = self
            .name_table
            .name_id_raw(self.current_module, &[base_str])
            .and_then(|name_id| self.entity_registry.type_by_name(name_id))
            .or_else(|| {
                self.entity_registry
                    .interface_by_short_name(base_str, &self.name_table)
            });

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
        params: &[Type],
        return_type: &Type,
        _interner: &Interner,
    ) -> String {
        let params_str: Vec<String> = params.iter().map(|t| self.type_display(t)).collect();
        format!(
            "({}) -> {}",
            params_str.join(", "),
            self.type_display(return_type)
        )
    }
}
