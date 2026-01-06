// src/sema/interface_registry.rs

use crate::frontend::Symbol;
use crate::sema::types::Type;
use std::collections::HashMap;

/// Definition of an interface field requirement
#[derive(Debug, Clone)]
pub struct InterfaceFieldDef {
    pub name: Symbol,
    pub ty: Type,
}

/// Definition of an interface method requirement
#[derive(Debug, Clone)]
pub struct InterfaceMethodDef {
    pub name: Symbol,
    pub params: Vec<Type>,
    pub return_type: Type,
    pub has_default: bool,
}

/// Complete interface definition
#[derive(Debug, Clone)]
pub struct InterfaceDef {
    pub name: Symbol,
    pub extends: Vec<Symbol>,
    pub fields: Vec<InterfaceFieldDef>,
    pub methods: Vec<InterfaceMethodDef>,
}

/// Registry of all interface definitions
#[derive(Debug, Default, Clone)]
pub struct InterfaceRegistry {
    interfaces: HashMap<Symbol, InterfaceDef>,
}

impl InterfaceRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register an interface definition
    pub fn register(&mut self, def: InterfaceDef) {
        self.interfaces.insert(def.name, def);
    }

    /// Look up an interface by name
    pub fn get(&self, name: Symbol) -> Option<&InterfaceDef> {
        self.interfaces.get(&name)
    }

    /// Merge another registry into this one
    pub fn merge(&mut self, other: &InterfaceRegistry) {
        for (name, def) in &other.interfaces {
            self.interfaces.insert(*name, def.clone());
        }
    }

    /// Check if an interface is a functional interface (single abstract method, no fields)
    pub fn is_functional(&self, name: Symbol) -> Option<&InterfaceMethodDef> {
        let interface = self.interfaces.get(&name)?;

        // Must have no required fields
        if !interface.fields.is_empty() {
            return None;
        }

        // Count abstract methods (no default)
        let abstract_methods: Vec<_> = interface
            .methods
            .iter()
            .filter(|m| !m.has_default)
            .collect();

        // Exactly one abstract method = functional interface
        if abstract_methods.len() == 1 {
            Some(abstract_methods[0])
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sym(id: u32) -> Symbol {
        Symbol(id)
    }

    #[test]
    fn register_and_get_interface() {
        let mut registry = InterfaceRegistry::new();
        let def = InterfaceDef {
            name: sym(1),
            extends: vec![],
            fields: vec![],
            methods: vec![InterfaceMethodDef {
                name: sym(2),
                params: vec![],
                return_type: Type::I64,
                has_default: false,
            }],
        };
        registry.register(def);

        let retrieved = registry.get(sym(1));
        assert!(retrieved.is_some());
        assert_eq!(retrieved.unwrap().methods.len(), 1);
    }

    #[test]
    fn is_functional_with_single_method() {
        let mut registry = InterfaceRegistry::new();
        let def = InterfaceDef {
            name: sym(1),
            extends: vec![],
            fields: vec![],
            methods: vec![InterfaceMethodDef {
                name: sym(2),
                params: vec![Type::I32],
                return_type: Type::Bool,
                has_default: false,
            }],
        };
        registry.register(def);

        assert!(registry.is_functional(sym(1)).is_some());
    }

    #[test]
    fn not_functional_with_fields() {
        let mut registry = InterfaceRegistry::new();
        let def = InterfaceDef {
            name: sym(1),
            extends: vec![],
            fields: vec![InterfaceFieldDef {
                name: sym(3),
                ty: Type::String,
            }],
            methods: vec![InterfaceMethodDef {
                name: sym(2),
                params: vec![],
                return_type: Type::I64,
                has_default: false,
            }],
        };
        registry.register(def);

        assert!(registry.is_functional(sym(1)).is_none());
    }

    #[test]
    fn not_functional_with_multiple_abstract_methods() {
        let mut registry = InterfaceRegistry::new();
        let def = InterfaceDef {
            name: sym(1),
            extends: vec![],
            fields: vec![],
            methods: vec![
                InterfaceMethodDef {
                    name: sym(2),
                    params: vec![],
                    return_type: Type::I64,
                    has_default: false,
                },
                InterfaceMethodDef {
                    name: sym(3),
                    params: vec![],
                    return_type: Type::Bool,
                    has_default: false,
                },
            ],
        };
        registry.register(def);

        assert!(registry.is_functional(sym(1)).is_none());
    }

    #[test]
    fn functional_ignores_default_methods() {
        let mut registry = InterfaceRegistry::new();
        let def = InterfaceDef {
            name: sym(1),
            extends: vec![],
            fields: vec![],
            methods: vec![
                InterfaceMethodDef {
                    name: sym(2),
                    params: vec![],
                    return_type: Type::I64,
                    has_default: false,
                },
                InterfaceMethodDef {
                    name: sym(3),
                    params: vec![],
                    return_type: Type::Bool,
                    has_default: true, // default method
                },
            ],
        };
        registry.register(def);

        // Should be functional - only one abstract method
        assert!(registry.is_functional(sym(1)).is_some());
    }

    #[test]
    fn merge_registries() {
        let mut registry1 = InterfaceRegistry::new();
        let mut registry2 = InterfaceRegistry::new();

        registry1.register(InterfaceDef {
            name: sym(1),
            extends: vec![],
            fields: vec![],
            methods: vec![InterfaceMethodDef {
                name: sym(10),
                params: vec![Type::I64],
                return_type: Type::Bool,
                has_default: false,
            }],
        });

        registry2.register(InterfaceDef {
            name: sym(2),
            extends: vec![],
            fields: vec![],
            methods: vec![InterfaceMethodDef {
                name: sym(11),
                params: vec![],
                return_type: Type::String,
                has_default: false,
            }],
        });

        registry1.merge(&registry2);

        assert!(registry1.get(sym(1)).is_some());
        assert!(registry1.get(sym(2)).is_some());
    }
}
