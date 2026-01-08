// src/sema/interface_registry.rs

use crate::frontend::Symbol;
use crate::sema::implement_registry::ExternalMethodInfo;
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
    /// String name for cross-interner lookups
    pub name_str: String,
    pub type_params: Vec<Symbol>,
    pub extends: Vec<Symbol>,
    pub fields: Vec<InterfaceFieldDef>,
    pub methods: Vec<InterfaceMethodDef>,
    pub external_methods: HashMap<Symbol, ExternalMethodInfo>,
}

/// Registry of all interface definitions
/// NOTE: Uses String keys instead of Symbol to allow cross-interner lookups
/// (prelude uses different interner than user code)
#[derive(Debug, Default, Clone)]
pub struct InterfaceRegistry {
    interfaces: HashMap<String, InterfaceDef>,
}

impl InterfaceRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register an interface definition
    pub fn register(&mut self, def: InterfaceDef) {
        self.interfaces.insert(def.name_str.clone(), def);
    }

    /// Look up an interface by string name
    pub fn get_by_str(&self, name: &str) -> Option<&InterfaceDef> {
        self.interfaces.get(name)
    }

    /// Look up an interface by Symbol (requires interner to resolve)
    pub fn get(&self, name: Symbol, interner: &crate::frontend::Interner) -> Option<&InterfaceDef> {
        let name_str = interner.resolve(name);
        self.interfaces.get(name_str)
    }

    /// Look up an external binding for an interface method
    pub fn external_method(
        &self,
        interface: Symbol,
        method: Symbol,
        interner: &crate::frontend::Interner,
    ) -> Option<&ExternalMethodInfo> {
        let interface = self.get(interface, interner)?;
        interface.external_methods.get(&method)
    }

    /// Check if every interface method is bound to an external function
    pub fn is_external_only(
        &self,
        interface: Symbol,
        interner: &crate::frontend::Interner,
    ) -> bool {
        let Some(def) = self.get(interface, interner) else {
            return false;
        };
        if def.methods.is_empty() || def.external_methods.len() != def.methods.len() {
            return false;
        }
        def.methods
            .iter()
            .all(|method| def.external_methods.contains_key(&method.name) && !method.has_default)
    }

    /// Merge another registry into this one
    pub fn merge(&mut self, other: &InterfaceRegistry) {
        for (name, def) in &other.interfaces {
            self.interfaces.insert(name.clone(), def.clone());
        }
    }

    /// Check if an interface is a functional interface (single abstract method, no fields)
    pub fn is_functional(
        &self,
        name: Symbol,
        interner: &crate::frontend::Interner,
    ) -> Option<&InterfaceMethodDef> {
        let name_str = interner.resolve(name);
        let interface = self.interfaces.get(name_str)?;

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
    use crate::frontend::Interner;

    fn sym(id: u32) -> Symbol {
        Symbol(id)
    }

    #[test]
    fn register_and_get_interface() {
        let mut registry = InterfaceRegistry::new();
        let def = InterfaceDef {
            name: sym(1),
            name_str: "TestInterface".to_string(),
            type_params: Vec::new(),
            extends: vec![],
            fields: vec![],
            methods: vec![InterfaceMethodDef {
                name: sym(2),
                params: vec![],
                return_type: Type::I64,
                has_default: false,
            }],
            external_methods: HashMap::new(),
        };
        registry.register(def);

        let retrieved = registry.get_by_str("TestInterface");
        assert!(retrieved.is_some());
        assert_eq!(retrieved.unwrap().methods.len(), 1);
    }

    #[test]
    fn is_functional_with_single_method() {
        let mut registry = InterfaceRegistry::new();
        let mut interner = Interner::new();
        let name_sym = interner.intern("Runnable");
        let def = InterfaceDef {
            name: name_sym,
            name_str: "Runnable".to_string(),
            type_params: Vec::new(),
            extends: vec![],
            fields: vec![],
            methods: vec![InterfaceMethodDef {
                name: sym(2),
                params: vec![Type::I32],
                return_type: Type::Bool,
                has_default: false,
            }],
            external_methods: HashMap::new(),
        };
        registry.register(def);

        assert!(registry.is_functional(name_sym, &interner).is_some());
    }

    #[test]
    fn not_functional_with_fields() {
        let mut registry = InterfaceRegistry::new();
        let mut interner = Interner::new();
        let name_sym = interner.intern("HasField");
        let def = InterfaceDef {
            name: name_sym,
            name_str: "HasField".to_string(),
            type_params: Vec::new(),
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
            external_methods: HashMap::new(),
        };
        registry.register(def);

        assert!(registry.is_functional(name_sym, &interner).is_none());
    }

    #[test]
    fn not_functional_with_multiple_abstract_methods() {
        let mut registry = InterfaceRegistry::new();
        let mut interner = Interner::new();
        let name_sym = interner.intern("MultiMethod");
        let def = InterfaceDef {
            name: name_sym,
            name_str: "MultiMethod".to_string(),
            type_params: Vec::new(),
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
            external_methods: HashMap::new(),
        };
        registry.register(def);

        assert!(registry.is_functional(name_sym, &interner).is_none());
    }

    #[test]
    fn functional_ignores_default_methods() {
        let mut registry = InterfaceRegistry::new();
        let mut interner = Interner::new();
        let name_sym = interner.intern("WithDefault");
        let def = InterfaceDef {
            name: name_sym,
            name_str: "WithDefault".to_string(),
            type_params: Vec::new(),
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
            external_methods: HashMap::new(),
        };
        registry.register(def);

        // Should be functional - only one abstract method
        assert!(registry.is_functional(name_sym, &interner).is_some());
    }

    #[test]
    fn merge_registries() {
        let mut registry1 = InterfaceRegistry::new();
        let mut registry2 = InterfaceRegistry::new();

        registry1.register(InterfaceDef {
            name: sym(1),
            name_str: "Interface1".to_string(),
            type_params: Vec::new(),
            extends: vec![],
            fields: vec![],
            methods: vec![InterfaceMethodDef {
                name: sym(10),
                params: vec![Type::I64],
                return_type: Type::Bool,
                has_default: false,
            }],
            external_methods: HashMap::new(),
        });

        registry2.register(InterfaceDef {
            name: sym(2),
            name_str: "Interface2".to_string(),
            type_params: Vec::new(),
            extends: vec![],
            fields: vec![],
            methods: vec![InterfaceMethodDef {
                name: sym(11),
                params: vec![],
                return_type: Type::String,
                has_default: false,
            }],
            external_methods: HashMap::new(),
        });

        registry1.merge(&registry2);

        assert!(registry1.get_by_str("Interface1").is_some());
        assert!(registry1.get_by_str("Interface2").is_some());
    }
}
