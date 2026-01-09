// src/sema/interface_registry.rs

use crate::frontend::Symbol;
use crate::identity::NameId;
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
    /// String name for cross-interner lookups
    pub name_str: String,
    pub params: Vec<Type>,
    pub return_type: Type,
    pub has_default: bool,
}

/// Complete interface definition
#[derive(Debug, Clone)]
pub struct InterfaceDef {
    pub name: Symbol,
    /// Canonical name ID for cross-interner lookups
    pub name_id: NameId,
    /// String name for error messages and debugging
    pub name_str: String,
    pub type_params: Vec<Symbol>,
    pub extends: Vec<Symbol>,
    pub fields: Vec<InterfaceFieldDef>,
    pub methods: Vec<InterfaceMethodDef>,
    /// External method bindings, keyed by method name STRING for cross-interner lookup
    pub external_methods: HashMap<String, ExternalMethodInfo>,
}

/// Registry of all interface definitions
/// Uses NameId keys for canonical cross-interner lookups
#[derive(Debug, Default, Clone)]
pub struct InterfaceRegistry {
    interfaces: HashMap<NameId, InterfaceDef>,
}

impl InterfaceRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register an interface definition
    pub fn register(&mut self, def: InterfaceDef) {
        self.interfaces.insert(def.name_id, def);
    }

    /// Look up an interface by NameId (canonical, cross-interner safe)
    pub fn get_by_name_id(&self, name_id: NameId) -> Option<&InterfaceDef> {
        self.interfaces.get(&name_id)
    }

    /// Look up an interface by Symbol (requires interner to resolve)
    /// Note: This iterates to find by string - prefer get_by_name_id when possible
    pub fn get(&self, name: Symbol, interner: &crate::frontend::Interner) -> Option<&InterfaceDef> {
        let name_str = interner.resolve(name);
        self.interfaces
            .values()
            .find(|def| def.name_str == name_str)
    }

    /// Look up an interface by string name directly (cross-interner safe)
    /// Use this when you have a string name but may not have the Symbol interned locally
    pub fn get_by_str(&self, name: &str) -> Option<&InterfaceDef> {
        self.interfaces.values().find(|def| def.name_str == name)
    }

    /// Look up an external binding for an interface method
    pub fn external_method(
        &self,
        interface_name_id: NameId,
        method: Symbol,
        interner: &crate::frontend::Interner,
    ) -> Option<&ExternalMethodInfo> {
        let interface = self.get_by_name_id(interface_name_id)?;
        let method_str = interner.resolve(method);
        interface.external_methods.get(method_str)
    }

    /// Check if every interface method is bound to an external function
    pub fn is_external_only(&self, interface_name_id: NameId) -> bool {
        let Some(def) = self.get_by_name_id(interface_name_id) else {
            return false;
        };
        if def.methods.is_empty() || def.external_methods.len() != def.methods.len() {
            return false;
        }
        def.methods.iter().all(|method| {
            def.external_methods.contains_key(&method.name_str) && !method.has_default
        })
    }

    /// Merge another registry into this one
    pub fn merge(&mut self, other: &InterfaceRegistry) {
        for (name_id, def) in &other.interfaces {
            self.interfaces.insert(*name_id, def.clone());
        }
    }

    /// Check if an interface is a functional interface (single abstract method, no fields)
    pub fn is_functional(
        &self,
        name: Symbol,
        interner: &crate::frontend::Interner,
    ) -> Option<&InterfaceMethodDef> {
        let interface = self.get(name, interner)?;

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
    use crate::identity::NameTable;

    #[test]
    fn register_and_get_interface() {
        let mut registry = InterfaceRegistry::new();
        let mut interner = Interner::new();
        let mut name_table = NameTable::new();
        let module_id = name_table.main_module();
        let name_sym = interner.intern("TestInterface");
        let name_id = name_table.intern(module_id, &[name_sym]);
        let method_sym = interner.intern("test_method");
        let def = InterfaceDef {
            name: name_sym,
            name_id,
            name_str: "TestInterface".to_string(),
            type_params: Vec::new(),
            extends: vec![],
            fields: vec![],
            methods: vec![InterfaceMethodDef {
                name: method_sym,
                name_str: "test_method".to_string(),
                params: vec![],
                return_type: Type::I64,
                has_default: false,
            }],
            external_methods: HashMap::new(),
        };
        registry.register(def);

        let retrieved = registry.get_by_name_id(name_id);
        assert!(retrieved.is_some());
        assert_eq!(retrieved.unwrap().methods.len(), 1);
    }

    #[test]
    fn is_functional_with_single_method() {
        let mut registry = InterfaceRegistry::new();
        let mut interner = Interner::new();
        let mut name_table = NameTable::new();
        let module_id = name_table.main_module();
        let name_sym = interner.intern("Runnable");
        let name_id = name_table.intern(module_id, &[name_sym]);
        let method_sym = interner.intern("run");
        let def = InterfaceDef {
            name: name_sym,
            name_id,
            name_str: "Runnable".to_string(),
            type_params: Vec::new(),
            extends: vec![],
            fields: vec![],
            methods: vec![InterfaceMethodDef {
                name: method_sym,
                name_str: "run".to_string(),
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
        let mut name_table = NameTable::new();
        let module_id = name_table.main_module();
        let name_sym = interner.intern("HasField");
        let name_id = name_table.intern(module_id, &[name_sym]);
        let field_sym = interner.intern("field");
        let method_sym = interner.intern("method");
        let def = InterfaceDef {
            name: name_sym,
            name_id,
            name_str: "HasField".to_string(),
            type_params: Vec::new(),
            extends: vec![],
            fields: vec![InterfaceFieldDef {
                name: field_sym,
                ty: Type::String,
            }],
            methods: vec![InterfaceMethodDef {
                name: method_sym,
                name_str: "method".to_string(),
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
        let mut name_table = NameTable::new();
        let module_id = name_table.main_module();
        let name_sym = interner.intern("MultiMethod");
        let name_id = name_table.intern(module_id, &[name_sym]);
        let method1_sym = interner.intern("method1");
        let method2_sym = interner.intern("method2");
        let def = InterfaceDef {
            name: name_sym,
            name_id,
            name_str: "MultiMethod".to_string(),
            type_params: Vec::new(),
            extends: vec![],
            fields: vec![],
            methods: vec![
                InterfaceMethodDef {
                    name: method1_sym,
                    name_str: "method1".to_string(),
                    params: vec![],
                    return_type: Type::I64,
                    has_default: false,
                },
                InterfaceMethodDef {
                    name: method2_sym,
                    name_str: "method2".to_string(),
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
        let mut name_table = NameTable::new();
        let module_id = name_table.main_module();
        let name_sym = interner.intern("WithDefault");
        let name_id = name_table.intern(module_id, &[name_sym]);
        let method1_sym = interner.intern("abstractMethod");
        let method2_sym = interner.intern("defaultMethod");
        let def = InterfaceDef {
            name: name_sym,
            name_id,
            name_str: "WithDefault".to_string(),
            type_params: Vec::new(),
            extends: vec![],
            fields: vec![],
            methods: vec![
                InterfaceMethodDef {
                    name: method1_sym,
                    name_str: "abstractMethod".to_string(),
                    params: vec![],
                    return_type: Type::I64,
                    has_default: false,
                },
                InterfaceMethodDef {
                    name: method2_sym,
                    name_str: "defaultMethod".to_string(),
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
        let mut interner = Interner::new();
        let mut name_table = NameTable::new();
        let module_id = name_table.main_module();

        let name1_sym = interner.intern("Interface1");
        let name1_id = name_table.intern(module_id, &[name1_sym]);
        let method1_sym = interner.intern("method1");
        registry1.register(InterfaceDef {
            name: name1_sym,
            name_id: name1_id,
            name_str: "Interface1".to_string(),
            type_params: Vec::new(),
            extends: vec![],
            fields: vec![],
            methods: vec![InterfaceMethodDef {
                name: method1_sym,
                name_str: "method1".to_string(),
                params: vec![Type::I64],
                return_type: Type::Bool,
                has_default: false,
            }],
            external_methods: HashMap::new(),
        });

        let name2_sym = interner.intern("Interface2");
        let name2_id = name_table.intern(module_id, &[name2_sym]);
        let method2_sym = interner.intern("method2");
        registry2.register(InterfaceDef {
            name: name2_sym,
            name_id: name2_id,
            name_str: "Interface2".to_string(),
            type_params: Vec::new(),
            extends: vec![],
            fields: vec![],
            methods: vec![InterfaceMethodDef {
                name: method2_sym,
                name_str: "method2".to_string(),
                params: vec![],
                return_type: Type::String,
                has_default: false,
            }],
            external_methods: HashMap::new(),
        });

        registry1.merge(&registry2);

        assert!(registry1.get_by_name_id(name1_id).is_some());
        assert!(registry1.get_by_name_id(name2_id).is_some());
    }
}
