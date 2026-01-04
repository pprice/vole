// src/sema/implement_registry.rs

use crate::frontend::Symbol;
use crate::sema::types::{FunctionType, Type};
use std::collections::HashMap;

/// Identifier for primitive types
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum PrimitiveTypeId {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Bool,
    String,
}

/// Unique identifier for types in the registry
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum TypeId {
    Primitive(PrimitiveTypeId),
    Array,  // All array types share methods
    Class(Symbol),
    Record(Symbol),
}

impl TypeId {
    /// Convert a Type to a TypeId for registry lookup
    pub fn from_type(ty: &Type) -> Option<Self> {
        match ty {
            Type::I8 => Some(TypeId::Primitive(PrimitiveTypeId::I8)),
            Type::I16 => Some(TypeId::Primitive(PrimitiveTypeId::I16)),
            Type::I32 => Some(TypeId::Primitive(PrimitiveTypeId::I32)),
            Type::I64 => Some(TypeId::Primitive(PrimitiveTypeId::I64)),
            Type::I128 => Some(TypeId::Primitive(PrimitiveTypeId::I128)),
            Type::U8 => Some(TypeId::Primitive(PrimitiveTypeId::U8)),
            Type::U16 => Some(TypeId::Primitive(PrimitiveTypeId::U16)),
            Type::U32 => Some(TypeId::Primitive(PrimitiveTypeId::U32)),
            Type::U64 => Some(TypeId::Primitive(PrimitiveTypeId::U64)),
            Type::F32 => Some(TypeId::Primitive(PrimitiveTypeId::F32)),
            Type::F64 => Some(TypeId::Primitive(PrimitiveTypeId::F64)),
            Type::Bool => Some(TypeId::Primitive(PrimitiveTypeId::Bool)),
            Type::String => Some(TypeId::Primitive(PrimitiveTypeId::String)),
            Type::Array(_) => Some(TypeId::Array),
            Type::Class(c) => Some(TypeId::Class(c.name)),
            Type::Record(r) => Some(TypeId::Record(r.name)),
            _ => None,
        }
    }
}

/// Key for looking up methods in the registry
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct MethodKey {
    pub type_id: TypeId,
    pub method_name: Symbol,
}

/// Implementation of a method
#[derive(Debug, Clone)]
pub struct MethodImpl {
    pub trait_name: Option<Symbol>,  // Which interface this implements
    pub func_type: FunctionType,     // Method signature
    pub is_builtin: bool,            // True for array.length(), etc.
}

/// Registry of methods added to types via `implement` blocks
#[derive(Debug, Default)]
pub struct ImplementRegistry {
    methods: HashMap<MethodKey, MethodImpl>,
}

impl ImplementRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a method for a type
    pub fn register_method(
        &mut self,
        type_id: TypeId,
        method_name: Symbol,
        impl_: MethodImpl,
    ) {
        let key = MethodKey { type_id, method_name };
        self.methods.insert(key, impl_);
    }

    /// Look up a method for a type
    pub fn get_method(&self, type_id: &TypeId, method_name: Symbol) -> Option<&MethodImpl> {
        let key = MethodKey {
            type_id: type_id.clone(),
            method_name,
        };
        self.methods.get(&key)
    }

    /// Get all methods for a type
    pub fn get_methods_for_type(&self, type_id: &TypeId) -> Vec<(Symbol, &MethodImpl)> {
        self.methods
            .iter()
            .filter(|(k, _)| &k.type_id == type_id)
            .map(|(k, v)| (k.method_name, v))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sym(id: u32) -> Symbol {
        Symbol(id)
    }

    #[test]
    fn register_and_get_method() {
        let mut registry = ImplementRegistry::new();
        let type_id = TypeId::Array;
        let method_name = sym(1); // "length"

        registry.register_method(
            type_id.clone(),
            method_name,
            MethodImpl {
                trait_name: Some(sym(2)), // "Sized"
                func_type: FunctionType {
                    params: vec![],
                    return_type: Box::new(Type::I64),
                    is_closure: false,
                },
                is_builtin: true,
            },
        );

        let method = registry.get_method(&type_id, method_name);
        assert!(method.is_some());
        assert!(method.unwrap().is_builtin);
    }

    #[test]
    fn get_nonexistent_method() {
        let registry = ImplementRegistry::new();
        let method = registry.get_method(&TypeId::Array, sym(1));
        assert!(method.is_none());
    }

    #[test]
    fn type_id_from_type() {
        assert_eq!(
            TypeId::from_type(&Type::I64),
            Some(TypeId::Primitive(PrimitiveTypeId::I64))
        );
        assert_eq!(
            TypeId::from_type(&Type::Array(Box::new(Type::I32))),
            Some(TypeId::Array)
        );
        assert_eq!(TypeId::from_type(&Type::Void), None);
    }

    #[test]
    fn get_methods_for_type() {
        let mut registry = ImplementRegistry::new();
        let type_id = TypeId::Primitive(PrimitiveTypeId::String);

        registry.register_method(
            type_id.clone(),
            sym(1), // "length"
            MethodImpl {
                trait_name: None,
                func_type: FunctionType {
                    params: vec![],
                    return_type: Box::new(Type::I64),
                    is_closure: false,
                },
                is_builtin: true,
            },
        );

        registry.register_method(
            type_id.clone(),
            sym(2), // "to_upper"
            MethodImpl {
                trait_name: None,
                func_type: FunctionType {
                    params: vec![],
                    return_type: Box::new(Type::String),
                    is_closure: false,
                },
                is_builtin: true,
            },
        );

        let methods = registry.get_methods_for_type(&type_id);
        assert_eq!(methods.len(), 2);
    }
}
