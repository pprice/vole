// src/sema/implement_registry.rs

use crate::frontend::Symbol;
use crate::identity::NameId;
use crate::sema::type_table::TypeTable;
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
    Range,
}

impl PrimitiveTypeId {
    /// Get the string name for this primitive type (used in method mangling)
    pub fn name(&self) -> &'static str {
        match self {
            PrimitiveTypeId::I8 => "i8",
            PrimitiveTypeId::I16 => "i16",
            PrimitiveTypeId::I32 => "i32",
            PrimitiveTypeId::I64 => "i64",
            PrimitiveTypeId::I128 => "i128",
            PrimitiveTypeId::U8 => "u8",
            PrimitiveTypeId::U16 => "u16",
            PrimitiveTypeId::U32 => "u32",
            PrimitiveTypeId::U64 => "u64",
            PrimitiveTypeId::F32 => "f32",
            PrimitiveTypeId::F64 => "f64",
            PrimitiveTypeId::Bool => "bool",
            PrimitiveTypeId::String => "string",
            PrimitiveTypeId::Range => "range",
        }
    }
}

/// Unique identifier for types in the registry
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct TypeId(NameId);

impl TypeId {
    pub fn from_name_id(name_id: NameId) -> Self {
        TypeId(name_id)
    }

    /// Convert a Type to a TypeId for registry lookup
    pub fn from_type(ty: &Type, types: &TypeTable) -> Option<Self> {
        match ty {
            Type::I8 => types.primitive_name_id(PrimitiveTypeId::I8).map(TypeId),
            Type::I16 => types.primitive_name_id(PrimitiveTypeId::I16).map(TypeId),
            Type::I32 => types.primitive_name_id(PrimitiveTypeId::I32).map(TypeId),
            Type::I64 => types.primitive_name_id(PrimitiveTypeId::I64).map(TypeId),
            Type::I128 => types.primitive_name_id(PrimitiveTypeId::I128).map(TypeId),
            Type::U8 => types.primitive_name_id(PrimitiveTypeId::U8).map(TypeId),
            Type::U16 => types.primitive_name_id(PrimitiveTypeId::U16).map(TypeId),
            Type::U32 => types.primitive_name_id(PrimitiveTypeId::U32).map(TypeId),
            Type::U64 => types.primitive_name_id(PrimitiveTypeId::U64).map(TypeId),
            Type::F32 => types.primitive_name_id(PrimitiveTypeId::F32).map(TypeId),
            Type::F64 => types.primitive_name_id(PrimitiveTypeId::F64).map(TypeId),
            Type::Bool => types.primitive_name_id(PrimitiveTypeId::Bool).map(TypeId),
            Type::String => types.primitive_name_id(PrimitiveTypeId::String).map(TypeId),
            Type::Range => types.primitive_name_id(PrimitiveTypeId::Range).map(TypeId),
            Type::Array(_) => types.array_name_id().map(TypeId),
            Type::Class(c) => Some(TypeId(c.name_id)),
            Type::Record(r) => Some(TypeId(r.name_id)),
            _ => None,
        }
    }

    /// Get the string name for method mangling (e.g., "i32" or record name)
    pub fn type_name(&self, names: &crate::identity::NameTable) -> String {
        names.display(self.0)
    }

    pub fn name_id(self) -> NameId {
        self.0
    }
}

/// Key for looking up methods in the registry
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct MethodKey {
    pub type_id: TypeId,
    pub method_name: NameId,
}

/// Info for external (native) methods
#[derive(Debug, Clone)]
pub struct ExternalMethodInfo {
    pub module_path: String,
    pub native_name: String,
    /// Declared Vole return type (for external functions with generic return types like Iterator<T>)
    /// Boxed to reduce enum variant size in ResolvedMethod
    pub return_type: Option<Box<Type>>,
}

/// Implementation of a method
#[derive(Debug, Clone)]
pub struct MethodImpl {
    pub trait_name: Option<Symbol>, // Which interface this implements
    pub func_type: FunctionType,    // Method signature
    pub is_builtin: bool,           // True for array.length(), etc.
    pub external_info: Option<ExternalMethodInfo>, // External (native) method info
}

/// Registry of methods added to types via `implement` blocks
#[derive(Debug, Default)]
pub struct ImplementRegistry {
    methods: HashMap<MethodKey, MethodImpl>,
    /// External function info by string name (module path and native name) for prelude functions
    external_func_info: HashMap<String, ExternalMethodInfo>,
}

impl ImplementRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register external function info for a function name
    pub fn register_external_func(&mut self, name: String, info: ExternalMethodInfo) {
        self.external_func_info.insert(name, info);
    }

    /// Look up external function info by name
    pub fn get_external_func(&self, name: &str) -> Option<&ExternalMethodInfo> {
        self.external_func_info.get(name)
    }

    /// Register a method for a type
    pub fn register_method(&mut self, type_id: TypeId, method_name: NameId, impl_: MethodImpl) {
        let key = MethodKey {
            type_id,
            method_name,
        };
        self.methods.insert(key, impl_);
    }

    /// Look up a method for a type
    pub fn get_method(&self, type_id: &TypeId, method_name: NameId) -> Option<&MethodImpl> {
        let key = MethodKey {
            type_id: *type_id,
            method_name,
        };
        self.methods.get(&key)
    }

    /// Get all methods for a type
    pub fn get_methods_for_type(&self, type_id: &TypeId) -> Vec<(NameId, &MethodImpl)> {
        self.methods
            .iter()
            .filter(|(k, _)| &k.type_id == type_id)
            .map(|(k, v)| (k.method_name, v))
            .collect()
    }

    /// Merge another registry into this one
    pub fn merge(&mut self, other: &ImplementRegistry) {
        for (key, method) in &other.methods {
            self.methods.insert(key.clone(), method.clone());
        }
        for (name, info) in &other.external_func_info {
            self.external_func_info.insert(name.clone(), info.clone());
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
    fn register_and_get_method() {
        let mut interner = crate::frontend::Interner::new();
        let length_sym = interner.intern("length");
        let mut names = crate::identity::NameTable::new();
        let builtin = names.builtin_module();
        let method_id = names.intern(builtin, &[length_sym], &interner);

        let mut registry = ImplementRegistry::new();
        let mut types = TypeTable::new();
        let array_name = names.intern_raw(builtin, &["array"]);
        types.register_array_name(array_name);
        let type_id = TypeId(array_name);

        registry.register_method(
            type_id.clone(),
            method_id,
            MethodImpl {
                trait_name: Some(sym(2)), // "Sized"
                func_type: FunctionType {
                    params: vec![],
                    return_type: Box::new(Type::I64),
                    is_closure: false,
                },
                is_builtin: true,
                external_info: None,
            },
        );

        let method = registry.get_method(&type_id, method_id);
        assert!(method.is_some());
        assert!(method.unwrap().is_builtin);
    }

    #[test]
    fn get_nonexistent_method() {
        let mut interner = crate::frontend::Interner::new();
        let length_sym = interner.intern("length");
        let mut names = crate::identity::NameTable::new();
        let builtin = names.builtin_module();
        let method_id = names.intern(builtin, &[length_sym], &interner);

        let registry = ImplementRegistry::new();
        let mut types = TypeTable::new();
        let array_name = names.intern_raw(builtin, &["array"]);
        types.register_array_name(array_name);
        let method = registry.get_method(&TypeId(array_name), method_id);
        assert!(method.is_none());
    }

    #[test]
    fn type_id_from_type() {
        let mut names = crate::identity::NameTable::new();
        let mut types = TypeTable::new();
        // Use pre-registered primitives from NameTable
        let i64_name = names.primitives.i64;
        let builtin = names.builtin_module();
        let array_name = names.intern_raw(builtin, &["array"]);
        types.register_primitive_name(PrimitiveTypeId::I64, i64_name);
        types.register_array_name(array_name);

        assert_eq!(
            TypeId::from_type(&Type::I64, &types),
            Some(TypeId(i64_name))
        );
        assert_eq!(
            TypeId::from_type(&Type::Array(Box::new(Type::I32)), &types),
            Some(TypeId(array_name))
        );
        assert_eq!(TypeId::from_type(&Type::Void, &types), None);
    }

    #[test]
    fn get_methods_for_type() {
        let mut interner = crate::frontend::Interner::new();
        let length_sym = interner.intern("length");
        let to_upper_sym = interner.intern("to_upper");
        let mut registry = ImplementRegistry::new();
        let mut names = crate::identity::NameTable::new();
        let mut types = TypeTable::new();
        // Use pre-registered primitives from NameTable
        let string_name = names.primitives.string;
        let builtin = names.builtin_module();
        let length_id = names.intern(builtin, &[length_sym], &interner);
        let to_upper_id = names.intern(builtin, &[to_upper_sym], &interner);
        types.register_primitive_name(PrimitiveTypeId::String, string_name);
        let type_id = TypeId(string_name);

        registry.register_method(
            type_id.clone(),
            length_id,
            MethodImpl {
                trait_name: None,
                func_type: FunctionType {
                    params: vec![],
                    return_type: Box::new(Type::I64),
                    is_closure: false,
                },
                is_builtin: true,
                external_info: None,
            },
        );

        registry.register_method(
            type_id.clone(),
            to_upper_id,
            MethodImpl {
                trait_name: None,
                func_type: FunctionType {
                    params: vec![],
                    return_type: Box::new(Type::String),
                    is_closure: false,
                },
                is_builtin: true,
                external_info: None,
            },
        );

        let methods = registry.get_methods_for_type(&type_id);
        assert_eq!(methods.len(), 2);
    }

    #[test]
    fn merge_registries() {
        let mut interner = crate::frontend::Interner::new();
        let equals_sym = interner.intern("equals");
        let length_sym = interner.intern("length");
        let mut registry1 = ImplementRegistry::new();
        let mut registry2 = ImplementRegistry::new();

        // Add method to registry1
        let mut names = crate::identity::NameTable::new();
        let mut types = TypeTable::new();
        // Use pre-registered primitives from NameTable
        let i64_name = names.primitives.i64;
        let string_name = names.primitives.string;
        let builtin = names.builtin_module();
        types.register_primitive_name(PrimitiveTypeId::I64, i64_name);
        types.register_primitive_name(PrimitiveTypeId::String, string_name);

        let equals_id = names.intern(builtin, &[equals_sym], &interner);
        let length_id = names.intern(builtin, &[length_sym], &interner);

        registry1.register_method(
            TypeId(i64_name),
            equals_id,
            MethodImpl {
                trait_name: Some(sym(20)), // "Equatable"
                func_type: FunctionType {
                    params: vec![Type::I64],
                    return_type: Box::new(Type::Bool),
                    is_closure: false,
                },
                is_builtin: false,
                external_info: None,
            },
        );

        // Add different method to registry2
        registry2.register_method(
            TypeId(string_name),
            length_id,
            MethodImpl {
                trait_name: None,
                func_type: FunctionType {
                    params: vec![],
                    return_type: Box::new(Type::I64),
                    is_closure: false,
                },
                is_builtin: false,
                external_info: None,
            },
        );

        // Merge registry2 into registry1
        registry1.merge(&registry2);

        // Both methods should be present
        assert!(registry1.get_method(&TypeId(i64_name), equals_id).is_some());
        assert!(
            registry1
                .get_method(&TypeId(string_name), length_id)
                .is_some()
        );
    }
}
