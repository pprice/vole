// src/sema/implement_registry.rs

use crate::frontend::Symbol;
use crate::identity::NameId;
use crate::sema::type_arena::{Type as ArenaType, TypeArena, TypeId};
use crate::sema::type_table::TypeTable;
use crate::sema::types::{FunctionType, LegacyType, NominalType, PrimitiveType};
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

/// Unique identifier for types in the implement registry.
/// Used for method lookup on types via implement blocks.
/// Note: This is different from type_arena::ImplTypeId which is for interned types.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct ImplTypeId(NameId);

impl ImplTypeId {
    pub fn from_name_id(name_id: NameId) -> Self {
        ImplTypeId(name_id)
    }

    /// Convert a Type to an ImplTypeId for registry lookup
    pub fn from_type(
        ty: &LegacyType,
        types: &TypeTable,
        entity_registry: &crate::sema::entity_registry::EntityRegistry,
    ) -> Option<Self> {
        match ty {
            LegacyType::Primitive(prim) => {
                let prim_id = match prim {
                    PrimitiveType::I8 => PrimitiveTypeId::I8,
                    PrimitiveType::I16 => PrimitiveTypeId::I16,
                    PrimitiveType::I32 => PrimitiveTypeId::I32,
                    PrimitiveType::I64 => PrimitiveTypeId::I64,
                    PrimitiveType::I128 => PrimitiveTypeId::I128,
                    PrimitiveType::U8 => PrimitiveTypeId::U8,
                    PrimitiveType::U16 => PrimitiveTypeId::U16,
                    PrimitiveType::U32 => PrimitiveTypeId::U32,
                    PrimitiveType::U64 => PrimitiveTypeId::U64,
                    PrimitiveType::F32 => PrimitiveTypeId::F32,
                    PrimitiveType::F64 => PrimitiveTypeId::F64,
                    PrimitiveType::Bool => PrimitiveTypeId::Bool,
                    PrimitiveType::String => PrimitiveTypeId::String,
                };
                types.primitive_name_id(prim_id).map(ImplTypeId)
            }
            LegacyType::Range => types
                .primitive_name_id(PrimitiveTypeId::Range)
                .map(ImplTypeId),
            LegacyType::Array(_) => types.array_name_id().map(ImplTypeId),
            LegacyType::Nominal(NominalType::Class(c)) => {
                Some(ImplTypeId(entity_registry.class_name_id(c)))
            }
            LegacyType::Nominal(NominalType::Record(r)) => {
                Some(ImplTypeId(entity_registry.record_name_id(r)))
            }
            _ => None,
        }
    }

    /// Convert a TypeId to an ImplTypeId for registry lookup (no LegacyType conversion needed)
    pub fn from_type_id(
        ty: TypeId,
        arena: &TypeArena,
        types: &TypeTable,
        entity_registry: &crate::sema::entity_registry::EntityRegistry,
    ) -> Option<Self> {
        match arena.get(ty) {
            ArenaType::Primitive(prim) => {
                let prim_id = match prim {
                    PrimitiveType::I8 => PrimitiveTypeId::I8,
                    PrimitiveType::I16 => PrimitiveTypeId::I16,
                    PrimitiveType::I32 => PrimitiveTypeId::I32,
                    PrimitiveType::I64 => PrimitiveTypeId::I64,
                    PrimitiveType::I128 => PrimitiveTypeId::I128,
                    PrimitiveType::U8 => PrimitiveTypeId::U8,
                    PrimitiveType::U16 => PrimitiveTypeId::U16,
                    PrimitiveType::U32 => PrimitiveTypeId::U32,
                    PrimitiveType::U64 => PrimitiveTypeId::U64,
                    PrimitiveType::F32 => PrimitiveTypeId::F32,
                    PrimitiveType::F64 => PrimitiveTypeId::F64,
                    PrimitiveType::Bool => PrimitiveTypeId::Bool,
                    PrimitiveType::String => PrimitiveTypeId::String,
                };
                types.primitive_name_id(prim_id).map(ImplTypeId)
            }
            ArenaType::Range => types
                .primitive_name_id(PrimitiveTypeId::Range)
                .map(ImplTypeId),
            ArenaType::Array(_) => types.array_name_id().map(ImplTypeId),
            ArenaType::Class { type_def_id, .. } => {
                Some(ImplTypeId(entity_registry.get_type(*type_def_id).name_id))
            }
            ArenaType::Record { type_def_id, .. } => {
                Some(ImplTypeId(entity_registry.get_type(*type_def_id).name_id))
            }
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
    pub type_id: ImplTypeId,
    pub method_name: NameId,
}

/// Info for external (native) methods
#[derive(Debug, Clone)]
pub struct ExternalMethodInfo {
    pub module_path: String,
    pub native_name: String,
    /// Declared Vole return type (for external functions with generic return types like Iterator<T>)
    /// Boxed to reduce enum variant size in ResolvedMethod
    pub return_type: Option<Box<LegacyType>>,
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
#[derive(Debug, Default, Clone)]
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
    pub fn register_method(&mut self, type_id: ImplTypeId, method_name: NameId, impl_: MethodImpl) {
        let key = MethodKey {
            type_id,
            method_name,
        };
        self.methods.insert(key, impl_);
    }

    /// Look up a method for a type
    pub fn get_method(&self, type_id: &ImplTypeId, method_name: NameId) -> Option<&MethodImpl> {
        let key = MethodKey {
            type_id: *type_id,
            method_name,
        };
        self.methods.get(&key)
    }

    /// Get all methods for a type
    pub fn get_methods_for_type(&self, type_id: &ImplTypeId) -> Vec<(NameId, &MethodImpl)> {
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
        let type_id = ImplTypeId(array_name);

        registry.register_method(
            type_id,
            method_id,
            MethodImpl {
                trait_name: Some(sym(2)), // "Sized"
                func_type: FunctionType { params: vec![].into(), return_type: Box::new(LegacyType::Primitive(PrimitiveType::I64)), is_closure: false, params_id: None, return_type_id: None },
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
        let method = registry.get_method(&ImplTypeId(array_name), method_id);
        assert!(method.is_none());
    }

    #[test]
    fn type_id_from_type() {
        let mut names = crate::identity::NameTable::new();
        let mut types = TypeTable::new();
        let entity_registry = crate::sema::entity_registry::EntityRegistry::new();
        // Use pre-registered primitives from NameTable
        let i64_name = names.primitives.i64;
        let builtin = names.builtin_module();
        let array_name = names.intern_raw(builtin, &["array"]);
        types.register_primitive_name(PrimitiveTypeId::I64, i64_name);
        types.register_array_name(array_name);

        assert_eq!(
            ImplTypeId::from_type(
                &LegacyType::Primitive(PrimitiveType::I64),
                &types,
                &entity_registry
            ),
            Some(ImplTypeId(i64_name))
        );
        assert_eq!(
            ImplTypeId::from_type(
                &LegacyType::Array(Box::new(LegacyType::Primitive(PrimitiveType::I32))),
                &types,
                &entity_registry
            ),
            Some(ImplTypeId(array_name))
        );
        assert_eq!(
            ImplTypeId::from_type(&LegacyType::Void, &types, &entity_registry),
            None
        );
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
        let type_id = ImplTypeId(string_name);

        registry.register_method(
            type_id,
            length_id,
            MethodImpl {
                trait_name: None,
                func_type: FunctionType { params: vec![].into(), return_type: Box::new(LegacyType::Primitive(PrimitiveType::I64)), is_closure: false, params_id: None, return_type_id: None },
                is_builtin: true,
                external_info: None,
            },
        );

        registry.register_method(
            type_id,
            to_upper_id,
            MethodImpl {
                trait_name: None,
                func_type: FunctionType { params: vec![].into(), return_type: Box::new(LegacyType::Primitive(PrimitiveType::String)), is_closure: false, params_id: None, return_type_id: None },
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
            ImplTypeId(i64_name),
            equals_id,
            MethodImpl {
                trait_name: Some(sym(20)), // "Equatable"
                func_type: FunctionType { params: vec![LegacyType::Primitive(PrimitiveType::I64)].into(), return_type: Box::new(LegacyType::Primitive(PrimitiveType::Bool)), is_closure: false, params_id: None, return_type_id: None },
                is_builtin: false,
                external_info: None,
            },
        );

        // Add different method to registry2
        registry2.register_method(
            ImplTypeId(string_name),
            length_id,
            MethodImpl {
                trait_name: None,
                func_type: FunctionType { params: vec![].into(), return_type: Box::new(LegacyType::Primitive(PrimitiveType::I64)), is_closure: false, params_id: None, return_type_id: None },
                is_builtin: false,
                external_info: None,
            },
        );

        // Merge registry2 into registry1
        registry1.merge(&registry2);

        // Both methods should be present
        assert!(
            registry1
                .get_method(&ImplTypeId(i64_name), equals_id)
                .is_some()
        );
        assert!(
            registry1
                .get_method(&ImplTypeId(string_name), length_id)
                .is_some()
        );
    }
}
