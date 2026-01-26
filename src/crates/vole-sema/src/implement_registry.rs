// src/sema/implement_registry.rs

use crate::type_arena::{SemaType as ArenaType, TypeArena, TypeId};
use crate::types::{FunctionType, PrimitiveType};
use rustc_hash::FxHashMap;
use vole_frontend::Symbol;
use vole_identity::NameId;

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

    /// Convert a TypeId to an ImplTypeId for registry lookup
    pub fn from_type_id(
        ty: TypeId,
        arena: &TypeArena,
        entity_registry: &crate::entity_registry::EntityRegistry,
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
                entity_registry.primitive_name_id(prim_id).map(ImplTypeId)
            }
            ArenaType::Range => entity_registry
                .primitive_name_id(PrimitiveTypeId::Range)
                .map(ImplTypeId),
            ArenaType::Array(_) => entity_registry.array_name_id().map(ImplTypeId),
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
    pub fn type_name(&self, names: &vole_identity::NameTable) -> String {
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

/// Info for external (native) methods.
/// Both fields are interned as single-segment NameIds for cheap Copy.
/// Use name_table.last_segment_str(field) to get the string value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExternalMethodInfo {
    pub module_path: NameId,
    pub native_name: NameId,
}

/// Type-to-intrinsic mapping for generic external functions.
/// Used during codegen to dispatch to the correct intrinsic based on concrete type.
#[derive(Debug, Clone)]
pub struct TypeMappingEntry {
    /// The concrete type that this mapping applies to
    pub type_id: TypeId,
    /// The intrinsic key to use when the function is called with this type
    pub intrinsic_key: String,
}

/// Info for generic external functions with type mappings.
/// Stored separately from ExternalMethodInfo because type mappings
/// require heap allocation (Vec) while ExternalMethodInfo is Copy.
#[derive(Debug, Clone)]
pub struct GenericExternalInfo {
    /// The module path for this external function
    pub module_path: NameId,
    /// Type-to-intrinsic mappings from the where block
    pub type_mappings: Vec<TypeMappingEntry>,
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
    methods: FxHashMap<MethodKey, MethodImpl>,
    /// External function info by string name (module path and native name) for prelude functions
    external_func_info: FxHashMap<String, ExternalMethodInfo>,
    /// Generic external function info with type mappings (from where blocks)
    generic_external_info: FxHashMap<String, GenericExternalInfo>,
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

    /// Register generic external function info with type mappings
    pub fn register_generic_external(&mut self, name: String, info: GenericExternalInfo) {
        self.generic_external_info.insert(name, info);
    }

    /// Look up generic external function info by name
    pub fn get_generic_external(&self, name: &str) -> Option<&GenericExternalInfo> {
        self.generic_external_info.get(name)
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
            self.external_func_info.insert(name.clone(), *info);
        }
        for (name, info) in &other.generic_external_info {
            self.generic_external_info
                .insert(name.clone(), info.clone());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TypeArena;

    fn sym(id: u32) -> Symbol {
        Symbol(id)
    }

    #[test]
    fn register_and_get_method() {
        let arena = TypeArena::new();
        let mut interner = vole_frontend::Interner::new();
        let length_sym = interner.intern("length");
        let mut names = vole_identity::NameTable::new();
        let builtin = names.builtin_module();
        let method_id = names.intern(builtin, &[length_sym], &interner);

        let mut registry = ImplementRegistry::new();
        let array_name = names.intern_raw(builtin, &["array"]);
        let type_id = ImplTypeId(array_name);

        registry.register_method(
            type_id,
            method_id,
            MethodImpl {
                trait_name: Some(sym(2)), // "Sized"
                func_type: FunctionType::from_ids(&[], arena.i64(), false),
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
        let mut interner = vole_frontend::Interner::new();
        let length_sym = interner.intern("length");
        let mut names = vole_identity::NameTable::new();
        let builtin = names.builtin_module();
        let method_id = names.intern(builtin, &[length_sym], &interner);

        let registry = ImplementRegistry::new();
        let array_name = names.intern_raw(builtin, &["array"]);
        let method = registry.get_method(&ImplTypeId(array_name), method_id);
        assert!(method.is_none());
    }

    #[test]
    fn impl_type_id_from_type_id() {
        use crate::type_arena::TypeId as ArenaTypeId;

        let mut arena = TypeArena::new();
        let mut names = vole_identity::NameTable::new();
        let mut entity_registry = crate::entity_registry::EntityRegistry::new();
        // Use pre-registered primitives from NameTable
        let i64_name = names.primitives.i64;
        let builtin = names.builtin_module();
        let array_name = names.intern_raw(builtin, &["array"]);
        entity_registry.register_primitive_name(PrimitiveTypeId::I64, i64_name);
        entity_registry.register_array_name(array_name);

        // Test primitive type
        assert_eq!(
            ImplTypeId::from_type_id(ArenaTypeId::I64, &arena, &entity_registry),
            Some(ImplTypeId(i64_name))
        );

        // Test array type
        let array_id = arena.array(ArenaTypeId::I32);
        assert_eq!(
            ImplTypeId::from_type_id(array_id, &arena, &entity_registry),
            Some(ImplTypeId(array_name))
        );

        // Test void (not registerable)
        assert_eq!(
            ImplTypeId::from_type_id(ArenaTypeId::VOID, &arena, &entity_registry),
            None
        );
    }

    #[test]
    fn get_methods_for_type() {
        let arena = TypeArena::new();
        let mut interner = vole_frontend::Interner::new();
        let length_sym = interner.intern("length");
        let to_upper_sym = interner.intern("to_upper");
        let mut registry = ImplementRegistry::new();
        let mut names = vole_identity::NameTable::new();
        // Use pre-registered primitives from NameTable
        let string_name = names.primitives.string;
        let builtin = names.builtin_module();
        let length_id = names.intern(builtin, &[length_sym], &interner);
        let to_upper_id = names.intern(builtin, &[to_upper_sym], &interner);
        let type_id = ImplTypeId(string_name);

        registry.register_method(
            type_id,
            length_id,
            MethodImpl {
                trait_name: None,
                func_type: FunctionType::from_ids(&[], arena.i64(), false),
                is_builtin: true,
                external_info: None,
            },
        );

        registry.register_method(
            type_id,
            to_upper_id,
            MethodImpl {
                trait_name: None,
                func_type: FunctionType::from_ids(&[], arena.string(), false),
                is_builtin: true,
                external_info: None,
            },
        );

        let methods = registry.get_methods_for_type(&type_id);
        assert_eq!(methods.len(), 2);
    }

    #[test]
    fn merge_registries() {
        let arena = TypeArena::new();
        let mut interner = vole_frontend::Interner::new();
        let equals_sym = interner.intern("equals");
        let length_sym = interner.intern("length");
        let mut registry1 = ImplementRegistry::new();
        let mut registry2 = ImplementRegistry::new();

        // Add method to registry1
        let mut names = vole_identity::NameTable::new();
        // Use pre-registered primitives from NameTable
        let i64_name = names.primitives.i64;
        let string_name = names.primitives.string;
        let builtin = names.builtin_module();

        let equals_id = names.intern(builtin, &[equals_sym], &interner);
        let length_id = names.intern(builtin, &[length_sym], &interner);

        registry1.register_method(
            ImplTypeId(i64_name),
            equals_id,
            MethodImpl {
                trait_name: Some(sym(20)), // "Equatable"
                func_type: FunctionType::from_ids(&[arena.i64()], arena.bool(), false),
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
                func_type: FunctionType::from_ids(&[], arena.i64(), false),
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
