// src/sema/type_table.rs
//
// Opaque type identities with optional printable names.

use std::collections::HashMap;

use crate::identity::{NameId, NameTable, TypeDefId};
use crate::sema::implement_registry::PrimitiveTypeId;
use crate::sema::types::{LegacyType, NominalType, PrimitiveType};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeKey(u32);

impl TypeKey {
    pub fn index(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone)]
pub struct TypeInfo {
    pub ty: LegacyType,
    pub name_id: Option<NameId>,
}

#[derive(Debug, Clone)]
pub struct TypeTable {
    types: Vec<TypeInfo>,
    name_lookup: HashMap<NameId, TypeKey>,
    type_def_lookup: HashMap<TypeDefId, TypeKey>,
    type_lookup: HashMap<LegacyType, TypeKey>,
    primitive_names: HashMap<PrimitiveTypeId, NameId>,
    array_name: Option<NameId>,
}

impl TypeTable {
    pub fn new() -> Self {
        Self {
            types: Vec::new(),
            name_lookup: HashMap::new(),
            type_def_lookup: HashMap::new(),
            type_lookup: HashMap::new(),
            primitive_names: HashMap::new(),
            array_name: None,
        }
    }

    pub fn register_primitive_name(&mut self, prim: PrimitiveTypeId, name_id: NameId) {
        if self.primitive_names.contains_key(&prim) {
            return;
        }
        self.primitive_names.insert(prim, name_id);
        let ty = match prim {
            PrimitiveTypeId::I8 => LegacyType::Primitive(PrimitiveType::I8),
            PrimitiveTypeId::I16 => LegacyType::Primitive(PrimitiveType::I16),
            PrimitiveTypeId::I32 => LegacyType::Primitive(PrimitiveType::I32),
            PrimitiveTypeId::I64 => LegacyType::Primitive(PrimitiveType::I64),
            PrimitiveTypeId::I128 => LegacyType::Primitive(PrimitiveType::I128),
            PrimitiveTypeId::U8 => LegacyType::Primitive(PrimitiveType::U8),
            PrimitiveTypeId::U16 => LegacyType::Primitive(PrimitiveType::U16),
            PrimitiveTypeId::U32 => LegacyType::Primitive(PrimitiveType::U32),
            PrimitiveTypeId::U64 => LegacyType::Primitive(PrimitiveType::U64),
            PrimitiveTypeId::F32 => LegacyType::Primitive(PrimitiveType::F32),
            PrimitiveTypeId::F64 => LegacyType::Primitive(PrimitiveType::F64),
            PrimitiveTypeId::Bool => LegacyType::Primitive(PrimitiveType::Bool),
            PrimitiveTypeId::String => LegacyType::Primitive(PrimitiveType::String),
            PrimitiveTypeId::Range => LegacyType::Range,
        };
        let _ = self.insert_named(ty, name_id);
    }

    pub fn register_array_name(&mut self, name_id: NameId) {
        if self.array_name.is_some() {
            return;
        }
        self.array_name = Some(name_id);
    }

    pub fn primitive_name_id(&self, prim: PrimitiveTypeId) -> Option<NameId> {
        self.primitive_names.get(&prim).copied()
    }

    pub fn array_name_id(&self) -> Option<NameId> {
        self.array_name
    }

    pub fn insert_named(&mut self, ty: LegacyType, name_id: NameId) -> TypeKey {
        let id = self.insert(TypeInfo {
            ty,
            name_id: Some(name_id),
        });
        self.name_lookup.insert(name_id, id);
        id
    }

    pub fn insert_anonymous(&mut self, ty: LegacyType) -> TypeKey {
        self.insert(TypeInfo { ty, name_id: None })
    }

    pub fn by_name(&self, name_id: NameId) -> Option<TypeKey> {
        self.name_lookup.get(&name_id).copied()
    }

    pub fn info(&self, key: TypeKey) -> &TypeInfo {
        &self.types[key.0 as usize]
    }

    pub fn display(&self, key: TypeKey, names: &NameTable) -> String {
        let info = self.info(key);
        match info.name_id {
            Some(name_id) => names.display(name_id),
            None => info.ty.to_string(),
        }
    }

    pub fn display_type(
        &self,
        ty: &LegacyType,
        names: &NameTable,
        entity_registry: &crate::sema::entity_registry::EntityRegistry,
    ) -> String {
        self.display_type_inner(ty, names, entity_registry)
    }

    pub fn key_for_type(&mut self, ty: &LegacyType) -> TypeKey {
        match ty {
            // Primitives: use registered name if available, otherwise intern by type
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
                self.intern_primitive(prim_id, ty)
            }
            // Nominal types with TypeDefId: use type_def_lookup for deduplication
            LegacyType::Nominal(NominalType::Class(class_type)) => {
                self.intern_type_def(ty.clone(), class_type.type_def_id)
            }
            LegacyType::Nominal(NominalType::Record(record_type)) => {
                self.intern_type_def(ty.clone(), record_type.type_def_id)
            }
            LegacyType::Nominal(NominalType::Interface(interface_type)) => {
                // Non-generic interfaces use type_def_lookup, generic use type_lookup
                if interface_type.type_args.is_empty() {
                    self.intern_type_def(ty.clone(), interface_type.type_def_id)
                } else {
                    self.intern_type(ty.clone())
                }
            }
            // All other types: use direct Type hashing
            _ => self.intern_type(ty.clone()),
        }
    }

    fn insert(&mut self, info: TypeInfo) -> TypeKey {
        let id = TypeKey(self.types.len() as u32);
        self.types.push(info);
        id
    }

    fn intern_named(&mut self, ty: LegacyType, name_id: NameId) -> TypeKey {
        if let Some(key) = self.name_lookup.get(&name_id) {
            return *key;
        }
        self.insert_named(ty, name_id)
    }

    fn intern_type_def(&mut self, ty: LegacyType, type_def_id: TypeDefId) -> TypeKey {
        if let Some(key) = self.type_def_lookup.get(&type_def_id) {
            return *key;
        }
        let key = self.insert_anonymous(ty);
        self.type_def_lookup.insert(type_def_id, key);
        key
    }

    fn intern_type(&mut self, ty: LegacyType) -> TypeKey {
        if let Some(key) = self.type_lookup.get(&ty) {
            return *key;
        }
        let key = self.insert_anonymous(ty.clone());
        self.type_lookup.insert(ty, key);
        key
    }

    fn intern_primitive(&mut self, prim: PrimitiveTypeId, ty: &LegacyType) -> TypeKey {
        if let Some(name_id) = self.primitive_names.get(&prim) {
            self.intern_named(ty.clone(), *name_id)
        } else {
            self.intern_type(ty.clone())
        }
    }

    fn display_type_inner(
        &self,
        ty: &LegacyType,
        names: &NameTable,
        entity_registry: &crate::sema::entity_registry::EntityRegistry,
    ) -> String {
        match ty {
            LegacyType::Function(ft) => {
                let params = ft
                    .params
                    .iter()
                    .map(|param| self.display_type_inner(param, names, entity_registry))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(
                    "({}) -> {}",
                    params,
                    self.display_type_inner(&ft.return_type, names, entity_registry)
                )
            }
            LegacyType::Union(variants) => variants
                .iter()
                .map(|variant| self.display_type_inner(variant, names, entity_registry))
                .collect::<Vec<_>>()
                .join(" | "),
            LegacyType::Array(elem) => {
                format!(
                    "[{}]",
                    self.display_type_inner(elem, names, entity_registry)
                )
            }
            LegacyType::Nominal(NominalType::Class(class_type)) => {
                let type_def = entity_registry.get_type(class_type.type_def_id);
                let base = names.display(type_def.name_id);
                if class_type.type_args.is_empty() {
                    base
                } else {
                    let arg_list = class_type
                        .type_args
                        .iter()
                        .map(|arg| self.display_type_inner(arg, names, entity_registry))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{}<{}>", base, arg_list)
                }
            }
            LegacyType::Nominal(NominalType::Record(record_type)) => {
                let type_def = entity_registry.get_type(record_type.type_def_id);
                let base = names.display(type_def.name_id);
                if record_type.type_args.is_empty() {
                    base
                } else {
                    let arg_list = record_type
                        .type_args
                        .iter()
                        .map(|arg| self.display_type_inner(arg, names, entity_registry))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{}<{}>", base, arg_list)
                }
            }
            LegacyType::Nominal(NominalType::Interface(interface_type)) => {
                let name_id = entity_registry.name_id(interface_type.type_def_id);
                let base = names.display(name_id);
                if interface_type.type_args.is_empty() {
                    base
                } else {
                    let arg_list = interface_type
                        .type_args
                        .iter()
                        .map(|arg| self.display_type_inner(arg, names, entity_registry))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{}<{}>", base, arg_list)
                }
            }
            LegacyType::Nominal(NominalType::Error(error_type)) => {
                names.display(entity_registry.name_id(error_type.type_def_id))
            }
            LegacyType::Fallible(ft) => format!(
                "fallible({}, {})",
                self.display_type_inner(&ft.success_type, names, entity_registry),
                self.display_type_inner(&ft.error_type, names, entity_registry)
            ),
            LegacyType::Module(module_type) => {
                format!("module(\"{}\")", names.module_path(module_type.module_id))
            }
            LegacyType::TypeParam(name_id) => {
                // For TypeParam, display the NameId
                // In practice, TypeParams should be substituted before display
                names.display(*name_id)
            }
            LegacyType::TypeParamRef(type_param_id) => {
                // TypeParamRef displays by its internal ID
                format!("TypeParam#{}", type_param_id.index())
            }
            LegacyType::Tuple(elements) => {
                let elem_list = elements
                    .iter()
                    .map(|elem| self.display_type_inner(elem, names, entity_registry))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("[{}]", elem_list)
            }
            _ => ty.name().to_string(),
        }
    }
}

impl Default for TypeTable {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::Interner;
    use crate::sema::entity_defs::TypeDefKind;
    use crate::sema::entity_registry::EntityRegistry;

    #[test]
    fn type_table_uses_name_when_available() {
        let mut interner = Interner::new();
        let foo = interner.intern("Foo");

        let mut names = NameTable::new();
        let main_module = names.main_module();
        let name_id = names.intern(main_module, &[foo], &interner);

        // Create EntityRegistry and register a class type to get TypeDefId
        let mut entity_registry = EntityRegistry::new();
        let type_def_id = entity_registry.register_type(name_id, TypeDefKind::Class, main_module);

        let mut types = TypeTable::new();
        let key = types.insert_named(
            LegacyType::Nominal(NominalType::Class(crate::sema::ClassType {
                type_def_id,
                type_args: vec![].into(),
                type_args_id: None,
            })),
            name_id,
        );

        assert_eq!(types.display(key, &names), "main::Foo");
    }
}
