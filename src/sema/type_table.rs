// src/sema/type_table.rs
//
// Opaque type identities with optional printable names.

use std::collections::HashMap;

use crate::identity::{ModuleId, NameId, NameTable, TypeDefId};
use crate::sema::Type;
use crate::sema::implement_registry::PrimitiveTypeId;
use crate::sema::types::{NominalType, PrimitiveType};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeKey(u32);

impl TypeKey {
    pub fn index(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone)]
pub struct TypeInfo {
    pub ty: Type,
    pub name_id: Option<NameId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum TypeFingerprint {
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
    Void,
    Nil,
    Done,
    Range,
    Unknown,
    Error,
    Type,
    Union(Vec<TypeKey>),
    Array(TypeKey),
    Interface {
        type_def_id: TypeDefId,
        args: Vec<TypeKey>,
    },
    ErrorType(TypeDefId),
    Function {
        params: Vec<TypeKey>,
        return_type: TypeKey,
    },
    Fallible {
        success: TypeKey,
        error: TypeKey,
    },
    Module(ModuleId),
    TypeParam(NameId),
    RuntimeIterator(TypeKey),
    Tuple(Vec<TypeKey>),
    FixedArray {
        element: TypeKey,
        size: usize,
    },
    Structural {
        fields: Vec<(NameId, TypeKey)>,
        methods: Vec<(NameId, Vec<TypeKey>, TypeKey)>,
    },
}

#[derive(Debug, Clone)]
pub struct TypeTable {
    types: Vec<TypeInfo>,
    name_lookup: HashMap<NameId, TypeKey>,
    type_def_lookup: HashMap<TypeDefId, TypeKey>,
    fingerprint_lookup: HashMap<TypeFingerprint, TypeKey>,
    primitive_names: HashMap<PrimitiveTypeId, NameId>,
    array_name: Option<NameId>,
}

impl TypeTable {
    pub fn new() -> Self {
        Self {
            types: Vec::new(),
            name_lookup: HashMap::new(),
            type_def_lookup: HashMap::new(),
            fingerprint_lookup: HashMap::new(),
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
            PrimitiveTypeId::I8 => Type::Primitive(PrimitiveType::I8),
            PrimitiveTypeId::I16 => Type::Primitive(PrimitiveType::I16),
            PrimitiveTypeId::I32 => Type::Primitive(PrimitiveType::I32),
            PrimitiveTypeId::I64 => Type::Primitive(PrimitiveType::I64),
            PrimitiveTypeId::I128 => Type::Primitive(PrimitiveType::I128),
            PrimitiveTypeId::U8 => Type::Primitive(PrimitiveType::U8),
            PrimitiveTypeId::U16 => Type::Primitive(PrimitiveType::U16),
            PrimitiveTypeId::U32 => Type::Primitive(PrimitiveType::U32),
            PrimitiveTypeId::U64 => Type::Primitive(PrimitiveType::U64),
            PrimitiveTypeId::F32 => Type::Primitive(PrimitiveType::F32),
            PrimitiveTypeId::F64 => Type::Primitive(PrimitiveType::F64),
            PrimitiveTypeId::Bool => Type::Primitive(PrimitiveType::Bool),
            PrimitiveTypeId::String => Type::Primitive(PrimitiveType::String),
            PrimitiveTypeId::Range => Type::Range,
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

    pub fn insert_named(&mut self, ty: Type, name_id: NameId) -> TypeKey {
        let id = self.insert(TypeInfo {
            ty,
            name_id: Some(name_id),
        });
        self.name_lookup.insert(name_id, id);
        id
    }

    pub fn insert_anonymous(&mut self, ty: Type) -> TypeKey {
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
        ty: &Type,
        names: &NameTable,
        entity_registry: &crate::sema::entity_registry::EntityRegistry,
    ) -> String {
        self.display_type_inner(ty, names, entity_registry)
    }

    pub fn key_for_type(&mut self, ty: &Type) -> TypeKey {
        match ty {
            Type::Primitive(prim) => match prim {
                PrimitiveType::I8 => {
                    self.intern_primitive(PrimitiveTypeId::I8, TypeFingerprint::I8, ty)
                }
                PrimitiveType::I16 => {
                    self.intern_primitive(PrimitiveTypeId::I16, TypeFingerprint::I16, ty)
                }
                PrimitiveType::I32 => {
                    self.intern_primitive(PrimitiveTypeId::I32, TypeFingerprint::I32, ty)
                }
                PrimitiveType::I64 => {
                    self.intern_primitive(PrimitiveTypeId::I64, TypeFingerprint::I64, ty)
                }
                PrimitiveType::I128 => {
                    self.intern_primitive(PrimitiveTypeId::I128, TypeFingerprint::I128, ty)
                }
                PrimitiveType::U8 => {
                    self.intern_primitive(PrimitiveTypeId::U8, TypeFingerprint::U8, ty)
                }
                PrimitiveType::U16 => {
                    self.intern_primitive(PrimitiveTypeId::U16, TypeFingerprint::U16, ty)
                }
                PrimitiveType::U32 => {
                    self.intern_primitive(PrimitiveTypeId::U32, TypeFingerprint::U32, ty)
                }
                PrimitiveType::U64 => {
                    self.intern_primitive(PrimitiveTypeId::U64, TypeFingerprint::U64, ty)
                }
                PrimitiveType::F32 => {
                    self.intern_primitive(PrimitiveTypeId::F32, TypeFingerprint::F32, ty)
                }
                PrimitiveType::F64 => {
                    self.intern_primitive(PrimitiveTypeId::F64, TypeFingerprint::F64, ty)
                }
                PrimitiveType::Bool => {
                    self.intern_primitive(PrimitiveTypeId::Bool, TypeFingerprint::Bool, ty)
                }
                PrimitiveType::String => {
                    self.intern_primitive(PrimitiveTypeId::String, TypeFingerprint::String, ty)
                }
            },
            Type::Void => self.intern_fingerprint(TypeFingerprint::Void, ty.clone()),
            Type::Nil => self.intern_fingerprint(TypeFingerprint::Nil, ty.clone()),
            Type::Done => self.intern_fingerprint(TypeFingerprint::Done, ty.clone()),
            Type::Range => self.intern_fingerprint(TypeFingerprint::Range, ty.clone()),
            Type::Placeholder(_) => self.intern_fingerprint(TypeFingerprint::Unknown, ty.clone()),
            Type::Invalid(_) => self.intern_fingerprint(TypeFingerprint::Error, ty.clone()),
            Type::Type => self.intern_fingerprint(TypeFingerprint::Type, ty.clone()),
            Type::Union(variants) => {
                let mut keys: Vec<TypeKey> = variants
                    .iter()
                    .map(|variant| self.key_for_type(variant))
                    .collect();
                keys.sort_by_key(|key| key.index());
                self.intern_fingerprint(TypeFingerprint::Union(keys), ty.clone())
            }
            Type::Array(elem) => {
                let elem_key = self.key_for_type(elem);
                self.intern_fingerprint(TypeFingerprint::Array(elem_key), ty.clone())
            }
            Type::Function(func) => {
                let params = func
                    .params
                    .iter()
                    .map(|param| self.key_for_type(param))
                    .collect();
                let return_type = self.key_for_type(&func.return_type);
                self.intern_fingerprint(
                    TypeFingerprint::Function {
                        params,
                        return_type,
                    },
                    ty.clone(),
                )
            }
            Type::Nominal(NominalType::Class(class_type)) => {
                self.intern_type_def(ty.clone(), class_type.type_def_id)
            }
            Type::Nominal(NominalType::Record(record_type)) => {
                self.intern_type_def(ty.clone(), record_type.type_def_id)
            }
            Type::Nominal(NominalType::Interface(interface_type)) => {
                let type_def_id = interface_type.type_def_id;
                if interface_type.type_args.is_empty() {
                    self.intern_type_def(ty.clone(), type_def_id)
                } else {
                    let args = interface_type
                        .type_args
                        .iter()
                        .map(|arg| self.key_for_type(arg))
                        .collect();
                    self.intern_fingerprint(
                        TypeFingerprint::Interface { type_def_id, args },
                        ty.clone(),
                    )
                }
            }
            Type::Nominal(NominalType::Error(error_type)) => self.intern_fingerprint(
                TypeFingerprint::ErrorType(error_type.type_def_id),
                ty.clone(),
            ),
            Type::Fallible(fallible) => {
                let success = self.key_for_type(&fallible.success_type);
                let error = self.key_for_type(&fallible.error_type);
                self.intern_fingerprint(TypeFingerprint::Fallible { success, error }, ty.clone())
            }
            Type::Module(module_type) => {
                self.intern_fingerprint(TypeFingerprint::Module(module_type.module_id), ty.clone())
            }
            Type::TypeParam(name_id) => {
                self.intern_fingerprint(TypeFingerprint::TypeParam(*name_id), ty.clone())
            }
            Type::RuntimeIterator(elem) => {
                let elem_key = self.key_for_type(elem);
                self.intern_fingerprint(TypeFingerprint::RuntimeIterator(elem_key), ty.clone())
            }
            Type::Tuple(elements) => {
                let elem_keys = elements
                    .iter()
                    .map(|elem| self.key_for_type(elem))
                    .collect();
                self.intern_fingerprint(TypeFingerprint::Tuple(elem_keys), ty.clone())
            }
            Type::FixedArray { element, size } => {
                let elem_key = self.key_for_type(element);
                self.intern_fingerprint(
                    TypeFingerprint::FixedArray {
                        element: elem_key,
                        size: *size,
                    },
                    ty.clone(),
                )
            }
            Type::Structural(structural) => {
                let fields: Vec<_> = structural
                    .fields
                    .iter()
                    .map(|f| (f.name, self.key_for_type(&f.ty)))
                    .collect();
                let methods: Vec<_> = structural
                    .methods
                    .iter()
                    .map(|m| {
                        let params: Vec<_> =
                            m.params.iter().map(|p| self.key_for_type(p)).collect();
                        (m.name, params, self.key_for_type(&m.return_type))
                    })
                    .collect();
                self.intern_fingerprint(TypeFingerprint::Structural { fields, methods }, ty.clone())
            }
        }
    }

    fn insert(&mut self, info: TypeInfo) -> TypeKey {
        let id = TypeKey(self.types.len() as u32);
        self.types.push(info);
        id
    }

    fn intern_named(&mut self, ty: Type, name_id: NameId) -> TypeKey {
        if let Some(key) = self.name_lookup.get(&name_id) {
            return *key;
        }
        self.insert_named(ty, name_id)
    }

    fn intern_type_def(&mut self, ty: Type, type_def_id: TypeDefId) -> TypeKey {
        if let Some(key) = self.type_def_lookup.get(&type_def_id) {
            return *key;
        }
        let key = self.insert_anonymous(ty);
        self.type_def_lookup.insert(type_def_id, key);
        key
    }

    fn intern_fingerprint(&mut self, fingerprint: TypeFingerprint, ty: Type) -> TypeKey {
        if let Some(key) = self.fingerprint_lookup.get(&fingerprint) {
            return *key;
        }
        let key = self.insert_anonymous(ty);
        self.fingerprint_lookup.insert(fingerprint, key);
        key
    }

    fn intern_primitive(
        &mut self,
        prim: PrimitiveTypeId,
        fingerprint: TypeFingerprint,
        ty: &Type,
    ) -> TypeKey {
        if let Some(name_id) = self.primitive_names.get(&prim) {
            self.intern_named(ty.clone(), *name_id)
        } else {
            self.intern_fingerprint(fingerprint, ty.clone())
        }
    }

    fn display_type_inner(
        &self,
        ty: &Type,
        names: &NameTable,
        entity_registry: &crate::sema::entity_registry::EntityRegistry,
    ) -> String {
        match ty {
            Type::Function(ft) => {
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
            Type::Union(variants) => variants
                .iter()
                .map(|variant| self.display_type_inner(variant, names, entity_registry))
                .collect::<Vec<_>>()
                .join(" | "),
            Type::Array(elem) => {
                format!(
                    "[{}]",
                    self.display_type_inner(elem, names, entity_registry)
                )
            }
            Type::Nominal(NominalType::Class(class_type)) => {
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
            Type::Nominal(NominalType::Record(record_type)) => {
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
            Type::Nominal(NominalType::Interface(interface_type)) => {
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
            Type::Nominal(NominalType::Error(error_type)) => {
                names.display(entity_registry.name_id(error_type.type_def_id))
            }
            Type::Fallible(ft) => format!(
                "fallible({}, {})",
                self.display_type_inner(&ft.success_type, names, entity_registry),
                self.display_type_inner(&ft.error_type, names, entity_registry)
            ),
            Type::Module(module_type) => {
                format!("module(\"{}\")", names.module_path(module_type.module_id))
            }
            Type::TypeParam(name_id) => {
                // For TypeParam, display the NameId
                // In practice, TypeParams should be substituted before display
                names.display(*name_id)
            }
            Type::Tuple(elements) => {
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
            Type::Nominal(NominalType::Class(crate::sema::ClassType {
                type_def_id,
                type_args: vec![],
            })),
            name_id,
        );

        assert_eq!(types.display(key, &names), "main::Foo");
    }
}
