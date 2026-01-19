// src/sema/type_table.rs
//
// Opaque type identities with optional printable names.

use std::collections::HashMap;

use crate::identity::{NameId, NameTable};
use crate::sema::implement_registry::PrimitiveTypeId;
use crate::sema::type_arena::{SemaType, TypeArena, TypeId as ArenaTypeId};
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
    pub type_id: Option<ArenaTypeId>,
    pub name_id: Option<NameId>,
}

#[derive(Debug, Clone)]
pub struct TypeTable {
    types: Vec<TypeInfo>,
    name_lookup: HashMap<NameId, TypeKey>,
    type_id_lookup: HashMap<ArenaTypeId, TypeKey>,
    primitive_names: HashMap<PrimitiveTypeId, NameId>,
    array_name: Option<NameId>,
}

impl TypeTable {
    pub fn new() -> Self {
        Self {
            types: Vec::new(),
            name_lookup: HashMap::new(),
            type_id_lookup: HashMap::new(),
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
            type_id: None,
            name_id: Some(name_id),
        });
        self.name_lookup.insert(name_id, id);
        id
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

    /// Display a TypeId directly from SemaType without LegacyType materialization
    pub fn display_type_id_direct(
        &self,
        type_id: ArenaTypeId,
        arena: &TypeArena,
        names: &NameTable,
        entity_registry: &crate::sema::entity_registry::EntityRegistry,
    ) -> String {
        self.display_sema_type(type_id, arena, names, entity_registry)
    }

    /// Internal: format a TypeId by matching on SemaType
    fn display_sema_type(
        &self,
        type_id: ArenaTypeId,
        arena: &TypeArena,
        names: &NameTable,
        entity_registry: &crate::sema::entity_registry::EntityRegistry,
    ) -> String {
        match arena.get(type_id) {
            SemaType::Primitive(prim) => prim.name().to_string(),
            SemaType::Void => "void".to_string(),
            SemaType::Nil => "nil".to_string(),
            SemaType::Done => "done".to_string(),
            SemaType::Range => "range".to_string(),
            SemaType::MetaType => "type".to_string(),
            SemaType::Invalid { .. } => "<invalid>".to_string(),

            SemaType::Function { params, ret, .. } => {
                let params_str = params
                    .iter()
                    .map(|&p| self.display_sema_type(p, arena, names, entity_registry))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(
                    "({}) -> {}",
                    params_str,
                    self.display_sema_type(*ret, arena, names, entity_registry)
                )
            }

            SemaType::Union(variants) => variants
                .iter()
                .map(|&v| self.display_sema_type(v, arena, names, entity_registry))
                .collect::<Vec<_>>()
                .join(" | "),

            SemaType::Array(elem) => {
                format!(
                    "[{}]",
                    self.display_sema_type(*elem, arena, names, entity_registry)
                )
            }

            SemaType::FixedArray { element, size } => {
                format!(
                    "[{}; {}]",
                    self.display_sema_type(*element, arena, names, entity_registry),
                    size
                )
            }

            SemaType::Tuple(elements) => {
                let elem_list = elements
                    .iter()
                    .map(|&e| self.display_sema_type(e, arena, names, entity_registry))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({})", elem_list)
            }

            SemaType::RuntimeIterator(elem) => {
                format!(
                    "Iterator<{}>",
                    self.display_sema_type(*elem, arena, names, entity_registry)
                )
            }

            SemaType::Class {
                type_def_id,
                type_args,
            } => {
                let type_def = entity_registry.get_type(*type_def_id);
                let base = names.display(type_def.name_id);
                if type_args.is_empty() {
                    base
                } else {
                    let args = type_args
                        .iter()
                        .map(|&a| self.display_sema_type(a, arena, names, entity_registry))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{}<{}>", base, args)
                }
            }

            SemaType::Record {
                type_def_id,
                type_args,
            } => {
                let type_def = entity_registry.get_type(*type_def_id);
                let base = names.display(type_def.name_id);
                if type_args.is_empty() {
                    base
                } else {
                    let args = type_args
                        .iter()
                        .map(|&a| self.display_sema_type(a, arena, names, entity_registry))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{}<{}>", base, args)
                }
            }

            SemaType::Interface {
                type_def_id,
                type_args,
            } => {
                let name_id = entity_registry.name_id(*type_def_id);
                let base = names.display(name_id);
                if type_args.is_empty() {
                    base
                } else {
                    let args = type_args
                        .iter()
                        .map(|&a| self.display_sema_type(a, arena, names, entity_registry))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("{}<{}>", base, args)
                }
            }

            SemaType::Error { type_def_id } => names.display(entity_registry.name_id(*type_def_id)),

            SemaType::Fallible { success, error } => format!(
                "fallible({}, {})",
                self.display_sema_type(*success, arena, names, entity_registry),
                self.display_sema_type(*error, arena, names, entity_registry)
            ),

            SemaType::Module(module) => {
                format!("module(\"{}\")", names.module_path(module.module_id))
            }

            SemaType::TypeParam(name_id) => names.display(*name_id),

            SemaType::TypeParamRef(type_param_id) => {
                format!("TypeParam#{}", type_param_id.index())
            }

            SemaType::Structural(structural) => {
                // Display structural type fields and methods
                let mut parts = Vec::new();
                for (name_id, type_id) in &structural.fields {
                    let name = names.last_segment_str(*name_id).unwrap_or_default();
                    let ty = self.display_sema_type(*type_id, arena, names, entity_registry);
                    parts.push(format!("{}: {}", name, ty));
                }
                for method in &structural.methods {
                    let name = names.last_segment_str(method.name).unwrap_or_default();
                    let params: Vec<String> = method
                        .params
                        .iter()
                        .map(|&p| self.display_sema_type(p, arena, names, entity_registry))
                        .collect();
                    let ret =
                        self.display_sema_type(method.return_type, arena, names, entity_registry);
                    parts.push(format!("func {}({}) -> {}", name, params.join(", "), ret));
                }
                format!("{{ {} }}", parts.join(", "))
            }

            SemaType::Placeholder(kind) => format!("placeholder({:?})", kind),
        }
    }

    /// Get a TypeKey for a TypeId (arena-based type).
    /// Since TypeArena already deduplicates, this is a simple lookup/insert.
    pub fn key_for_type_id(&mut self, type_id: ArenaTypeId, arena: &TypeArena) -> TypeKey {
        if let Some(key) = self.type_id_lookup.get(&type_id) {
            return *key;
        }
        // Convert to LegacyType for storage (transitional)
        let ty = arena.to_type(type_id);
        let key = self.insert(TypeInfo {
            ty,
            type_id: Some(type_id),
            name_id: None,
        });
        self.type_id_lookup.insert(type_id, key);
        key
    }

    fn insert(&mut self, info: TypeInfo) -> TypeKey {
        let id = TypeKey(self.types.len() as u32);
        self.types.push(info);
        id
    }

    fn display_type_inner(
        &self,
        ty: &LegacyType,
        names: &NameTable,
        entity_registry: &crate::sema::entity_registry::EntityRegistry,
    ) -> String {
        match ty {
            // FunctionType only has TypeIds - use arena-based display_type_id_direct for proper names
            // Here we just show the TypeId-based representation
            LegacyType::Function(ft) => format!("{}", ft),
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
                if class_type.type_args_id.is_empty() {
                    base
                } else {
                    // Type args require arena for display; show placeholder
                    format!("{}<{} args>", base, class_type.type_args_id.len())
                }
            }
            LegacyType::Nominal(NominalType::Record(record_type)) => {
                let type_def = entity_registry.get_type(record_type.type_def_id);
                let base = names.display(type_def.name_id);
                if record_type.type_args_id.is_empty() {
                    base
                } else {
                    // Type args require arena for display; show placeholder
                    format!("{}<{} args>", base, record_type.type_args_id.len())
                }
            }
            LegacyType::Nominal(NominalType::Interface(interface_type)) => {
                let name_id = entity_registry.name_id(interface_type.type_def_id);
                let base = names.display(name_id);
                if interface_type.type_args_id.is_empty() {
                    base
                } else {
                    // Type args require arena for display; show placeholder
                    format!("{}<{} args>", base, interface_type.type_args_id.len())
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
    use crate::sema::type_arena::TypeIdVec;

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
                type_args_id: TypeIdVec::new(),
            })),
            name_id,
        );

        assert_eq!(types.display(key, &names), "main::Foo");
    }
}
