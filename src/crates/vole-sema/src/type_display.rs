//! Type display utilities for formatting types in error messages.
//!
//! This module provides functions to display types directly from TypeId.

use crate::entity_registry::EntityRegistry;
use crate::type_arena::{InternedStructural, SemaType, TypeArena, TypeId};
use vole_identity::{NameId, NameTable, TypeDefId};

/// Minimal trait for type display: look up a type's name by its ID.
///
/// Both `EntityRegistry` (sema) and `VirEntityMetadata` (codegen) implement
/// this, allowing `display_type_id_short` to work without a concrete registry.
pub trait TypeDefProvider {
    fn type_name_id(&self, id: TypeDefId) -> NameId;
}

impl TypeDefProvider for EntityRegistry {
    fn type_name_id(&self, id: TypeDefId) -> NameId {
        EntityRegistry::get_type(self, id).name_id
    }
}

impl TypeDefProvider for vole_vir::VirEntityMetadata {
    fn type_name_id(&self, id: TypeDefId) -> NameId {
        self.get_type_def(id)
            .expect("VirEntityMetadata: missing TypeDefId in type_name_id()")
            .name_id
    }
}

/// Display a TypeId by matching on SemaType.
/// This is the canonical way to format types for error messages.
pub fn display_type_id(
    type_id: TypeId,
    arena: &TypeArena,
    names: &NameTable,
    entity_registry: &EntityRegistry,
) -> String {
    display_sema_type(type_id, arena, names, entity_registry, false)
}

/// Display a TypeId using short names (no module paths) for nominal types.
/// E.g. `Point` instead of `/path/to/file.vole::Point`.
pub fn display_type_id_short(
    type_id: TypeId,
    arena: &TypeArena,
    names: &NameTable,
    provider: &impl TypeDefProvider,
) -> String {
    display_sema_type(type_id, arena, names, provider, true)
}

/// Display an InternedStructural constraint for error messages.
/// Returns a string like `{ name: string, age: i64 }`.
pub(crate) fn display_structural_constraint(
    structural: &InternedStructural,
    arena: &TypeArena,
    names: &NameTable,
    entity_registry: &EntityRegistry,
) -> String {
    let mut parts: Vec<String> = structural
        .fields
        .iter()
        .map(|(name_id, type_id)| {
            let name = names.last_segment_str(*name_id).unwrap_or_default();
            let ty = display_sema_type(*type_id, arena, names, entity_registry, false);
            format!("{}: {}", name, ty)
        })
        .collect();
    parts.extend(structural.methods.iter().map(|method| {
        let name = names.last_segment_str(method.name).unwrap_or_default();
        let params: Vec<String> = method
            .params
            .iter()
            .map(|&p| display_sema_type(p, arena, names, entity_registry, false))
            .collect();
        let ret = display_sema_type(method.return_type, arena, names, entity_registry, false);
        format!("func {}({}) -> {}", name, params.join(", "), ret)
    }));
    format!("{{ {} }}", parts.join(", "))
}

fn display_sema_type(
    type_id: TypeId,
    arena: &TypeArena,
    names: &NameTable,
    provider: &impl TypeDefProvider,
    short: bool,
) -> String {
    // Sentinel types display with their short name (e.g., "nil", "Done"),
    // not the fully-qualified module path.
    if arena.is_sentinel(type_id)
        && let SemaType::Struct { type_def_id, .. } = arena.get(type_id)
    {
        let name_id = provider.type_name_id(*type_def_id);
        if let Some(name) = names.last_segment_str(name_id) {
            return name;
        }
    }
    match arena.get(type_id) {
        SemaType::Primitive(prim) => prim.name().to_string(),
        SemaType::Handle => "handle".to_string(),
        SemaType::Void => "void".to_string(),
        SemaType::Range => "range".to_string(),
        SemaType::MetaType => "type".to_string(),
        SemaType::Never => "never".to_string(),
        SemaType::Unknown => "unknown".to_string(),
        SemaType::Invalid { .. } => "<invalid>".to_string(),

        SemaType::Function { params, ret, .. } => {
            let params_str = params
                .iter()
                .map(|&p| display_sema_type(p, arena, names, provider, short))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "({}) -> {}",
                params_str,
                display_sema_type(*ret, arena, names, provider, short)
            )
        }

        SemaType::Union(variants) => variants
            .iter()
            .map(|&v| display_sema_type(v, arena, names, provider, short))
            .collect::<Vec<_>>()
            .join(" | "),

        SemaType::Array(elem) => {
            format!(
                "[{}]",
                display_sema_type(*elem, arena, names, provider, short)
            )
        }

        SemaType::FixedArray { element, size } => {
            format!(
                "[{}; {}]",
                display_sema_type(*element, arena, names, provider, short),
                size
            )
        }

        SemaType::Tuple(elements) => {
            let elem_list = elements
                .iter()
                .map(|&e| display_sema_type(e, arena, names, provider, short))
                .collect::<Vec<_>>()
                .join(", ");
            format!("({})", elem_list)
        }

        SemaType::Class {
            type_def_id,
            type_args,
        }
        | SemaType::Interface {
            type_def_id,
            type_args,
        }
        | SemaType::Struct {
            type_def_id,
            type_args,
        } => {
            let name_id = provider.type_name_id(*type_def_id);
            let base = if short {
                names
                    .last_segment_str(name_id)
                    .unwrap_or_else(|| names.display(name_id))
            } else {
                names.display(name_id)
            };
            if type_args.is_empty() {
                base
            } else {
                let args = type_args
                    .iter()
                    .map(|&a| display_sema_type(a, arena, names, provider, short))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}<{}>", base, args)
            }
        }

        SemaType::Error { type_def_id } => {
            let name_id = provider.type_name_id(*type_def_id);
            if short {
                names
                    .last_segment_str(name_id)
                    .unwrap_or_else(|| names.display(name_id))
            } else {
                names.display(name_id)
            }
        }

        SemaType::Fallible { success, error } => format!(
            "fallible({}, {})",
            display_sema_type(*success, arena, names, provider, short),
            display_sema_type(*error, arena, names, provider, short)
        ),

        SemaType::Module(module) => {
            format!("module(\"{}\")", names.module_path(module.module_id))
        }

        SemaType::TypeParam(name_id) => names.display(*name_id),

        SemaType::TypeParamRef(type_param_id) => {
            format!("TypeParam#{}", type_param_id.index())
        }

        SemaType::Structural(structural) => {
            let mut parts: Vec<String> = structural
                .fields
                .iter()
                .map(|(name_id, type_id)| {
                    let name = names.last_segment_str(*name_id).unwrap_or_default();
                    let ty = display_sema_type(*type_id, arena, names, provider, short);
                    format!("{}: {}", name, ty)
                })
                .collect();
            parts.extend(structural.methods.iter().map(|method| {
                let name = names.last_segment_str(method.name).unwrap_or_default();
                let params: Vec<String> = method
                    .params
                    .iter()
                    .map(|&p| display_sema_type(p, arena, names, provider, short))
                    .collect();
                let ret = display_sema_type(method.return_type, arena, names, provider, short);
                format!("func {}({}) -> {}", name, params.join(", "), ret)
            }));
            format!("{{ {} }}", parts.join(", "))
        }

        SemaType::Placeholder(kind) => format!("placeholder({:?})", kind),
    }
}
