//! Type display utilities for formatting types in error messages.
//!
//! This module provides functions to display types directly from TypeId.

use crate::entity_registry::EntityRegistry;
use crate::type_arena::{InternedStructural, SemaType, TypeArena, TypeId};
use vole_identity::NameTable;

/// Display a TypeId by matching on SemaType.
/// This is the canonical way to format types for error messages.
pub fn display_type_id(
    type_id: TypeId,
    arena: &TypeArena,
    names: &NameTable,
    entity_registry: &EntityRegistry,
) -> String {
    display_sema_type(type_id, arena, names, entity_registry)
}

/// Display an InternedStructural constraint for error messages.
/// Returns a string like `{ name: string, age: i64 }`.
pub fn display_structural_constraint(
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
            let ty = display_sema_type(*type_id, arena, names, entity_registry);
            format!("{}: {}", name, ty)
        })
        .collect();
    parts.extend(structural.methods.iter().map(|method| {
        let name = names.last_segment_str(method.name).unwrap_or_default();
        let params: Vec<String> = method
            .params
            .iter()
            .map(|&p| display_sema_type(p, arena, names, entity_registry))
            .collect();
        let ret = display_sema_type(method.return_type, arena, names, entity_registry);
        format!("func {}({}) -> {}", name, params.join(", "), ret)
    }));
    format!("{{ {} }}", parts.join(", "))
}

fn display_sema_type(
    type_id: TypeId,
    arena: &TypeArena,
    names: &NameTable,
    entity_registry: &EntityRegistry,
) -> String {
    // Sentinel types display with their short name (e.g., "nil", "Done"),
    // not the fully-qualified module path.
    if arena.is_sentinel(type_id)
        && let SemaType::Struct { type_def_id, .. } = arena.get(type_id)
    {
        let type_def = entity_registry.get_type(*type_def_id);
        if let Some(name) = names.last_segment_str(type_def.name_id) {
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
                .map(|&p| display_sema_type(p, arena, names, entity_registry))
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "({}) -> {}",
                params_str,
                display_sema_type(*ret, arena, names, entity_registry)
            )
        }

        SemaType::Union(variants) => variants
            .iter()
            .map(|&v| display_sema_type(v, arena, names, entity_registry))
            .collect::<Vec<_>>()
            .join(" | "),

        SemaType::Array(elem) => {
            format!(
                "[{}]",
                display_sema_type(*elem, arena, names, entity_registry)
            )
        }

        SemaType::FixedArray { element, size } => {
            format!(
                "[{}; {}]",
                display_sema_type(*element, arena, names, entity_registry),
                size
            )
        }

        SemaType::Tuple(elements) => {
            let elem_list = elements
                .iter()
                .map(|&e| display_sema_type(e, arena, names, entity_registry))
                .collect::<Vec<_>>()
                .join(", ");
            format!("({})", elem_list)
        }

        SemaType::RuntimeIterator(elem) => {
            format!(
                "Iterator<{}>",
                display_sema_type(*elem, arena, names, entity_registry)
            )
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
            let base = names.display(entity_registry.name_id(*type_def_id));
            if type_args.is_empty() {
                base
            } else {
                let args = type_args
                    .iter()
                    .map(|&a| display_sema_type(a, arena, names, entity_registry))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{}<{}>", base, args)
            }
        }

        SemaType::Error { type_def_id } => names.display(entity_registry.name_id(*type_def_id)),

        SemaType::Fallible { success, error } => format!(
            "fallible({}, {})",
            display_sema_type(*success, arena, names, entity_registry),
            display_sema_type(*error, arena, names, entity_registry)
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
                    let ty = display_sema_type(*type_id, arena, names, entity_registry);
                    format!("{}: {}", name, ty)
                })
                .collect();
            parts.extend(structural.methods.iter().map(|method| {
                let name = names.last_segment_str(method.name).unwrap_or_default();
                let params: Vec<String> = method
                    .params
                    .iter()
                    .map(|&p| display_sema_type(p, arena, names, entity_registry))
                    .collect();
                let ret = display_sema_type(method.return_type, arena, names, entity_registry);
                format!("func {}({}) -> {}", name, params.join(", "), ret)
            }));
            format!("{{ {} }}", parts.join(", "))
        }

        SemaType::Placeholder(kind) => format!("placeholder({:?})", kind),
    }
}
