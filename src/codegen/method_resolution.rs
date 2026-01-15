use std::collections::HashMap;

use crate::codegen::structs::get_type_name_id;
use crate::codegen::types::{MethodInfo, method_name_id_by_str, type_metadata_by_name_id};
use crate::commands::common::AnalyzedProgram;
use crate::errors::CodegenError;
use crate::frontend::Symbol;
use crate::identity::{MethodId, NameId, TypeDefId};
use crate::sema::implement_registry::{ExternalMethodInfo, TypeId};
use crate::sema::resolution::ResolvedMethod;
use crate::sema::types::NominalType;
use crate::sema::{FunctionType, LegacyType, PrimitiveType, Type};

#[derive(Debug)]
pub(crate) enum MethodTarget {
    Direct {
        method_info: MethodInfo,
        return_type: LegacyType,
    },
    Implemented {
        method_info: MethodInfo,
        return_type: LegacyType,
    },
    Default {
        method_info: MethodInfo,
        return_type: LegacyType,
    },
    FunctionalInterface {
        func_type: FunctionType,
    },
    External {
        external_info: ExternalMethodInfo,
        return_type: LegacyType,
    },
    InterfaceDispatch {
        interface_type_id: TypeDefId,
        method_name_id: NameId,
        func_type: FunctionType,
    },
    #[allow(dead_code)] // Handled earlier via ResolvedMethod::Static
    StaticMethod {
        type_def_id: TypeDefId,
        method_id: MethodId,
        func_type: FunctionType,
    },
}

pub(crate) struct MethodResolutionInput<'a> {
    pub analyzed: &'a AnalyzedProgram,
    pub type_metadata: &'a HashMap<Symbol, crate::codegen::types::TypeMetadata>,
    pub impl_method_infos: &'a HashMap<(TypeId, NameId), MethodInfo>,
    pub method_name_str: &'a str,
    pub object_type: &'a Type,
    pub method_id: NameId,
    pub resolution: Option<&'a ResolvedMethod>,
}

pub(crate) fn resolve_method_target(
    input: MethodResolutionInput<'_>,
) -> Result<MethodTarget, String> {
    let lookup_direct_method = |type_name_id: NameId| {
        type_metadata_by_name_id(
            input.type_metadata,
            type_name_id,
            &input.analyzed.entity_registry,
        )
        .and_then(|meta| meta.method_infos.get(&input.method_id))
        .cloned()
        .ok_or_else(|| {
            format!(
                "Method {} not found on type {:?}",
                input.method_name_str, type_name_id
            )
        })
    };

    let lookup_impl_method = |type_id: TypeId| {
        input
            .impl_method_infos
            .get(&(type_id, input.method_id))
            .cloned()
            .ok_or_else(|| {
                format!(
                    "Unknown method {} on {}",
                    input.method_name_str,
                    crate::codegen::types::display_type(
                        input.analyzed,
                        &input.analyzed.interner,
                        input.object_type
                    )
                )
            })
    };

    // Filter out InterfaceMethod resolution when the concrete type is not an interface.
    // This happens in monomorphized code where sema stored InterfaceMethod for TypeParam,
    // but at codegen time the type is concrete (e.g., i64).
    let effective_resolution = input.resolution.filter(|resolution| {
        !matches!(resolution, ResolvedMethod::InterfaceMethod { .. })
            || matches!(input.object_type, LegacyType::Nominal(NominalType::Interface(_)))
    });

    if let Some(resolution) = effective_resolution {
        return match resolution {
            ResolvedMethod::Direct { func_type } => {
                let type_name_id =
                    get_type_name_id(input.object_type, &input.analyzed.entity_registry)?;
                let method_info = lookup_direct_method(type_name_id)?;
                Ok(MethodTarget::Direct {
                    method_info,
                    return_type: (*func_type.return_type).clone(),
                })
            }
            ResolvedMethod::Implemented {
                func_type,
                is_builtin,
                external_info,
                ..
            } => {
                if *is_builtin {
                    return Err(CodegenError::internal_with_context(
                        "unhandled builtin method",
                        input.method_name_str,
                    )
                    .into());
                }

                // For interface types, we need vtable dispatch - the external_info is for
                // the default implementation, but the concrete type may override it
                if let LegacyType::Nominal(NominalType::Interface(interface_type)) = input.object_type {
                    // Use TypeDefId directly for EntityRegistry-based dispatch
                    let interface_type_id = interface_type.type_def_id;
                    let method_name_id = method_name_id_by_str(
                        input.analyzed,
                        &input.analyzed.interner,
                        input.method_name_str,
                    )
                    .ok_or_else(|| {
                        format!("method name {} not found as NameId", input.method_name_str)
                    })?;
                    return Ok(MethodTarget::InterfaceDispatch {
                        interface_type_id,
                        method_name_id,
                        func_type: func_type.clone(),
                    });
                }

                if let Some(ext_info) = external_info {
                    // For concrete types with external implementation, call external directly
                    return Ok(MethodTarget::External {
                        external_info: ext_info.clone(),
                        return_type: (*func_type.return_type).clone(),
                    });
                }
                let type_id = TypeId::from_type(
                    input.object_type,
                    &input.analyzed.entity_registry.type_table,
                    &input.analyzed.entity_registry,
                )
                .ok_or_else(|| {
                    CodegenError::not_found(
                        "method",
                        format!(
                            "{} on {}",
                            input.method_name_str,
                            crate::codegen::types::display_type(
                                input.analyzed,
                                &input.analyzed.interner,
                                input.object_type
                            )
                        ),
                    )
                    .to_string()
                })?;
                let method_info = lookup_impl_method(type_id)?;
                Ok(MethodTarget::Implemented {
                    method_info,
                    return_type: (*func_type.return_type).clone(),
                })
            }
            ResolvedMethod::FunctionalInterface { func_type } => {
                Ok(MethodTarget::FunctionalInterface {
                    func_type: func_type.clone(),
                })
            }
            ResolvedMethod::DefaultMethod {
                func_type,
                external_info,
                ..
            } => {
                // If the default method is an external (like Iterator methods), call external
                if let Some(ext_info) = external_info {
                    return Ok(MethodTarget::External {
                        external_info: ext_info.clone(),
                        return_type: (*func_type.return_type).clone(),
                    });
                }
                // Otherwise, get the name_id from the object type since DefaultMethod is called on a class/record
                let type_name_id =
                    get_type_name_id(input.object_type, &input.analyzed.entity_registry)?;
                let method_info = lookup_direct_method(type_name_id)?;
                Ok(MethodTarget::Default {
                    method_info,
                    return_type: (*func_type.return_type).clone(),
                })
            }
            ResolvedMethod::InterfaceMethod {
                interface_name: _,
                method_name: _,
                func_type,
            } => {
                // This branch is only taken when object_type is an interface
                // (non-interface types are filtered out before the match)
                let interface_type = match input.object_type {
                    LegacyType::Nominal(NominalType::Interface(it)) => it,
                    _ => unreachable!("InterfaceMethod filtered out for non-interface types"),
                };
                let method_name_id = method_name_id_by_str(
                    input.analyzed,
                    &input.analyzed.interner,
                    input.method_name_str,
                )
                .ok_or_else(|| {
                    format!("method name {} not found as NameId", input.method_name_str)
                })?;
                Ok(MethodTarget::InterfaceDispatch {
                    interface_type_id: interface_type.type_def_id,
                    method_name_id,
                    func_type: func_type.clone(),
                })
            }
            ResolvedMethod::Static {
                type_def_id,
                method_id,
                func_type,
            } => {
                // Static method call - will be compiled similarly to direct methods
                // but without an implicit self parameter
                Ok(MethodTarget::StaticMethod {
                    type_def_id: *type_def_id,
                    method_id: *method_id,
                    func_type: func_type.clone(),
                })
            }
        };
    }

    // No resolution found - try implement block methods first, then direct methods.
    // This happens in monomorphized generic functions where the resolution was computed
    // for the type parameter, not the concrete type.

    // First, try EntityRegistry method bindings (cross-interner safe, works for all types)
    // This is the authoritative source for method implementations.
    if let Some(type_def_id) = get_type_def_id_for_codegen(input.object_type, input.analyzed)
        && let Some(method_name_id) = method_name_id_by_str(
            input.analyzed,
            &input.analyzed.interner,
            input.method_name_str,
        )
        && let Some(binding) = input
            .analyzed
            .entity_registry
            .find_method_binding(type_def_id, method_name_id)
    {
        // Found method binding in EntityRegistry - now get the compiled MethodInfo
        // Try impl_method_infos first (uses TypeId key)
        if let Some(type_id) = TypeId::from_type(
            input.object_type,
            &input.analyzed.entity_registry.type_table,
            &input.analyzed.entity_registry,
        ) && let Some(method_info) = input
            .impl_method_infos
            .get(&(type_id, input.method_id))
            .cloned()
        {
            return Ok(MethodTarget::Implemented {
                method_info,
                return_type: (*binding.func_type.return_type).clone(),
            });
        }

        // Fallback: try looking up by method_name_id from EntityRegistry
        if let Some(type_id) = TypeId::from_type(
            input.object_type,
            &input.analyzed.entity_registry.type_table,
            &input.analyzed.entity_registry,
        ) && let Some(method_info) = input
            .impl_method_infos
            .get(&(type_id, method_name_id))
            .cloned()
        {
            return Ok(MethodTarget::Implemented {
                method_info,
                return_type: (*binding.func_type.return_type).clone(),
            });
        }

        // If binding has external_info, use that directly
        // This handles external methods from prelude that aren't in impl_method_infos
        if let Some(external_info) = &binding.external_info {
            return Ok(MethodTarget::External {
                external_info: external_info.clone(),
                return_type: (*binding.func_type.return_type).clone(),
            });
        }
    }

    // Fallback: try impl_method_infos directly (legacy path)
    if let Some(type_id) = TypeId::from_type(
        input.object_type,
        &input.analyzed.entity_registry.type_table,
        &input.analyzed.entity_registry,
    ) && let Ok(method_info) = lookup_impl_method(type_id)
    {
        let return_type = method_info.return_type.clone();
        return Ok(MethodTarget::Implemented {
            method_info,
            return_type,
        });
    }

    // Try direct methods (methods defined inside class/record)
    // This only works for classes/records, not primitives.
    if let Ok(type_name_id) = get_type_name_id(input.object_type, &input.analyzed.entity_registry)
        && let Ok(method_info) = lookup_direct_method(type_name_id)
    {
        let return_type = method_info.return_type.clone();
        return Ok(MethodTarget::Direct {
            method_info,
            return_type,
        });
    }

    // Neither found - return error
    Err(format!(
        "Method {} not found on type {}",
        input.method_name_str,
        crate::codegen::types::display_type(
            input.analyzed,
            &input.analyzed.interner,
            input.object_type
        )
    ))
}

/// Get TypeDefId for a type during codegen (handles primitives, records, classes, interfaces)
fn get_type_def_id_for_codegen(ty: &LegacyType, analyzed: &AnalyzedProgram) -> Option<TypeDefId> {
    // For Class, Record, and Interface, we already have the TypeDefId
    match ty {
        LegacyType::Nominal(NominalType::Class(c)) => return Some(c.type_def_id),
        LegacyType::Nominal(NominalType::Record(r)) => return Some(r.type_def_id),
        LegacyType::Nominal(NominalType::Interface(i)) => return Some(i.type_def_id),
        _ => {}
    }

    let name_id = match ty {
        // Primitives - look up via well-known NameIds
        LegacyType::Primitive(PrimitiveType::I8) => Some(analyzed.name_table.primitives.i8),
        LegacyType::Primitive(PrimitiveType::I16) => Some(analyzed.name_table.primitives.i16),
        LegacyType::Primitive(PrimitiveType::I32) => Some(analyzed.name_table.primitives.i32),
        LegacyType::Primitive(PrimitiveType::I64) => Some(analyzed.name_table.primitives.i64),
        LegacyType::Primitive(PrimitiveType::I128) => Some(analyzed.name_table.primitives.i128),
        LegacyType::Primitive(PrimitiveType::U8) => Some(analyzed.name_table.primitives.u8),
        LegacyType::Primitive(PrimitiveType::U16) => Some(analyzed.name_table.primitives.u16),
        LegacyType::Primitive(PrimitiveType::U32) => Some(analyzed.name_table.primitives.u32),
        LegacyType::Primitive(PrimitiveType::U64) => Some(analyzed.name_table.primitives.u64),
        LegacyType::Primitive(PrimitiveType::F32) => Some(analyzed.name_table.primitives.f32),
        LegacyType::Primitive(PrimitiveType::F64) => Some(analyzed.name_table.primitives.f64),
        LegacyType::Primitive(PrimitiveType::Bool) => Some(analyzed.name_table.primitives.bool),
        LegacyType::Primitive(PrimitiveType::String) => Some(analyzed.name_table.primitives.string),
        _ => None,
    }?;

    analyzed.entity_registry.type_by_name(name_id)
}
