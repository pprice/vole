use std::collections::HashMap;

use crate::AnalyzedProgram;
use crate::errors::CodegenError;
use crate::types::{MethodInfo, method_name_id_by_str, type_metadata_by_name_id};
use vole_frontend::Symbol;
use vole_identity::{MethodId, NameId, TypeDefId};
use vole_sema::PrimitiveType;
use vole_sema::implement_registry::{ExternalMethodInfo, ImplTypeId};
use vole_sema::resolution::ResolvedMethod;
use vole_sema::type_arena::TypeId;

#[derive(Debug)]
pub(crate) enum MethodTarget {
    Direct {
        method_info: MethodInfo,
        return_type: TypeId,
    },
    Implemented {
        method_info: MethodInfo,
        return_type: TypeId,
    },
    Default {
        method_info: MethodInfo,
        return_type: TypeId,
    },
    FunctionalInterface {
        func_type_id: TypeId,
    },
    External {
        external_info: ExternalMethodInfo,
        return_type: TypeId,
    },
    InterfaceDispatch {
        interface_type_id: TypeDefId,
        method_name_id: NameId,
        func_type_id: TypeId,
    },
    #[allow(dead_code)] // Handled earlier via ResolvedMethod::Static
    StaticMethod {
        type_def_id: TypeDefId,
        method_id: MethodId,
        func_type_id: TypeId,
    },
}

/// Method resolution input.
pub(crate) struct MethodResolutionInputId<'a> {
    pub analyzed: &'a AnalyzedProgram,
    pub type_metadata: &'a HashMap<Symbol, crate::types::TypeMetadata>,
    pub impl_method_infos: &'a HashMap<(ImplTypeId, NameId), MethodInfo>,
    pub method_name_str: &'a str,
    pub object_type_id: TypeId,
    pub method_id: NameId,
    pub resolution: Option<&'a ResolvedMethod>,
}

/// Resolve method target to determine how to call it.
pub(crate) fn resolve_method_target_id(
    input: MethodResolutionInputId<'_>,
) -> Result<MethodTarget, String> {
    use crate::structs::get_type_name_id_from_type_id;

    // Check if object is an interface
    let is_interface = input
        .analyzed
        .type_arena
        .borrow()
        .is_interface(input.object_type_id);

    // Filter out InterfaceMethod resolution when the concrete type is not an interface.
    let effective_resolution = input.resolution.filter(|resolution| {
        !matches!(resolution, ResolvedMethod::InterfaceMethod { .. }) || is_interface
    });

    // Helper closures for method lookup
    let lookup_direct_method = |type_name_id: NameId| {
        type_metadata_by_name_id(
            input.type_metadata,
            type_name_id,
            &input.analyzed.entity_registry,
            &input.analyzed.type_arena.borrow(),
        )
        .and_then(|meta| meta.method_infos.get(&input.method_id))
        .copied()
        .ok_or_else(|| {
            format!(
                "Method {} not found on type {:?}",
                input.method_name_str, type_name_id
            )
        })
    };

    let lookup_impl_method = |type_id: ImplTypeId| {
        input
            .impl_method_infos
            .get(&(type_id, input.method_id))
            .copied()
            .ok_or_else(|| format!("Unknown method {} on type", input.method_name_str,))
    };

    if let Some(resolution) = effective_resolution {
        return match resolution {
            ResolvedMethod::Direct { func_type, .. } => {
                let arena = input.analyzed.type_arena.borrow();
                let type_name_id = get_type_name_id_from_type_id(
                    input.object_type_id,
                    &arena,
                    &input.analyzed.entity_registry,
                )?;
                let method_info = lookup_direct_method(type_name_id)?;
                Ok(MethodTarget::Direct {
                    method_info,
                    return_type: func_type.return_type_id,
                })
            }
            ResolvedMethod::Implemented {
                func_type,
                func_type_id,
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

                // For interface types, we need vtable dispatch
                if let Some((interface_type_id, _)) = input
                    .analyzed
                    .type_arena
                    .borrow()
                    .unwrap_interface(input.object_type_id)
                {
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
                        func_type_id: *func_type_id,
                    });
                }

                if let Some(ext_info) = external_info {
                    return Ok(MethodTarget::External {
                        external_info: ext_info.clone(),
                        return_type: func_type.return_type_id,
                    });
                }

                let type_id = ImplTypeId::from_type_id(
                    input.object_type_id,
                    &input.analyzed.type_arena.borrow(),
                    &input.analyzed.entity_registry,
                )
                .ok_or_else(|| {
                    format!("Cannot get ImplTypeId for method {}", input.method_name_str,)
                })?;
                let method_info = lookup_impl_method(type_id)?;
                Ok(MethodTarget::Implemented {
                    method_info,
                    return_type: func_type.return_type_id,
                })
            }
            ResolvedMethod::FunctionalInterface { func_type_id, .. } => {
                Ok(MethodTarget::FunctionalInterface {
                    func_type_id: *func_type_id,
                })
            }
            ResolvedMethod::DefaultMethod {
                func_type,
                external_info,
                ..
            } => {
                if let Some(ext_info) = external_info {
                    return Ok(MethodTarget::External {
                        external_info: ext_info.clone(),
                        return_type: func_type.return_type_id,
                    });
                }
                let arena = input.analyzed.type_arena.borrow();
                let type_name_id = get_type_name_id_from_type_id(
                    input.object_type_id,
                    &arena,
                    &input.analyzed.entity_registry,
                )?;
                let method_info = lookup_direct_method(type_name_id)?;
                Ok(MethodTarget::Default {
                    method_info,
                    return_type: func_type.return_type_id,
                })
            }
            ResolvedMethod::InterfaceMethod { func_type_id, .. } => {
                // This branch is only taken when object_type is an interface
                let (interface_type_id, _) = input
                    .analyzed
                    .type_arena
                    .borrow()
                    .unwrap_interface(input.object_type_id)
                    .ok_or_else(|| "InterfaceMethod on non-interface type".to_string())?;
                let method_name_id = method_name_id_by_str(
                    input.analyzed,
                    &input.analyzed.interner,
                    input.method_name_str,
                )
                .ok_or_else(|| {
                    format!("method name {} not found as NameId", input.method_name_str)
                })?;
                Ok(MethodTarget::InterfaceDispatch {
                    interface_type_id,
                    method_name_id,
                    func_type_id: *func_type_id,
                })
            }
            ResolvedMethod::Static {
                type_def_id,
                method_id,
                func_type_id,
                ..
            } => Ok(MethodTarget::StaticMethod {
                type_def_id: *type_def_id,
                method_id: *method_id,
                func_type_id: *func_type_id,
            }),
        };
    }

    // No resolution found - try implement block methods first, then direct methods.
    let arena = input.analyzed.type_arena.borrow();

    // First, try EntityRegistry method bindings
    if let Some(type_def_id) =
        get_type_def_id_for_codegen_id(input.object_type_id, &arena, input.analyzed)
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
        drop(arena);

        // Found method binding in EntityRegistry - now get the compiled MethodInfo
        if let Some(type_id) = ImplTypeId::from_type_id(
            input.object_type_id,
            &input.analyzed.type_arena.borrow(),
            &input.analyzed.entity_registry,
        ) && let Some(method_info) = input
            .impl_method_infos
            .get(&(type_id, input.method_id))
            .copied()
        {
            return Ok(MethodTarget::Implemented {
                method_info,
                return_type: binding.func_type.return_type_id,
            });
        }

        // Fallback: try looking up by method_name_id from EntityRegistry
        if let Some(type_id) = ImplTypeId::from_type_id(
            input.object_type_id,
            &input.analyzed.type_arena.borrow(),
            &input.analyzed.entity_registry,
        ) && let Some(method_info) = input
            .impl_method_infos
            .get(&(type_id, method_name_id))
            .copied()
        {
            return Ok(MethodTarget::Implemented {
                method_info,
                return_type: binding.func_type.return_type_id,
            });
        }

        // If binding has external_info, use that directly
        if let Some(external_info) = &binding.external_info {
            return Ok(MethodTarget::External {
                external_info: external_info.clone(),
                return_type: binding.func_type.return_type_id,
            });
        }
    } else {
        drop(arena);
    }

    // Fallback: try impl_method_infos directly
    if let Some(type_id) = ImplTypeId::from_type_id(
        input.object_type_id,
        &input.analyzed.type_arena.borrow(),
        &input.analyzed.entity_registry,
    ) && let Ok(method_info) = lookup_impl_method(type_id)
    {
        return Ok(MethodTarget::Implemented {
            method_info,
            return_type: method_info.return_type,
        });
    }

    // Try direct methods (methods defined inside class/record)
    let arena = input.analyzed.type_arena.borrow();
    if let Ok(type_name_id) = get_type_name_id_from_type_id(
        input.object_type_id,
        &arena,
        &input.analyzed.entity_registry,
    ) && let Ok(method_info) = lookup_direct_method(type_name_id)
    {
        return Ok(MethodTarget::Direct {
            method_info,
            return_type: method_info.return_type,
        });
    }

    // Neither found - return error
    Err(format!(
        "Method {} not found on type",
        input.method_name_str,
    ))
}

/// Get TypeDefId for a type during codegen using TypeId
fn get_type_def_id_for_codegen_id(
    type_id: TypeId,
    arena: &vole_sema::type_arena::TypeArena,
    analyzed: &AnalyzedProgram,
) -> Option<TypeDefId> {
    use vole_sema::type_arena::SemaType;

    // For Class, Record, and Interface, extract TypeDefId directly
    match arena.get(type_id) {
        SemaType::Class { type_def_id, .. } => return Some(*type_def_id),
        SemaType::Record { type_def_id, .. } => return Some(*type_def_id),
        SemaType::Interface { type_def_id, .. } => return Some(*type_def_id),
        SemaType::Primitive(prim) => {
            let name_id = match prim {
                PrimitiveType::I8 => analyzed.name_table.primitives.i8,
                PrimitiveType::I16 => analyzed.name_table.primitives.i16,
                PrimitiveType::I32 => analyzed.name_table.primitives.i32,
                PrimitiveType::I64 => analyzed.name_table.primitives.i64,
                PrimitiveType::I128 => analyzed.name_table.primitives.i128,
                PrimitiveType::U8 => analyzed.name_table.primitives.u8,
                PrimitiveType::U16 => analyzed.name_table.primitives.u16,
                PrimitiveType::U32 => analyzed.name_table.primitives.u32,
                PrimitiveType::U64 => analyzed.name_table.primitives.u64,
                PrimitiveType::F32 => analyzed.name_table.primitives.f32,
                PrimitiveType::F64 => analyzed.name_table.primitives.f64,
                PrimitiveType::Bool => analyzed.name_table.primitives.bool,
                PrimitiveType::String => analyzed.name_table.primitives.string,
            };
            return analyzed.entity_registry.type_by_name(name_id);
        }
        _ => {}
    }
    None
}
