use std::collections::HashMap;

use crate::codegen::structs::get_type_name_id;
use crate::codegen::types::{MethodInfo, type_metadata_by_name_id};
use crate::commands::common::AnalyzedProgram;
use crate::errors::CodegenError;
use crate::frontend::Symbol;
use crate::identity::NameId;
use crate::sema::implement_registry::{ExternalMethodInfo, TypeId};
use crate::sema::resolution::ResolvedMethod;
use crate::sema::{FunctionType, Type};

#[derive(Debug)]
pub(crate) enum MethodTarget {
    Direct {
        method_info: MethodInfo,
        return_type: Type,
    },
    Implemented {
        method_info: MethodInfo,
        return_type: Type,
    },
    Default {
        method_info: MethodInfo,
        return_type: Type,
    },
    FunctionalInterface {
        func_type: FunctionType,
    },
    External {
        external_info: ExternalMethodInfo,
        return_type: Type,
    },
    InterfaceDispatch {
        interface_name: Symbol,
        method_name: Symbol,
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
        type_metadata_by_name_id(input.type_metadata, type_name_id)
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

    if let Some(resolution) = input.resolution {
        return match resolution {
            ResolvedMethod::Direct { func_type } => {
                let type_name_id = get_type_name_id(input.object_type)?;
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
                if let Type::Interface(interface_type) = input.object_type {
                    // Look up interface by name_id to get the correct symbol for the current interner
                    let iface_def = input
                        .analyzed
                        .interface_registry
                        .get_by_name_id(interface_type.name_id)
                        .ok_or_else(|| {
                            format!(
                                "interface {:?} not found by name_id",
                                interface_type.name_id
                            )
                        })?;
                    // Look up interface name symbol in current interner
                    let interface_name_sym = input
                        .analyzed
                        .interner
                        .lookup(&iface_def.name_str)
                        .ok_or_else(|| {
                            format!("interface name {} not interned", iface_def.name_str)
                        })?;
                    let method_name_sym = input
                        .analyzed
                        .interner
                        .lookup(input.method_name_str)
                        .ok_or_else(|| {
                            format!("method name {} not interned", input.method_name_str)
                        })?;
                    return Ok(MethodTarget::InterfaceDispatch {
                        interface_name: interface_name_sym,
                        method_name: method_name_sym,
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
                let type_id = TypeId::from_type(input.object_type, &input.analyzed.type_table)
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
            ResolvedMethod::DefaultMethod { func_type, .. } => {
                // Get the name_id from the object type since DefaultMethod is called on a class/record
                let type_name_id = get_type_name_id(input.object_type)?;
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
                // Use object type's interface info for cross-interner safety
                if let Type::Interface(interface_type) = input.object_type {
                    let iface_def = input
                        .analyzed
                        .interface_registry
                        .get_by_name_id(interface_type.name_id)
                        .ok_or_else(|| {
                            format!(
                                "interface {:?} not found by name_id",
                                interface_type.name_id
                            )
                        })?;
                    let interface_name_sym = input
                        .analyzed
                        .interner
                        .lookup(&iface_def.name_str)
                        .ok_or_else(|| {
                            format!("interface name {} not interned", iface_def.name_str)
                        })?;
                    let method_name_sym = input
                        .analyzed
                        .interner
                        .lookup(input.method_name_str)
                        .ok_or_else(|| {
                            format!("method name {} not interned", input.method_name_str)
                        })?;
                    Ok(MethodTarget::InterfaceDispatch {
                        interface_name: interface_name_sym,
                        method_name: method_name_sym,
                        func_type: func_type.clone(),
                    })
                } else {
                    Err(format!(
                        "InterfaceMethod resolution on non-interface type: {:?}",
                        input.object_type
                    ))
                }
            }
        };
    }

    // No resolution found - try direct method lookup for default method bodies.
    let type_name_id = get_type_name_id(input.object_type)?;
    let method_info = lookup_direct_method(type_name_id)?;
    let return_type = method_info.return_type.clone();
    Ok(MethodTarget::Direct {
        method_info,
        return_type,
    })
}
