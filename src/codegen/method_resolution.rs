use std::collections::HashMap;

use crate::codegen::structs::get_type_name_symbol;
use crate::codegen::types::MethodInfo;
use crate::commands::common::AnalyzedProgram;
use crate::frontend::Symbol;
use crate::identity::NameId;
use crate::sema::implement_registry::{ExternalMethodInfo, TypeId};
use crate::sema::resolution::ResolvedMethod;
use crate::sema::{FunctionType, Type};

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

pub(crate) struct MethodResolutionInput<'a, F>
where
    F: Fn(Symbol) -> String,
{
    pub analyzed: &'a AnalyzedProgram,
    pub type_metadata: &'a HashMap<Symbol, crate::codegen::types::TypeMetadata>,
    pub impl_method_infos: &'a HashMap<(TypeId, NameId), MethodInfo>,
    pub method_name_str: &'a str,
    pub object_type: &'a Type,
    pub method_id: NameId,
    pub resolution: Option<&'a ResolvedMethod>,
    pub display_type_symbol: F,
}

pub(crate) fn resolve_method_target<F>(
    input: MethodResolutionInput<'_, F>,
) -> Result<MethodTarget, String>
where
    F: Fn(Symbol) -> String,
{
    let lookup_direct_method = |type_name: Symbol| {
        input
            .type_metadata
            .get(&type_name)
            .and_then(|meta| meta.method_infos.get(&input.method_id))
            .cloned()
            .ok_or_else(|| {
                format!(
                    "Method {} not found on type {}",
                    input.method_name_str,
                    (input.display_type_symbol)(type_name)
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
                let type_name = get_type_name_symbol(input.object_type)?;
                let method_info = lookup_direct_method(type_name)?;
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
                    return Err(format!(
                        "Unhandled builtin method: {}",
                        input.method_name_str
                    ));
                }
                if let Some(ext_info) = external_info {
                    return Ok(MethodTarget::External {
                        external_info: ext_info.clone(),
                        return_type: (*func_type.return_type).clone(),
                    });
                }
                let type_id = TypeId::from_type(input.object_type, &input.analyzed.type_table)
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
                type_name,
                func_type,
                ..
            } => {
                let method_info = lookup_direct_method(*type_name)?;
                Ok(MethodTarget::Default {
                    method_info,
                    return_type: (*func_type.return_type).clone(),
                })
            }
            ResolvedMethod::InterfaceMethod {
                interface_name,
                method_name,
                func_type,
            } => Ok(MethodTarget::InterfaceDispatch {
                interface_name: *interface_name,
                method_name: *method_name,
                func_type: func_type.clone(),
            }),
        };
    }

    // No resolution found - try direct method lookup for default method bodies.
    let type_name = get_type_name_symbol(input.object_type)?;
    let method_info = lookup_direct_method(type_name)?;
    let return_type = method_info.return_type.clone();
    Ok(MethodTarget::Direct {
        method_info,
        return_type,
    })
}
