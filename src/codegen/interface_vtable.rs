use std::collections::{HashMap, HashSet};

use cranelift::prelude::*;
use cranelift_codegen::ir::FuncRef;
use cranelift_module::{DataDescription, DataId, Linkage, Module};

use crate::codegen::RuntimeFn;
use crate::codegen::types::{
    CompileCtx, CompiledValue, MethodInfo, method_name_id_by_str, type_metadata_by_name_id,
    type_to_cranelift, value_to_word, word_to_value,
};
use crate::errors::CodegenError;
use crate::frontend::Symbol;
use crate::identity::{MethodId, NameId, TypeDefId};
use crate::sema::entity_defs::TypeDefKind;
use crate::sema::generic::substitute_type;
use crate::sema::implement_registry::{ExternalMethodInfo, TypeId};
use crate::sema::{EntityRegistry, FunctionType, Type};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
enum InterfaceConcreteType {
    TypeId(TypeId),
    Function { is_closure: bool },
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
struct InterfaceVtableKey {
    interface_name: Symbol,
    concrete: InterfaceConcreteType,
}

#[derive(Debug, Default)]
pub(crate) struct InterfaceVtableRegistry {
    vtables: HashMap<InterfaceVtableKey, DataId>,
    wrapper_counter: u32,
}

enum VtableMethodTarget {
    Direct {
        method_info: MethodInfo,
        func_type: FunctionType,
    },
    Implemented {
        method_info: MethodInfo,
        func_type: FunctionType,
    },
    External {
        external_info: ExternalMethodInfo,
        func_type: FunctionType,
    },
    Function {
        func_type: FunctionType,
    },
}

impl InterfaceVtableRegistry {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    #[tracing::instrument(skip(self, ctx, interface_type_args), fields(interface = %ctx.interner.resolve(interface_name)))]
    pub(crate) fn get_or_create(
        &mut self,
        ctx: &mut CompileCtx,
        interface_name: Symbol,
        interface_type_args: &[Type],
        concrete_type: &Type,
    ) -> Result<DataId, String> {
        let concrete_key = match concrete_type {
            Type::Function(func_type) => InterfaceConcreteType::Function {
                is_closure: func_type.is_closure,
            },
            _ => {
                let type_id = TypeId::from_type(concrete_type, &ctx.analyzed.type_table)
                    .ok_or_else(|| {
                        format!(
                            "cannot build vtable for unsupported type {:?}",
                            concrete_type
                        )
                    })?;
                InterfaceConcreteType::TypeId(type_id)
            }
        };
        let key = InterfaceVtableKey {
            interface_name,
            concrete: concrete_key,
        };
        if let Some(data_id) = self.vtables.get(&key) {
            return Ok(*data_id);
        }

        // Get interface TypeDefId via Resolver, with short name fallback for prelude interfaces
        let interface_name_str = ctx.interner.resolve(interface_name);
        let interface_type_id = ctx
            .resolver()
            .resolve_type_str_or_interface(interface_name_str, &ctx.analyzed.entity_registry)
            .ok_or_else(|| format!("unknown interface {:?}", interface_name_str))?;
        let interface_name_id = ctx
            .analyzed
            .entity_registry
            .get_type(interface_type_id)
            .name_id;

        // Build substitution map from interface type params to concrete type args
        let interface_def = ctx.analyzed.entity_registry.get_type(interface_type_id);
        let substitutions: HashMap<NameId, Type> = interface_def
            .type_params
            .iter()
            .zip(interface_type_args.iter())
            .map(|(param_name_id, arg)| (*param_name_id, arg.clone()))
            .collect();

        // Collect methods via EntityRegistry
        let method_ids = collect_interface_methods_via_entity_registry(
            interface_type_id,
            &ctx.analyzed.entity_registry,
        )?;

        let word_bytes = ctx.pointer_type.bytes() as usize;

        tracing::debug!(
            interface = %ctx.interner.resolve(interface_name),
            concrete_type = ?concrete_type,
            method_count = method_ids.len(),
            "building vtable"
        );

        let type_name = match concrete_key {
            InterfaceConcreteType::TypeId(type_id) => {
                ctx.analyzed.name_table.display(type_id.name_id())
            }
            InterfaceConcreteType::Function { is_closure } => {
                if is_closure {
                    "closure".to_string()
                } else {
                    "function".to_string()
                }
            }
        };
        let vtable_name = format!(
            "__vole_iface_vtable_{}_{}",
            ctx.interner.resolve(interface_name),
            type_name
        );
        let data_id = ctx
            .module
            .declare_data(&vtable_name, Linkage::Local, false, false)
            .map_err(|e| e.to_string())?;

        let mut data = DataDescription::new();
        data.define_zeroinit(word_bytes * method_ids.len());
        data.set_align(word_bytes as u64);

        for (index, &method_id) in method_ids.iter().enumerate() {
            let method = ctx.analyzed.entity_registry.get_method(method_id);
            let method_name_str = ctx.analyzed.name_table.display(method.name_id);
            let target = resolve_vtable_target(
                ctx,
                interface_name_id,
                concrete_type,
                method_id,
                &substitutions,
            )?;
            let wrapper_id = self.compile_wrapper(
                ctx,
                interface_name_str,
                &method_name_str,
                concrete_type,
                &target,
            )?;
            let func_ref = ctx.module.declare_func_in_data(wrapper_id, &mut data);
            data.write_function_addr((index * word_bytes) as u32, func_ref);
            let target_type = match &target {
                VtableMethodTarget::Direct { .. } => "Direct",
                VtableMethodTarget::Implemented { .. } => "Implemented",
                VtableMethodTarget::External { .. } => "External",
                VtableMethodTarget::Function { .. } => "Function",
            };
            tracing::debug!(
                slot = index,
                method = %method_name_str,
                target = target_type,
                wrapper = ?wrapper_id,
                "vtable slot"
            );
        }

        ctx.module
            .define_data(data_id, &data)
            .map_err(|e| e.to_string())?;
        self.vtables.insert(key, data_id);
        Ok(data_id)
    }

    fn compile_wrapper(
        &mut self,
        ctx: &mut CompileCtx,
        interface_name: &str,
        method_name: &str,
        concrete_type: &Type,
        target: &VtableMethodTarget,
    ) -> Result<cranelift_module::FuncId, String> {
        let func_type = match target {
            VtableMethodTarget::Direct { func_type, .. }
            | VtableMethodTarget::Implemented { func_type, .. }
            | VtableMethodTarget::External { func_type, .. }
            | VtableMethodTarget::Function { func_type } => func_type,
        };

        let word_type = ctx.pointer_type;
        let mut sig = ctx.module.make_signature();
        sig.params.push(AbiParam::new(word_type));
        for _ in &func_type.params {
            sig.params.push(AbiParam::new(word_type));
        }
        if func_type.return_type.as_ref() != &Type::Void {
            sig.returns.push(AbiParam::new(word_type));
        }

        let wrapper_name = format!(
            "__vole_iface_wrap_{}_{}_{}",
            interface_name, method_name, self.wrapper_counter
        );
        self.wrapper_counter += 1;

        let func_id = ctx
            .module
            .declare_function(&wrapper_name, Linkage::Local, &sig)
            .map_err(|e| e.to_string())?;

        let mut func_ctx = ctx.module.make_context();
        func_ctx.func.signature = sig;
        let mut builder_ctx = FunctionBuilderContext::new();
        {
            let mut builder = FunctionBuilder::new(&mut func_ctx.func, &mut builder_ctx);
            let entry = builder.create_block();
            builder.append_block_params_for_function_params(entry);
            builder.switch_to_block(entry);
            builder.seal_block(entry);

            let params = builder.block_params(entry).to_vec();
            // self_word is now the boxed interface pointer [data_ptr, vtable_ptr]
            // We need to extract data_ptr for most targets
            let box_ptr = params[0];
            let data_word = builder.ins().load(word_type, MemFlags::new(), box_ptr, 0);
            let results = match target {
                VtableMethodTarget::Function { func_type } => {
                    let self_val =
                        word_to_value(&mut builder, data_word, concrete_type, ctx.pointer_type);
                    let mut args = Vec::with_capacity(func_type.params.len() + 1);
                    for (param_word, param_ty) in params[1..].iter().zip(func_type.params.iter()) {
                        args.push(word_to_value(
                            &mut builder,
                            *param_word,
                            param_ty,
                            ctx.pointer_type,
                        ));
                    }

                    let (func_ptr, call_args, sig) = if func_type.is_closure {
                        let closure_get_key = ctx
                            .func_registry
                            .runtime_key(RuntimeFn::ClosureGetFunc)
                            .ok_or_else(|| "closure get func not registered".to_string())?;
                        let closure_get_id = ctx
                            .func_registry
                            .func_id(closure_get_key)
                            .ok_or_else(|| "closure get func id missing".to_string())?;
                        let closure_get_ref = ctx
                            .module
                            .declare_func_in_func(closure_get_id, builder.func);
                        let closure_call = builder.ins().call(closure_get_ref, &[self_val]);
                        let func_ptr = builder.inst_results(closure_call)[0];

                        let mut sig = ctx.module.make_signature();
                        sig.params.push(AbiParam::new(type_to_cranelift(
                            concrete_type,
                            ctx.pointer_type,
                        )));
                        for param_type in &func_type.params {
                            sig.params.push(AbiParam::new(type_to_cranelift(
                                param_type,
                                ctx.pointer_type,
                            )));
                        }
                        if func_type.return_type.as_ref() != &Type::Void {
                            sig.returns.push(AbiParam::new(type_to_cranelift(
                                &func_type.return_type,
                                ctx.pointer_type,
                            )));
                        }

                        let mut call_args = Vec::with_capacity(args.len() + 1);
                        call_args.push(self_val);
                        call_args.extend(args);
                        (func_ptr, call_args, sig)
                    } else {
                        let mut sig = ctx.module.make_signature();
                        for param_type in &func_type.params {
                            sig.params.push(AbiParam::new(type_to_cranelift(
                                param_type,
                                ctx.pointer_type,
                            )));
                        }
                        if func_type.return_type.as_ref() != &Type::Void {
                            sig.returns.push(AbiParam::new(type_to_cranelift(
                                &func_type.return_type,
                                ctx.pointer_type,
                            )));
                        }
                        (self_val, args, sig)
                    };

                    let sig_ref = builder.import_signature(sig);
                    let call = builder.ins().call_indirect(sig_ref, func_ptr, &call_args);
                    builder.inst_results(call).to_vec()
                }
                VtableMethodTarget::Direct { method_info, .. }
                | VtableMethodTarget::Implemented { method_info, .. } => {
                    let self_val =
                        word_to_value(&mut builder, data_word, concrete_type, ctx.pointer_type);
                    let mut call_args = Vec::with_capacity(1 + func_type.params.len());
                    call_args.push(self_val);
                    for (param_word, param_ty) in params[1..].iter().zip(func_type.params.iter()) {
                        call_args.push(word_to_value(
                            &mut builder,
                            *param_word,
                            param_ty,
                            ctx.pointer_type,
                        ));
                    }
                    let func_id = ctx
                        .func_registry
                        .func_id(method_info.func_key)
                        .ok_or_else(|| "method function id not found".to_string())?;
                    let func_ref = ctx.module.declare_func_in_func(func_id, builder.func);
                    let call = builder.ins().call(func_ref, &call_args);
                    builder.inst_results(call).to_vec()
                }
                VtableMethodTarget::External {
                    external_info,
                    func_type,
                } => {
                    // For Iterator interface, wrap the boxed interface in a UnifiedIterator
                    // so external functions like vole_iter_collect can iterate via vtable.
                    let self_val = if interface_name == "Iterator" {
                        // Call vole_interface_iter(box_ptr) to create UnifiedIterator adapter
                        let interface_iter_fn = ctx
                            .native_registry
                            .lookup("std:intrinsics", "interface_iter")
                            .ok_or_else(|| {
                                "native function std:intrinsics::interface_iter not found"
                                    .to_string()
                            })?;
                        let mut iter_sig = ctx.module.make_signature();
                        iter_sig.params.push(AbiParam::new(ctx.pointer_type));
                        iter_sig.returns.push(AbiParam::new(ctx.pointer_type));
                        let iter_sig_ref = builder.import_signature(iter_sig);
                        let iter_fn_ptr = builder
                            .ins()
                            .iconst(ctx.pointer_type, interface_iter_fn.ptr as i64);
                        let iter_call =
                            builder
                                .ins()
                                .call_indirect(iter_sig_ref, iter_fn_ptr, &[box_ptr]);
                        builder.inst_results(iter_call)[0]
                    } else {
                        word_to_value(&mut builder, data_word, concrete_type, ctx.pointer_type)
                    };
                    let mut call_args = Vec::with_capacity(1 + func_type.params.len());
                    call_args.push(self_val);
                    for (param_word, param_ty) in params[1..].iter().zip(func_type.params.iter()) {
                        call_args.push(word_to_value(
                            &mut builder,
                            *param_word,
                            param_ty,
                            ctx.pointer_type,
                        ));
                    }
                    let native_func = ctx
                        .native_registry
                        .lookup(&external_info.module_path, &external_info.native_name)
                        .ok_or_else(|| {
                            format!(
                                "native function {}::{} not found",
                                external_info.module_path, external_info.native_name
                            )
                        })?;
                    let mut native_sig = ctx.module.make_signature();
                    // For Iterator, the self param is now *mut UnifiedIterator (pointer)
                    let self_param_type = if interface_name == "Iterator" {
                        ctx.pointer_type
                    } else {
                        type_to_cranelift(concrete_type, ctx.pointer_type)
                    };
                    native_sig.params.push(AbiParam::new(self_param_type));
                    for param_type in &func_type.params {
                        native_sig.params.push(AbiParam::new(type_to_cranelift(
                            param_type,
                            ctx.pointer_type,
                        )));
                    }
                    if func_type.return_type.as_ref() != &Type::Void {
                        native_sig.returns.push(AbiParam::new(type_to_cranelift(
                            &func_type.return_type,
                            ctx.pointer_type,
                        )));
                    }
                    let sig_ref = builder.import_signature(native_sig);
                    let func_ptr_val = builder
                        .ins()
                        .iconst(ctx.pointer_type, native_func.ptr as i64);
                    let call = builder
                        .ins()
                        .call_indirect(sig_ref, func_ptr_val, &call_args);
                    builder.inst_results(call).to_vec()
                }
            };

            if func_type.return_type.as_ref() == &Type::Void {
                builder.ins().return_(&[]);
            } else {
                let Some(result) = results.first().copied() else {
                    return Err(
                        CodegenError::internal("interface wrapper missing return value").into(),
                    );
                };
                let heap_alloc_ref = runtime_heap_alloc_ref(ctx, &mut builder)?;
                let word = value_to_word(
                    &mut builder,
                    &CompiledValue {
                        value: result,
                        ty: type_to_cranelift(&func_type.return_type, ctx.pointer_type),
                        vole_type: (*func_type.return_type).clone(),
                    },
                    ctx.pointer_type,
                    Some(heap_alloc_ref),
                )?;
                builder.ins().return_(&[word]);
            }

            builder.finalize();
        }

        ctx.module
            .define_function(func_id, &mut func_ctx)
            .map_err(|e| e.to_string())?;
        ctx.module.clear_context(&mut func_ctx);

        Ok(func_id)
    }
}

/// Look up an interface method slot using EntityRegistry (TypeDefId-based)
///
/// This uses TypeDefId and NameId to locate methods without string comparisons.
pub(crate) fn interface_method_slot_by_type_def_id(
    interface_id: TypeDefId,
    method_name_id: NameId,
    entity_registry: &EntityRegistry,
) -> Result<usize, String> {
    // Collect all methods from the interface and its parents
    let methods = collect_interface_methods_via_entity_registry(interface_id, entity_registry)?;

    // Find the method by its name_id
    methods
        .iter()
        .position(|method_id| {
            let method = entity_registry.get_method(*method_id);
            method.name_id == method_name_id
        })
        .ok_or_else(|| {
            format!(
                "method with name_id {:?} not found on interface {:?}",
                method_name_id, interface_id
            )
        })
}

/// Collect all methods from an interface and its parent interfaces using EntityRegistry
///
/// Returns methods in a consistent order for vtable slot assignment.
/// Parent interface methods come first, then the interface's own methods.
/// This matches the order used by collect_interface_methods.
/// Collect all methods from an interface and its parent interfaces using EntityRegistry
pub(crate) fn collect_interface_methods_via_entity_registry(
    interface_id: TypeDefId,
    entity_registry: &EntityRegistry,
) -> Result<Vec<MethodId>, String> {
    let interface = entity_registry.get_type(interface_id);

    // Verify this is an interface
    if interface.kind != TypeDefKind::Interface {
        return Err(format!(
            "TypeDefId {:?} is not an interface (kind: {:?})",
            interface_id, interface.kind
        ));
    }

    let mut methods = Vec::new();
    let mut seen_interfaces = HashSet::new();
    let mut seen_methods = HashSet::new();

    collect_interface_methods_inner_entity_registry(
        interface_id,
        entity_registry,
        &mut methods,
        &mut seen_interfaces,
        &mut seen_methods,
    );

    Ok(methods)
}

fn collect_interface_methods_inner_entity_registry(
    interface_id: TypeDefId,
    entity_registry: &EntityRegistry,
    methods: &mut Vec<MethodId>,
    seen_interfaces: &mut HashSet<TypeDefId>,
    seen_methods: &mut HashSet<NameId>,
) {
    if !seen_interfaces.insert(interface_id) {
        return;
    }

    let interface = entity_registry.get_type(interface_id);

    // Process parent interfaces first (to match the order of collect_interface_methods)
    for parent_id in interface.extends.clone() {
        collect_interface_methods_inner_entity_registry(
            parent_id,
            entity_registry,
            methods,
            seen_interfaces,
            seen_methods,
        );
    }

    // Add this interface's methods
    for method_id in &interface.methods {
        let method = entity_registry.get_method(*method_id);
        if seen_methods.insert(method.name_id) {
            methods.push(*method_id);
        }
    }
}

#[tracing::instrument(skip(builder, ctx, value), fields(interface_type = ?interface_type))]
pub(crate) fn box_interface_value(
    builder: &mut FunctionBuilder,
    ctx: &mut CompileCtx,
    value: CompiledValue,
    interface_type: &Type,
) -> Result<CompiledValue, String> {
    let Type::Interface(interface) = interface_type else {
        return Ok(value);
    };

    // Look up the interface Symbol name for vtable operations via EntityRegistry
    let interface_type_id = ctx
        .analyzed
        .entity_registry
        .type_by_name(interface.name_id)
        .ok_or_else(|| format!("unknown interface with name_id {:?}", interface.name_id))?;
    let interface_def = ctx.analyzed.entity_registry.get_type(interface_type_id);
    // Get the interface Symbol by looking up the short name in the interner
    let interface_name_str = ctx
        .analyzed
        .name_table
        .last_segment_str(interface_def.name_id)
        .ok_or_else(|| {
            format!(
                "cannot get interface name string for {:?}",
                interface.name_id
            )
        })?;
    let interface_name = ctx.interner.lookup(&interface_name_str).ok_or_else(|| {
        format!(
            "interface name '{}' not found in interner",
            interface_name_str
        )
    })?;

    tracing::debug!(
        interface = %ctx.interner.resolve(interface_name),
        value_type = ?value.vole_type,
        "boxing value as interface"
    );

    if matches!(value.vole_type, Type::Interface(_)) {
        tracing::debug!("already interface, skip boxing");
        return Ok(value);
    }

    // Check if this is an external-only interface via EntityRegistry
    let interface_type_id = ctx
        .analyzed
        .entity_registry
        .type_by_name(interface.name_id)
        .ok_or_else(|| {
            format!(
                "interface {:?} not found in entity_registry",
                interface.name_id
            )
        })?;

    if ctx
        .analyzed
        .entity_registry
        .is_external_only(interface_type_id)
    {
        tracing::debug!("external-only interface, skip boxing");
        return Ok(CompiledValue {
            value: value.value,
            ty: ctx.pointer_type,
            vole_type: interface_type.clone(),
        });
    }

    let heap_alloc_ref = runtime_heap_alloc_ref(ctx, builder)?;
    let data_word = value_to_word(builder, &value, ctx.pointer_type, Some(heap_alloc_ref))?;
    let vtable_id = ctx.interface_vtables.borrow_mut().get_or_create(
        ctx,
        interface_name,
        &interface.type_args,
        &value.vole_type,
    )?;
    let vtable_gv = ctx.module.declare_data_in_func(vtable_id, builder.func);
    let vtable_ptr = builder.ins().global_value(ctx.pointer_type, vtable_gv);

    let word_bytes = ctx.pointer_type.bytes() as i64;
    let size_val = builder.ins().iconst(ctx.pointer_type, word_bytes * 2);
    let alloc_call = builder.ins().call(heap_alloc_ref, &[size_val]);
    let iface_ptr = builder.inst_results(alloc_call)[0];

    builder
        .ins()
        .store(MemFlags::new(), data_word, iface_ptr, 0);
    builder
        .ins()
        .store(MemFlags::new(), vtable_ptr, iface_ptr, word_bytes as i32);

    Ok(CompiledValue {
        value: iface_ptr,
        ty: ctx.pointer_type,
        vole_type: interface_type.clone(),
    })
}

fn resolve_vtable_target(
    ctx: &CompileCtx,
    interface_name_id: NameId,
    concrete_type: &Type,
    interface_method_id: MethodId,
    substitutions: &HashMap<NameId, Type>,
) -> Result<VtableMethodTarget, String> {
    // Get method info from EntityRegistry
    let interface_method = ctx.analyzed.entity_registry.get_method(interface_method_id);
    let method_name_str = ctx.analyzed.name_table.display(interface_method.name_id);

    // Apply substitutions to get concrete param/return types
    let substituted_params: Vec<Type> = interface_method
        .signature
        .params
        .iter()
        .map(|t| substitute_type(t, substitutions))
        .collect();
    let substituted_return_type =
        substitute_type(&interface_method.signature.return_type, substitutions);

    if let Type::Function(func_type) = concrete_type {
        return Ok(VtableMethodTarget::Function {
            func_type: func_type.clone(),
        });
    }

    let type_id = TypeId::from_type(concrete_type, &ctx.analyzed.type_table).ok_or_else(|| {
        format!(
            "cannot resolve interface method {} on {:?}",
            method_name_str, concrete_type
        )
    })?;
    // Use string-based lookup for cross-interner safety (method_def is from stdlib interner)
    // This may return None for default interface methods that aren't explicitly implemented
    let method_name_id = method_name_id_by_str(ctx.analyzed, ctx.interner, &method_name_str);

    // Check implement registry for explicit implementations
    if let Some(method_name_id) = method_name_id
        && let Some(impl_) = ctx
            .analyzed
            .implement_registry
            .get_method(&type_id, method_name_id)
    {
        if let Some(external_info) = impl_.external_info.clone() {
            return Ok(VtableMethodTarget::External {
                external_info,
                func_type: impl_.func_type.clone(),
            });
        }
        let method_info = ctx
            .impl_method_infos
            .get(&(type_id, method_name_id))
            .cloned()
            .ok_or_else(|| "implement method info not found".to_string())?;
        return Ok(VtableMethodTarget::Implemented {
            method_info,
            func_type: impl_.func_type.clone(),
        });
    }

    // Check direct methods on class/record
    if let Some(method_name_id) = method_name_id
        && let Some(type_name_id) = match concrete_type {
            Type::Class(class_type) => Some(class_type.name_id),
            Type::Record(record_type) => Some(record_type.name_id),
            _ => None,
        }
        && let Some(meta) = type_metadata_by_name_id(ctx.type_metadata, type_name_id)
        && let Some(method_info) = meta.method_infos.get(&method_name_id).cloned()
    {
        // Look up method type via EntityRegistry
        let func_type = ctx
            .analyzed
            .entity_registry
            .type_by_name(type_name_id)
            .and_then(|type_def_id| {
                ctx.analyzed
                    .entity_registry
                    .find_method_on_type(type_def_id, method_name_id)
            })
            .map(|m_id| {
                ctx.analyzed
                    .entity_registry
                    .get_method(m_id)
                    .signature
                    .clone()
            })
            .unwrap_or_else(|| FunctionType {
                params: substituted_params.clone(),
                return_type: Box::new(substituted_return_type.clone()),
                is_closure: false,
            });
        return Ok(VtableMethodTarget::Direct {
            method_info,
            func_type,
        });
    }

    // Fall back to interface default if method has one
    if interface_method.has_default {
        // Check for default external binding via EntityRegistry
        if let Some(interface_type_id) =
            ctx.analyzed.entity_registry.type_by_name(interface_name_id)
            && let Some(method_name_id) = method_name_id
            && let Some(found_method_id) = ctx
                .analyzed
                .entity_registry
                .find_method_on_type(interface_type_id, method_name_id)
            && let Some(external_info) = ctx
                .analyzed
                .entity_registry
                .get_external_binding(found_method_id)
        {
            return Ok(VtableMethodTarget::External {
                external_info: external_info.clone(),
                func_type: FunctionType {
                    params: substituted_params,
                    return_type: Box::new(substituted_return_type),
                    is_closure: false,
                },
            });
        }
        // TODO: Handle Vole body defaults when interface method bodies are supported
    }

    Err(CodegenError::not_found(
        "method implementation",
        format!("{} on {:?}", method_name_str, concrete_type),
    )
    .into())
}

fn runtime_heap_alloc_ref(
    ctx: &mut CompileCtx,
    builder: &mut FunctionBuilder,
) -> Result<FuncRef, String> {
    let key = ctx
        .func_registry
        .runtime_key(RuntimeFn::HeapAlloc)
        .ok_or_else(|| "heap allocator not registered".to_string())?;
    let func_id = ctx
        .func_registry
        .func_id(key)
        .ok_or_else(|| "heap allocator function id missing".to_string())?;
    Ok(ctx.module.declare_func_in_func(func_id, builder.func))
}
