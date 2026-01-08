use std::collections::{HashMap, HashSet};

use cranelift::prelude::*;
use cranelift_codegen::ir::FuncRef;
use cranelift_module::{DataDescription, DataId, Linkage, Module};

use crate::codegen::RuntimeFn;
use crate::codegen::types::{
    CompileCtx, CompiledValue, MethodInfo, method_name_id, type_to_cranelift, value_to_word,
    word_to_value,
};
use crate::errors::CodegenError;
use crate::frontend::{Interner, Symbol};
use crate::sema::implement_registry::{ExternalMethodInfo, TypeId};
use crate::sema::interface_registry::InterfaceMethodDef;
use crate::sema::{FunctionType, Type};

pub(crate) fn iface_debug_enabled() -> bool {
    std::env::var_os("VOLE_DEBUG_IFACE").is_some()
}

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

    pub(crate) fn get_or_create(
        &mut self,
        ctx: &mut CompileCtx,
        interface_name: Symbol,
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

        let methods = collect_interface_methods(
            interface_name,
            &ctx.analyzed.interface_registry,
            ctx.interner,
        )
        .ok_or_else(|| {
            format!(
                "unknown interface {:?}",
                ctx.interner.resolve(interface_name)
            )
        })?;
        let word_bytes = ctx.pointer_type.bytes() as usize;

        if iface_debug_enabled() {
            eprintln!(
                "iface_vtable: interface={} type={:?} methods={}",
                ctx.interner.resolve(interface_name),
                concrete_type,
                methods.len()
            );
        }

        let type_name = match concrete_key {
            InterfaceConcreteType::TypeId(type_id) => ctx
                .analyzed
                .name_table
                .display(type_id.name_id(), ctx.interner),
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
        data.define_zeroinit(word_bytes * methods.len());
        data.set_align(word_bytes as u64);

        for (index, method_def) in methods.iter().enumerate() {
            let target = resolve_vtable_target(ctx, concrete_type, method_def)?;
            let wrapper_id =
                self.compile_wrapper(ctx, interface_name, method_def.name, concrete_type, &target)?;
            let func_ref = ctx.module.declare_func_in_data(wrapper_id, &mut data);
            data.write_function_addr((index * word_bytes) as u32, func_ref);
            if iface_debug_enabled() {
                eprintln!(
                    "iface_vtable: slot={} method={} wrapper={:?}",
                    index,
                    ctx.interner.resolve(method_def.name),
                    wrapper_id
                );
            }
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
        interface_name: Symbol,
        method_name: Symbol,
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
            ctx.interner.resolve(interface_name),
            ctx.interner.resolve(method_name),
            self.wrapper_counter
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
            let self_word = params[0];
            let results = match target {
                VtableMethodTarget::Function { func_type } => {
                    let self_val =
                        word_to_value(&mut builder, self_word, concrete_type, ctx.pointer_type);
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
                        word_to_value(&mut builder, self_word, concrete_type, ctx.pointer_type);
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
                    let self_val =
                        word_to_value(&mut builder, self_word, concrete_type, ctx.pointer_type);
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
                    native_sig.params.push(AbiParam::new(type_to_cranelift(
                        concrete_type,
                        ctx.pointer_type,
                    )));
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

pub(crate) fn interface_method_slot(
    interface_name: Symbol,
    method_name: Symbol,
    registry: &crate::sema::interface_registry::InterfaceRegistry,
    interner: &Interner,
) -> Result<usize, String> {
    let methods = collect_interface_methods(interface_name, registry, interner)
        .ok_or_else(|| format!("unknown interface {}", interner.resolve(interface_name)))?;
    methods
        .iter()
        .position(|m| m.name == method_name)
        .ok_or_else(|| {
            format!(
                "method {} not found on interface {}",
                interner.resolve(method_name),
                interner.resolve(interface_name)
            )
        })
}

pub(crate) fn box_interface_value(
    builder: &mut FunctionBuilder,
    ctx: &mut CompileCtx,
    value: CompiledValue,
    interface_type: &Type,
) -> Result<CompiledValue, String> {
    let Type::Interface(interface) = interface_type else {
        return Ok(value);
    };

    if iface_debug_enabled() {
        eprintln!(
            "iface_box: target={} value_type={:?}",
            ctx.interner.resolve(interface.name),
            value.vole_type
        );
    }

    if matches!(value.vole_type, Type::Interface(_)) {
        if iface_debug_enabled() {
            eprintln!("iface_box: already interface, skip boxing");
        }
        return Ok(value);
    }

    if ctx
        .analyzed
        .interface_registry
        .is_external_only(interface.name, ctx.interner)
    {
        if iface_debug_enabled() {
            eprintln!("iface_box: external-only interface, skip boxing");
        }
        return Ok(CompiledValue {
            value: value.value,
            ty: ctx.pointer_type,
            vole_type: interface_type.clone(),
        });
    }

    let heap_alloc_ref = runtime_heap_alloc_ref(ctx, builder)?;
    let data_word = value_to_word(builder, &value, ctx.pointer_type, Some(heap_alloc_ref))?;
    let vtable_id =
        ctx.interface_vtables
            .borrow_mut()
            .get_or_create(ctx, interface.name, &value.vole_type)?;
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

fn collect_interface_methods(
    interface_name: Symbol,
    registry: &crate::sema::interface_registry::InterfaceRegistry,
    interner: &Interner,
) -> Option<Vec<InterfaceMethodDef>> {
    let mut methods = Vec::new();
    let mut seen_interfaces = HashSet::new();
    let mut seen_methods = HashSet::new();
    collect_interface_methods_inner(
        interface_name,
        registry,
        interner,
        &mut methods,
        &mut seen_interfaces,
        &mut seen_methods,
    )?;
    Some(methods)
}

fn collect_interface_methods_inner(
    interface_name: Symbol,
    registry: &crate::sema::interface_registry::InterfaceRegistry,
    interner: &Interner,
    methods: &mut Vec<InterfaceMethodDef>,
    seen_interfaces: &mut HashSet<Symbol>,
    seen_methods: &mut HashSet<Symbol>,
) -> Option<()> {
    if !seen_interfaces.insert(interface_name) {
        return Some(());
    }
    let iface = registry.get(interface_name, interner)?;
    for parent in &iface.extends {
        collect_interface_methods_inner(
            *parent,
            registry,
            interner,
            methods,
            seen_interfaces,
            seen_methods,
        )?;
    }
    for method in &iface.methods {
        if seen_methods.insert(method.name) {
            methods.push(method.clone());
        }
    }
    Some(())
}

fn resolve_vtable_target(
    ctx: &CompileCtx,
    concrete_type: &Type,
    method_def: &InterfaceMethodDef,
) -> Result<VtableMethodTarget, String> {
    if let Type::Function(func_type) = concrete_type {
        return Ok(VtableMethodTarget::Function {
            func_type: func_type.clone(),
        });
    }

    let type_id = TypeId::from_type(concrete_type, &ctx.analyzed.type_table).ok_or_else(|| {
        format!(
            "cannot resolve interface method {} on {:?}",
            ctx.interner.resolve(method_def.name),
            concrete_type
        )
    })?;
    let method_id =
        method_name_id(ctx.analyzed, ctx.interner, method_def.name).ok_or_else(|| {
            format!(
                "method name not interned: {}",
                ctx.interner.resolve(method_def.name)
            )
        })?;

    if let Some(impl_) = ctx
        .analyzed
        .implement_registry
        .get_method(&type_id, method_id)
    {
        if let Some(external_info) = impl_.external_info.clone() {
            return Ok(VtableMethodTarget::External {
                external_info,
                func_type: impl_.func_type.clone(),
            });
        }
        let method_info = ctx
            .impl_method_infos
            .get(&(type_id, method_id))
            .cloned()
            .ok_or_else(|| "implement method info not found".to_string())?;
        return Ok(VtableMethodTarget::Implemented {
            method_info,
            func_type: impl_.func_type.clone(),
        });
    }

    if let Some(type_sym) = match concrete_type {
        Type::Class(class_type) => Some(class_type.name),
        Type::Record(record_type) => Some(record_type.name),
        _ => None,
    } && let Some(meta) = ctx.type_metadata.get(&type_sym)
        && let Some(method_info) = meta.method_infos.get(&method_id).cloned()
    {
        let func_type = match &meta.vole_type {
            Type::Class(class_type) => ctx
                .analyzed
                .methods
                .get(&(class_type.name_id, method_id))
                .cloned(),
            Type::Record(record_type) => ctx
                .analyzed
                .methods
                .get(&(record_type.name_id, method_id))
                .cloned(),
            _ => None,
        };
        let func_type = func_type.unwrap_or_else(|| FunctionType {
            params: method_def.params.clone(),
            return_type: Box::new(method_def.return_type.clone()),
            is_closure: false,
        });
        return Ok(VtableMethodTarget::Direct {
            method_info,
            func_type,
        });
    }

    Err(CodegenError::not_found(
        "method implementation",
        format!(
            "{} on {:?}",
            ctx.interner.resolve(method_def.name),
            concrete_type
        ),
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
