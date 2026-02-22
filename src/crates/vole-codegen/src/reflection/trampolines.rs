// src/codegen/reflection/trampolines.rs
//
// Compile getter, setter, and constructor trampoline functions for FieldMeta
// and TypeMeta. Each trampoline is a JIT-compiled function wrapped in a
// zero-capture closure.

use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};
use vole_identity::TypeDefId;
use vole_runtime::value::RuntimeTypeId;
use vole_sema::type_arena::TypeId;

use crate::RuntimeKey;
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::CompiledValue;

use super::ReflectionTypeInfo;

/// Resolve a RuntimeKey to a FuncId through the function registry.
fn resolve_runtime(cg: &mut Cg, key: RuntimeKey) -> CodegenResult<FuncId> {
    let func_key = cg
        .funcs()
        .runtime_key(key)
        .ok_or_else(|| CodegenError::not_found("runtime function", key.name()))?;
    cg.funcs()
        .func_id(func_key)
        .ok_or_else(|| CodegenError::not_found("runtime func_id", key.name()))
}

/// Build a getter closure for a field: `(unknown) -> unknown`.
///
/// The getter extracts the instance from the unknown argument,
/// reads the field via InstanceGetField, and returns it boxed as unknown.
/// `runtime_tag` is the RuntimeTypeId tag for boxing the result (e.g.
/// `RuntimeTypeId::String` for string fields, `RuntimeTypeId::I64` for i64).
pub(super) fn build_getter(
    cg: &mut Cg,
    _target_type_def_id: TypeDefId,
    field_slot: usize,
    runtime_tag: i64,
) -> CodegenResult<CompiledValue> {
    let ptr_type = cg.ptr_type();
    let lambda_id = cg.next_lambda_id();

    // Resolve runtime FuncIds before creating the builder
    let get_field_func = resolve_runtime(cg, RuntimeKey::InstanceGetField)?;
    let heap_alloc_func = resolve_runtime(cg, RuntimeKey::HeapAlloc)?;

    // Signature: (closure_ptr, unknown_ptr) -> unknown_ptr
    let mut sig = cg.jit_module().make_signature();
    sig.params.push(AbiParam::new(ptr_type)); // closure ptr (ignored)
    sig.params.push(AbiParam::new(ptr_type)); // instance as unknown ptr
    sig.returns.push(AbiParam::new(ptr_type)); // field value as unknown ptr

    let func_key = cg.funcs().intern_lambda(lambda_id);
    let func_name = cg.funcs().display(func_key);
    let func_id = cg
        .jit_module()
        .declare_function(&func_name, cranelift_module::Linkage::Local, &sig)
        .map_err(CodegenError::cranelift)?;
    cg.funcs().set_func_id(func_key, func_id);

    let mut ctx = cg.jit_module().make_context();
    ctx.func.signature = sig;
    {
        let mut fbc = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fbc);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        let params = builder.block_params(entry).to_vec();
        let unknown_ptr = params[1];

        // Extract instance pointer from TaggedValue payload (offset 8)
        let instance_raw = builder
            .ins()
            .load(types::I64, MemFlags::new(), unknown_ptr, 8);
        let instance_ptr = builder
            .ins()
            .bitcast(ptr_type, MemFlags::new(), instance_raw);

        // Read field: InstanceGetField(instance, slot) -> i64
        let get_ref = cg
            .jit_module()
            .declare_func_in_func(get_field_func, builder.func);
        let slot_val = builder.ins().iconst(types::I32, field_slot as i64);
        let call = builder.ins().call(get_ref, &[instance_ptr, slot_val]);
        let field_raw = builder.inst_results(call)[0];

        // Box result as unknown: allocate 16-byte TaggedValue on heap
        let tagged_ptr = emit_heap_tagged_value(
            &mut builder,
            cg.jit_module(),
            heap_alloc_func,
            ptr_type,
            runtime_tag,
            field_raw,
        );

        builder.ins().return_(&[tagged_ptr]);
        builder.seal_all_blocks();
        builder.finalize();
    }

    cg.jit_module()
        .define_function(func_id, &mut ctx)
        .map_err(CodegenError::cranelift)?;

    wrap_in_closure(cg, func_id)
}

/// Build a setter closure for a field: `(unknown, unknown) -> void`.
pub(super) fn build_setter(
    cg: &mut Cg,
    _target_type_def_id: TypeDefId,
    field_slot: usize,
) -> CodegenResult<CompiledValue> {
    let ptr_type = cg.ptr_type();
    let lambda_id = cg.next_lambda_id();

    let set_field_func = resolve_runtime(cg, RuntimeKey::InstanceSetField)?;

    // Signature: (closure_ptr, unknown_ptr, unknown_ptr) -> i64 (void)
    let mut sig = cg.jit_module().make_signature();
    sig.params.push(AbiParam::new(ptr_type)); // closure ptr
    sig.params.push(AbiParam::new(ptr_type)); // instance as unknown
    sig.params.push(AbiParam::new(ptr_type)); // value as unknown
    sig.returns.push(AbiParam::new(types::I64)); // void return

    let func_key = cg.funcs().intern_lambda(lambda_id);
    let func_name = cg.funcs().display(func_key);
    let func_id = cg
        .jit_module()
        .declare_function(&func_name, cranelift_module::Linkage::Local, &sig)
        .map_err(CodegenError::cranelift)?;
    cg.funcs().set_func_id(func_key, func_id);

    let mut ctx = cg.jit_module().make_context();
    ctx.func.signature = sig;
    {
        let mut fbc = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fbc);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        let params = builder.block_params(entry).to_vec();
        let unknown_instance = params[1];
        let unknown_value = params[2];

        // Extract instance pointer from TaggedValue payload
        let inst_raw = builder
            .ins()
            .load(types::I64, MemFlags::new(), unknown_instance, 8);
        let instance_ptr = builder.ins().bitcast(ptr_type, MemFlags::new(), inst_raw);

        // Extract field value from TaggedValue payload
        let field_val = builder
            .ins()
            .load(types::I64, MemFlags::new(), unknown_value, 8);

        // Write field: InstanceSetField(instance, slot, value)
        let set_ref = cg
            .jit_module()
            .declare_func_in_func(set_field_func, builder.func);
        let slot_val = builder.ins().iconst(types::I32, field_slot as i64);
        builder
            .ins()
            .call(set_ref, &[instance_ptr, slot_val, field_val]);

        let zero = builder.ins().iconst(types::I64, 0);
        builder.ins().return_(&[zero]);
        builder.seal_all_blocks();
        builder.finalize();
    }

    cg.jit_module()
        .define_function(func_id, &mut ctx)
        .map_err(CodegenError::cranelift)?;

    wrap_in_closure(cg, func_id)
}

/// Build a constructor closure: `([unknown]) -> unknown`.
///
/// Allocates a new instance, sets fields from array elements, returns as unknown.
pub(super) fn build_constructor(
    cg: &mut Cg,
    target_type_def_id: TypeDefId,
    _info: &ReflectionTypeInfo,
) -> CodegenResult<CompiledValue> {
    let ptr_type = cg.ptr_type();
    let lambda_id = cg.next_lambda_id();

    // Gather metadata before building the function
    let meta = cg
        .type_metadata()
        .get(&target_type_def_id)
        .ok_or_else(|| CodegenError::not_found("target type", "type_metadata for constructor"))?;
    let runtime_type_id = meta.type_id;
    let field_count = meta.physical_slot_count;

    // Resolve all runtime FuncIds upfront
    let new_func = resolve_runtime(cg, RuntimeKey::InstanceNew)?;
    let set_field_func = resolve_runtime(cg, RuntimeKey::InstanceSetField)?;
    let array_get_val_func = resolve_runtime(cg, RuntimeKey::ArrayGetValue)?;
    let heap_alloc_func = resolve_runtime(cg, RuntimeKey::HeapAlloc)?;

    // Signature: (closure_ptr, array_ptr) -> unknown_ptr
    let mut sig = cg.jit_module().make_signature();
    sig.params.push(AbiParam::new(ptr_type)); // closure ptr
    sig.params.push(AbiParam::new(ptr_type)); // [unknown] array
    sig.returns.push(AbiParam::new(ptr_type)); // result as unknown ptr

    let func_key = cg.funcs().intern_lambda(lambda_id);
    let func_name = cg.funcs().display(func_key);
    let func_id = cg
        .jit_module()
        .declare_function(&func_name, cranelift_module::Linkage::Local, &sig)
        .map_err(CodegenError::cranelift)?;
    cg.funcs().set_func_id(func_key, func_id);

    let mut ctx = cg.jit_module().make_context();
    ctx.func.signature = sig;
    {
        let mut fbc = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fbc);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        let params = builder.block_params(entry).to_vec();
        let array_ptr = params[1];

        // Allocate instance: InstanceNew(type_id, field_count, RuntimeTypeId::Instance)
        let new_ref = cg.jit_module().declare_func_in_func(new_func, builder.func);
        let type_id_val = builder.ins().iconst(types::I32, runtime_type_id as i64);
        let field_count_val = builder.ins().iconst(types::I32, field_count as i64);
        let rt_type = builder
            .ins()
            .iconst(types::I32, RuntimeTypeId::Instance as i64);
        let new_call = builder
            .ins()
            .call(new_ref, &[type_id_val, field_count_val, rt_type]);
        let instance_ptr = builder.inst_results(new_call)[0];

        // For each field, read from the [unknown] array and store to instance.
        // ArrayGetValue returns the raw i64 stored in the array slot.
        // For [unknown], each element is a heap pointer to a TaggedValue.
        // We load the TaggedValue's payload (offset 8) to get the actual value.
        let get_val_ref = cg
            .jit_module()
            .declare_func_in_func(array_get_val_func, builder.func);
        let set_ref = cg
            .jit_module()
            .declare_func_in_func(set_field_func, builder.func);

        for slot in 0..field_count {
            let idx = builder.ins().iconst(types::I64, slot as i64);
            let elem_call = builder.ins().call(get_val_ref, &[array_ptr, idx]);
            let tagged_ptr_raw = builder.inst_results(elem_call)[0];

            // The array element is a heap pointer to a TaggedValue.
            // Load the payload (offset 8) to get the actual field value.
            let tagged_ptr = builder
                .ins()
                .bitcast(ptr_type, MemFlags::new(), tagged_ptr_raw);
            let field_val = builder
                .ins()
                .load(types::I64, MemFlags::new(), tagged_ptr, 8);

            let slot_val = builder.ins().iconst(types::I32, slot as i64);
            builder
                .ins()
                .call(set_ref, &[instance_ptr, slot_val, field_val]);
        }

        // Box instance as unknown
        let instance_as_i64 = builder
            .ins()
            .bitcast(types::I64, MemFlags::new(), instance_ptr);
        let tagged_ptr = emit_heap_tagged_value(
            &mut builder,
            cg.jit_module(),
            heap_alloc_func,
            ptr_type,
            RuntimeTypeId::Instance as i64,
            instance_as_i64,
        );

        builder.ins().return_(&[tagged_ptr]);
        builder.seal_all_blocks();
        builder.finalize();
    }

    cg.jit_module()
        .define_function(func_id, &mut ctx)
        .map_err(CodegenError::cranelift)?;

    wrap_in_closure(cg, func_id)
}

/// Emit code to allocate a 16-byte TaggedValue on the heap and store tag+value.
fn emit_heap_tagged_value(
    builder: &mut FunctionBuilder,
    module: &mut cranelift_jit::JITModule,
    heap_alloc_func: FuncId,
    ptr_type: Type,
    tag: i64,
    value: Value,
) -> Value {
    let alloc_ref = module.declare_func_in_func(heap_alloc_func, builder.func);
    let size_val = builder.ins().iconst(ptr_type, 16);
    let alloc_call = builder.ins().call(alloc_ref, &[size_val]);
    let tagged_ptr = builder.inst_results(alloc_call)[0];

    let tag_val = builder.ins().iconst(types::I64, tag);
    builder.ins().store(MemFlags::new(), tag_val, tagged_ptr, 0);
    builder.ins().store(MemFlags::new(), value, tagged_ptr, 8);

    tagged_ptr
}

/// Wrap a compiled function in a zero-capture closure.
fn wrap_in_closure(cg: &mut Cg, func_id: FuncId) -> CodegenResult<CompiledValue> {
    let func_ref = cg
        .codegen_ctx
        .jit_module()
        .declare_func_in_func(func_id, cg.builder.func);
    let ptr_type = cg.ptr_type();
    let func_addr = cg.builder.ins().func_addr(ptr_type, func_ref);

    let alloc_ref = cg.runtime_func_ref(RuntimeKey::ClosureAlloc)?;
    let zero_captures = cg.iconst_cached(types::I64, 0);
    let alloc_call = cg
        .builder
        .ins()
        .call(alloc_ref, &[func_addr, zero_captures]);
    let closure_ptr = cg.builder.inst_results(alloc_call)[0];

    // Use a generic function type — the closure type will be coerced as needed.
    let cv = CompiledValue::new(closure_ptr, ptr_type, TypeId::UNKNOWN);
    Ok(cg.mark_rc_owned(cv))
}
