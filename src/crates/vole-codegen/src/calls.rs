// src/codegen/calls.rs
//
// Call-related codegen - impl Cg methods and standalone helpers.

use cranelift::prelude::*;
use cranelift_jit::JITModule;
use cranelift_module::{DataDescription, FuncId, Linkage, Module};
use smallvec::{SmallVec, smallvec};

use crate::errors::{CodegenError, CodegenResult};

/// SmallVec for call arguments - most calls have <= 8 args
type ArgVec = SmallVec<[Value; 8]>;
use vole_frontend::{
    CallExpr, Decl, Expr, ExprKind, LambdaExpr, NodeId, Program, Stmt, StringPart, Symbol,
};
use vole_identity::{ModuleId, NameId};
use vole_runtime::native_registry::{NativeFunction, NativeType};
use vole_sema::type_arena::TypeId;

use super::context::Cg;
use super::types::{CompiledValue, native_type_to_cranelift, type_id_to_cranelift};
use super::{FunctionKey, FunctionRegistry, RuntimeFn};

/// Compile a string literal as a static RcString baked into the JIT data section.
/// Returns the raw Cranelift Value (pointer to the static RcString) - caller should
/// wrap with string_value() for CompiledValue.
///
/// The RcString is built at compile time with RC_PINNED refcount so rc_inc/rc_dec
/// are no-ops, making string literals zero-allocation at runtime.
pub(crate) fn compile_string_literal(
    builder: &mut FunctionBuilder,
    s: &str,
    pointer_type: Type,
    module: &mut JITModule,
    func_registry: &mut FunctionRegistry,
) -> CodegenResult<Value> {
    use vole_runtime::{RC_PINNED, TYPE_STRING, fnv1a_hash};

    // Build complete RcString struct as bytes:
    //   RcHeader { ref_count: u32, type_id: u32, drop_fn: Option<fn> }  = 16 bytes
    //   len: usize                                                       =  8 bytes
    //   hash: u64                                                        =  8 bytes
    //   data: [u8; s.len()]                                              =  N bytes
    let mut data = Vec::with_capacity(32 + s.len());
    // RcHeader
    data.extend_from_slice(&RC_PINNED.to_ne_bytes()); // ref_count = pinned (no-op inc/dec)
    data.extend_from_slice(&TYPE_STRING.to_ne_bytes()); // type_id
    data.extend_from_slice(&0u64.to_ne_bytes()); // drop_fn = null (no cleanup needed)
    // RcString fields
    data.extend_from_slice(&s.len().to_ne_bytes()); // len
    data.extend_from_slice(&fnv1a_hash(s.as_bytes()).to_ne_bytes()); // hash
    data.extend_from_slice(s.as_bytes()); // inline string data

    // Embed in JIT data section
    let data_name = func_registry.next_string_data_name();
    let data_id = module
        .declare_data(&data_name, Linkage::Local, false, false)
        .map_err(|e| CodegenError::internal_with_context("cranelift error", e.to_string()))?;

    let mut data_desc = DataDescription::new();
    data_desc.define(data.into_boxed_slice());
    data_desc.set_align(8);
    module
        .define_data(data_id, &data_desc)
        .map_err(|e| CodegenError::internal_with_context("cranelift error", e.to_string()))?;

    // The data section pointer IS the RcString pointer
    let data_gv = module.declare_data_in_func(data_id, builder.func);
    Ok(builder.ins().global_value(pointer_type, data_gv))
}
impl Cg<'_, '_, '_> {
    /// Compile a string literal
    pub fn string_literal(&mut self, s: &str) -> CodegenResult<CompiledValue> {
        let value = compile_string_literal(
            self.builder,
            s,
            self.ptr_type(),
            self.codegen_ctx.module,
            self.codegen_ctx.func_registry,
        )?;
        Ok(self.string_temp(value))
    }

    /// Compile an interpolated string using StringBuilder for efficient single-allocation
    pub fn interpolated_string(&mut self, parts: &[StringPart]) -> CodegenResult<CompiledValue> {
        if parts.is_empty() {
            return self.string_literal("");
        }

        // Collect all string values, tracking which need cleanup after the build.
        // - Literals: static (pinned RC), rc_dec is a no-op
        // - Expr already string: borrowed or owned from expression
        // - Expr converted via to_string: owned, needs rc_dec
        let mut string_values: Vec<Value> = Vec::new();
        let mut owned_flags: Vec<bool> = Vec::new();
        for part in parts {
            let (str_val, is_owned) = match part {
                StringPart::Literal(s) => (self.string_literal(s)?.value, true),
                StringPart::Expr(expr) => {
                    let compiled = self.expr(expr)?;
                    if compiled.type_id == TypeId::STRING {
                        (compiled.value, compiled.is_owned())
                    } else {
                        (self.value_to_string(compiled)?, true)
                    }
                }
            };
            string_values.push(str_val);
            owned_flags.push(is_owned);
        }

        // Single part — return directly, no builder needed
        if string_values.len() == 1 {
            return Ok(self.string_temp(string_values[0]));
        }

        // Multi-part: use StringBuilder — one allocation instead of N concats
        let sb = self.call_runtime(RuntimeFn::SbNew, &[])?;

        for &sv in &string_values {
            self.call_runtime_void(RuntimeFn::SbPushString, &[sb, sv])?;
        }

        let result = self.call_runtime(RuntimeFn::SbFinish, &[sb])?;

        // Free all owned input parts — builder has copied the bytes
        for (val, is_owned) in string_values.iter().zip(owned_flags.iter()) {
            if *is_owned {
                self.emit_rc_dec(*val)?;
            }
        }

        Ok(self.string_temp(result))
    }

    /// Convert a value to a string
    fn value_to_string(&mut self, val: CompiledValue) -> CodegenResult<Value> {
        if val.type_id == TypeId::STRING {
            return Ok(val.value);
        }

        // Handle arrays
        if self.arena().is_array(val.type_id) {
            return self.call_runtime(RuntimeFn::ArrayI64ToString, &[val.value]);
        }

        // Handle nil type directly
        if val.type_id.is_nil() {
            return self.call_runtime(RuntimeFn::NilToString, &[]);
        }

        // Handle optionals (unions with nil variant)
        if let Some(nil_idx) = self.find_nil_variant(val.type_id) {
            let arena = self.arena();
            if let Some(variants) = arena.unwrap_union(val.type_id) {
                let variants_vec: Vec<TypeId> = variants.to_vec();
                return self.optional_to_string_by_id(val.value, &variants_vec, nil_idx);
            }
        }

        let (runtime, call_val) = if val.ty == types::F64 {
            (RuntimeFn::F64ToString, val.value)
        } else if val.ty == types::F32 {
            (RuntimeFn::F32ToString, val.value)
        } else if val.ty == types::I128 {
            (RuntimeFn::I128ToString, val.value)
        } else if val.ty == types::I8 {
            (RuntimeFn::BoolToString, val.value)
        } else {
            let extended = if val.ty.is_int() && val.ty != types::I64 {
                self.builder.ins().sextend(types::I64, val.value)
            } else {
                val.value
            };
            (RuntimeFn::I64ToString, extended)
        };

        self.call_runtime(runtime, &[call_val])
    }

    /// Convert an optional (union with nil) to string using TypeId variants
    fn optional_to_string_by_id(
        &mut self,
        ptr: Value,
        variants: &[TypeId],
        nil_idx: usize,
    ) -> CodegenResult<Value> {
        // Check if the tag equals nil
        let is_nil = self.tag_eq(ptr, nil_idx as i64);

        // Create blocks for branching
        let nil_block = self.builder.create_block();
        let some_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        // Add block param for the result string
        self.builder
            .append_block_param(merge_block, self.ptr_type());

        self.builder
            .ins()
            .brif(is_nil, nil_block, &[], some_block, &[]);

        // Nil case: return "nil"
        self.builder.switch_to_block(nil_block);
        let nil_str = self.call_runtime(RuntimeFn::NilToString, &[])?;
        self.builder.ins().jump(merge_block, &[nil_str.into()]);

        // Some case: extract inner value and convert to string
        self.builder.switch_to_block(some_block);
        // Find the non-nil variant using arena
        let arena = self.arena();
        let inner_type_id = variants
            .iter()
            .find(|&&v| !arena.is_nil(v))
            .copied()
            .unwrap_or(TypeId::NIL);
        let inner_cr_type = type_id_to_cranelift(inner_type_id, arena, self.ptr_type());

        // Only load payload if inner type has data (non-zero size).
        // Sentinel-only unions have no payload bytes allocated at offset 8.
        let inner_size = self.type_size(inner_type_id);
        let inner_val = if inner_size > 0 {
            self.builder
                .ins()
                .load(inner_cr_type, MemFlags::new(), ptr, 8)
        } else {
            self.builder.ins().iconst(inner_cr_type, 0)
        };

        let inner_compiled = CompiledValue::new(inner_val, inner_cr_type, inner_type_id);
        let some_str = self.value_to_string(inner_compiled)?;
        self.builder.ins().jump(merge_block, &[some_str.into()]);

        // Merge and return result
        self.builder.switch_to_block(merge_block);
        Ok(self.builder.block_params(merge_block)[0])
    }

    /// Compile a function call
    #[tracing::instrument(skip(self, call))]
    pub fn call(
        &mut self,
        call: &CallExpr,
        call_line: u32,
        call_expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let callee_sym = match &call.callee.kind {
            ExprKind::Identifier(sym) => *sym,
            _ => return self.indirect_call(call),
        };

        let callee_name = self.interner().resolve(callee_sym);

        // Handle builtins
        // assert uses inline codegen (brif) to avoid function-call overhead
        // and a pre-existing class-field-access register clobber bug (v-a1f9).
        match callee_name {
            "print_char" => return self.call_print_char(call),
            "assert" => return self.call_assert(call, call_line),
            _ => {}
        }

        // Check if it's a module binding (from destructuring import)
        if let Some(&(module_id, export_name, export_type_id)) =
            self.module_bindings.get(&callee_sym)
        {
            // Check if this is a generic external function that needs monomorphization
            if let Some(result) =
                self.try_call_generic_external_intrinsic_from_monomorph(call_expr_id, call)?
            {
                return Ok(result);
            }

            return self.call_module_binding(
                module_id,
                export_name,
                export_type_id,
                call,
                call_expr_id,
            );
        }

        // Check if it's a closure variable
        if let Some((var, type_id)) = self.vars.get(&callee_sym)
            && self.arena().is_function(*type_id)
        {
            return self.call_closure(*var, *type_id, call, call_expr_id);
        }

        // Check if it's a captured closure (e.g., recursive lambda or captured function)
        if self.has_captures()
            && let Some(binding) = self.get_capture(&callee_sym).copied()
            && self.arena().is_function(binding.vole_type)
        {
            let captured = self.load_capture(&binding)?;
            return self.call_closure_value(captured.value, binding.vole_type, call, call_expr_id);
        }

        // Check if it's a functional interface variable
        if let Some((var, type_id)) = self.vars.get(&callee_sym) {
            let value = self.builder.use_var(*var);
            let obj = CompiledValue::new(value, self.cranelift_type(*type_id), *type_id);
            if let Some(result) = self.try_call_functional_interface(&obj, &call.args)? {
                return Ok(result);
            }
        }

        // Check if it's a global lambda or global functional interface
        if let Some(init_expr) = self.global_init(callee_sym).cloned() {
            // Compile the global's initializer to get its value
            let lambda_val = self.expr(&init_expr)?;

            // Get declared type from GlobalDef (uses sema-resolved type, not TypeExpr)
            // Scope the name_table borrow to avoid conflicts with later mutable borrows
            let global_type_id = {
                let name_table = self.name_table();
                let module_id = self.current_module().unwrap_or(self.env.analyzed.module_id);
                name_table
                    .name_id(module_id, &[callee_sym], self.interner())
                    .and_then(|name_id| self.query().global(name_id))
                    .map(|global_def| global_def.type_id)
            };

            if let Some(declared_type_id) = global_type_id {
                // If declared as functional interface, call via vtable dispatch
                let iface_info = self.interface_type_def_id(declared_type_id);
                if let Some(type_def_id) = iface_info
                    && let Some(method_id) = self.query().is_functional_interface(type_def_id)
                {
                    let method = self.query().get_method(method_id);
                    let func_type_id = method.signature_id;
                    let method_name_id = method.name_id;
                    // Box the lambda value to create the interface representation
                    let boxed = self.box_interface_value(lambda_val, declared_type_id)?;
                    let result = self.interface_dispatch_call_args_by_type_def_id(
                        &boxed,
                        &call.args,
                        type_def_id,
                        method_name_id,
                        func_type_id,
                    )?;
                    // Dec the boxed interface instance (which transitively frees
                    // the closure via instance_drop).
                    self.emit_rc_dec_for_type(boxed.value, boxed.type_id)?;
                    return Ok(result);
                }
            }

            // If it's a function type, call as closure
            // Note: Global lambdas don't support default params lookup (use call.callee.id as placeholder)
            if self.arena().is_function(lambda_val.type_id) {
                let result = self.call_closure_value(
                    lambda_val.value,
                    lambda_val.type_id,
                    call,
                    call.callee.id,
                )?;
                // The global init re-compiles the lambda each call, creating a
                // fresh closure allocation. Dec it now that the call has finished.
                let mut tmp = lambda_val;
                self.consume_rc_value(&mut tmp)?;
                return Ok(result);
            }

            // If it's an interface type (functional interface), call via vtable
            if let Some(result) = self.try_call_functional_interface(&lambda_val, &call.args)? {
                // Dec the interface instance created by the global init.
                self.emit_rc_dec_for_type(lambda_val.value, lambda_val.type_id)?;
                return Ok(result);
            }
        }

        // Check if this is a call to a generic function (via monomorphization)
        // IMPORTANT: Only check monomorph_for in main program context, not module context.
        // Module code doesn't have generic function calls that need monomorphization,
        // and NodeIds can collide between module code and main program code.
        if self.current_module.is_none()
            && let Some(result) =
                self.try_call_monomorphized_function(call_expr_id, call, callee_sym, callee_name)?
        {
            return Ok(result);
        }

        // Regular function call - handle module context
        // 1. Try direct function lookup
        // 2. If in module context, try mangled name
        // 3. If in module context, try FFI call
        let program_module = self.current_module().unwrap_or(self.env.analyzed.module_id);
        let direct_name_id = {
            let names = self.name_table();
            names.name_id(program_module, &[callee_sym], self.interner())
        };
        if let Some(name_id) = direct_name_id {
            let func_key = self.funcs().intern_name_id(name_id);
            if let Some(func_id) = self.funcs_ref().func_id(func_key) {
                return self.call_func_id(func_key, func_id, call, callee_sym);
            }
        }

        // Check module context for mangled name or FFI
        if let Some(module_id) = self.current_module() {
            let module_path = self.name_table().module_path(module_id).to_string();
            let name_id = crate::types::module_name_id(self.analyzed(), module_id, callee_name);
            if let Some(name_id) = name_id {
                let func_key = self.funcs().intern_name_id(name_id);
                if let Some(func_id) = self.funcs().func_id(func_key) {
                    // Found module function with qualified name
                    return self.call_func_id(func_key, func_id, call, callee_sym);
                }
            }

            // Try FFI call for external module functions
            if let Some(native_func) = self.native_funcs().lookup(&module_path, callee_name) {
                // Get expected Cranelift types from native function signature
                let expected_types: Vec<Type> = native_func
                    .signature
                    .params
                    .iter()
                    .map(|nt| native_type_to_cranelift(nt, self.ptr_type()))
                    .collect();
                // Compile args with defaults for omitted parameters
                let args = self.compile_external_call_args(callee_sym, call, &expected_types)?;
                let call_inst = self.call_native_indirect(native_func, &args);
                if native_func.signature.return_type == NativeType::Nil {
                    return Ok(self.void_value());
                }
                // Sema records return types for all module external calls.
                let type_id = self
                    .get_expr_type(&call_expr_id)
                    .expect("INTERNAL: external call: missing sema return type");
                let type_id = self.maybe_convert_iterator_return_type(type_id);
                return Ok(self.native_call_result(call_inst, native_func, type_id));
            }

            // Fall through to try prelude external functions
        }

        // Try prelude external functions (works in module context too)
        // Look up the external info (module path and native name) from implement_registry
        let ext_info = self
            .analyzed()
            .implement_registry()
            .get_external_func(callee_name)
            .copied();
        if let Some(ref info) = ext_info {
            // Check if this is a compiler intrinsic (e.g., panic)
            let module_path_str = self
                .name_table()
                .last_segment_str(info.module_path)
                .unwrap_or_default();
            if module_path_str == Cg::COMPILER_INTRINSIC_MODULE {
                // Compile args and dispatch through intrinsic handler
                let mut args = Vec::new();
                for arg in &call.args {
                    let compiled = self.expr(arg)?;
                    args.push(compiled.value);
                }
                let native_name_str = self
                    .name_table()
                    .last_segment_str(info.native_name)
                    .unwrap_or_default();
                let return_type_id = self.get_expr_type(&call_expr_id).unwrap_or(TypeId::VOID);
                return self.call_compiler_intrinsic_with_line(
                    &native_name_str,
                    &args,
                    return_type_id,
                    call_line,
                );
            }
        }
        let native_func = ext_info.as_ref().and_then(|info| {
            let name_table = self.name_table();
            let module_path = name_table.last_segment_str(info.module_path)?;
            let native_name = name_table.last_segment_str(info.native_name)?;
            self.native_funcs().lookup(&module_path, &native_name)
        });
        if let Some(native_func) = native_func {
            // Get expected Cranelift types from native function signature
            let expected_types: Vec<Type> = native_func
                .signature
                .params
                .iter()
                .map(|nt| native_type_to_cranelift(nt, self.ptr_type()))
                .collect();
            // Compile args with defaults for omitted parameters
            let args = self.compile_external_call_args(callee_sym, call, &expected_types)?;
            let call_inst = self.call_native_indirect(native_func, &args);
            if native_func.signature.return_type == NativeType::Nil {
                return Ok(self.void_value());
            }
            // Sema records return types for all prelude external calls.
            let type_id = self
                .get_expr_type(&call_expr_id)
                .expect("INTERNAL: prelude call: missing sema return type");
            let type_id = self.maybe_convert_iterator_return_type(type_id);
            return Ok(self.native_call_result(call_inst, native_func, type_id));
        }

        // Try prelude Vole functions (e.g., assert from builtins.vole)
        let prelude_paths: Vec<String> = self
            .query()
            .module_paths()
            .filter(|p| p.starts_with("std:prelude/"))
            .map(String::from)
            .collect();
        for module_path in &prelude_paths {
            let module_id = self.query().module_id_or_main(module_path);
            let name_id = crate::types::module_name_id(self.analyzed(), module_id, callee_name);
            if let Some(name_id) = name_id {
                let func_key = self.funcs().intern_name_id(name_id);
                if let Some(func_id) = self.funcs_ref().func_id(func_key) {
                    return self.call_func_id_by_name_id(func_key, func_id, call, name_id);
                }
            }
        }

        Err(CodegenError::not_found("function", callee_name))
    }

    /// Call a function via destructured module binding.
    /// Looks up the function by module_id and export_name, then calls via FFI or compiled function.
    fn call_module_binding(
        &mut self,
        module_id: ModuleId,
        export_name: Symbol,
        export_type_id: TypeId,
        call: &CallExpr,
        call_expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let module_path = self.name_table().module_path(module_id).to_string();
        let export_name_str = self.interner().resolve(export_name);

        // Try to find the function by qualified name in the function registry
        let name_id = crate::types::module_name_id(self.analyzed(), module_id, export_name_str);
        if let Some(name_id) = name_id {
            let func_key = self.funcs().intern_name_id(name_id);
            if let Some(func_id) = self.funcs_ref().func_id(func_key) {
                // Found compiled module function
                return self.call_func_id(func_key, func_id, call, export_name);
            }
        }

        // Try FFI call for external module functions
        if let Some(native_func) = self.native_funcs().lookup(&module_path, export_name_str) {
            // Get expected Cranelift types from native function signature
            let expected_types: Vec<Type> = native_func
                .signature
                .params
                .iter()
                .map(|nt| native_type_to_cranelift(nt, self.ptr_type()))
                .collect();
            // Compile args with defaults for omitted parameters
            let args = self.compile_external_call_args(export_name, call, &expected_types)?;
            let call_inst = self.call_native_indirect(native_func, &args);
            if native_func.signature.return_type == NativeType::Nil {
                return Ok(self.void_value());
            }
            let type_id = self.get_expr_type(&call_expr_id).unwrap_or(export_type_id);
            let type_id = self.maybe_convert_iterator_return_type(type_id);
            return Ok(self.native_call_result(call_inst, native_func, type_id));
        }

        Err(CodegenError::not_found(
            "module function",
            format!("{}.{}", module_path, export_name_str),
        ))
    }

    /// Helper to call a function by its FuncId
    fn call_func_id(
        &mut self,
        func_key: FunctionKey,
        func_id: FuncId,
        call: &CallExpr,
        callee_sym: Symbol,
    ) -> CodegenResult<CompiledValue> {
        let func_ref = self
            .codegen_ctx
            .jit_module()
            .declare_func_in_func(func_id, self.builder.func);

        // Get return type early to check for sret convention
        let return_type_id = self
            .codegen_ctx
            .funcs()
            .return_type(func_key)
            .unwrap_or_else(|| self.env.analyzed.type_arena().void());

        let is_sret = self.is_sret_struct_return(return_type_id);

        // Get expected parameter types from the function's signature
        let sig_ref = self.builder.func.dfg.ext_funcs[func_ref].signature;
        let sig = &self.builder.func.dfg.signatures[sig_ref];
        let expected_types: Vec<Type> = sig.params.iter().map(|p| p.value_type).collect();

        // For sret convention, allocate return buffer and prepend as first arg
        let ptr_type = self.ptr_type();
        let mut args = Vec::new();
        let sret_slot = if is_sret {
            let flat_count = self
                .struct_flat_slot_count(return_type_id)
                .expect("INTERNAL: sret call: missing flat slot count");
            let total_size = (flat_count as u32) * 8;
            let slot = self.alloc_stack(total_size);
            let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
            args.push(ptr);
            Some(slot)
        } else {
            None
        };

        // Determine the offset into expected_types for user args (skip sret param)
        let user_param_offset = if is_sret { 1 } else { 0 };

        // Get parameter TypeIds from the function definition for union coercion
        let param_type_ids: Vec<TypeId> = {
            let module_id = self.current_module().unwrap_or(self.env.analyzed.module_id);
            let name_id = self.query().try_function_name_id(module_id, callee_sym);
            let func_id_sema = name_id.and_then(|id| self.registry().function_by_name(id));
            if let Some(fid) = func_id_sema {
                let func_def = self.registry().get_function(fid);
                func_def.signature.params_id.iter().copied().collect()
            } else {
                Vec::new()
            }
        };

        // Compile arguments with type narrowing, tracking RC temps for cleanup
        let mut rc_temp_args = Vec::new();
        for (i, arg) in call.args.iter().enumerate() {
            let compiled = self.expr(arg)?;
            if compiled.is_owned() {
                rc_temp_args.push(compiled);
            }

            // Coerce argument to parameter type if needed (e.g., string -> string?)
            let compiled = if let Some(&param_type_id) = param_type_ids.get(i) {
                self.coerce_to_type(compiled, param_type_id)?
            } else {
                compiled
            };

            let expected_ty = expected_types.get(i + user_param_offset).copied();

            // Narrow/extend integer types if needed
            let arg_value = if let Some(expected) = expected_ty {
                if compiled.ty.is_int() && expected.is_int() && expected.bits() < compiled.ty.bits()
                {
                    self.builder.ins().ireduce(expected, compiled.value)
                } else if compiled.ty.is_int()
                    && expected.is_int()
                    && expected.bits() > compiled.ty.bits()
                {
                    self.builder.ins().sextend(expected, compiled.value)
                } else {
                    compiled.value
                }
            } else {
                compiled.value
            };
            args.push(arg_value);
        }

        // If there are fewer provided args than expected, compile default expressions
        let total_user_args = args.len() - user_param_offset;
        let expected_user_params = expected_types.len() - user_param_offset;
        if total_user_args < expected_user_params {
            let provided_args = total_user_args;
            let remaining_start = user_param_offset + provided_args;
            let remaining_expected_types = expected_types[remaining_start..].to_vec();
            let (default_args, rc_owned) =
                self.compile_default_args(callee_sym, provided_args, &remaining_expected_types)?;
            args.extend(default_args);
            rc_temp_args.extend(rc_owned);
        }

        let call_inst = self.builder.ins().call(func_ref, &args);
        self.field_cache.clear(); // Callee may mutate instance fields

        // If the return type is a union, copy the data from the callee's stack to our own
        // BEFORE consuming RC args. The rc_dec calls in consume_rc_args can clobber the
        // callee's stack frame, invalidating the returned pointer.
        let union_copy = if sret_slot.is_none() && self.arena().is_union(return_type_id) {
            let results = self.builder.inst_results(call_inst);
            let src_ptr = results[0];
            let union_size = self.type_size(return_type_id);
            let slot = self.alloc_stack(union_size);

            let tag = self
                .builder
                .ins()
                .load(types::I8, MemFlags::new(), src_ptr, 0);
            self.builder.ins().stack_store(tag, slot, 0);

            if union_size > 8 {
                let payload = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), src_ptr, 8);
                self.builder.ins().stack_store(payload, slot, 8);
            }

            let ptr_type = self.ptr_type();
            let new_ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
            Some(self.compiled(new_ptr, return_type_id))
        } else {
            None
        };

        // Dec RC temp args after the call has consumed them
        self.consume_rc_args(&mut rc_temp_args)?;

        // If we already copied the union data, return that
        if let Some(result) = union_copy {
            return Ok(result);
        }

        // For sret, the returned value is the sret pointer we passed in
        if sret_slot.is_some() {
            let results = self.builder.inst_results(call_inst);
            return Ok(CompiledValue::new(results[0], ptr_type, return_type_id));
        }

        Ok(self.call_result(call_inst, return_type_id))
    }

    /// Call a function by FuncId using NameId for default parameter lookup.
    /// Used for prelude Vole functions where the callee's NameId is already known.
    fn call_func_id_by_name_id(
        &mut self,
        func_key: FunctionKey,
        func_id: FuncId,
        call: &CallExpr,
        name_id: NameId,
    ) -> CodegenResult<CompiledValue> {
        let func_ref = self
            .codegen_ctx
            .jit_module()
            .declare_func_in_func(func_id, self.builder.func);

        // Get return type early to check for sret convention
        let return_type_id = self
            .codegen_ctx
            .funcs()
            .return_type(func_key)
            .unwrap_or_else(|| self.env.analyzed.type_arena().void());

        let is_sret = self.is_sret_struct_return(return_type_id);

        // Get expected parameter types from the function's signature
        let sig_ref = self.builder.func.dfg.ext_funcs[func_ref].signature;
        let sig = &self.builder.func.dfg.signatures[sig_ref];
        let expected_types: Vec<Type> = sig.params.iter().map(|p| p.value_type).collect();

        // For sret convention, allocate return buffer and prepend as first arg
        let ptr_type = self.ptr_type();
        let mut args = Vec::new();
        let sret_slot = if is_sret {
            let flat_count = self
                .struct_flat_slot_count(return_type_id)
                .expect("INTERNAL: sret call: missing flat slot count");
            let total_size = (flat_count as u32) * 8;
            let slot = self.alloc_stack(total_size);
            let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
            args.push(ptr);
            Some(slot)
        } else {
            None
        };

        let user_param_offset = if is_sret { 1 } else { 0 };

        // Get parameter TypeIds from the function definition for union coercion
        let param_type_ids: Vec<TypeId> = {
            let func_id_sema = self.registry().function_by_name(name_id);
            if let Some(fid) = func_id_sema {
                let func_def = self.registry().get_function(fid);
                func_def.signature.params_id.iter().copied().collect()
            } else {
                Vec::new()
            }
        };

        // Compile arguments with type narrowing, tracking RC temps for cleanup
        let mut rc_temp_args = Vec::new();
        for (i, arg) in call.args.iter().enumerate() {
            let compiled = self.expr(arg)?;
            if compiled.is_owned() {
                rc_temp_args.push(compiled);
            }

            // Coerce argument to parameter type if needed (e.g., string -> string?)
            let compiled = if let Some(&param_type_id) = param_type_ids.get(i) {
                self.coerce_to_type(compiled, param_type_id)?
            } else {
                compiled
            };

            let expected_ty = expected_types.get(i + user_param_offset).copied();
            let arg_value = if let Some(expected) = expected_ty {
                if compiled.ty.is_int() && expected.is_int() && expected.bits() < compiled.ty.bits()
                {
                    self.builder.ins().ireduce(expected, compiled.value)
                } else if compiled.ty.is_int()
                    && expected.is_int()
                    && expected.bits() > compiled.ty.bits()
                {
                    self.builder.ins().sextend(expected, compiled.value)
                } else {
                    compiled.value
                }
            } else {
                compiled.value
            };
            args.push(arg_value);
        }

        // If there are fewer provided args than expected, compile default expressions
        let total_user_args = args.len() - user_param_offset;
        let expected_user_params = expected_types.len() - user_param_offset;
        if total_user_args < expected_user_params {
            let provided_args = total_user_args;
            let remaining_start = user_param_offset + provided_args;
            let remaining_expected_types = expected_types[remaining_start..].to_vec();
            let (default_args, rc_owned) = self.compile_default_args_by_name_id(
                name_id,
                provided_args,
                &remaining_expected_types,
            )?;
            args.extend(default_args);
            rc_temp_args.extend(rc_owned);
        }

        let call_inst = self.builder.ins().call(func_ref, &args);
        self.field_cache.clear(); // Callee may mutate instance fields

        // If the return type is a union, copy the data from the callee's stack to our own
        // BEFORE consuming RC args. The rc_dec calls in consume_rc_args can clobber the
        // callee's stack frame, invalidating the returned pointer.
        let union_copy = if sret_slot.is_none() && self.arena().is_union(return_type_id) {
            let results = self.builder.inst_results(call_inst);
            let src_ptr = results[0];
            let union_size = self.type_size(return_type_id);
            let slot = self.alloc_stack(union_size);

            let tag = self
                .builder
                .ins()
                .load(types::I8, MemFlags::new(), src_ptr, 0);
            self.builder.ins().stack_store(tag, slot, 0);

            if union_size > 8 {
                let payload = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), src_ptr, 8);
                self.builder.ins().stack_store(payload, slot, 8);
            }

            let ptr_type = self.ptr_type();
            let new_ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
            Some(self.compiled(new_ptr, return_type_id))
        } else {
            None
        };

        // Dec RC temp args after the call has consumed them
        self.consume_rc_args(&mut rc_temp_args)?;

        if let Some(result) = union_copy {
            return Ok(result);
        }

        if sret_slot.is_some() {
            let results = self.builder.inst_results(call_inst);
            return Ok(CompiledValue::new(results[0], ptr_type, return_type_id));
        }

        Ok(self.call_result(call_inst, return_type_id))
    }

    /// Compile default expressions using a NameId directly (for cross-module calls).
    fn compile_default_args_by_name_id(
        &mut self,
        name_id: NameId,
        start_index: usize,
        _expected_types: &[Type],
    ) -> CodegenResult<(Vec<Value>, Vec<CompiledValue>)> {
        let func_id = self.registry().function_by_name(name_id);
        let Some(func_id) = func_id else {
            return Ok((Vec::new(), Vec::new()));
        };

        let (default_ptrs, param_type_ids): (Vec<Option<*const Expr>>, Vec<TypeId>) = {
            let func_def = self.registry().get_function(func_id);
            let ptrs = func_def
                .param_defaults
                .iter()
                .map(|opt| opt.as_ref().map(|e| e.as_ref() as *const Expr))
                .collect();
            let type_ids = func_def.signature.params_id.iter().copied().collect();
            (ptrs, type_ids)
        };

        self.compile_defaults_from_ptrs(
            &default_ptrs,
            start_index,
            &param_type_ids[start_index..],
            false,
        )
    }

    /// Compile default expressions for omitted function parameters.
    /// Returns compiled values for parameters starting at `start_index`.
    ///
    /// Uses the unified `compile_defaults_from_ptrs` helper.
    fn compile_default_args(
        &mut self,
        callee_sym: Symbol,
        start_index: usize,
        _expected_types: &[Type], // Kept for API compatibility, but we use TypeIds from FunctionDef
    ) -> CodegenResult<(Vec<Value>, Vec<CompiledValue>)> {
        let module_id = self.current_module().unwrap_or(self.env.analyzed.module_id);

        // Get the function ID
        let func_id = {
            let name_id = self.query().try_function_name_id(module_id, callee_sym);
            name_id.and_then(|id| self.registry().function_by_name(id))
        };

        let Some(func_id) = func_id else {
            return Ok((Vec::new(), Vec::new()));
        };

        // Get raw pointers to default expressions and param TypeIds from FunctionDef.
        let (default_ptrs, param_type_ids): (Vec<Option<*const Expr>>, Vec<TypeId>) = {
            let func_def = self.registry().get_function(func_id);
            let ptrs = func_def
                .param_defaults
                .iter()
                .map(|opt| opt.as_ref().map(|e| e.as_ref() as *const Expr))
                .collect();
            let type_ids = func_def.signature.params_id.iter().copied().collect();
            (ptrs, type_ids)
        };

        // Use the unified helper
        self.compile_defaults_from_ptrs(
            &default_ptrs,
            start_index,
            &param_type_ids[start_index..],
            false, // Not a generic class call
        )
    }

    /// Compile call arguments for an external function, including defaults for omitted parameters.
    /// Looks up the function by Symbol in EntityRegistry to get default expressions.
    /// `expected_types` are the Cranelift types from the native function signature.
    fn compile_external_call_args(
        &mut self,
        callee_sym: Symbol,
        call: &CallExpr,
        expected_types: &[Type],
    ) -> CodegenResult<Vec<Value>> {
        // Compile provided arguments
        let mut args = self.compile_call_args(&call.args)?;

        let expected_param_count = expected_types.len();

        // If we have all expected arguments, we're done
        if args.len() >= expected_param_count {
            return Ok(args);
        }

        // Otherwise, we need to compile defaults for the missing parameters
        let module_id = self.current_module().unwrap_or(self.env.analyzed.module_id);

        // Get the function ID from EntityRegistry
        let func_id = {
            let name_id = self.query().try_function_name_id(module_id, callee_sym);
            name_id.and_then(|id| self.registry().function_by_name(id))
        };

        let Some(func_id) = func_id else {
            return Ok(args);
        };

        // Get raw pointers to default expressions.
        // These point to data in EntityRegistry which lives for the duration of AnalyzedProgram.
        // We use raw pointers to work around the borrow checker since self.expr() needs &mut self.
        let default_ptrs: Vec<Option<*const Expr>> = {
            let func_def = self.registry().get_function(func_id);
            func_def
                .param_defaults
                .iter()
                .map(|opt| opt.as_ref().map(|e| e.as_ref() as *const Expr))
                .collect()
        };

        // Compile defaults for missing parameters
        let start_index = args.len();
        for (param_idx, &expected_ty) in expected_types
            .iter()
            .enumerate()
            .skip(start_index)
            .take(expected_param_count - start_index)
        {
            if let Some(Some(default_ptr)) = default_ptrs.get(param_idx) {
                // SAFETY: The pointer points to data in EntityRegistry which is owned by
                // AnalyzedProgram. AnalyzedProgram outlives this entire compilation session.
                // The data is not moved or modified, so the pointer remains valid.
                let default_expr: &Expr = unsafe { &**default_ptr };
                let compiled = self.expr(default_expr)?;

                // Narrow/extend integer types if needed
                let arg_value = if compiled.ty.is_int()
                    && expected_ty.is_int()
                    && expected_ty.bits() < compiled.ty.bits()
                {
                    self.builder.ins().ireduce(expected_ty, compiled.value)
                } else if compiled.ty.is_int()
                    && expected_ty.is_int()
                    && expected_ty.bits() > compiled.ty.bits()
                {
                    self.builder.ins().sextend(expected_ty, compiled.value)
                } else {
                    compiled.value
                };
                args.push(arg_value);
            }
        }

        Ok(args)
    }

    /// Compile an indirect call (closure or function value)
    fn indirect_call(&mut self, call: &CallExpr) -> CodegenResult<CompiledValue> {
        let callee = self.expr(&call.callee)?;

        if self.arena().is_function(callee.type_id) {
            // Note: Indirect calls don't support default params lookup (use callee.id as placeholder)
            return self.call_closure_value(callee.value, callee.type_id, call, call.callee.id);
        }

        Err(CodegenError::type_mismatch(
            "call expression",
            "function",
            "non-function",
        ))
    }

    /// Compile print_char builtin for ASCII output
    fn call_print_char(&mut self, call: &CallExpr) -> CodegenResult<CompiledValue> {
        if call.args.len() != 1 {
            return Err(CodegenError::arg_count("print_char", 1, call.args.len()));
        }

        let arg = self.expr(&call.args[0])?;

        // Convert to u8 if needed (truncate from i64)
        let char_val = if arg.ty == types::I64 {
            self.builder.ins().ireduce(types::I8, arg.value)
        } else if arg.ty == types::I8 {
            arg.value
        } else {
            return Err(CodegenError::type_mismatch(
                "print_char argument",
                "i32 or i64",
                "non-integer",
            ));
        };

        self.call_runtime_void(RuntimeFn::PrintChar, &[char_val])?;
        Ok(self.void_value())
    }

    /// Compile assert as inline codegen.
    /// Uses brif + assert_fail instead of a function call to avoid
    /// a pre-existing class-field-access register clobber bug (v-a1f9).
    fn call_assert(&mut self, call: &CallExpr, call_line: u32) -> CodegenResult<CompiledValue> {
        if call.args.is_empty() {
            return Err(CodegenError::arg_count("assert", 1, 0));
        }

        let cond = self.expr(&call.args[0])?;
        let cond_i32 = self.cond_to_i32(cond.value);

        let pass_block = self.builder.create_block();
        let fail_block = self.builder.create_block();

        self.builder
            .ins()
            .brif(cond_i32, pass_block, &[], fail_block, &[]);

        self.switch_and_seal(fail_block);

        // vole_assert_fail(file_ptr, file_len, line)
        let (file_ptr, file_len) = self.source_file();
        let ptr_type = self.ptr_type();
        let file_ptr_val = self.builder.ins().iconst(ptr_type, file_ptr as i64);
        let file_len_val = self.builder.ins().iconst(ptr_type, file_len as i64);
        let line_val = self.builder.ins().iconst(types::I32, call_line as i64);

        self.call_runtime_void(
            RuntimeFn::AssertFail,
            &[file_ptr_val, file_len_val, line_val],
        )?;
        self.builder.ins().jump(pass_block, &[]);

        self.switch_and_seal(pass_block);

        Ok(self.void_value())
    }

    /// Emit a panic with a static message at the given line.
    /// Used for runtime errors like division by zero that don't have a user-provided message.
    /// Returns Ok(()) on success, but note that control flow doesn't continue after this
    /// (an unreachable block is created for any following code).
    pub fn emit_panic_static(&mut self, msg: &str, line: u32) -> CodegenResult<()> {
        // Create the message string constant
        let msg_val = self.string_literal(msg)?;

        // vole_panic(msg, file_ptr, file_len, line)
        let (file_ptr, file_len) = self.source_file();
        let ptr_type = self.ptr_type();
        let file_ptr_val = self.builder.ins().iconst(ptr_type, file_ptr as i64);
        let file_len_val = self.builder.ins().iconst(ptr_type, file_len as i64);
        let line_val = self.builder.ins().iconst(types::I32, line as i64);

        self.call_runtime_void(
            RuntimeFn::Panic,
            &[msg_val.value, file_ptr_val, file_len_val, line_val],
        )?;

        // Since panic never returns, emit trap and create unreachable block
        self.builder.ins().trap(TrapCode::unwrap_user(3));

        // Create an unreachable block for code that follows the panic call
        let unreachable_block = self.builder.create_block();
        self.switch_and_seal(unreachable_block);

        Ok(())
    }

    /// Call a function via variable (dispatches to closure or pure function call)
    fn call_closure(
        &mut self,
        func_var: Variable,
        func_type_id: TypeId,
        call: &CallExpr,
        call_expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let func_ptr_or_closure = self.builder.use_var(func_var);
        self.call_closure_value(func_ptr_or_closure, func_type_id, call, call_expr_id)
    }

    /// Call a function via value (always uses closure calling convention now that
    /// all lambdas are wrapped in Closure structs for consistent behavior)
    fn call_closure_value(
        &mut self,
        func_ptr_or_closure: Value,
        func_type_id: TypeId,
        call: &CallExpr,
        call_expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        // Always use closure calling convention since all lambdas are now
        // wrapped in Closure structs for consistency with interface dispatch
        self.call_actual_closure(func_ptr_or_closure, func_type_id, call, call_expr_id)
    }

    /// Call an actual closure (with closure pointer)
    fn call_actual_closure(
        &mut self,
        closure_ptr: Value,
        func_type_id: TypeId,
        call: &CallExpr,
        call_expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let func_ptr = self.call_runtime(RuntimeFn::ClosureGetFunc, &[closure_ptr])?;

        // Get function components from arena
        let (params, ret, _is_closure) = {
            let arena = self.arena();
            let (params, ret, is_closure) =
                arena.unwrap_function(func_type_id).ok_or_else(|| {
                    CodegenError::type_mismatch(
                        "call_actual_closure",
                        "function type",
                        "non-function type",
                    )
                })?;
            (params.clone(), ret, is_closure)
        };

        // Build signature (closure ptr + params)
        let mut sig = self.jit_module().make_signature();
        sig.params.push(AbiParam::new(self.ptr_type())); // closure ptr
        for &param_type_id in &params {
            sig.params
                .push(AbiParam::new(self.cranelift_type(param_type_id)));
        }
        let arena = self.arena();
        if ret != arena.void() {
            // For fallible returns, use multi-value return (tag: i64, payload: i64)
            if arena.unwrap_fallible(ret).is_some() {
                sig.returns.push(AbiParam::new(types::I64)); // tag
                sig.returns.push(AbiParam::new(types::I64)); // payload
            } else {
                sig.returns.push(AbiParam::new(type_id_to_cranelift(
                    ret,
                    arena,
                    self.ptr_type(),
                )));
            }
        }

        let sig_ref = self.builder.import_signature(sig);

        let mut args: ArgVec = smallvec![closure_ptr];

        // Check if this call has lambda defaults
        let lambda_defaults = self
            .analyzed()
            .expression_data
            .get_lambda_defaults(call_expr_id)
            .cloned();

        // Compile provided arguments, tracking RC temps for cleanup
        let mut rc_temp_args = Vec::new();
        for (arg, &param_type_id) in call.args.iter().zip(params.iter()) {
            let compiled = self.expr(arg)?;
            if compiled.is_owned() {
                rc_temp_args.push(compiled);
            }
            let compiled = self.coerce_to_type(compiled, param_type_id)?;
            args.push(compiled.value);
        }

        // Compile default expressions for missing arguments
        if let Some(defaults_info) = lambda_defaults
            && call.args.len() < params.len()
        {
            // Find the lambda expression by NodeId to get its default expressions
            // Use raw pointers to avoid borrow conflicts (the data lives in Program AST
            // which is owned by AnalyzedProgram and outlives this compilation session)
            let lambda_node_id = defaults_info.lambda_node_id;
            let Some(lambda) = self.find_lambda_by_node_id(lambda_node_id) else {
                return Err(CodegenError::internal_with_context(
                    "lambda expression not found",
                    format!("NodeId {:?}", lambda_node_id),
                ));
            };
            // Get raw pointers to the default expressions for params we need
            let default_ptrs: Vec<Option<*const Expr>> = lambda
                .params
                .iter()
                .skip(call.args.len())
                .map(|p| p.default_value.as_ref().map(|e| e.as_ref() as *const Expr))
                .collect();

            // Compile defaults for missing params (starting from call.args.len())
            for (default_ptr_opt, &param_type_id) in
                default_ptrs.iter().zip(params.iter().skip(call.args.len()))
            {
                let Some(default_ptr) = default_ptr_opt else {
                    return Err(CodegenError::internal(
                        "missing default expression for parameter in lambda call",
                    ));
                };
                // SAFETY: The pointer points to data in Program AST which is owned by
                // AnalyzedProgram. AnalyzedProgram outlives this entire compilation session.
                let default_expr = unsafe { &**default_ptr };
                let compiled = self.expr(default_expr)?;
                if compiled.is_owned() {
                    rc_temp_args.push(compiled);
                }
                let compiled = self.coerce_to_type(compiled, param_type_id)?;
                args.push(compiled.value);
            }
        }

        let call_inst = self.builder.ins().call_indirect(sig_ref, func_ptr, &args);
        self.field_cache.clear(); // Callee may mutate instance fields

        // Dec RC temp args after the call has consumed them
        self.consume_rc_args(&mut rc_temp_args)?;
        let results = self.builder.inst_results(call_inst);

        if results.is_empty() {
            Ok(self.void_value())
        } else if results.len() == 2 && self.arena().unwrap_fallible(ret).is_some() {
            // Fallible multi-value return: pack (tag, payload) into stack slot
            let tag = results[0];
            let payload = results[1];

            let slot_size = 16u32; // 8 bytes tag + 8 bytes payload
            let slot = self.alloc_stack(slot_size);

            self.builder.ins().stack_store(tag, slot, 0);
            self.builder.ins().stack_store(payload, slot, 8);

            let ptr_type = self.ptr_type();
            let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

            Ok(CompiledValue::new(ptr, ptr_type, ret))
        } else {
            // If the return type is a union, the returned value is a pointer to callee's stack.
            // We need to copy the union data to our own stack to prevent it from being
            // overwritten on subsequent calls to the same closure.
            if self.arena().is_union(ret) {
                let src_ptr = results[0];
                let union_size = self.type_size(ret);
                let slot = self.alloc_stack(union_size);

                // Copy the union data (tag + payload)
                // Tag is at offset 0 (1 byte)
                let tag = self
                    .builder
                    .ins()
                    .load(types::I8, MemFlags::new(), src_ptr, 0);
                self.builder.ins().stack_store(tag, slot, 0);

                // Payload is at offset 8 (8 bytes) - only copy if union has payload data.
                // Sentinel-only unions (e.g. A | B where both are zero-sized) have
                // union_size == 8 (tag only), so there's no payload to copy.
                if union_size > 8 {
                    let payload = self
                        .builder
                        .ins()
                        .load(types::I64, MemFlags::new(), src_ptr, 8);
                    self.builder.ins().stack_store(payload, slot, 8);
                }

                let ptr_type = self.ptr_type();
                let new_ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);
                Ok(self.compiled(new_ptr, ret))
            } else {
                Ok(self.compiled(results[0], ret))
            }
        }
    }

    /// Emit an indirect call to a native function.
    ///
    /// This helper builds the Cranelift signature from NativeSignature,
    /// imports it, and emits the indirect call. Returns the call instruction
    /// so callers can handle results with their own type logic.
    ///
    /// For struct returns, uses C ABI conventions:
    /// - Small structs (1-2 fields): multi-value return in registers
    /// - Large structs (3+ fields): sret convention with hidden first param
    fn call_native_indirect(
        &mut self,
        native_func: &NativeFunction,
        args: &[Value],
    ) -> cranelift_codegen::ir::Inst {
        // Check for struct return type with special ABI handling
        if let NativeType::Struct { field_count } = &native_func.signature.return_type {
            return self.call_native_indirect_struct(native_func, args, *field_count);
        }

        // Build the Cranelift signature from NativeSignature
        let mut sig = self.jit_module().make_signature();
        for param_type in &native_func.signature.params {
            sig.params.push(AbiParam::new(native_type_to_cranelift(
                param_type,
                self.ptr_type(),
            )));
        }
        if native_func.signature.return_type != NativeType::Nil {
            sig.returns.push(AbiParam::new(native_type_to_cranelift(
                &native_func.signature.return_type,
                self.ptr_type(),
            )));
        }

        // Import the signature and emit an indirect call
        let sig_ref = self.builder.import_signature(sig);
        let ptr_type = self.ptr_type();
        let func_ptr_val = self.builder.ins().iconst(ptr_type, native_func.ptr as i64);
        let inst = self
            .builder
            .ins()
            .call_indirect(sig_ref, func_ptr_val, args);
        self.field_cache.clear(); // Native calls may mutate instance fields
        inst
    }

    /// Emit a native call that returns a C-ABI struct.
    ///
    /// For small structs (1-2 fields), the C ABI returns values in RAX+RDX,
    /// which maps to a multi-value return in Cranelift.
    /// For large structs (3+ fields), uses sret convention.
    fn call_native_indirect_struct(
        &mut self,
        native_func: &NativeFunction,
        args: &[Value],
        field_count: usize,
    ) -> cranelift_codegen::ir::Inst {
        let ptr_type = self.ptr_type();
        let mut sig = self.jit_module().make_signature();

        if field_count <= 2 {
            // Small struct: C returns in registers (RAX, RDX)
            for param_type in &native_func.signature.params {
                sig.params.push(AbiParam::new(native_type_to_cranelift(
                    param_type, ptr_type,
                )));
            }
            for _ in 0..field_count.max(1) {
                sig.returns.push(AbiParam::new(types::I64));
            }
            // Pad to 2 for consistent convention
            if field_count < 2 {
                sig.returns.push(AbiParam::new(types::I64));
            }

            let sig_ref = self.builder.import_signature(sig);
            let func_ptr_val = self.builder.ins().iconst(ptr_type, native_func.ptr as i64);
            let inst = self
                .builder
                .ins()
                .call_indirect(sig_ref, func_ptr_val, args);
            self.field_cache.clear(); // Native calls may mutate instance fields
            inst
        } else {
            // Large struct: sret convention
            // Add hidden sret pointer as first parameter
            sig.params.push(AbiParam::new(ptr_type)); // sret
            for param_type in &native_func.signature.params {
                sig.params.push(AbiParam::new(native_type_to_cranelift(
                    param_type, ptr_type,
                )));
            }
            sig.returns.push(AbiParam::new(ptr_type)); // returns sret pointer

            // Allocate buffer for the return value
            let total_size = (field_count as u32) * 8;
            let slot = self.alloc_stack(total_size);
            let sret_ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

            // Prepend sret pointer to args
            let mut sret_args = Vec::with_capacity(args.len() + 1);
            sret_args.push(sret_ptr);
            sret_args.extend_from_slice(args);

            let sig_ref = self.builder.import_signature(sig);
            let func_ptr_val = self.builder.ins().iconst(ptr_type, native_func.ptr as i64);
            let inst = self
                .builder
                .ins()
                .call_indirect(sig_ref, func_ptr_val, &sret_args);
            self.field_cache.clear(); // Native calls may mutate instance fields
            inst
        }
    }

    /// Extract the result of a native function call as a CompiledValue.
    ///
    /// For struct-returning native functions, this reconstructs the struct from
    /// the multi-value return registers or sret pointer.
    fn native_call_result(
        &mut self,
        call_inst: cranelift_codegen::ir::Inst,
        native_func: &NativeFunction,
        type_id: TypeId,
    ) -> CompiledValue {
        let results = self.builder.inst_results(call_inst);

        if results.is_empty() {
            return self.void_value();
        }

        // Handle struct return types
        if let NativeType::Struct { field_count } = &native_func.signature.return_type {
            if *field_count <= 2 {
                // Small struct: reconstruct from register values
                let results_vec: Vec<Value> = results.to_vec();
                return self.reconstruct_struct_from_regs(&results_vec, type_id);
            }
            // Large struct (sret): result[0] is already the pointer to our buffer
            return CompiledValue::new(results[0], self.ptr_type(), type_id);
        }

        // Non-struct: standard single result
        CompiledValue::new(
            results[0],
            native_type_to_cranelift(&native_func.signature.return_type, self.ptr_type()),
            type_id,
        )
    }

    /// Compile a native function call with known Vole types (for generic external functions)
    /// This uses the concrete types from the monomorphized FunctionType rather than
    /// inferring types from the native signature.
    fn compile_native_call_with_types(
        &mut self,
        native_func: &NativeFunction,
        call: &CallExpr,
        return_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let args = self.compile_call_args(&call.args)?;
        let call_inst = self.call_native_indirect(native_func, &args);
        let type_id = self.substitute_type(return_type_id);
        let type_id = self.maybe_convert_iterator_return_type(type_id);
        Ok(self.native_call_result(call_inst, native_func, type_id))
    }

    /// Find the intrinsic key for a generic external function call based on type mappings.
    /// Looks at the monomorphization substitutions and finds a matching type in the mappings.
    pub(crate) fn find_intrinsic_key_for_monomorph(
        &self,
        type_mappings: &[vole_sema::implement_registry::TypeMappingEntry],
        substitutions: &rustc_hash::FxHashMap<NameId, TypeId>,
    ) -> Option<String> {
        // Check each mapping to see if it matches any of the substituted types
        for mapping in type_mappings {
            // For each type param substitution, check if it matches this mapping's type
            for &concrete_type in substitutions.values() {
                if concrete_type == mapping.type_id {
                    return Some(mapping.intrinsic_key.clone());
                }
            }
        }
        None
    }

    /// Call a generic external function as a compiler intrinsic.
    /// Uses the intrinsic key from type mappings to dispatch to the correct handler.
    fn call_generic_external_intrinsic(
        &mut self,
        module_path: &str,
        intrinsic_key: &str,
        call: &CallExpr,
        return_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        self.call_generic_external_intrinsic_args(
            module_path,
            intrinsic_key,
            &call.args,
            return_type_id,
        )
    }

    /// Call a generic external function as a compiler intrinsic (takes args directly).
    /// Used by both direct calls and module method calls.
    pub(crate) fn call_generic_external_intrinsic_args(
        &mut self,
        module_path: &str,
        intrinsic_key: &str,
        args_exprs: &[Expr],
        return_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Check if this is a compiler intrinsic module
        if module_path == Self::COMPILER_INTRINSIC_MODULE {
            // Compile arguments (for intrinsics that take args)
            let args = self.compile_call_args(args_exprs)?;
            return self.call_compiler_intrinsic(intrinsic_key, &args, return_type_id);
        }

        // Otherwise, look up in native registry (not supported for args-only version)
        Err(CodegenError::not_found(
            "generic external intrinsic",
            format!(
                "{}::{} (non-intrinsic native calls not supported via method syntax)",
                module_path, intrinsic_key
            ),
        ))
    }

    /// Try to call a generic external function via monomorphization intrinsic resolution.
    /// Returns Some(result) if the call was handled, None if it should fall through.
    fn try_call_generic_external_intrinsic_from_monomorph(
        &mut self,
        call_expr_id: NodeId,
        call: &CallExpr,
    ) -> CodegenResult<Option<CompiledValue>> {
        let Some(monomorph_key) = self.query().monomorph_for(call_expr_id) else {
            return Ok(None);
        };

        let instance_data = self.monomorph_cache().get(monomorph_key).map(|inst| {
            (
                inst.original_name,
                inst.func_type.return_type_id,
                inst.substitutions.clone(),
            )
        });

        let Some((original_name, return_type_id, substitutions)) = instance_data else {
            return Ok(None);
        };

        let Some(callee_name) = self.name_table().last_segment_str(original_name) else {
            return Ok(None);
        };

        let Some(generic_ext_info) = self
            .analyzed()
            .implement_registry()
            .get_generic_external(&callee_name)
        else {
            return Ok(None);
        };

        let Some(key) =
            self.find_intrinsic_key_for_monomorph(&generic_ext_info.type_mappings, &substitutions)
        else {
            return Ok(None);
        };

        let module_path = self
            .name_table()
            .last_segment_str(generic_ext_info.module_path)
            .unwrap_or_default();

        let return_type_id = self.substitute_type(return_type_id);

        self.call_generic_external_intrinsic(&module_path, &key, call, return_type_id)
            .map(Some)
    }

    /// Try to call a value as a functional interface.
    /// Returns Some(result) if the value is a functional interface, None otherwise.
    fn try_call_functional_interface(
        &mut self,
        obj: &CompiledValue,
        args: &[Expr],
    ) -> CodegenResult<Option<CompiledValue>> {
        let Some(iface_type_def_id) = self.interface_type_def_id(obj.type_id) else {
            return Ok(None);
        };

        let Some(method_id) = self.query().is_functional_interface(iface_type_def_id) else {
            return Ok(None);
        };

        let method = self.query().get_method(method_id);
        let func_type_id = method.signature_id;
        let method_name_id = method.name_id;

        self.interface_dispatch_call_args_by_type_def_id(
            obj,
            args,
            iface_type_def_id,
            method_name_id,
            func_type_id,
        )
        .map(Some)
    }

    /// Try to call a monomorphized function.
    /// Returns Some(result) if the call was handled, None if it should fall through.
    fn try_call_monomorphized_function(
        &mut self,
        call_expr_id: NodeId,
        call: &CallExpr,
        callee_sym: Symbol,
        callee_name: &str,
    ) -> CodegenResult<Option<CompiledValue>> {
        let Some(monomorph_key) = self.query().monomorph_for(call_expr_id) else {
            return Ok(None);
        };

        tracing::trace!(
            call_expr_id = ?call_expr_id,
            callee = callee_name,
            has_monomorph = true,
            "checking for generic function call"
        );

        let instance_data = self.monomorph_cache().get(monomorph_key).map(|inst| {
            (
                inst.original_name,
                inst.mangled_name,
                inst.func_type.return_type_id,
                inst.substitutions.clone(),
            )
        });

        let Some((original_name, mangled_name, return_type_id, substitutions)) = instance_data
        else {
            return Ok(None);
        };

        tracing::trace!(
            instance_name = ?original_name,
            mangled_name = ?mangled_name,
            "found monomorph instance"
        );

        let func_key = self.funcs().intern_name_id(mangled_name);
        if let Some(func_id) = self.funcs().func_id(func_key) {
            tracing::trace!("found func_id, using regular path");
            return self
                .call_func_id(func_key, func_id, call, callee_sym)
                .map(Some);
        }

        tracing::trace!("no func_id, checking for external function");

        // For generic external functions with type mappings, look up intrinsic by concrete type
        if let Some(generic_ext_info) = self
            .analyzed()
            .implement_registry()
            .get_generic_external(callee_name)
            && let Some(key) = self
                .find_intrinsic_key_for_monomorph(&generic_ext_info.type_mappings, &substitutions)
        {
            let module_path = self
                .name_table()
                .last_segment_str(generic_ext_info.module_path)
                .unwrap_or_default();

            let return_type_id = self.substitute_type(return_type_id);

            return self
                .call_generic_external_intrinsic(&module_path, &key, call, return_type_id)
                .map(Some);
        }

        // Fallback: For generic external functions without type mappings,
        // call them directly with type erasure via native_registry
        if let Some(ext_info) = self
            .analyzed()
            .implement_registry()
            .get_external_func(callee_name)
        {
            let name_table = self.name_table();
            let module_path = name_table.last_segment_str(ext_info.module_path);
            let native_name = name_table.last_segment_str(ext_info.native_name);
            if let (Some(module_path), Some(native_name)) = (module_path, native_name)
                && let Some(native_func) = self.native_funcs().lookup(&module_path, &native_name)
            {
                let return_type_id = self.substitute_type(return_type_id);
                return self
                    .compile_native_call_with_types(native_func, call, return_type_id)
                    .map(Some);
            }
        }

        Ok(None)
    }
}

impl Cg<'_, '_, '_> {
    /// Find a lambda expression by NodeId in the program.
    fn find_lambda_by_node_id(&self, node_id: NodeId) -> Option<&LambdaExpr> {
        find_lambda_in_program(&self.analyzed().program, node_id)
    }
}

/// Find a lambda expression by NodeId in a program.
fn find_lambda_in_program(program: &Program, node_id: NodeId) -> Option<&LambdaExpr> {
    // Search expressions in declarations and statements
    for decl in &program.declarations {
        if let Some(lambda) = find_lambda_in_decl(decl, node_id) {
            return Some(lambda);
        }
    }
    None
}

/// Find a lambda in a declaration.
fn find_lambda_in_decl(decl: &Decl, node_id: NodeId) -> Option<&LambdaExpr> {
    match decl {
        Decl::Function(func) => {
            // Search function body for lambdas
            match &func.body {
                vole_frontend::FuncBody::Expr(expr) => find_lambda_in_expr(expr, node_id),
                vole_frontend::FuncBody::Block(block) => {
                    find_lambda_in_stmts(&block.stmts, node_id)
                }
            }
        }
        Decl::Let(let_stmt) => {
            if let vole_frontend::LetInit::Expr(expr) = &let_stmt.init {
                find_lambda_in_expr(expr, node_id)
            } else {
                None
            }
        }
        Decl::Tests(tests) => {
            // Search scoped declarations first
            for inner_decl in &tests.decls {
                if let Some(lambda) = find_lambda_in_decl(inner_decl, node_id) {
                    return Some(lambda);
                }
            }
            // Then search test cases
            for test in &tests.tests {
                if let Some(lambda) = find_lambda_in_func_body(&test.body, node_id) {
                    return Some(lambda);
                }
            }
            None
        }
        _ => None,
    }
}

/// Find a lambda in a function body.
fn find_lambda_in_func_body(
    body: &vole_frontend::FuncBody,
    node_id: NodeId,
) -> Option<&LambdaExpr> {
    match body {
        vole_frontend::FuncBody::Expr(expr) => find_lambda_in_expr(expr, node_id),
        vole_frontend::FuncBody::Block(block) => find_lambda_in_stmts(&block.stmts, node_id),
    }
}

/// Find a lambda in a list of statements.
fn find_lambda_in_stmts(stmts: &[Stmt], node_id: NodeId) -> Option<&LambdaExpr> {
    for stmt in stmts {
        if let Some(lambda) = find_lambda_in_stmt(stmt, node_id) {
            return Some(lambda);
        }
    }
    None
}

/// Find a lambda in a statement.
fn find_lambda_in_stmt(stmt: &Stmt, node_id: NodeId) -> Option<&LambdaExpr> {
    match stmt {
        Stmt::Let(let_stmt) => {
            if let vole_frontend::LetInit::Expr(expr) = &let_stmt.init {
                find_lambda_in_expr(expr, node_id)
            } else {
                None
            }
        }
        Stmt::LetTuple(let_tuple) => find_lambda_in_expr(&let_tuple.init, node_id),
        Stmt::Expr(expr_stmt) => find_lambda_in_expr(&expr_stmt.expr, node_id),
        Stmt::Return(ret_stmt) => ret_stmt
            .value
            .as_ref()
            .and_then(|e| find_lambda_in_expr(e, node_id)),
        Stmt::If(if_stmt) => {
            if let Some(lambda) = find_lambda_in_expr(&if_stmt.condition, node_id) {
                return Some(lambda);
            }
            if let Some(lambda) = find_lambda_in_stmts(&if_stmt.then_branch.stmts, node_id) {
                return Some(lambda);
            }
            if let Some(else_branch) = &if_stmt.else_branch
                && let Some(lambda) = find_lambda_in_stmts(&else_branch.stmts, node_id)
            {
                return Some(lambda);
            }
            None
        }
        Stmt::While(while_stmt) => {
            if let Some(lambda) = find_lambda_in_expr(&while_stmt.condition, node_id) {
                return Some(lambda);
            }
            find_lambda_in_stmts(&while_stmt.body.stmts, node_id)
        }
        Stmt::For(for_stmt) => {
            if let Some(lambda) = find_lambda_in_expr(&for_stmt.iterable, node_id) {
                return Some(lambda);
            }
            find_lambda_in_stmts(&for_stmt.body.stmts, node_id)
        }
        Stmt::Raise(raise_stmt) => {
            // Raise has fields that could contain lambdas
            for field in &raise_stmt.fields {
                if let Some(lambda) = find_lambda_in_expr(&field.value, node_id) {
                    return Some(lambda);
                }
            }
            None
        }
        Stmt::Break(_) | Stmt::Continue(_) => None,
    }
}

/// Find a lambda in an expression.
fn find_lambda_in_expr(expr: &Expr, node_id: NodeId) -> Option<&LambdaExpr> {
    if expr.id == node_id
        && let ExprKind::Lambda(lambda) = &expr.kind
    {
        return Some(lambda);
    }

    match &expr.kind {
        ExprKind::Lambda(lambda) => {
            // Check body for nested lambdas
            match &lambda.body {
                vole_frontend::FuncBody::Expr(body) => find_lambda_in_expr(body, node_id),
                vole_frontend::FuncBody::Block(block) => {
                    find_lambda_in_stmts(&block.stmts, node_id)
                }
            }
        }
        ExprKind::Call(call) => {
            if let Some(lambda) = find_lambda_in_expr(&call.callee, node_id) {
                return Some(lambda);
            }
            for arg in &call.args {
                if let Some(lambda) = find_lambda_in_expr(arg, node_id) {
                    return Some(lambda);
                }
            }
            None
        }
        ExprKind::Binary(binary) => find_lambda_in_expr(&binary.left, node_id)
            .or_else(|| find_lambda_in_expr(&binary.right, node_id)),
        ExprKind::Unary(unary) => find_lambda_in_expr(&unary.operand, node_id),
        ExprKind::Block(block) => find_lambda_in_stmts(&block.stmts, node_id),
        ExprKind::If(if_expr) => {
            if let Some(lambda) = find_lambda_in_expr(&if_expr.condition, node_id) {
                return Some(lambda);
            }
            if let Some(lambda) = find_lambda_in_expr(&if_expr.then_branch, node_id) {
                return Some(lambda);
            }
            if let Some(else_branch) = &if_expr.else_branch {
                find_lambda_in_expr(else_branch, node_id)
            } else {
                None
            }
        }
        ExprKind::ArrayLiteral(elems) => {
            for elem in elems {
                if let Some(lambda) = find_lambda_in_expr(elem, node_id) {
                    return Some(lambda);
                }
            }
            None
        }
        ExprKind::RepeatLiteral { element, .. } => find_lambda_in_expr(element, node_id),
        ExprKind::Index(idx) => find_lambda_in_expr(&idx.object, node_id)
            .or_else(|| find_lambda_in_expr(&idx.index, node_id)),
        ExprKind::FieldAccess(fa) => find_lambda_in_expr(&fa.object, node_id),
        ExprKind::MethodCall(mc) => {
            if let Some(lambda) = find_lambda_in_expr(&mc.object, node_id) {
                return Some(lambda);
            }
            for arg in &mc.args {
                if let Some(lambda) = find_lambda_in_expr(arg, node_id) {
                    return Some(lambda);
                }
            }
            None
        }
        ExprKind::Assign(assign) => find_lambda_in_expr(&assign.value, node_id),
        ExprKind::CompoundAssign(compound) => find_lambda_in_expr(&compound.value, node_id),
        ExprKind::Grouping(inner) => find_lambda_in_expr(inner, node_id),
        ExprKind::Range(range) => find_lambda_in_expr(&range.start, node_id)
            .or_else(|| find_lambda_in_expr(&range.end, node_id)),
        ExprKind::NullCoalesce(nc) => find_lambda_in_expr(&nc.value, node_id)
            .or_else(|| find_lambda_in_expr(&nc.default, node_id)),
        ExprKind::Is(is_expr) => find_lambda_in_expr(&is_expr.value, node_id),
        ExprKind::StructLiteral(lit) => {
            for field in &lit.fields {
                if let Some(lambda) = find_lambda_in_expr(&field.value, node_id) {
                    return Some(lambda);
                }
            }
            None
        }
        ExprKind::OptionalChain(oc) => find_lambda_in_expr(&oc.object, node_id),
        ExprKind::Try(inner) => find_lambda_in_expr(inner, node_id),
        ExprKind::Yield(y) => find_lambda_in_expr(&y.value, node_id),
        ExprKind::Match(m) => {
            if let Some(lambda) = find_lambda_in_expr(&m.scrutinee, node_id) {
                return Some(lambda);
            }
            for arm in &m.arms {
                if let Some(lambda) = find_lambda_in_expr(&arm.body, node_id) {
                    return Some(lambda);
                }
            }
            None
        }
        ExprKind::When(w) => {
            for arm in &w.arms {
                if let Some(ref cond) = arm.condition
                    && let Some(lambda) = find_lambda_in_expr(cond, node_id)
                {
                    return Some(lambda);
                }
                if let Some(lambda) = find_lambda_in_expr(&arm.body, node_id) {
                    return Some(lambda);
                }
            }
            None
        }
        // Leaf nodes with no sub-expressions
        ExprKind::IntLiteral(..)
        | ExprKind::FloatLiteral(..)
        | ExprKind::BoolLiteral(_)
        | ExprKind::StringLiteral(_)
        | ExprKind::InterpolatedString(_)
        | ExprKind::Identifier(_)
        | ExprKind::Unreachable
        | ExprKind::TypeLiteral(_)
        | ExprKind::Import(_) => None,
    }
}
