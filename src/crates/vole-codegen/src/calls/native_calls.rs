// calls/native_calls.rs
//
// Native (FFI) call compilation: calling native functions, struct returns,
// generic external intrinsics, monomorphization dispatch, and functional interface calls.

use cranelift::prelude::*;
use cranelift_module::Module;

use vole_frontend::ast::CallExpr;
use vole_frontend::{Expr, NodeId, Symbol};
use vole_identity::ModuleId;
use vole_runtime::native_registry::{NativeFunction, NativeType};
use vole_sema::implement_registry::{TypeMappingEntry, TypeMappingKind};
use vole_sema::type_arena::TypeId;

use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, native_type_to_cranelift};

use super::super::context::Cg;

impl Cg<'_, '_, '_> {
    /// Compile and execute a native (FFI) function call.
    ///
    /// Shared logic for module FFI calls, prelude external calls, and module binding calls.
    pub(super) fn call_native_external(
        &mut self,
        native_func: &NativeFunction,
        callee_sym: Symbol,
        call: &CallExpr,
        call_expr_id: &NodeId,
    ) -> CodegenResult<CompiledValue> {
        let expected_types: Vec<Type> = native_func
            .signature
            .params
            .iter()
            .map(|nt| native_type_to_cranelift(nt, self.ptr_type()))
            .collect();
        let args = self.compile_external_call_args(callee_sym, call, &expected_types)?;
        let call_inst = self.call_native_indirect(native_func, &args);
        if native_func.signature.return_type == NativeType::Nil {
            return Ok(self.void_value());
        }
        let type_id = self
            .get_expr_type_substituted(call_expr_id)
            .expect("INTERNAL: native call: missing sema return type");
        let type_id = self.maybe_convert_iterator_return_type(type_id);
        Ok(self.native_call_result(call_inst, native_func, type_id))
    }

    /// Call a function via destructured module binding.
    /// Looks up the function by module_id and export_name, then calls via FFI or compiled function.
    pub(super) fn call_module_binding(
        &mut self,
        module_id: ModuleId,
        export_name: Symbol,
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
                return self.call_func_id(func_key, func_id, call, export_name, call_expr_id);
            }
        }

        // Try FFI call for external module functions
        if let Some(native_func) = self.native_registry().lookup(&module_path, export_name_str) {
            return self.call_native_external(native_func, export_name, call, &call_expr_id);
        }

        Err(CodegenError::not_found(
            "module function",
            format!("{}.{}", module_path, export_name_str),
        ))
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
    pub(crate) fn call_native_indirect(
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

        // Coerce args to match signature types -- boolean values from when/match
        // block params can be i64 while the native signature expects i8.
        let coerced_args: Vec<Value> = args
            .iter()
            .zip(sig.params.iter())
            .map(|(&arg, param)| {
                let expected_ty = param.value_type;
                let actual_ty = self.builder.func.dfg.value_type(arg);
                self.coerce_cranelift_value(arg, actual_ty, expected_ty)
            })
            .collect();

        // Try to devirtualize: if we know the symbol name for this function
        // pointer, import it and emit a direct `call` instead of `call_indirect`.
        let inst = if let Some(func_ref) = self.try_import_native_func(native_func.ptr, &sig) {
            let coerced = self.coerce_call_args(func_ref, &coerced_args);
            self.builder.ins().call(func_ref, &coerced)
        } else {
            let sig_ref = self.builder.import_signature(sig);
            let ptr_type = self.ptr_type();
            let func_ptr_val = self.iconst_cached(ptr_type, native_func.ptr as i64);
            self.builder
                .ins()
                .call_indirect(sig_ref, func_ptr_val, &coerced_args)
        };
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

        if field_count <= crate::MAX_SMALL_STRUCT_FIELDS {
            // Small struct: C returns in registers (RAX, RDX)
            for param_type in &native_func.signature.params {
                sig.params.push(AbiParam::new(native_type_to_cranelift(
                    param_type, ptr_type,
                )));
            }
            for _ in 0..field_count.max(1) {
                sig.returns.push(AbiParam::new(types::I64));
            }
            // Pad to MAX_SMALL_STRUCT_FIELDS for consistent calling convention
            if field_count < crate::MAX_SMALL_STRUCT_FIELDS {
                sig.returns.push(AbiParam::new(types::I64));
            }

            let inst = if let Some(func_ref) = self.try_import_native_func(native_func.ptr, &sig) {
                let coerced = self.coerce_call_args(func_ref, args);
                self.builder.ins().call(func_ref, &coerced)
            } else {
                let sig_ref = self.builder.import_signature(sig);
                let func_ptr_val = self.iconst_cached(ptr_type, native_func.ptr as i64);
                self.builder
                    .ins()
                    .call_indirect(sig_ref, func_ptr_val, args)
            };
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

            let inst = if let Some(func_ref) = self.try_import_native_func(native_func.ptr, &sig) {
                let coerced = self.coerce_call_args(func_ref, &sret_args);
                self.builder.ins().call(func_ref, &coerced)
            } else {
                let sig_ref = self.builder.import_signature(sig);
                let func_ptr_val = self.iconst_cached(ptr_type, native_func.ptr as i64);
                self.builder
                    .ins()
                    .call_indirect(sig_ref, func_ptr_val, &sret_args)
            };
            self.field_cache.clear(); // Native calls may mutate instance fields
            inst
        }
    }

    /// Extract the result of a native function call as a CompiledValue.
    ///
    /// For struct-returning native functions, this reconstructs the struct from
    /// the multi-value return registers or sret pointer.
    pub(super) fn native_call_result(
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
            if *field_count <= crate::MAX_SMALL_STRUCT_FIELDS {
                // Small struct: reconstruct from register values
                let results_vec: Vec<Value> = results.to_vec();
                return self.reconstruct_struct_from_regs(&results_vec, type_id);
            }
            // Large struct (sret): result[0] is already the pointer to our buffer
            return CompiledValue::new(results[0], self.ptr_type(), type_id);
        }

        // Non-struct: standard single result
        let actual_ty =
            native_type_to_cranelift(&native_func.signature.return_type, self.ptr_type());
        let expected_ty = self.cranelift_type(type_id);
        let value = if actual_ty == expected_ty {
            results[0]
        } else {
            self.coerce_cranelift_value(results[0], actual_ty, expected_ty)
        };
        CompiledValue::new(value, expected_ty, type_id)
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

    /// Resolve the intrinsic key for a generic external function call.
    ///
    /// Resolution order:
    /// 1. exact type arm (`Type => "key"`)
    /// 2. fallback arm (`default => "key"`)
    pub(crate) fn resolve_intrinsic_key_for_monomorph(
        &self,
        callee_name: &str,
        type_mappings: &[TypeMappingEntry],
        substitutions: &rustc_hash::FxHashMap<vole_identity::NameId, TypeId>,
    ) -> CodegenResult<String> {
        let substitution_types: std::collections::HashSet<TypeId> =
            substitutions.values().copied().collect();
        let mut default_key = None;
        let mut exact_matches: Vec<(TypeId, &str)> = Vec::new();

        for mapping in type_mappings {
            match mapping.kind {
                TypeMappingKind::Exact(type_id) => {
                    if substitution_types.contains(&type_id) {
                        exact_matches.push((type_id, mapping.intrinsic_key.as_str()));
                    }
                }
                TypeMappingKind::Default => {
                    default_key = Some(mapping.intrinsic_key.as_str());
                }
            }
        }

        if exact_matches.len() == 1 {
            return Ok(exact_matches[0].1.to_string());
        }

        if exact_matches.len() > 1 {
            let mut matches_display: Vec<String> = exact_matches
                .iter()
                .map(|(ty, key)| format!("{} => \"{}\"", self.arena().display_basic(*ty), key))
                .collect();
            matches_display.sort();
            matches_display.dedup();
            return Err(CodegenError::not_found(
                "generic external mapping",
                format!(
                    "{callee_name}: ambiguous where mapping; multiple exact arms match concrete substitutions: {}",
                    matches_display.join(", ")
                ),
            ));
        }

        if let Some(key) = default_key {
            return Ok(key.to_string());
        }

        let mut concrete_types: Vec<String> = substitutions
            .values()
            .copied()
            .map(|ty| self.arena().display_basic(ty))
            .collect();
        concrete_types.sort();
        concrete_types.dedup();

        Err(CodegenError::not_found(
            "generic external mapping",
            format!(
                "{callee_name}: no where mapping arm for concrete type(s): {}",
                concrete_types.join(", ")
            ),
        ))
    }

    fn compile_intrinsic_args_with_expected_types(
        &mut self,
        args_exprs: &[Expr],
        expected_param_type_ids: Option<&[TypeId]>,
    ) -> CodegenResult<Vec<CompiledValue>> {
        let mut args = Vec::with_capacity(args_exprs.len());
        for (index, arg_expr) in args_exprs.iter().enumerate() {
            let compiled = if let Some(param_type_ids) = expected_param_type_ids
                && let Some(&param_type_id) = param_type_ids.get(index)
            {
                let compiled = self.expr_with_expected_type(arg_expr, param_type_id)?;
                self.coerce_to_type(compiled, param_type_id)?
            } else {
                self.expr(arg_expr)?
            };
            args.push(compiled);
        }
        Ok(args)
    }

    /// Call a generic external function as a compiler intrinsic.
    /// Uses the intrinsic key from type mappings to dispatch to the correct handler.
    fn call_generic_external_intrinsic(
        &mut self,
        module_path: &str,
        intrinsic_key: &str,
        call: &CallExpr,
        return_type_id: TypeId,
        expected_param_type_ids: Option<&[TypeId]>,
    ) -> CodegenResult<CompiledValue> {
        self.call_generic_external_intrinsic_args(
            module_path,
            intrinsic_key,
            &call.args,
            return_type_id,
            expected_param_type_ids,
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
        expected_param_type_ids: Option<&[TypeId]>,
    ) -> CodegenResult<CompiledValue> {
        // Check if this is a compiler intrinsic module
        if module_path == Self::COMPILER_INTRINSIC_MODULE {
            let typed_args = self
                .compile_intrinsic_args_with_expected_types(args_exprs, expected_param_type_ids)?;
            return self.call_compiler_intrinsic_key_typed_with_line(
                crate::IntrinsicKey::from(intrinsic_key),
                &typed_args,
                return_type_id,
                0,
            );
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
    pub(super) fn try_call_generic_external_intrinsic_from_monomorph(
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
                inst.func_type.params_id.to_vec(),
                inst.func_type.return_type_id,
                inst.substitutions.clone(),
            )
        });

        let Some((original_name, param_type_ids, return_type_id, substitutions)) = instance_data
        else {
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

        let key = self.resolve_intrinsic_key_for_monomorph(
            &callee_name,
            &generic_ext_info.type_mappings,
            &substitutions,
        )?;

        let module_path = self
            .name_table()
            .last_segment_str(generic_ext_info.module_path)
            .unwrap_or_default();

        let return_type_id = self.substitute_type(return_type_id);
        let concrete_param_type_ids: Vec<TypeId> = param_type_ids
            .iter()
            .map(|&ty| {
                self.arena().expect_substitute(
                    ty,
                    &substitutions,
                    "generic external intrinsic args",
                )
            })
            .collect();

        self.call_generic_external_intrinsic(
            &module_path,
            &key,
            call,
            return_type_id,
            Some(&concrete_param_type_ids),
        )
        .map(Some)
    }

    /// Try to call a value as a functional interface.
    /// Returns Some(result) if the value is a functional interface, None otherwise.
    pub(super) fn try_call_functional_interface(
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
    pub(super) fn try_call_monomorphized_function(
        &mut self,
        call_expr_id: NodeId,
        call: &CallExpr,
        _callee_sym: Symbol,
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
                inst.func_type.params_id.to_vec(),
                inst.func_type.return_type_id,
                inst.substitutions.clone(),
            )
        });

        let Some((original_name, mangled_name, param_types_raw, return_type_id, substitutions)) =
            instance_data
        else {
            return Ok(None);
        };

        let param_type_display: Vec<String> = param_types_raw
            .iter()
            .map(|&ty| self.arena().display_basic(ty))
            .collect();
        tracing::debug!(
            call_expr_id = ?call_expr_id,
            callee = callee_name,
            mangled = ?mangled_name,
            ?param_types_raw,
            ?param_type_display,
            ?substitutions,
            "monomorph call instance"
        );

        tracing::trace!(
            instance_name = ?original_name,
            mangled_name = ?mangled_name,
            "found monomorph instance"
        );

        let func_key = self.funcs().intern_name_id(mangled_name);
        if let Some(func_id) = self.funcs().func_id(func_key) {
            let arena = self.arena();
            let param_type_ids: Vec<TypeId> = param_types_raw
                .iter()
                .map(|&ty| arena.expect_substitute(ty, &substitutions, "monomorph call args"))
                .collect();
            tracing::trace!("found func_id, using regular path");
            return self
                .call_func_id_impl(
                    func_key,
                    func_id,
                    call,
                    Some(original_name),
                    Some(param_type_ids),
                    self.get_expr_type_substituted(&call_expr_id),
                )
                .map(Some);
        }

        tracing::trace!("no func_id, checking for external function");

        // For generic external functions with type mappings, look up intrinsic by concrete type
        if let Some(generic_ext_info) = self
            .analyzed()
            .implement_registry()
            .get_generic_external(callee_name)
        {
            let key = self.resolve_intrinsic_key_for_monomorph(
                callee_name,
                &generic_ext_info.type_mappings,
                &substitutions,
            )?;
            let module_path = self
                .name_table()
                .last_segment_str(generic_ext_info.module_path)
                .unwrap_or_default();

            let return_type_id = self.substitute_type(return_type_id);
            let concrete_param_type_ids: Vec<TypeId> = param_types_raw
                .iter()
                .map(|&ty| {
                    self.arena().expect_substitute(
                        ty,
                        &substitutions,
                        "generic external intrinsic args",
                    )
                })
                .collect();

            return self
                .call_generic_external_intrinsic(
                    &module_path,
                    &key,
                    call,
                    return_type_id,
                    Some(&concrete_param_type_ids),
                )
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
                && let Some(native_func) = self.native_registry().lookup(&module_path, &native_name)
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
