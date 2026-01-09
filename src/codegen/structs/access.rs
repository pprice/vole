// src/codegen/structs/access.rs

use super::helpers::{convert_field_value, convert_to_i64_for_storage, get_field_slot_and_type};
use crate::codegen::RuntimeFn;
use crate::codegen::context::Cg;
use crate::codegen::method_resolution::{
    MethodResolutionInput, MethodTarget, resolve_method_target,
};
use crate::codegen::types::{CompiledValue, method_name_id, module_name_id, type_to_cranelift};
use crate::errors::CodegenError;
use crate::frontend::{Expr, FieldAccessExpr, NodeId, OptionalChainExpr, Symbol};
use crate::sema::Type;
use crate::sema::resolution::ResolvedMethod;
use crate::sema::types::ConstantValue;
use cranelift::prelude::*;

impl Cg<'_, '_, '_> {
    pub fn field_access(
        &mut self,
        fa: &FieldAccessExpr,
        expr_id: NodeId,
    ) -> Result<CompiledValue, String> {
        // Check if this field access was resolved as a property-style method call
        // (e.g., `s.length` calling `s.length()`)
        if let Some(resolved) = self.ctx.analyzed.method_resolutions.get(expr_id) {
            let obj = self.expr(&fa.object)?;
            let method_name = self.ctx.interner.resolve(fa.field);

            // First check if it's a builtin method (like string.length)
            if let Some(result) = self.builtin_method(&obj, method_name)? {
                return Ok(result);
            }

            // Otherwise, use method resolution to call the method
            return self.property_style_method_call(&obj, fa.field, expr_id, resolved);
        }

        let obj = self.expr(&fa.object)?;

        // Handle module field access for constants (e.g., math.PI)
        if let Type::Module(ref module_type) = obj.vole_type {
            let field_name = self.ctx.interner.resolve(fa.field);
            let module_path = self
                .ctx
                .analyzed
                .name_table
                .module_path(module_type.module_id);
            let name_id = module_name_id(self.ctx.analyzed, module_type.module_id, field_name);

            // Look up constant value in module
            if let Some(name_id) = name_id
                && let Some(const_val) = module_type.constants.get(&name_id)
            {
                return match const_val {
                    ConstantValue::F64(v) => {
                        let val = self.builder.ins().f64const(*v);
                        Ok(CompiledValue {
                            value: val,
                            ty: types::F64,
                            vole_type: Type::F64,
                        })
                    }
                    ConstantValue::I64(v) => {
                        let val = self.builder.ins().iconst(types::I64, *v);
                        Ok(CompiledValue {
                            value: val,
                            ty: types::I64,
                            vole_type: Type::I64,
                        })
                    }
                    ConstantValue::Bool(v) => {
                        let val = self.builder.ins().iconst(types::I8, if *v { 1 } else { 0 });
                        Ok(CompiledValue {
                            value: val,
                            ty: types::I8,
                            vole_type: Type::Bool,
                        })
                    }
                    ConstantValue::String(s) => self.string_literal(s),
                };
            }

            // Check if it's a function export
            if let Some(name_id) = name_id
                && let Some(export_type) = module_type.exports.get(&name_id)
            {
                if matches!(export_type, Type::Function(_)) {
                    return Err(CodegenError::unsupported_with_context(
                        "function as field value",
                        format!("use {}() to call the function", field_name),
                    )
                    .into());
                }

                return Err(CodegenError::unsupported_with_context(
                    "non-constant module export",
                    format!("{} cannot be accessed at compile time", field_name),
                )
                .into());
            }

            return Err(CodegenError::not_found(
                "module export",
                format!("{}.{}", module_path, field_name),
            )
            .into());
        }

        let (slot, field_type) = get_field_slot_and_type(&obj.vole_type, fa.field, self.ctx)?;

        let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
        let result_raw = self.call_runtime(RuntimeFn::InstanceGetField, &[obj.value, slot_val])?;

        let (result_val, cranelift_ty) = convert_field_value(self.builder, result_raw, &field_type);

        Ok(CompiledValue {
            value: result_val,
            ty: cranelift_ty,
            vole_type: field_type,
        })
    }

    pub fn optional_chain(&mut self, oc: &OptionalChainExpr) -> Result<CompiledValue, String> {
        let obj = self.expr(&oc.object)?;

        // The object should be an optional type (union with nil)
        let Type::Union(variants) = &obj.vole_type else {
            return Err(CodegenError::type_mismatch(
                "optional chain",
                "optional type",
                "non-optional",
            )
            .into());
        };

        // Find the nil tag
        let nil_tag = variants
            .iter()
            .position(|v| v == &Type::Nil)
            .unwrap_or(usize::MAX);

        // Check if object is nil by reading the tag
        let tag = self
            .builder
            .ins()
            .load(types::I8, MemFlags::new(), obj.value, 0);
        let nil_tag_val = self.builder.ins().iconst(types::I8, nil_tag as i64);
        let is_nil = self.builder.ins().icmp(IntCC::Equal, tag, nil_tag_val);

        // Create blocks for branching
        let nil_block = self.builder.create_block();
        let not_nil_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        // Get the inner (non-nil) type for field access
        let inner_type = obj.vole_type.unwrap_optional().unwrap_or(Type::Error);

        // Get the field type from the inner type
        let (slot, field_type) = get_field_slot_and_type(&inner_type, oc.field, self.ctx)?;

        // Result type is field_type | nil (optional)
        // But if field type is already optional, don't double-wrap
        let result_vole_type = if field_type.is_optional() {
            field_type.clone()
        } else {
            Type::optional(field_type.clone())
        };
        let cranelift_type = type_to_cranelift(&result_vole_type, self.ctx.pointer_type);
        self.builder.append_block_param(merge_block, cranelift_type);

        self.builder
            .ins()
            .brif(is_nil, nil_block, &[], not_nil_block, &[]);

        // Nil block: return nil wrapped in the optional type
        self.builder.switch_to_block(nil_block);
        self.builder.seal_block(nil_block);
        let nil_val = self.nil_value();
        let nil_union = self.construct_union(nil_val, &result_vole_type)?;
        self.builder
            .ins()
            .jump(merge_block, &[nil_union.value.into()]);

        // Not-nil block: do field access and wrap result in optional
        self.builder.switch_to_block(not_nil_block);
        self.builder.seal_block(not_nil_block);

        // Load the actual object from the union payload (offset 8)
        let inner_cranelift_type = type_to_cranelift(&inner_type, self.ctx.pointer_type);
        let inner_obj =
            self.builder
                .ins()
                .load(inner_cranelift_type, MemFlags::new(), obj.value, 8);

        // Get field from the inner object
        let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
        let field_raw = self.call_runtime(RuntimeFn::InstanceGetField, &[inner_obj, slot_val])?;
        let (field_val, field_cranelift_ty) =
            convert_field_value(self.builder, field_raw, &field_type);

        // Wrap the field value in an optional (using construct_union)
        // But if field type is already optional, it's already a union - just use it directly
        let field_compiled = CompiledValue {
            value: field_val,
            ty: field_cranelift_ty,
            vole_type: field_type.clone(),
        };
        let final_value = if field_type.is_optional() {
            // Field is already optional, use as-is
            field_compiled
        } else {
            // Wrap non-optional field in optional
            self.construct_union(field_compiled, &result_vole_type)?
        };
        self.builder
            .ins()
            .jump(merge_block, &[final_value.value.into()]);

        // Merge block
        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);

        let result = self.builder.block_params(merge_block)[0];
        Ok(CompiledValue {
            value: result,
            ty: cranelift_type,
            vole_type: result_vole_type,
        })
    }

    pub fn field_assign(
        &mut self,
        object: &Expr,
        field: Symbol,
        value_expr: &Expr,
    ) -> Result<CompiledValue, String> {
        let obj = self.expr(object)?;
        let value = self.expr(value_expr)?;

        let (slot, field_type) = get_field_slot_and_type(&obj.vole_type, field, self.ctx)?;
        let value = if matches!(field_type, Type::Interface(_)) {
            crate::codegen::interface_vtable::box_interface_value(
                self.builder,
                self.ctx,
                value,
                &field_type,
            )?
        } else {
            value
        };

        let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
        let store_value = convert_to_i64_for_storage(self.builder, &value);

        self.call_runtime_void(
            RuntimeFn::InstanceSetField,
            &[obj.value, slot_val, store_value],
        )?;

        Ok(value)
    }

    /// Handle property-style method calls (e.g., `s.length` -> `s.length()`)
    /// This is called when sema resolved a field access as a zero-arg method call.
    fn property_style_method_call(
        &mut self,
        obj: &CompiledValue,
        method_sym: Symbol,
        _expr_id: NodeId,
        resolved: &ResolvedMethod,
    ) -> Result<CompiledValue, String> {
        let method_name_str = self.ctx.interner.resolve(method_sym);
        let method_id = method_name_id(self.ctx.analyzed, self.ctx.interner, method_sym)
            .ok_or_else(|| {
                format!(
                    "codegen error: method name not interned (method: {})",
                    method_name_str
                )
            })?;

        let display_type_symbol = |sym: Symbol| {
            self.ctx
                .type_metadata
                .get(&sym)
                .and_then(|meta| match &meta.vole_type {
                    Type::Class(class_type) => Some(class_type.name_id),
                    Type::Record(record_type) => Some(record_type.name_id),
                    _ => None,
                })
                .map(|name_id| {
                    self.ctx
                        .analyzed
                        .name_table
                        .display(name_id, self.ctx.interner)
                })
                .unwrap_or_else(|| self.ctx.interner.resolve(sym).to_string())
        };

        let target = resolve_method_target(MethodResolutionInput {
            analyzed: self.ctx.analyzed,
            type_metadata: self.ctx.type_metadata,
            impl_method_infos: self.ctx.impl_method_infos,
            method_name_str,
            object_type: &obj.vole_type,
            method_id,
            resolution: Some(resolved),
            display_type_symbol,
        })?;

        let (method_info, return_type) = match target {
            MethodTarget::External {
                external_info,
                return_type,
            } => {
                // Call external method with receiver as first argument (no other args for property)
                let args = vec![obj.value];
                return self.call_external(&external_info, &args, &return_type);
            }
            MethodTarget::Direct {
                method_info,
                return_type,
            }
            | MethodTarget::Implemented {
                method_info,
                return_type,
            }
            | MethodTarget::Default {
                method_info,
                return_type,
            } => (method_info, return_type),
            MethodTarget::FunctionalInterface { .. } | MethodTarget::InterfaceDispatch { .. } => {
                return Err(CodegenError::unsupported(
                    "property-style access for interface methods",
                )
                .into());
            }
        };

        let method_func_ref = self.func_ref(method_info.func_key)?;

        // For property-style method calls, the only argument is the receiver
        let args = vec![obj.value];
        let call = self.builder.ins().call(method_func_ref, &args);
        let results = self.builder.inst_results(call);

        if results.is_empty() {
            Ok(self.void_value())
        } else {
            Ok(CompiledValue {
                value: results[0],
                ty: type_to_cranelift(&return_type, self.ctx.pointer_type),
                vole_type: return_type,
            })
        }
    }
}
