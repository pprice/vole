// src/codegen/structs/access.rs

use super::helpers::{convert_to_i64_for_storage, get_field_slot_and_type_id_cg, reconstruct_i128};
use crate::RuntimeKey;
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::{CompiledValue, RcLifecycle, module_name_id};
use cranelift::prelude::*;
use vole_frontend::{Expr, FieldAccessExpr, NodeId, OptionalChainExpr, Symbol};
use vole_sema::type_arena::TypeId;
use vole_sema::types::ConstantValue;

impl Cg<'_, '_, '_> {
    /// Convenience wrapper: compute struct field byte offset, panicking on invalid types.
    pub(super) fn struct_field_byte_offset(&self, type_id: TypeId, slot: usize) -> i32 {
        super::helpers::struct_field_byte_offset(type_id, slot, self.arena(), self.registry())
            .expect("INTERNAL: struct field offset must be computable for valid struct type")
    }

    #[tracing::instrument(skip(self, fa), fields(field = %self.interner().resolve(fa.field)))]
    pub fn field_access(&mut self, fa: &FieldAccessExpr) -> CodegenResult<CompiledValue> {
        let obj = self.expr(&fa.object)?;

        let module_info = {
            let arena = self.arena();
            arena.unwrap_module(obj.type_id).map(|m| {
                let exports = m.exports.clone();
                (m.module_id, exports)
            })
        };
        if let Some((module_id, exports)) = module_info {
            tracing::trace!(?module_id, "field access on module");
            let field_name = self.interner().resolve(fa.field);
            let module_path = self.name_table().module_path(module_id).to_string();
            let name_id = module_name_id(self.analyzed(), module_id, field_name);

            // Look up constant value in module metadata
            let const_val = {
                let arena = self.arena();
                name_id.and_then(|nid| {
                    arena
                        .module_metadata(module_id)
                        .and_then(|meta| meta.constants.get(&nid).cloned())
                })
            };
            if let Some(const_val) = const_val {
                let arena = self.arena();
                let f64_id = arena.f64();
                let i64_id = arena.i64();
                let bool_id = arena.bool();
                return match const_val {
                    ConstantValue::F64(v) => {
                        let val = self.builder.ins().f64const(v);
                        Ok(CompiledValue::new(val, types::F64, f64_id))
                    }
                    ConstantValue::I64(v) => {
                        let val = self.builder.ins().iconst(types::I64, v);
                        Ok(CompiledValue::new(val, types::I64, i64_id))
                    }
                    ConstantValue::Bool(v) => {
                        let val = self.builder.ins().iconst(types::I8, if v { 1 } else { 0 });
                        Ok(CompiledValue::new(val, types::I8, bool_id))
                    }
                    ConstantValue::String(s) => self.string_literal(&s),
                };
            }

            // Check if it's an export (function or other)
            let export_type_id = name_id
                .and_then(|nid| exports.iter().find(|(n, _)| *n == nid).map(|(_, tid)| *tid));
            if let Some(export_type_id) = export_type_id {
                let is_function = self.arena().is_function(export_type_id);
                if is_function {
                    return Err(CodegenError::unsupported_with_context(
                        "function as field value",
                        format!("use {}() to call the function", field_name),
                    ));
                }

                // Sentinel exports are zero-field structs - emit i8(0)
                if self.arena().is_sentinel(export_type_id) {
                    let value = self.builder.ins().iconst(types::I8, 0);
                    return Ok(CompiledValue::new(value, types::I8, export_type_id));
                }

                return Err(CodegenError::unsupported_with_context(
                    "non-constant module export",
                    format!("{} cannot be accessed at compile time", field_name),
                ));
            }

            return Err(CodegenError::not_found(
                "module export",
                format!("{}.{}", module_path, field_name),
            ));
        }

        // Non-module field access - use TypeId-based helpers
        let field_name = self.interner().resolve(fa.field);
        let (slot, field_type_id) = get_field_slot_and_type_id_cg(obj.type_id, field_name, self)?;

        self.extract_field(obj, slot, field_type_id)
    }

    /// Extract a field from a container object, handling struct/instance dispatch
    /// and RC cleanup. If the container is an owned RC temporary, the field is
    /// rc_inc'd (if RC) and the container is rc_dec'd so intermediate objects
    /// don't leak.
    fn extract_field(
        &mut self,
        obj: CompiledValue,
        slot: usize,
        field_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Struct types are stack-allocated: load field directly from pointer + offset
        let is_struct = self.arena().is_struct(obj.type_id);
        if is_struct {
            return self.struct_field_load(obj.value, slot, field_type_id, obj.type_id);
        }

        // i128 fields use 2 consecutive slots - load both and reconstruct
        let is_wide = crate::types::is_wide_type(field_type_id, self.arena());
        let mut cv = if is_wide {
            let get_func_ref = self.runtime_func_ref(RuntimeKey::InstanceGetField)?;
            let wide_i128 =
                super::helpers::load_wide_field(self.builder, get_func_ref, obj.value, slot);
            if field_type_id == self.arena().f128() {
                let value = self
                    .builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), wide_i128);
                CompiledValue::new(value, types::F128, field_type_id)
            } else {
                CompiledValue::new(wide_i128, types::I128, field_type_id)
            }
        } else {
            let result_raw = self.get_field_cached(obj.value, slot as u32)?;
            self.convert_field_value(result_raw, field_type_id)
        };

        // If the object is an owned RC temporary (e.g., method call result used
        // inline: `obj.method().field`), we must clean it up after extracting
        // the field. If the field itself is RC, we must rc_inc it first so the
        // field value survives the container's rc_dec (which may free the container
        // and cascade to its fields).
        if obj.is_owned() && self.rc_state(obj.type_id).needs_cleanup() {
            if self.rc_state(field_type_id).needs_cleanup() {
                self.emit_rc_inc_for_type(cv.value, field_type_id)?;
                // The field is now an owned reference (we inc'd it out of the container)
                cv.rc_lifecycle = RcLifecycle::Owned;
            }
            self.emit_rc_dec_for_type(obj.value, obj.type_id)?;
        } else {
            self.mark_borrowed_if_rc(&mut cv);
        }

        Ok(cv)
    }

    pub fn optional_chain(
        &mut self,
        oc: &OptionalChainExpr,
        expr_id: NodeId,
    ) -> CodegenResult<CompiledValue> {
        let obj = self.expr(&oc.object)?;

        // The object should be an optional type (union with nil)
        let (_variants, nil_tag, inner_type_id) = {
            let arena = self.arena();
            let variants = arena.unwrap_union(obj.type_id).ok_or_else(|| {
                CodegenError::type_mismatch("optional chain", "optional type", "non-optional")
            })?;
            let nil_id = arena.nil();
            let nil_tag = variants
                .iter()
                .position(|&v| v == nil_id)
                .expect("INTERNAL: optional type must have nil variant");
            let inner_type_id = arena.unwrap_optional(obj.type_id).ok_or_else(|| {
                CodegenError::type_mismatch(
                    "optional chain",
                    "optional type",
                    "union without inner type",
                )
            })?;
            (variants.clone(), nil_tag, inner_type_id)
        };

        // Check if object is nil by reading the tag
        let is_nil = self.tag_eq(obj.value, nil_tag as i64);

        // Create blocks for branching
        let nil_block = self.builder.create_block();
        let not_nil_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        // Get the field type from the inner type using TypeId-based helper
        let field_name = self.interner().resolve(oc.field);
        let (slot, field_type_id) = get_field_slot_and_type_id_cg(inner_type_id, field_name, self)?;

        // Get result type from sema (already computed as Optional<T> or T if T is already optional)
        // Sema handles the double-wrapping logic in check_optional_chain_expr
        let result_type_id = self
            .get_expr_type(&expr_id)
            .expect("INTERNAL: optional_chain: sema did not record expression type");
        let is_field_optional = self.arena().is_optional(field_type_id);

        let cranelift_type = {
            let arena = self.arena();
            crate::types::type_id_to_cranelift(result_type_id, arena, self.ptr_type())
        };
        self.builder.append_block_param(merge_block, cranelift_type);

        self.builder
            .ins()
            .brif(is_nil, nil_block, &[], not_nil_block, &[]);

        // Nil block: return nil wrapped in the optional type
        self.switch_and_seal(nil_block);
        let nil_val = self.nil_value();
        let nil_union = self.construct_union_id(nil_val, result_type_id)?;
        self.builder
            .ins()
            .jump(merge_block, &[nil_union.value.into()]);

        // Not-nil block: do field access and wrap result in optional
        self.switch_and_seal(not_nil_block);

        // Load the actual object from the union payload (offset 8)
        // Only load if union has payload data.
        // Sentinel-only unions have union_size == 8 (tag only), no payload to read.
        let inner_cranelift_type = {
            let arena = self.arena();
            crate::types::type_id_to_cranelift(inner_type_id, arena, self.ptr_type())
        };
        let inner_obj = self.load_union_payload(obj.value, obj.type_id, inner_cranelift_type);

        // Construct a CompiledValue for the inner object with lifecycle
        // inherited from the original optional. When the optional is
        // borrowed (e.g. from a variable with union scope cleanup), the
        // inner object is also borrowed — scope cleanup handles the dec.
        // When the optional is a temporary (lifecycle None — e.g. result
        // of a prior optional chain like `c?.ceo`), and the inner type
        // needs RC, mark it as Owned so extract_field will rc_inc the
        // field and rc_dec this container, preventing the leak.
        let inner_cv = {
            let needs_rc = self.rc_state(inner_type_id).needs_cleanup();
            let mut cv = CompiledValue::new(inner_obj, inner_cranelift_type, inner_type_id);
            if obj.is_owned() || (!obj.is_borrowed() && needs_rc) {
                cv.rc_lifecycle = RcLifecycle::Owned;
            }
            cv
        };

        // Extract field with RC cleanup (rc_inc field + rc_dec container if owned)
        let field_compiled = self.extract_field(inner_cv, slot, field_type_id)?;

        // Wrap the field value in an optional (using construct_union_id)
        // But if field type is already optional, it's already a union - just use it directly
        let final_value = if is_field_optional {
            // Field is already optional, use as-is
            field_compiled
        } else {
            // Wrap non-optional field in optional
            self.construct_union_id(field_compiled, result_type_id)?
        };
        self.builder
            .ins()
            .jump(merge_block, &[final_value.value.into()]);

        // Merge block
        self.switch_and_seal(merge_block);

        let result = self.builder.block_params(merge_block)[0];
        let mut cv = CompiledValue::new(result, cranelift_type, result_type_id);
        self.mark_borrowed_if_rc(&mut cv);
        Ok(cv)
    }

    pub fn field_assign(
        &mut self,
        object: &Expr,
        field: Symbol,
        value_expr: &Expr,
    ) -> CodegenResult<CompiledValue> {
        let obj = self.expr(object)?;
        let value = self.expr(value_expr)?;

        let field_name = self.interner().resolve(field);
        let (slot, field_type_id) = get_field_slot_and_type_id_cg(obj.type_id, field_name, self)?;

        // Struct types: store directly to pointer + offset
        let is_struct = self.arena().is_struct(obj.type_id);
        if is_struct {
            let offset = self.struct_field_byte_offset(obj.type_id, slot);

            // If assigning a nested struct, copy all flat slots inline
            let nested_flat = {
                let arena = self.arena();
                let entities = self.registry();
                super::helpers::struct_flat_slot_count(value.type_id, arena, entities)
            };
            if let Some(nested_flat) = nested_flat {
                for i in 0..nested_flat {
                    let src_off = (i as i32) * 8;
                    let dst_off = offset + src_off;
                    let val =
                        self.builder
                            .ins()
                            .load(types::I64, MemFlags::new(), value.value, src_off);
                    self.builder
                        .ins()
                        .store(MemFlags::new(), val, obj.value, dst_off);
                }
            } else {
                // RC bookkeeping for struct field overwrite:
                // 1. Load old value (before store)
                // 2. rc_inc new if it's a borrow
                // 3. Store new value
                // 4. rc_dec old (after store, in case old == new)
                let rc_old = if self.rc_scopes.has_active_scope()
                    && self.rc_state(field_type_id).needs_cleanup()
                {
                    Some(
                        self.builder
                            .ins()
                            .load(types::I64, MemFlags::new(), obj.value, offset),
                    )
                } else {
                    None
                };
                if rc_old.is_some() && value.is_borrowed() {
                    self.emit_rc_inc_for_type(value.value, field_type_id)?;
                }
                if value.ty == types::I128 || value.ty == types::F128 {
                    // Wide types need 2 x 8-byte stores (low then high).
                    let wide = if value.ty == types::F128 {
                        self.builder
                            .ins()
                            .bitcast(types::I128, MemFlags::new(), value.value)
                    } else {
                        value.value
                    };
                    let (low, high) = super::helpers::split_i128_for_storage(self.builder, wide);
                    self.builder
                        .ins()
                        .store(MemFlags::new(), low, obj.value, offset);
                    self.builder
                        .ins()
                        .store(MemFlags::new(), high, obj.value, offset + 8);
                } else {
                    let store_value = convert_to_i64_for_storage(self.builder, &value);
                    self.builder
                        .ins()
                        .store(MemFlags::new(), store_value, obj.value, offset);
                }
                if let Some(old_val) = rc_old {
                    self.emit_rc_dec_for_type(old_val, field_type_id)?;
                }
            }
            // The assignment consumed the temp — ownership transfers
            // to the struct field; the struct's cleanup handles the dec.
            let mut value = value;
            value.mark_consumed();
            value.debug_assert_rc_handled("struct field assign (stack)");
            return Ok(value);
        }

        let value = if self.arena().is_interface(field_type_id) {
            self.box_interface_value(value, field_type_id)?
        } else {
            value
        };

        // RC bookkeeping for instance field overwrite:
        // 1. Load old value (before store) via InstanceGetField
        // 2. rc_inc new if it's a borrow
        // 3. Store new value
        // 4. rc_dec old (after store, in case old == new)
        let rc_old =
            if self.rc_scopes.has_active_scope() && self.rc_state(field_type_id).needs_cleanup() {
                let get_func_ref = self.runtime_func_ref(RuntimeKey::InstanceGetField)?;
                let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
                let call = self
                    .builder
                    .ins()
                    .call(get_func_ref, &[obj.value, slot_val]);
                Some(self.builder.inst_results(call)[0])
            } else {
                None
            };
        if rc_old.is_some() && value.is_borrowed() {
            self.emit_rc_inc_for_type(value.value, field_type_id)?;
        }

        // Store field value, handling i128 which needs 2 slots
        let set_func_ref = self.runtime_func_ref(RuntimeKey::InstanceSetField)?;
        super::helpers::store_field_value(self.builder, set_func_ref, obj.value, slot, &value);
        self.field_cache.clear(); // Invalidate cached field reads

        if let Some(old_val) = rc_old {
            self.emit_rc_dec_for_type(old_val, field_type_id)?;
        }

        // The assignment consumed the temp — ownership transfers
        // to the instance field; the instance's cleanup handles the dec.
        let mut value = value;
        value.mark_consumed();
        value.debug_assert_rc_handled("instance field assign");
        Ok(value)
    }

    /// Load a field from a struct pointer at the given slot.
    /// Uses flat layout: nested struct fields are stored inline and
    /// field offsets account for variable-size preceding fields.
    pub fn struct_field_load(
        &mut self,
        struct_ptr: Value,
        slot: usize,
        field_type_id: TypeId,
        parent_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        // Compute byte offset accounting for nested struct sizes
        let offset = self.struct_field_byte_offset(parent_type_id, slot);

        // If the field is itself a struct, return a pointer into the parent data
        let is_nested_struct = self.arena().is_struct(field_type_id);
        if is_nested_struct {
            let ptr_type = self.ptr_type();
            // iadd_imm to compute pointer into the parent struct's inline data
            let field_ptr = if offset == 0 {
                struct_ptr
            } else {
                self.builder.ins().iadd_imm(struct_ptr, offset as i64)
            };
            return Ok(CompiledValue::new(field_ptr, ptr_type, field_type_id));
        }

        // i128 fields occupy 2 x 8-byte slots: load low and high halves, reconstruct
        let is_wide = {
            let arena = self.arena();
            crate::types::is_wide_type(field_type_id, arena)
        };
        if is_wide {
            let low = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), struct_ptr, offset);
            let high = self
                .builder
                .ins()
                .load(types::I64, MemFlags::new(), struct_ptr, offset + 8);
            let wide_i128 = reconstruct_i128(self.builder, low, high);
            if field_type_id == self.arena().f128() {
                let value = self
                    .builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), wide_i128);
                return Ok(CompiledValue::new(value, types::F128, field_type_id));
            }
            return Ok(CompiledValue::new(wide_i128, types::I128, field_type_id));
        }

        // Non-struct field: load as i64, then convert to proper type
        let raw_value = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), struct_ptr, offset);
        let mut cv = self.convert_field_value(raw_value, field_type_id);
        self.mark_borrowed_if_rc(&mut cv);
        Ok(cv)
    }
}
