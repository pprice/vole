// src/codegen/structs/literals.rs

use std::collections::{HashMap, HashSet};

use rustc_hash::FxHashMap;

use super::helpers::{convert_to_i64_for_storage, store_field_value};
use crate::RuntimeFn;
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::types::CompiledValue;
use cranelift::prelude::*;
use cranelift_codegen::ir::StackSlot;
use vole_frontend::{Decl, Expr, FieldDef, Program, StructLiteralExpr, Symbol};
use vole_sema::entity_defs::TypeDefKind;
use vole_sema::type_arena::TypeId;

/// Find the field definitions for a type by looking up the class declaration in the program.
/// For qualified paths, only the last segment (the type name) is used to find the declaration.
fn find_type_fields(program: &Program, type_name: Symbol) -> Option<&[FieldDef]> {
    for decl in &program.declarations {
        match decl {
            Decl::Class(class) if class.name == type_name => return Some(&class.fields),
            Decl::Struct(s) if s.name == type_name => return Some(&s.fields),
            _ => {}
        }
    }
    None
}

/// Format a struct literal path as a dot-separated string for error messages
fn format_path(path: &[Symbol], interner: &vole_frontend::Interner) -> String {
    path.iter()
        .map(|s| interner.resolve(*s))
        .collect::<Vec<_>>()
        .join(".")
}

impl Cg<'_, '_, '_> {
    pub fn struct_literal(
        &mut self,
        sl: &StructLiteralExpr,
        expr: &Expr,
    ) -> CodegenResult<CompiledValue> {
        // Get the resolved type from semantic analysis, which handles:
        // - Simple types like `Point`
        // - Module-qualified types like `time.Duration`
        // - Generic instantiation
        let path_str = format_path(&sl.path, self.interner());

        // Resolve the TypeDefId. Prefer the semantic analysis type (handles shadowing,
        // generic instantiation, module-qualified paths). Fall back to string-based
        // resolution for consistency across multiple file compilations.
        let type_def_id = self
            .get_expr_type(&expr.id)
            .and_then(|expr_type_id| {
                let arena = self.arena();
                if let Some((id, _)) = arena.unwrap_class(expr_type_id) {
                    Some(id)
                } else if let Some((id, _)) = arena.unwrap_struct(expr_type_id) {
                    Some(id)
                } else {
                    None
                }
            })
            .or_else(|| {
                if sl.path.len() == 1 {
                    // Simple type name - use string-based resolution as fallback
                    let type_name = self.interner().resolve(sl.path[0]);
                    let query = self.query();
                    // Use current module (for imported modules) or program module (for main program)
                    let module_id = self
                        .current_module_id()
                        .unwrap_or(self.env.analyzed.module_id);
                    let mut resolved_id = query.resolve_type_def_by_str(module_id, type_name);

                    // If this is a type alias, resolve through to the underlying type
                    if let Some(def_id) = resolved_id {
                        let type_def = query.registry().get_type(def_id);
                        if type_def.kind == TypeDefKind::Alias
                            && let Some(aliased_type_id) = type_def.aliased_type
                        {
                            let arena = self.arena();
                            // Get the underlying TypeDefId from the aliased type
                            if let Some((underlying_id, _)) = arena.unwrap_class(aliased_type_id) {
                                resolved_id = Some(underlying_id);
                            } else if let Some((underlying_id, _)) =
                                arena.unwrap_struct(aliased_type_id)
                            {
                                resolved_id = Some(underlying_id);
                            }
                        }
                    }
                    resolved_id
                } else {
                    None
                }
            })
            .ok_or_else(|| format!("Unknown type: {} (not in entity registry)", path_str))?;

        // Sentinels (e.g. Done, nil) are zero-field structs represented as i8(0).
        // They may not be in type_metadata if they come from prelude modules,
        // so handle them early before the metadata lookup.
        {
            let kind = self.registry().type_kind(type_def_id);
            if kind == TypeDefKind::Sentinel {
                let sentinel_type_id = self.get_expr_type(&expr.id).unwrap_or_else(|| {
                    // Fall back to the base TypeId from entity registry, or type_metadata
                    self.registry()
                        .get_type(type_def_id)
                        .base_type_id
                        .or_else(|| self.type_metadata().get(&type_def_id).map(|m| m.vole_type))
                        .unwrap_or(TypeId::NIL)
                });
                let value = self.builder.ins().iconst(types::I8, 0);
                return Ok(CompiledValue::new(value, types::I8, sentinel_type_id));
            }
        }

        let metadata = self
            .type_metadata()
            .get(&type_def_id)
            .ok_or_else(|| format!("Unknown type: {} (not in type_metadata)", path_str))?;

        // Check if this is a struct type (stack-allocated value type)
        let is_struct_type = {
            let kind = self.registry().type_kind(type_def_id);
            kind == TypeDefKind::Struct
        };

        if is_struct_type {
            let result_type_id = self.get_expr_type(&expr.id).unwrap_or(metadata.vole_type);
            let field_slots = metadata.field_slots.clone();
            return self.struct_value_literal(
                sl,
                &field_slots,
                result_type_id,
                &path_str,
                type_def_id,
            );
        }

        let base_type_id = metadata.type_id;
        let field_count = metadata.physical_slot_count as u32;
        // Prefer the type from semantic analysis (handles generic instantiation, module-aware)
        let result_type_id = self.get_expr_type(&expr.id).unwrap_or(metadata.vole_type);
        // In monomorphized contexts, result_type_id may contain unsubstituted type params
        // (e.g., Entry<K> instead of Entry<i64>). Substitute to get the concrete type so
        // downstream code (union variant matching, etc.) sees the correct type.
        let result_type_id = self.try_substitute_type(result_type_id);
        let field_slots = metadata.field_slots.clone();

        // For generic class instances, resolve a monomorphized type_id with correct
        // field type tags for RC cleanup. This ensures instance_drop properly rc_dec's
        // fields that are RC types after type parameter substitution.
        //
        // When inside a monomorphized function, get_expr_type may return a concrete type
        // from a different instantiation (since all instantiations share the same AST).
        // We reconstruct the correct concrete type by substituting the class's type args
        // using the current function's substitutions.
        let type_id = if let Some(subs) = self.substitutions {
            // In a monomorphized context, get_expr_type may return a concrete type
            // from a different instantiation (since all share the same AST).
            // We compute the correct concrete type args by looking up each class
            // type parameter in the current function's substitution map.
            let type_def = self.query().get_type(type_def_id);
            if let Some(generic_info) = &type_def.generic_info {
                if !generic_info.type_params.is_empty() {
                    let concrete_args: Vec<_> = generic_info
                        .type_params
                        .iter()
                        .filter_map(|tp| subs.get(&tp.name_id).copied())
                        .collect();
                    if concrete_args.len() == generic_info.type_params.len() {
                        self.mono_instance_type_id_with_args(
                            base_type_id,
                            type_def_id,
                            concrete_args,
                        )
                    } else {
                        // Not all type params found in substitutions - class type params
                        // don't match function type params. Fall back to result_type_id.
                        // But first try substituting result_type_id's type args through
                        // the function's substitution map to get correct concrete args.
                        let result_type_id = self.substitute_type(result_type_id);
                        self.mono_instance_type_id(base_type_id, result_type_id)
                    }
                } else {
                    base_type_id
                }
            } else {
                base_type_id
            }
        } else {
            self.mono_instance_type_id(base_type_id, result_type_id)
        };

        let type_id_val = self.builder.ins().iconst(types::I32, type_id as i64);
        let field_count_val = self.builder.ins().iconst(types::I32, field_count as i64);
        let runtime_type = self.builder.ins().iconst(types::I32, 7); // TYPE_INSTANCE

        let instance_ptr = self.call_runtime(
            RuntimeFn::InstanceNew,
            &[type_id_val, field_count_val, runtime_type],
        )?;

        let set_func_ref = self.runtime_func_ref(RuntimeFn::InstanceSetField)?;

        // Get field types for wrapping optional values using arena methods
        let field_types: HashMap<String, TypeId> = {
            let arena = self.arena();
            let type_def_id = arena.unwrap_class(result_type_id).map(|(id, _)| id);

            if let Some(type_def_id) = type_def_id {
                let type_def = self.query().get_type(type_def_id);
                if let Some(generic_info) = &type_def.generic_info {
                    generic_info
                        .field_names
                        .iter()
                        .zip(generic_info.field_types.iter())
                        .map(|(name_id, ty_id)| {
                            (
                                self.name_table()
                                    .last_segment_str(*name_id)
                                    .unwrap_or_default(),
                                *ty_id,
                            )
                        })
                        .collect()
                } else {
                    HashMap::new()
                }
            } else {
                HashMap::new()
            }
        };

        // Collect names of fields that were explicitly provided in the struct literal
        let provided_fields: HashSet<String> = sl
            .fields
            .iter()
            .map(|init| self.interner().resolve(init.name).to_string())
            .collect();

        // Compile explicitly provided fields
        for init in &sl.fields {
            let init_name = self.interner().resolve(init.name);
            let slot = *field_slots
                .get(init_name)
                .ok_or_else(|| format!("Unknown field: {} in type {}", init_name, path_str))?;

            let mut value = self.expr(&init.value)?;

            // RC: inc borrowed field values (e.g., reading from a variable) so the
            // instance gets its own reference. instance_drop will rc_dec these fields
            // when the instance refcount reaches zero.
            // Skip union types: union fields are copied to new heap buffers below
            // (via copy_union_to_heap / construct_union_heap_id), which handle
            // RC-incrementing the payload. The union buffer itself is not RC-managed.
            if self.rc_scopes.has_active_scope()
                && self.rc_state(value.type_id).needs_cleanup()
                && value.is_borrowed()
                && !self.arena().is_union(value.type_id)
            {
                self.emit_rc_inc_for_type(value.value, value.type_id)?;
            }
            // The field value is consumed into the instance.
            value.mark_consumed();

            // If field type is optional (union) and value type is not a union, wrap it
            // Use heap allocation for unions stored in class fields since stack slots
            // don't persist beyond the current function's stack frame
            let final_value = if let Some(&field_type_id) = field_types.get(init_name) {
                let arena = self.arena();
                let field_is_union = arena.is_union(field_type_id);
                let field_is_interface = arena.is_interface(field_type_id);
                let value_is_union = arena.is_union(value.type_id);

                if field_is_union && !value_is_union {
                    self.construct_union_heap_id(value, field_type_id)?
                } else if field_is_union && value_is_union {
                    // Union value stored in class field must be heap-allocated.
                    // The value may be stack-allocated (from construct_union_id),
                    // so copy the 16-byte buffer to the heap.
                    self.copy_union_to_heap(value)?
                } else if field_is_interface && arena.is_interface(value.type_id) {
                    // Value is already an interface fat pointer. Copy it into a new
                    // heap allocation so instance_drop can free it independently.
                    self.copy_interface_fat_ptr(value)?
                } else if field_is_interface {
                    self.box_interface_value(value, field_type_id)?
                } else {
                    value
                }
            } else {
                value
            };

            store_field_value(self.builder, set_func_ref, instance_ptr, slot, &final_value);
        }

        // Handle omitted fields with default values
        // Look up the original type declaration to get default expressions
        // We use raw pointers to the original AST to avoid cloning, which would
        // invalidate string literal pointers during JIT execution.
        // For qualified paths, we need the type name (last segment) for looking up field declarations
        let type_name = sl.path.last().copied();
        let field_default_ptrs = if let Some(type_name) = type_name {
            self.collect_field_default_ptrs(type_name, &provided_fields, type_def_id)
        } else {
            Vec::new()
        };

        for (field_name, default_expr_ptr) in field_default_ptrs {
            let slot = *field_slots.get(&field_name).ok_or_else(|| {
                format!(
                    "Unknown field: {} in type {} (default)",
                    field_name, path_str
                )
            })?;

            // SAFETY: The pointer points to an Expr in the original AST (either main Program
            // or a module Program), both owned by AnalyzedProgram. Since AnalyzedProgram
            // outlives this entire compilation, the pointer remains valid.
            let default_expr: &Expr = unsafe { &*default_expr_ptr };

            // Compile the default expression
            let value = self.expr(default_expr)?;

            // If field type is optional (union) and value type is not a union, wrap it
            let final_value = if let Some(&field_type_id) = field_types.get(&field_name) {
                let arena = self.arena();
                let field_is_union = arena.is_union(field_type_id);
                let field_is_interface = arena.is_interface(field_type_id);
                let value_is_union = arena.is_union(value.type_id);

                if field_is_union && !value_is_union {
                    self.construct_union_heap_id(value, field_type_id)?
                } else if field_is_union && value_is_union {
                    self.copy_union_to_heap(value)?
                } else if field_is_interface && arena.is_interface(value.type_id) {
                    // Value is already an interface fat pointer. Copy it into a new
                    // heap allocation so instance_drop can free it independently.
                    self.copy_interface_fat_ptr(value)?
                } else if field_is_interface {
                    self.box_interface_value(value, field_type_id)?
                } else {
                    value
                }
            } else {
                value
            };

            store_field_value(self.builder, set_func_ref, instance_ptr, slot, &final_value);
        }

        Ok(CompiledValue::new(
            instance_ptr,
            self.ptr_type(),
            result_type_id,
        ))
    }

    /// Collect raw pointers to default expressions for omitted fields in a struct literal.
    /// Returns Vec of (field_name, raw_pointer_to_expression) pairs for fields that have
    /// defaults but were not provided in the struct literal.
    ///
    /// # Safety
    /// The returned raw pointers are valid for the lifetime of AnalyzedProgram, which
    /// owns both the main Program and all module Programs. Since AnalyzedProgram outlives
    /// all compilation, these pointers remain valid during struct literal compilation.
    fn collect_field_default_ptrs(
        &self,
        type_name: Symbol,
        provided_fields: &HashSet<String>,
        type_def_id: vole_identity::TypeDefId,
    ) -> Vec<(String, *const Expr)> {
        let mut defaults = Vec::new();

        // Get the type definition to find out which module it's in
        let type_def = self.query().get_type(type_def_id);
        let type_module = type_def.module;

        // Get the program module (the module of the file being compiled).
        // Types defined in the main program are registered with program_module(),
        // which may differ from main_module() when using shared caches.
        let program_module = self.env.analyzed.module_id;

        if type_module == program_module {
            // Type is in the main program - search there
            if let Some(fields) = find_type_fields(&self.analyzed().program, type_name) {
                for field in fields {
                    let field_name = self.interner().resolve(field.name).to_string();
                    if !provided_fields.contains(&field_name)
                        && let Some(default_value) = &field.default_value
                    {
                        // Store raw pointer to the original expression
                        defaults.push((field_name, default_value.as_ref() as *const Expr));
                    }
                }
            }
        } else {
            // Type is in a module - find the module path and search there
            let module_path = self.name_table().module_path(type_module).to_string();
            if let Some((program, module_interner)) =
                self.analyzed().module_programs.get(&module_path)
            {
                // Get the type name in the module's interner
                let type_name_str = self.interner().resolve(type_name);
                if let Some(module_type_sym) = module_interner.lookup(type_name_str)
                    && let Some(fields) = find_type_fields(program, module_type_sym)
                {
                    for field in fields {
                        let field_name = module_interner.resolve(field.name).to_string();
                        if !provided_fields.contains(&field_name)
                            && let Some(default_value) = &field.default_value
                        {
                            // Store raw pointer to the original expression
                            defaults.push((field_name, default_value.as_ref() as *const Expr));
                        }
                    }
                }
            }
        }

        defaults
    }

    /// Construct a union value on the heap (for storing in class fields).
    /// Unlike the stack-based construct_union_id, this allocates on the heap so the
    /// union persists beyond the current function's stack frame.
    pub(crate) fn construct_union_heap_id(
        &mut self,
        value: CompiledValue,
        union_type_id: TypeId,
    ) -> CodegenResult<CompiledValue> {
        let arena = self.arena();
        let variants = arena.unwrap_union(union_type_id).ok_or_else(|| {
            CodegenError::type_mismatch("union construction", "union type", "non-union")
        })?;
        let variants = variants.clone();

        // If the value is already the same union type, just return it
        if value.type_id == union_type_id {
            return Ok(value);
        }

        // Find the tag for the value type
        let tag = variants
            .iter()
            .position(|&v| v == value.type_id)
            .ok_or_else(|| {
                let expected = variants
                    .iter()
                    .map(|&variant| self.arena().display_basic(variant))
                    .collect::<Vec<_>>()
                    .join(" | ");
                let found = self.arena().display_basic(value.type_id);
                CodegenError::type_mismatch(
                    "union variant",
                    format!("compatible type ({expected})"),
                    found,
                )
            })?;

        // Get heap_alloc function ref
        let heap_alloc_ref = self.runtime_func_ref(RuntimeFn::HeapAlloc)?;

        // Allocate union storage on the heap
        let ptr_type = self.ptr_type();
        let union_size = self.type_size(union_type_id);
        let size_val = self.builder.ins().iconst(ptr_type, union_size as i64);
        let alloc_call = self.builder.ins().call(heap_alloc_ref, &[size_val]);
        let heap_ptr = self.builder.inst_results(alloc_call)[0];

        // Store tag at offset 0
        let tag_val = self.builder.ins().iconst(types::I8, tag as i64);
        self.builder
            .ins()
            .store(MemFlags::new(), tag_val, heap_ptr, 0);

        // Store is_rc flag at offset 1: 1 if the variant is RC-managed, 0 otherwise.
        // This flag is used by union_heap_cleanup to know whether to rc_dec the payload.
        let is_rc = self.rc_state(value.type_id).needs_cleanup();
        let is_rc_val = self.builder.ins().iconst(types::I8, is_rc as i64);
        self.builder
            .ins()
            .store(MemFlags::new(), is_rc_val, heap_ptr, 1);

        // Sentinel types (nil, Done, user-defined) have no payload - only the tag matters
        if !self.arena().is_sentinel(value.type_id) {
            self.builder
                .ins()
                .store(MemFlags::new(), value.value, heap_ptr, 8);
        }

        Ok(CompiledValue::new(heap_ptr, self.ptr_type(), union_type_id))
    }

    /// Copy a union value (possibly stack-allocated) to a heap-allocated buffer.
    ///
    /// Union buffers are 16 bytes: `[tag: i8, is_rc: i8, pad(6), payload: i64]`.
    /// Class fields with FieldTypeTag::UnionHeap expect heap-allocated buffers
    /// that will be freed by `union_heap_cleanup` during instance_drop.
    pub(crate) fn copy_union_to_heap(
        &mut self,
        value: CompiledValue,
    ) -> CodegenResult<CompiledValue> {
        let heap_alloc_ref = self.runtime_func_ref(RuntimeFn::HeapAlloc)?;
        let ptr_type = self.ptr_type();
        let union_size = self.type_size(value.type_id);
        let size_val = self.builder.ins().iconst(ptr_type, union_size as i64);
        let alloc_call = self.builder.ins().call(heap_alloc_ref, &[size_val]);
        let heap_ptr = self.builder.inst_results(alloc_call)[0];

        // Copy tag (offset 0) and is_rc (offset 1) as i16 for one load
        let tag_and_rc = self
            .builder
            .ins()
            .load(types::I16, MemFlags::new(), value.value, 0);
        self.builder
            .ins()
            .store(MemFlags::new(), tag_and_rc, heap_ptr, 0);

        // Copy payload (offset 8)
        let payload = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), value.value, 8);
        self.builder
            .ins()
            .store(MemFlags::new(), payload, heap_ptr, 8);

        // If the payload is RC-managed, increment its refcount since both the
        // original and the copy will need independent cleanup
        let is_rc = self
            .builder
            .ins()
            .load(types::I8, MemFlags::new(), value.value, 1);
        let is_rc_nonzero = self.builder.ins().icmp_imm(IntCC::NotEqual, is_rc, 0);
        let payload_nonzero = self.builder.ins().icmp_imm(IntCC::NotEqual, payload, 0);
        let needs_inc = self.builder.ins().band(is_rc_nonzero, payload_nonzero);

        let then_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder
            .ins()
            .brif(needs_inc, then_block, &[], merge_block, &[]);

        self.builder.switch_to_block(then_block);
        self.builder.seal_block(then_block);
        let rc_inc_ref = self.runtime_func_ref(RuntimeFn::RcInc)?;
        let payload_ptr = self
            .builder
            .ins()
            .bitcast(ptr_type, MemFlags::new(), payload);
        self.builder.ins().call(rc_inc_ref, &[payload_ptr]);
        self.builder.ins().jump(merge_block, &[]);

        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);

        Ok(CompiledValue::new(heap_ptr, ptr_type, value.type_id))
    }

    /// Copy an interface fat pointer into a new heap allocation.
    ///
    /// Interface fat pointers are 16-byte heap allocations: `[data_word, vtable_ptr]`.
    /// They have no RcHeader, so they cannot be shared between multiple owners.
    /// When storing an interface value into a class field, we must create an
    /// independent copy so that `instance_drop` can free it without invalidating
    /// the original pointer.
    ///
    /// Note: The caller is responsible for rc_inc'ing the data_word if the value
    /// is borrowed (the standard rc_inc at class literal field init handles this).
    pub(crate) fn copy_interface_fat_ptr(
        &mut self,
        value: CompiledValue,
    ) -> CodegenResult<CompiledValue> {
        let heap_alloc_ref = self.runtime_func_ref(RuntimeFn::HeapAlloc)?;
        let ptr_type = self.ptr_type();
        let word_bytes = ptr_type.bytes() as i64;

        // Allocate 16 bytes for [data_word, vtable_ptr]
        let size_val = self.builder.ins().iconst(ptr_type, word_bytes * 2);
        let alloc_call = self.builder.ins().call(heap_alloc_ref, &[size_val]);
        let heap_ptr = self.builder.inst_results(alloc_call)[0];

        // Copy data_word (offset 0)
        let data_word = self
            .builder
            .ins()
            .load(types::I64, MemFlags::new(), value.value, 0);
        self.builder
            .ins()
            .store(MemFlags::new(), data_word, heap_ptr, 0);

        // Copy vtable_ptr (offset 8)
        let vtable_ptr =
            self.builder
                .ins()
                .load(types::I64, MemFlags::new(), value.value, word_bytes as i32);
        self.builder
            .ins()
            .store(MemFlags::new(), vtable_ptr, heap_ptr, word_bytes as i32);

        Ok(CompiledValue::new(heap_ptr, ptr_type, value.type_id))
    }

    /// Compile a struct literal to a stack-allocated value.
    /// Nested struct fields are stored inline (all leaf fields flattened).
    fn struct_value_literal(
        &mut self,
        sl: &StructLiteralExpr,
        field_slots: &FxHashMap<String, usize>,
        result_type_id: TypeId,
        path_str: &str,
        type_def_id: vole_identity::TypeDefId,
    ) -> CodegenResult<CompiledValue> {
        // Use flat total size to account for nested struct fields
        let total_size = {
            let arena = self.arena();
            let entities = self.registry();
            super::helpers::struct_total_byte_size(result_type_id, arena, entities)
                .expect("INTERNAL: valid struct must have computable size")
        };

        // Allocate stack slot for the struct
        let slot = self.alloc_stack(total_size);

        // Compile and store each explicitly provided field
        for init in &sl.fields {
            let init_name = self.interner().resolve(init.name);
            let field_slot = *field_slots
                .get(init_name)
                .ok_or_else(|| format!("Unknown field: {} in type {}", init_name, path_str))?;

            let offset = {
                let arena = self.arena();
                let entities = self.registry();
                super::helpers::struct_field_byte_offset(
                    result_type_id,
                    field_slot,
                    arena,
                    entities,
                )
                .expect("INTERNAL: struct field offset must be computable for valid struct type")
            };

            let mut value = self.expr(&init.value)?;
            // RC: inc borrowed field values (e.g., reading from another struct's field)
            // so the new struct gets its own reference.
            if self.rc_scopes.has_active_scope()
                && self.rc_state(value.type_id).needs_cleanup()
                && value.is_borrowed()
            {
                self.emit_rc_inc_for_type(value.value, value.type_id)?;
            }
            self.store_struct_field(value, slot, offset)?;
            // The field value is consumed into the struct literal.
            value.mark_consumed();
            value.debug_assert_rc_handled("struct literal field");
        }

        // Handle omitted fields with default values
        let provided_fields: HashSet<String> = sl
            .fields
            .iter()
            .map(|init| self.interner().resolve(init.name).to_string())
            .collect();

        let type_name = sl.path.last().copied();
        let field_default_ptrs = if let Some(type_name) = type_name {
            self.collect_field_default_ptrs(type_name, &provided_fields, type_def_id)
        } else {
            Vec::new()
        };

        for (field_name, default_expr_ptr) in field_default_ptrs {
            let field_slot = *field_slots.get(&field_name).ok_or_else(|| {
                format!(
                    "Unknown field: {} in type {} (default)",
                    field_name, path_str
                )
            })?;

            let offset = {
                let arena = self.arena();
                let entities = self.registry();
                super::helpers::struct_field_byte_offset(
                    result_type_id,
                    field_slot,
                    arena,
                    entities,
                )
                .expect("INTERNAL: struct field offset must be computable for valid struct type")
            };

            // SAFETY: See collect_field_default_ptrs documentation
            let default_expr: &Expr = unsafe { &*default_expr_ptr };
            let value = self.expr(default_expr)?;
            self.store_struct_field(value, slot, offset)?;
        }

        // Return pointer to the struct
        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

        Ok(CompiledValue::new(ptr, ptr_type, result_type_id))
    }

    /// Store a value into a struct field's stack slot, handling nested structs and i128.
    fn store_struct_field(
        &mut self,
        value: CompiledValue,
        slot: StackSlot,
        offset: i32,
    ) -> CodegenResult<()> {
        let field_flat_slots = {
            let arena = self.arena();
            let entities = self.registry();
            super::helpers::struct_flat_slot_count(value.type_id, arena, entities)
        };
        if let Some(nested_flat) = field_flat_slots {
            for i in 0..nested_flat {
                let src_off = (i as i32) * 8;
                let dst_off = offset + src_off;
                let val =
                    self.builder
                        .ins()
                        .load(types::I64, MemFlags::new(), value.value, src_off);
                self.builder.ins().stack_store(val, slot, dst_off);
            }
        } else if value.ty == types::I128 {
            // i128 needs 2 x 8-byte slots: low 64 bits at offset, high 64 bits at offset+8
            let low = self.builder.ins().ireduce(types::I64, value.value);
            self.builder.ins().stack_store(low, slot, offset);
            let sixty_four_i64 = self.builder.ins().iconst(types::I64, 64);
            let sixty_four = self.builder.ins().uextend(types::I128, sixty_four_i64);
            let shifted = self.builder.ins().ushr(value.value, sixty_four);
            let high = self.builder.ins().ireduce(types::I64, shifted);
            self.builder.ins().stack_store(high, slot, offset + 8);
        } else {
            let store_value = convert_to_i64_for_storage(self.builder, &value);
            self.builder.ins().stack_store(store_value, slot, offset);
        }
        Ok(())
    }
}
