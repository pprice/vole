// src/codegen/structs/literals.rs

use std::collections::{HashMap, HashSet};

use rustc_hash::FxHashMap;

use super::helpers::convert_to_i64_for_storage;
use crate::RuntimeFn;
use crate::context::Cg;
use crate::errors::CodegenError;
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
    ) -> Result<CompiledValue, String> {
        // Get the resolved type from semantic analysis, which handles:
        // - Simple types like `Point`
        // - Module-qualified types like `time.Duration`
        // - Generic instantiation
        let path_str = format_path(&sl.path, self.interner());

        // Resolve the TypeDefId based on path length:
        // - Single-segment paths (e.g., `Duration`): Use string-based resolution like the original code
        //   to maintain consistency across multiple file compilations
        // - Multi-segment paths (e.g., `time.Duration`): Use semantic analysis types which have
        //   already resolved the module-qualified path
        let type_def_id = if sl.path.len() == 1 {
            // Simple type name - use string-based resolution for consistency
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
                    } else if let Some((underlying_id, _)) = arena.unwrap_struct(aliased_type_id) {
                        resolved_id = Some(underlying_id);
                    }
                }
            }
            resolved_id
        } else {
            // Qualified path - extract TypeDefId from semantic analysis
            self.get_expr_type(&expr.id).and_then(|expr_type_id| {
                let arena = self.arena();
                if let Some((id, _)) = arena.unwrap_class(expr_type_id) {
                    Some(id)
                } else if let Some((id, _)) = arena.unwrap_struct(expr_type_id) {
                    Some(id)
                } else {
                    None
                }
            })
        }
        .ok_or_else(|| format!("Unknown type: {} (not in entity registry)", path_str))?;

        // Sentinels (e.g. Done, nil) are zero-field structs represented as i8(0).
        // They may not be in type_metadata if they come from prelude modules,
        // so handle them early before the metadata lookup.
        {
            let kind = self.query().registry().type_kind(type_def_id);
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
                return Ok(CompiledValue {
                    value,
                    ty: types::I8,
                    type_id: sentinel_type_id,
                });
            }
        }

        let metadata = self
            .type_metadata()
            .get(&type_def_id)
            .ok_or_else(|| format!("Unknown type: {} (not in type_metadata)", path_str))?;

        // Check if this is a struct type (stack-allocated value type)
        let is_struct_type = {
            let kind = self.query().registry().type_kind(type_def_id);
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

        let type_id = metadata.type_id;
        let field_count = metadata.field_slots.len() as u32;
        // Prefer the type from semantic analysis (handles generic instantiation, module-aware)
        let result_type_id = self.get_expr_type(&expr.id).unwrap_or(metadata.vole_type);
        let field_slots = metadata.field_slots.clone();

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

            let value = self.expr(&init.value)?;

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
                } else if field_is_interface {
                    self.box_interface_value(value, field_type_id)?
                } else {
                    value
                }
            } else {
                value
            };

            let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
            let store_value = convert_to_i64_for_storage(self.builder, &final_value);

            self.builder
                .ins()
                .call(set_func_ref, &[instance_ptr, slot_val, store_value]);
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
                } else if field_is_interface {
                    self.box_interface_value(value, field_type_id)?
                } else {
                    value
                }
            } else {
                value
            };

            let slot_val = self.builder.ins().iconst(types::I32, slot as i64);
            let store_value = convert_to_i64_for_storage(self.builder, &final_value);

            self.builder
                .ins()
                .call(set_func_ref, &[instance_ptr, slot_val, store_value]);
        }

        Ok(CompiledValue {
            value: instance_ptr,
            ty: self.ptr_type(),
            type_id: result_type_id,
        })
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
    fn construct_union_heap_id(
        &mut self,
        value: CompiledValue,
        union_type_id: TypeId,
    ) -> Result<CompiledValue, String> {
        let arena = self.arena();
        let variants = arena.unwrap_union(union_type_id).ok_or_else(|| {
            CodegenError::type_mismatch("union construction", "union type", "non-union").to_string()
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
                CodegenError::type_mismatch("union variant", "compatible type", "incompatible type")
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

        // Sentinel types (nil, Done, user-defined) have no payload - only the tag matters
        if !self.arena().is_sentinel(value.type_id) {
            self.builder
                .ins()
                .store(MemFlags::new(), value.value, heap_ptr, 8);
        }

        Ok(CompiledValue {
            value: heap_ptr,
            ty: self.ptr_type(),
            type_id: union_type_id,
        })
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
    ) -> Result<CompiledValue, String> {
        // Use flat total size to account for nested struct fields
        let total_size = {
            let arena = self.arena();
            let entities = self.query().registry();
            super::helpers::struct_total_byte_size(result_type_id, arena, entities)
                .unwrap_or_else(|| (field_slots.len() as u32) * 8)
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
                let entities = self.query().registry();
                super::helpers::struct_field_byte_offset(
                    result_type_id,
                    field_slot,
                    arena,
                    entities,
                )
                .unwrap_or((field_slot as i32) * 8)
            };

            let value = self.expr(&init.value)?;
            self.store_struct_field(value, slot, offset)?;
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
                let entities = self.query().registry();
                super::helpers::struct_field_byte_offset(
                    result_type_id,
                    field_slot,
                    arena,
                    entities,
                )
                .unwrap_or((field_slot as i32) * 8)
            };

            // SAFETY: See collect_field_default_ptrs documentation
            let default_expr: &Expr = unsafe { &*default_expr_ptr };
            let value = self.expr(default_expr)?;
            self.store_struct_field(value, slot, offset)?;
        }

        // Return pointer to the struct
        let ptr_type = self.ptr_type();
        let ptr = self.builder.ins().stack_addr(ptr_type, slot, 0);

        Ok(CompiledValue {
            value: ptr,
            ty: ptr_type,
            type_id: result_type_id,
        })
    }

    /// Store a value into a struct field's stack slot, handling nested structs.
    fn store_struct_field(
        &mut self,
        value: CompiledValue,
        slot: StackSlot,
        offset: i32,
    ) -> Result<(), String> {
        let field_flat_slots = {
            let arena = self.arena();
            let entities = self.query().registry();
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
        } else {
            let store_value = convert_to_i64_for_storage(self.builder, &value);
            self.builder.ins().stack_store(store_value, slot, offset);
        }
        Ok(())
    }
}
