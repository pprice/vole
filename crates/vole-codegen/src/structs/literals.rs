// src/codegen/structs/literals.rs

use std::collections::{HashMap, HashSet};

use super::helpers::convert_to_i64_for_storage;
use crate::RuntimeFn;
use crate::context::Cg;
use crate::errors::CodegenError;
use crate::types::CompiledValue;
use cranelift::prelude::*;
use vole_frontend::{Decl, Expr, FieldDef, Program, StructLiteralExpr, Symbol};
use vole_sema::type_arena::TypeId;

/// Find the field definitions for a type by looking up the class/record declaration in the program
fn find_type_fields(program: &Program, type_name: Symbol) -> Option<&[FieldDef]> {
    for decl in &program.declarations {
        match decl {
            Decl::Class(class) if class.name == type_name => return Some(&class.fields),
            Decl::Record(record) if record.name == type_name => return Some(&record.fields),
            _ => {}
        }
    }
    None
}

impl Cg<'_, '_, '_> {
    pub fn struct_literal(
        &mut self,
        sl: &StructLiteralExpr,
        expr: &Expr,
    ) -> Result<CompiledValue, String> {
        // Look up TypeDefId from type name using the full resolution chain.
        // This handles prelude types like Set, Map that are registered in separate modules.
        // Note: We use the string name rather than Symbol because the current interner
        // may be module-specific while the query uses the main program's interner.
        let type_name = self.interner().resolve(sl.name);
        let query = self.query();
        let module_id = self
            .current_module_id()
            .unwrap_or_else(|| query.main_module());

        let type_def_id = query
            .resolve_type_def_by_str(module_id, type_name)
            .ok_or_else(|| format!("Unknown type: {} (not in entity registry)", type_name))?;
        let metadata = self
            .type_metadata()
            .get(&type_def_id)
            .ok_or_else(|| format!("Unknown type: {} (not in type_metadata)", type_name))?;

        let type_id = metadata.type_id;
        let field_count = metadata.field_slots.len() as u32;
        // Prefer the type from semantic analysis (handles generic instantiation)
        let result_type_id = self.query().type_of(expr.id).unwrap_or(metadata.vole_type);
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
            let type_def_id = arena
                .unwrap_record(result_type_id)
                .map(|(id, _)| id)
                .or_else(|| arena.unwrap_class(result_type_id).map(|(id, _)| id));

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
            let slot = *field_slots.get(init_name).ok_or_else(|| {
                format!(
                    "Unknown field: {} in type {}",
                    init_name,
                    self.interner().resolve(sl.name)
                )
            })?;

            let value = self.expr(&init.value)?;

            // If field type is optional (union) and value type is not a union, wrap it
            // Use heap allocation for unions stored in class/record fields since stack slots
            // don't persist beyond the current function's stack frame
            let final_value = if let Some(&field_type_id) = field_types.get(init_name) {
                let arena = self.arena();
                let field_is_union = arena.is_union(field_type_id);
                let field_is_interface = arena.is_interface(field_type_id);
                let value_is_union = arena.is_union(value.type_id);
                drop(arena);

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
        let field_default_ptrs =
            self.collect_field_default_ptrs(sl.name, &provided_fields, type_def_id);

        for (field_name, default_expr_ptr) in field_default_ptrs {
            let slot = *field_slots.get(&field_name).ok_or_else(|| {
                format!(
                    "Unknown field: {} in type {} (default)",
                    field_name,
                    self.interner().resolve(sl.name)
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
                drop(arena);

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

        // Get the main module to check if this type is in the main program
        let main_module = self.query().main_module();

        if type_module == main_module {
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

    /// Construct a union value on the heap (for storing in class/record fields).
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
        let nil_id = arena.nil();
        drop(arena);

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

        // Store payload at offset 8 (if not nil)
        if value.type_id != nil_id {
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
}
