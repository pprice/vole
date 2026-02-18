// src/codegen/compound_assign.rs
//
// Compound assignment operations (+=, -=, *=, etc.) — impl Cg methods.

use cranelift::prelude::*;

use crate::RuntimeKey;
use crate::context::Cg;
use crate::errors::{CodegenError, CodegenResult};
use crate::structs::get_field_slot_and_type_id_cg;
use crate::types::CompiledValue;
use vole_frontend::{AssignTarget, CompoundAssignExpr};

impl Cg<'_, '_, '_> {
    /// Compile compound assignment (+=, -=, etc.)
    pub fn compound_assign(
        &mut self,
        compound: &CompoundAssignExpr,
        line: u32,
    ) -> CodegenResult<CompiledValue> {
        match &compound.target {
            AssignTarget::Discard => {
                // Compound assignment to discard doesn't make sense
                // Sema should catch this, but handle it gracefully
                Err(CodegenError::unsupported(
                    "compound assignment with discard pattern",
                ))
            }
            AssignTarget::Variable(sym) => self.compound_assign_var(*sym, compound, line),
            AssignTarget::Index { object, index } => {
                self.compound_assign_index(object, index, compound, line)
            }
            AssignTarget::Field { object, field, .. } => {
                self.compound_assign_field(object, *field, compound, line)
            }
        }
    }

    /// Compound assignment to variable
    fn compound_assign_var(
        &mut self,
        sym: vole_frontend::Symbol,
        compound: &CompoundAssignExpr,
        line: u32,
    ) -> CodegenResult<CompiledValue> {
        let (var, var_type_id) = self
            .vars
            .get(&sym)
            .ok_or_else(|| CodegenError::not_found("variable", self.interner().resolve(sym)))?;
        let var = *var;
        let var_type_id = *var_type_id;
        let current_val = self.builder.use_var(var);

        let current = self.compiled(current_val, var_type_id);

        let rhs = self.expr(&compound.value)?;
        let binary_op = compound.op.to_binary_op();
        let result = self.binary_op(current, rhs, binary_op, line)?;

        self.builder.def_var(var, result.value);
        // The compound assignment consumed the temp — ownership transfers
        // to the variable binding; scope cleanup handles the dec.
        let mut result = result;
        result.mark_consumed();
        result.debug_assert_rc_handled("compound assign to variable");
        Ok(result)
    }

    /// Compound assignment to array index
    fn compound_assign_index(
        &mut self,
        object: &vole_frontend::Expr,
        index: &vole_frontend::Expr,
        compound: &CompoundAssignExpr,
        line: u32,
    ) -> CodegenResult<CompiledValue> {
        let arr = self.expr(object)?;
        let idx = self.expr(index)?;

        let elem_type_id = {
            let arena = self.arena();
            arena
                .unwrap_array(arr.type_id)
                .unwrap_or_else(|| arena.i64())
        };
        let resolved_elem_type_id = self.try_substitute_type(elem_type_id);

        // Load current element
        let raw_value = self.call_runtime(RuntimeKey::ArrayGetValue, &[arr.value, idx.value])?;
        let current = if self.arena().is_union(resolved_elem_type_id) {
            if self.union_array_prefers_inline_storage(resolved_elem_type_id) {
                let raw_tag =
                    self.call_runtime(RuntimeKey::ArrayGetTag, &[arr.value, idx.value])?;
                self.decode_dynamic_array_union_element(raw_tag, raw_value, resolved_elem_type_id)
            } else {
                self.copy_union_heap_to_stack(raw_value, resolved_elem_type_id)
            }
        } else if resolved_elem_type_id == self.arena().i128()
            || resolved_elem_type_id == self.arena().f128()
        {
            let wide_bits = self.call_runtime(RuntimeKey::Wide128Unbox, &[raw_value])?;
            if resolved_elem_type_id == self.arena().f128() {
                let value = self
                    .builder
                    .ins()
                    .bitcast(types::F128, MemFlags::new(), wide_bits);
                CompiledValue::new(value, types::F128, resolved_elem_type_id)
            } else {
                CompiledValue::new(wide_bits, types::I128, resolved_elem_type_id)
            }
        } else {
            self.convert_field_value(raw_value, resolved_elem_type_id)
        };

        let rhs = self.expr(&compound.value)?;
        let binary_op = compound.op.to_binary_op();
        let result = self.binary_op(current, rhs, binary_op, line)?;

        // Store back
        let (tag_val, store_value, _stored) =
            self.prepare_dynamic_array_store(result, resolved_elem_type_id)?;
        let array_set_ref = self.runtime_func_ref(RuntimeKey::ArraySet)?;

        let set_args =
            self.coerce_call_args(array_set_ref, &[arr.value, idx.value, tag_val, store_value]);
        self.builder.ins().call(array_set_ref, &set_args);

        Ok(result)
    }

    /// Compound assignment to field
    fn compound_assign_field(
        &mut self,
        object: &vole_frontend::Expr,
        field: vole_frontend::Symbol,
        compound: &CompoundAssignExpr,
        line: u32,
    ) -> CodegenResult<CompiledValue> {
        let obj = self.expr(object)?;

        let field_name = self.interner().resolve(field);
        let (slot, field_type_id) = get_field_slot_and_type_id_cg(obj.type_id, field_name, self)?;

        // Load current field (i128 uses 2 slots)
        let current = self.get_instance_field(obj.value, slot, field_type_id)?;

        let rhs = self.expr(&compound.value)?;
        let binary_op = compound.op.to_binary_op();
        let result = self.binary_op(current, rhs, binary_op, line)?;

        // Store back (i128 uses 2 slots)
        let set_func_ref = self.runtime_func_ref(RuntimeKey::InstanceSetField)?;
        crate::structs::helpers::store_field_value(
            self.builder,
            set_func_ref,
            obj.value,
            slot,
            &result,
        );
        self.field_cache.clear(); // Invalidate cached field reads

        Ok(result)
    }
}
