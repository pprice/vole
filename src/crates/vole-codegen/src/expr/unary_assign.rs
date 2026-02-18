// src/codegen/expr/unary_assign.rs
//
// Unary operations and assignment compilation.

use cranelift::prelude::*;

use crate::RuntimeKey;
use crate::errors::{CodegenError, CodegenResult};
use crate::ops::try_constant_value;
use crate::types::CompiledValue;

use vole_frontend::{AssignTarget, Expr, Symbol, UnaryOp};
use vole_sema::type_arena::TypeId;

use super::super::context::Cg;

impl Cg<'_, '_, '_> {
    /// Compile a unary expression
    pub(super) fn unary(
        &mut self,
        un: &vole_frontend::ast::UnaryExpr,
    ) -> CodegenResult<CompiledValue> {
        let operand = self.expr(&un.operand)?;
        let result = match un.op {
            UnaryOp::Neg => {
                if operand.ty == types::F128 {
                    let bits = self.call_runtime(RuntimeKey::F128Neg, &[operand.value])?;
                    self.builder
                        .ins()
                        .bitcast(types::F128, MemFlags::new(), bits)
                } else if operand.ty.is_float() {
                    self.builder.ins().fneg(operand.value)
                } else {
                    self.builder.ins().ineg(operand.value)
                }
            }
            UnaryOp::Not => {
                // Boolean not: 1 - value.  Operand may be wider than i8 when
                // a boolean flows through block parameters (e.g. deeply nested
                // when/match expressions), so narrow to i8 first.
                let op_val = if operand.ty != types::I8 {
                    self.builder.ins().ireduce(types::I8, operand.value)
                } else {
                    operand.value
                };
                // Constant-fold: if operand is a known constant, emit the
                // negated constant directly instead of `iconst 1; isub`.
                if let Some(c) = try_constant_value(self.builder.func, op_val) {
                    self.builder
                        .ins()
                        .iconst(types::I8, if c == 0 { 1 } else { 0 })
                } else {
                    let one = self.builder.ins().iconst(types::I8, 1);
                    self.builder.ins().isub(one, op_val)
                }
            }
            UnaryOp::BitNot => self.builder.ins().bnot(operand.value),
        };
        Ok(operand.with_value(result))
    }

    /// Compile an assignment expression
    pub(super) fn assign(
        &mut self,
        assign: &vole_frontend::ast::AssignExpr,
    ) -> CodegenResult<CompiledValue> {
        match &assign.target {
            AssignTarget::Discard => {
                // Discard pattern: _ = expr
                // Compile the expression for side effects, discard result
                let mut value = self.expr(&assign.value)?;
                // Consume RC value since the result is discarded
                self.consume_rc_value(&mut value)?;
                // Return a void value
                Ok(CompiledValue::new(
                    self.builder.ins().iconst(types::I64, 0),
                    types::I64,
                    TypeId::VOID,
                ))
            }
            AssignTarget::Variable(sym) => self.assign_variable(*sym, &assign.value),
            AssignTarget::Field { object, field, .. } => {
                self.field_assign(object, *field, &assign.value)
            }
            AssignTarget::Index { object, index } => {
                self.index_assign(object, index, &assign.value)
            }
        }
    }

    /// Compile assignment to a variable, handling RC snapshots and cleanup.
    fn assign_variable(&mut self, sym: Symbol, value_expr: &Expr) -> CodegenResult<CompiledValue> {
        // Read the old value BEFORE evaluating the new expression,
        // so we can rc_dec it after the assignment.
        let (rc_old, composite_rc_old, union_rc_old) = self.snapshot_rc_for_reassignment(&sym);

        let mut value = self.expr(value_expr)?;

        // Check for captured variable assignment
        if let Some(binding) = self.get_capture(&sym).copied() {
            return self.store_capture(&binding, value);
        }

        let (var, var_type_id) = self
            .vars
            .get(&sym)
            .ok_or_else(|| CodegenError::not_found("variable", self.interner().resolve(sym)))?;
        let var = *var;
        let var_type_id = *var_type_id;

        value = self.coerce_to_type(value, var_type_id)?;

        // RC bookkeeping for reassignment:
        // 1. rc_inc new value if it's a borrow (variable copy)
        // 2. Store the new value
        // 3. rc_dec old value (after store, in case old == new)
        if rc_old.is_some() && value.is_borrowed() {
            self.emit_rc_inc_for_type(value.value, var_type_id)?;
        }
        self.builder.def_var(var, value.value);
        if let Some(old_val) = rc_old {
            self.emit_rc_dec_for_type(old_val, var_type_id)?;
        }

        // Composite RC reassignment: rc_dec each RC field of the OLD struct.
        // The new struct's fields are already alive (fresh from the literal).
        if let Some((old_ptr, offsets)) = composite_rc_old {
            for off in &offsets {
                let field_ptr = self
                    .builder
                    .ins()
                    .load(types::I64, MemFlags::new(), old_ptr, *off);
                self.emit_rc_dec(field_ptr)?;
            }
            // Update the composite RC local's offsets so scope-exit cleanup
            // covers nested RC fields in the new value too.
            self.rc_scopes.update_composite_offsets(var, offsets);
        }

        // Union RC reassignment: rc_dec the RC payload of the OLD union value.
        // The new value's payload is already alive (fresh from the expression).
        if let Some((old_ptr, rc_tags)) = union_rc_old {
            self.emit_union_rc_dec(old_ptr, &rc_tags)?;
        }

        // The assignment consumed the temp — ownership transfers
        // to the variable binding; scope cleanup handles the dec.
        value.mark_consumed();
        value.debug_assert_rc_handled("assign to variable");
        Ok(value)
    }

    /// Snapshot RC state for a variable before reassignment.
    ///
    /// Returns (rc_old, composite_rc_old, union_rc_old) — each `Some` if the
    /// variable's old value needs RC cleanup after the new value is stored.
    #[expect(clippy::type_complexity)]
    fn snapshot_rc_for_reassignment(
        &mut self,
        sym: &Symbol,
    ) -> (
        Option<Value>,
        Option<(Value, Vec<i32>)>,
        Option<(Value, Vec<(u8, bool)>)>,
    ) {
        if !self.rc_scopes.has_active_scope() {
            return (None, None, None);
        }
        let Some(&(var, type_id)) = self.vars.get(sym) else {
            return (None, None, None);
        };

        let rc_old = if self.rc_state(type_id).needs_cleanup() {
            Some(self.builder.use_var(var))
        } else {
            None
        };

        let composite_rc_old = self
            .rc_state(type_id)
            .deep_offsets()
            .map(|offsets| (self.builder.use_var(var), offsets.to_vec()));

        let union_rc_old = self
            .rc_state(type_id)
            .union_variants()
            .map(|rc_tags| (self.builder.use_var(var), rc_tags.to_vec()));

        (rc_old, composite_rc_old, union_rc_old)
    }
}
