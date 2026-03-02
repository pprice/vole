// src/codegen/expr/unary_assign.rs
//
// Shared assignment helpers (RC snapshot for reassignment).

use cranelift::prelude::*;

use vole_frontend::Symbol;

use super::super::context::Cg;

impl Cg<'_, '_, '_> {
    /// Snapshot RC state for a variable before reassignment.
    ///
    /// Returns (rc_old, composite_rc_old, union_rc_old) — each `Some` if the
    /// variable's old value needs RC cleanup after the new value is stored.
    #[expect(clippy::type_complexity)]
    pub(super) fn snapshot_rc_for_reassignment(
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
        let Some(&(var, vir_ty)) = self.vars.get(sym) else {
            return (None, None, None);
        };

        // Bridge to sema TypeId for RC state computation.
        let type_id = self.cv_type_id_from_vir(vir_ty);

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
