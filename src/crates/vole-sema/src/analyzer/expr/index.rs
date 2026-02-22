use super::super::type_helpers::SequenceInfo;
use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;

impl Analyzer {
    /// Check index expression (array[index], tuple[index]).
    pub(super) fn check_index_expr(
        &mut self,
        expr_id: NodeId,
        idx: &IndexExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let obj_ty_id = self.check_expr(&idx.object, interner)?;
        let index_ty_id = self.check_expr(&idx.index, interner)?;

        // Index must be integer (using TypeId check)
        if !self.is_integer_id(index_ty_id) {
            self.type_error_id("integer", index_ty_id, idx.index.span);
        }

        // Object must be array, tuple, or fixed array
        // Use unified sequence unwrapping helper
        if let Some(seq_info) = self.unwrap_sequence_id(obj_ty_id) {
            match seq_info {
                SequenceInfo::Array(elem_id) | SequenceInfo::FixedArray(elem_id, _) => {
                    // Annotate union storage kind for array element unions.
                    self.annotate_union_storage_for_array_elem(expr_id, elem_id);
                    Ok(elem_id)
                }
                SequenceInfo::Tuple(elem_ids) => {
                    // For tuples, try to get element type from constant index
                    if let ExprKind::IntLiteral(i, _) = &idx.index.kind {
                        let i = *i as usize;
                        if i < elem_ids.len() {
                            Ok(elem_ids[i])
                        } else {
                            self.add_error(
                                SemanticError::IndexOutOfBounds {
                                    index: i,
                                    len: elem_ids.len(),
                                    span: idx.index.span.into(),
                                },
                                idx.index.span,
                            );
                            Ok(ArenaTypeId::INVALID)
                        }
                    } else {
                        // Non-constant index - return first element type (common case: 2-tuples)
                        Ok(elem_ids.first().copied().unwrap_or(ArenaTypeId::INVALID))
                    }
                }
            }
        } else {
            if !obj_ty_id.is_invalid() {
                self.type_error_id("array", obj_ty_id, idx.object.span);
            }
            Ok(ArenaTypeId::INVALID)
        }
    }
}
