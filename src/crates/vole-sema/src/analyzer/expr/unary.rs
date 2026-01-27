use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;

impl Analyzer {
    /// Check unary operator expression.
    /// Handles negation, logical not, and bitwise not.
    pub(super) fn check_unary_expr(
        &mut self,
        expr: &Expr,
        un: &UnaryExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let operand_ty = self.check_expr(&un.operand, interner)?;

        match un.op {
            UnaryOp::Neg => {
                if operand_ty.is_numeric() {
                    Ok(operand_ty)
                } else {
                    self.type_error_id("numeric", operand_ty, expr.span);
                    Ok(ArenaTypeId::INVALID)
                }
            }
            UnaryOp::Not => {
                if operand_ty == ArenaTypeId::BOOL {
                    Ok(ArenaTypeId::BOOL)
                } else {
                    self.type_error_id("bool", operand_ty, expr.span);
                    Ok(ArenaTypeId::INVALID)
                }
            }
            UnaryOp::BitNot => {
                if operand_ty.is_integer() {
                    Ok(operand_ty)
                } else {
                    self.type_error_id("integer", operand_ty, expr.span);
                    Ok(ArenaTypeId::INVALID)
                }
            }
        }
    }
}
