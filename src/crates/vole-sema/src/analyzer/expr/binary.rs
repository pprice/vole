use super::super::*;
use crate::type_arena::TypeId as ArenaTypeId;

impl Analyzer {
    /// Check binary operator expression.
    /// Handles arithmetic, comparison, logical, and bitwise operators.
    pub(super) fn check_binary_expr(
        &mut self,
        expr: &Expr,
        bin: &BinaryExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let left_ty = self.check_expr(&bin.left, interner)?;
        let right_ty = self.check_expr(&bin.right, interner)?;

        match bin.op {
            BinaryOp::Add => self.check_add_op(left_ty, right_ty, bin, expr.span, interner),
            BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
                self.check_arithmetic_op(left_ty, right_ty, expr.span)
            }
            BinaryOp::Eq | BinaryOp::Ne => {
                self.check_nil_comparison(left_ty, right_ty, bin.op, expr.span);
                Ok(ArenaTypeId::BOOL)
            }
            BinaryOp::Lt | BinaryOp::Gt | BinaryOp::Le | BinaryOp::Ge => {
                self.check_ordering_op(left_ty, right_ty, expr.span)
            }
            BinaryOp::And | BinaryOp::Or => self.check_logical_op(left_ty, right_ty, expr.span),
            BinaryOp::BitAnd
            | BinaryOp::BitOr
            | BinaryOp::BitXor
            | BinaryOp::Shl
            | BinaryOp::Shr => self.check_bitwise_op(left_ty, right_ty, expr.span),
        }
    }

    /// Check addition operator - handles both numeric addition and string concatenation.
    fn check_add_op(
        &mut self,
        left_ty: ArenaTypeId,
        right_ty: ArenaTypeId,
        bin: &BinaryExpr,
        span: Span,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // Handle string concatenation: string + Stringable
        if left_ty == ArenaTypeId::STRING {
            // Left is string - check if right implements Stringable
            if right_ty == ArenaTypeId::STRING {
                // string + string is always valid
                Ok(ArenaTypeId::STRING)
            } else if self.satisfies_stringable_id(right_ty, interner) {
                // Right implements Stringable, so string + X is valid
                Ok(ArenaTypeId::STRING)
            } else {
                // Right doesn't implement Stringable
                self.type_error_id("Stringable", right_ty, bin.right.span);
                Ok(ArenaTypeId::INVALID)
            }
        } else if left_ty.is_numeric() && right_ty.is_numeric() {
            // Numeric addition - use helper for type promotion
            Ok(self.numeric_result_type(left_ty, right_ty))
        } else {
            self.type_error_pair_id("numeric or string", left_ty, right_ty, span);
            Ok(ArenaTypeId::INVALID)
        }
    }

    /// Check arithmetic operators (sub, mul, div, mod).
    fn check_arithmetic_op(
        &mut self,
        left_ty: ArenaTypeId,
        right_ty: ArenaTypeId,
        span: Span,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        if left_ty.is_numeric() && right_ty.is_numeric() {
            Ok(self.numeric_result_type(left_ty, right_ty))
        } else {
            self.type_error_pair_id("numeric", left_ty, right_ty, span);
            Ok(ArenaTypeId::INVALID)
        }
    }

    /// Check logical operators (and, or).
    fn check_logical_op(
        &mut self,
        left_ty: ArenaTypeId,
        right_ty: ArenaTypeId,
        span: Span,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        if left_ty == ArenaTypeId::BOOL && right_ty == ArenaTypeId::BOOL {
            Ok(ArenaTypeId::BOOL)
        } else {
            self.type_error_pair_id("bool", left_ty, right_ty, span);
            Ok(ArenaTypeId::INVALID)
        }
    }

    /// Check ordering comparison operators (lt, gt, le, ge).
    /// Handle type does not support ordering - only equality is allowed.
    fn check_ordering_op(
        &mut self,
        left_ty: ArenaTypeId,
        right_ty: ArenaTypeId,
        span: Span,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        if left_ty == ArenaTypeId::HANDLE || right_ty == ArenaTypeId::HANDLE {
            self.type_error_pair_id("orderable", left_ty, right_ty, span);
            Ok(ArenaTypeId::INVALID)
        } else {
            Ok(ArenaTypeId::BOOL)
        }
    }

    /// Check for invalid nil comparisons (non-optional compared to nil).
    /// This catches cases like `f64 != nil` which are always tautological.
    pub(crate) fn check_nil_comparison(
        &mut self,
        left_ty: ArenaTypeId,
        right_ty: ArenaTypeId,
        op: BinaryOp,
        span: Span,
    ) {
        use crate::errors::SemanticError;

        // Check if one side is nil and the other is not optional
        let (non_nil_ty, is_nil_comparison) = if left_ty.is_nil() {
            (right_ty, true)
        } else if right_ty.is_nil() {
            (left_ty, true)
        } else {
            return; // Not a nil comparison
        };

        if !is_nil_comparison {
            return;
        }

        // Check if the non-nil side is optional
        let is_optional = self.type_arena().is_optional(non_nil_ty);

        // If not optional and not nil itself, emit an error
        if !is_optional && !non_nil_ty.is_nil() {
            let ty_str = self.type_display_id(non_nil_ty);
            let result = match op {
                BinaryOp::Eq => "false",
                BinaryOp::Ne => "true",
                _ => unreachable!(),
            };
            self.add_error(
                SemanticError::NonOptionalNilComparison {
                    ty: ty_str,
                    result: result.to_string(),
                    span: span.into(),
                },
                span,
            );
        }
    }

    /// Check bitwise operators (and, or, xor, shift left, shift right).
    fn check_bitwise_op(
        &mut self,
        left_ty: ArenaTypeId,
        right_ty: ArenaTypeId,
        span: Span,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        if left_ty.is_integer() && right_ty.is_integer() {
            Ok(self.integer_result_type(left_ty, right_ty))
        } else {
            self.type_error_pair_id("integer", left_ty, right_ty, span);
            Ok(ArenaTypeId::INVALID)
        }
    }
}
