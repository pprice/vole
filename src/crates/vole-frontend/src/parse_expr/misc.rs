use super::super::ast::*;
use super::super::parser::{ParseError, Parser};

impl<'src> Parser<'src> {
    /// Parse a try expression (propagation operator)
    pub(super) fn try_expr(&mut self) -> Result<Expr, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'try'

        // Parse the inner expression - try binds tightly (like unary)
        let inner = self.unary()?;
        let span = start_span.merge(inner.span);

        Ok(Expr {
            id: self.next_id(),
            kind: ExprKind::Try(Box::new(inner)),
            span,
        })
    }

    /// Parse a yield expression (generator yield)
    pub(super) fn yield_expr(&mut self) -> Result<Expr, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume 'yield'

        // Parse the value to yield
        let value = self.expression(0)?;
        let span = start_span.merge(value.span);

        Ok(Expr {
            id: self.next_id(),
            kind: ExprKind::Yield(Box::new(YieldExpr { value, span })),
            span,
        })
    }

    /// Convert a token to a TypeExpr if it's a primitive type keyword
    pub(super) fn token_to_type_expr(
        &self,
        token: &super::super::token::Token,
    ) -> Option<TypeExpr> {
        let prim = token.ty.to_primitive_type()?;
        Some(TypeExpr::new(TypeExprKind::Primitive(prim), token.span))
    }
}
