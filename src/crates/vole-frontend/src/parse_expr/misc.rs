use super::super::ast::*;
use super::super::parser::{ParseError, Parser};
use super::super::token::TokenType;

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

    /// Convert a token to a TypeExpr if it's a primitive type or nil keyword
    pub(super) fn token_to_type_expr(
        &self,
        token: &super::super::token::Token,
    ) -> Option<TypeExpr> {
        let kind = match token.ty {
            TokenType::KwI8 => TypeExprKind::Primitive(PrimitiveType::I8),
            TokenType::KwI16 => TypeExprKind::Primitive(PrimitiveType::I16),
            TokenType::KwI32 => TypeExprKind::Primitive(PrimitiveType::I32),
            TokenType::KwI64 => TypeExprKind::Primitive(PrimitiveType::I64),
            TokenType::KwI128 => TypeExprKind::Primitive(PrimitiveType::I128),
            TokenType::KwU8 => TypeExprKind::Primitive(PrimitiveType::U8),
            TokenType::KwU16 => TypeExprKind::Primitive(PrimitiveType::U16),
            TokenType::KwU32 => TypeExprKind::Primitive(PrimitiveType::U32),
            TokenType::KwU64 => TypeExprKind::Primitive(PrimitiveType::U64),
            TokenType::KwF32 => TypeExprKind::Primitive(PrimitiveType::F32),
            TokenType::KwF64 => TypeExprKind::Primitive(PrimitiveType::F64),
            TokenType::KwBool => TypeExprKind::Primitive(PrimitiveType::Bool),
            TokenType::KwString => TypeExprKind::Primitive(PrimitiveType::String),
            _ => return None,
        };
        Some(TypeExpr::new(kind, token.span))
    }
}
