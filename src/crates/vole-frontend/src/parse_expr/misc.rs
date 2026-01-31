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
        match token.ty {
            TokenType::KwI8 => Some(TypeExpr::Primitive(PrimitiveType::I8)),
            TokenType::KwI16 => Some(TypeExpr::Primitive(PrimitiveType::I16)),
            TokenType::KwI32 => Some(TypeExpr::Primitive(PrimitiveType::I32)),
            TokenType::KwI64 => Some(TypeExpr::Primitive(PrimitiveType::I64)),
            TokenType::KwI128 => Some(TypeExpr::Primitive(PrimitiveType::I128)),
            TokenType::KwU8 => Some(TypeExpr::Primitive(PrimitiveType::U8)),
            TokenType::KwU16 => Some(TypeExpr::Primitive(PrimitiveType::U16)),
            TokenType::KwU32 => Some(TypeExpr::Primitive(PrimitiveType::U32)),
            TokenType::KwU64 => Some(TypeExpr::Primitive(PrimitiveType::U64)),
            TokenType::KwF32 => Some(TypeExpr::Primitive(PrimitiveType::F32)),
            TokenType::KwF64 => Some(TypeExpr::Primitive(PrimitiveType::F64)),
            TokenType::KwBool => Some(TypeExpr::Primitive(PrimitiveType::Bool)),
            TokenType::KwString => Some(TypeExpr::Primitive(PrimitiveType::String)),
            _ => None,
        }
    }
}
