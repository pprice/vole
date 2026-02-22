//! Vole frontend: lexer, parser, and AST.

pub mod ast;
pub mod ast_display;
pub mod errors;
pub mod intern;
pub mod lexer;
mod parse_decl;
mod parse_expr;
mod parse_external;
mod parse_generic;
mod parse_lambda;
mod parse_stmt;
mod parse_string;
mod parse_type;
pub mod parser;
pub mod token;

pub use ast::{
    AsCastExpr, AsCastKind, AssignTarget, BinaryExpr, BinaryOp, Block, CallArg, Capture,
    CompoundAssignExpr, Decl, Expr, ExprId, ExprKind, FieldAccessExpr, FieldDef, FuncBody,
    FuncDecl, LambdaExpr, LambdaParam, LambdaPurity, LetInit, LetStmt, MatchExpr, MetaAccessExpr,
    MethodCallExpr, ModuleId, NodeId, OptionalChainExpr, OptionalMethodCallExpr, Param, Pattern,
    PatternKind, PrimitiveType, Program, Stmt, StructLiteralExpr, Symbol, TypeExpr, TypeExprKind,
    UnaryOp,
};
pub use ast_display::AstPrinter;
pub use errors::{LexerError, ParserError};
pub use intern::Interner;
pub use lexer::Lexer;
pub use parser::{ParseError, Parser};
pub use token::{Span, Token, TokenType};
