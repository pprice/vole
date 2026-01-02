// src/frontend/ast.rs

use crate::frontend::Span;

/// Unique identifier for symbols (interned strings)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(pub u32);

/// A complete program
#[derive(Debug)]
pub struct Program {
    pub declarations: Vec<Decl>,
}

/// Top-level declarations
#[derive(Debug)]
pub enum Decl {
    Function(FuncDecl),
    Tests(TestsDecl),
}

/// Function declaration
#[derive(Debug)]
pub struct FuncDecl {
    pub name: Symbol,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub body: Block,
    pub span: Span,
}

/// Tests block declaration
#[derive(Debug)]
pub struct TestsDecl {
    pub tests: Vec<TestCase>,
    pub span: Span,
}

/// Individual test case
#[derive(Debug)]
pub struct TestCase {
    pub name: String,
    pub body: Block,
    pub span: Span,
}

/// Function parameter
#[derive(Debug)]
pub struct Param {
    pub name: Symbol,
    pub ty: TypeExpr,
    pub span: Span,
}

/// Type expression
#[derive(Debug, Clone)]
pub enum TypeExpr {
    Primitive(PrimitiveType),
    Named(Symbol),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimitiveType {
    I32,
    I64,
    F64,
    Bool,
    String,
}

/// Block of statements
#[derive(Debug)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

/// Statements
#[derive(Debug)]
pub enum Stmt {
    Let(LetStmt),
    Expr(ExprStmt),
    While(WhileStmt),
    If(IfStmt),
    Break(Span),
    Return(ReturnStmt),
}

/// Let binding: let x = expr or let mut x = expr
#[derive(Debug)]
pub struct LetStmt {
    pub name: Symbol,
    pub ty: Option<TypeExpr>,
    pub mutable: bool,
    pub init: Expr,
    pub span: Span,
}

/// Expression statement
#[derive(Debug)]
pub struct ExprStmt {
    pub expr: Expr,
    pub span: Span,
}

/// While loop
#[derive(Debug)]
pub struct WhileStmt {
    pub condition: Expr,
    pub body: Block,
    pub span: Span,
}

/// If statement/expression
#[derive(Debug)]
pub struct IfStmt {
    pub condition: Expr,
    pub then_branch: Block,
    pub else_branch: Option<Block>,
    pub span: Span,
}

/// Return statement
#[derive(Debug)]
pub struct ReturnStmt {
    pub value: Option<Expr>,
    pub span: Span,
}

/// Expressions
#[derive(Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum ExprKind {
    // Literals
    IntLiteral(i64),
    FloatLiteral(f64),
    BoolLiteral(bool),
    StringLiteral(String),
    InterpolatedString(Vec<StringPart>),

    // Variables
    Identifier(Symbol),

    // Operations
    Binary(Box<BinaryExpr>),
    Unary(Box<UnaryExpr>),
    Call(Box<CallExpr>),
    Assign(Box<AssignExpr>),

    // Grouping
    Grouping(Box<Expr>),
}

/// Part of an interpolated string
#[derive(Debug)]
pub enum StringPart {
    Literal(String),
    Expr(Box<Expr>),
}

/// Binary expression
#[derive(Debug)]
pub struct BinaryExpr {
    pub left: Expr,
    pub op: BinaryOp,
    pub right: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
}

/// Unary expression
#[derive(Debug)]
pub struct UnaryExpr {
    pub op: UnaryOp,
    pub operand: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
}

/// Function call
#[derive(Debug)]
pub struct CallExpr {
    pub callee: Expr,
    pub args: Vec<Expr>,
}

/// Assignment
#[derive(Debug)]
pub struct AssignExpr {
    pub target: Symbol,
    pub value: Expr,
}
