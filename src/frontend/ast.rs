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
    Let(LetStmt),
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
    pub label: Option<String>,
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
    Array(Box<TypeExpr>),    // [i32], [string], etc.
    Optional(Box<TypeExpr>), // T? syntax (desugars to Union with Nil)
    Union(Vec<TypeExpr>),    // A | B | C
    Nil,                     // nil type
    Function {
        params: Vec<TypeExpr>,
        return_type: Box<TypeExpr>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimitiveType {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Bool,
    String,
}

/// Block of statements
#[derive(Debug, Clone)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

/// Statements
#[derive(Debug, Clone)]
pub enum Stmt {
    Let(LetStmt),
    Expr(ExprStmt),
    While(WhileStmt),
    For(ForStmt),
    If(IfStmt),
    Break(Span),
    Continue(Span),
    Return(ReturnStmt),
}

/// Let binding: let x = expr or let mut x = expr
#[derive(Debug, Clone)]
pub struct LetStmt {
    pub name: Symbol,
    pub ty: Option<TypeExpr>,
    pub mutable: bool,
    pub init: Expr,
    pub span: Span,
}

/// Expression statement
#[derive(Debug, Clone)]
pub struct ExprStmt {
    pub expr: Expr,
    pub span: Span,
}

/// While loop
#[derive(Debug, Clone)]
pub struct WhileStmt {
    pub condition: Expr,
    pub body: Block,
    pub span: Span,
}

/// For-in loop
#[derive(Debug, Clone)]
pub struct ForStmt {
    pub var_name: Symbol,
    pub iterable: Expr,
    pub body: Block,
    pub span: Span,
}

/// If statement/expression
#[derive(Debug, Clone)]
pub struct IfStmt {
    pub condition: Expr,
    pub then_branch: Block,
    pub else_branch: Option<Block>,
    pub span: Span,
}

/// Return statement
#[derive(Debug, Clone)]
pub struct ReturnStmt {
    pub value: Option<Expr>,
    pub span: Span,
}

/// Expressions
#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
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
    Range(Box<RangeExpr>),

    // Grouping
    Grouping(Box<Expr>),

    /// Array literal: [1, 2, 3]
    ArrayLiteral(Vec<Expr>),

    /// Index expression: arr[0]
    Index(Box<IndexExpr>),

    /// Match expression
    Match(Box<MatchExpr>),

    /// Nil literal
    Nil,

    /// Null coalescing: value ?? default
    NullCoalesce(Box<NullCoalesceExpr>),

    /// Type test: value is Type
    Is(Box<IsExpr>),

    /// Lambda expression: (x) => x + 1
    Lambda(Box<LambdaExpr>),
}

/// Range expression (e.g., 0..10 or 0..=10)
#[derive(Debug, Clone)]
pub struct RangeExpr {
    pub start: Expr,
    pub end: Expr,
    pub inclusive: bool,
}

/// Part of an interpolated string
#[derive(Debug, Clone)]
pub enum StringPart {
    Literal(String),
    Expr(Box<Expr>),
}

/// Binary expression
#[derive(Debug, Clone)]
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
    And,
    Or,
    BitAnd, // &
    BitOr,  // |
    BitXor, // ^
    Shl,    // <<
    Shr,    // >>
}

/// Unary expression
#[derive(Debug, Clone)]
pub struct UnaryExpr {
    pub op: UnaryOp,
    pub operand: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
    BitNot, // ~
}

/// Function call
#[derive(Debug, Clone)]
pub struct CallExpr {
    pub callee: Expr,
    pub args: Vec<Expr>,
}

/// Index expression
#[derive(Debug, Clone)]
pub struct IndexExpr {
    pub object: Expr,
    pub index: Expr,
}

/// Assignment
#[derive(Debug, Clone)]
pub struct AssignExpr {
    pub target: Symbol,
    pub value: Expr,
}

/// Match expression
#[derive(Debug, Clone)]
pub struct MatchExpr {
    pub scrutinee: Expr,
    pub arms: Vec<MatchArm>,
    pub span: Span,
}

/// A single arm in a match expression
#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
    pub span: Span,
}

/// Null coalescing expression: value ?? default
#[derive(Debug, Clone)]
pub struct NullCoalesceExpr {
    pub value: Expr,
    pub default: Expr,
}

/// Type test expression: value is Type
#[derive(Debug, Clone)]
pub struct IsExpr {
    pub value: Expr,
    pub type_expr: TypeExpr,
    pub type_span: Span,
}

/// Lambda expression: (params) => body
#[derive(Debug, Clone)]
pub struct LambdaExpr {
    pub params: Vec<LambdaParam>,
    pub return_type: Option<TypeExpr>,
    pub body: LambdaBody,
    pub span: Span,
}

/// Lambda parameter (may have inferred type)
#[derive(Debug, Clone)]
pub struct LambdaParam {
    pub name: Symbol,
    pub ty: Option<TypeExpr>,
    pub span: Span,
}

/// Lambda body - expression or block
#[derive(Debug, Clone)]
pub enum LambdaBody {
    Expr(Box<Expr>),
    Block(Block),
}

/// Captured variable from enclosing scope
#[derive(Debug, Clone)]
pub struct Capture {
    pub name: Symbol,
    pub is_mutable: bool,
    pub is_mutated: bool,
}

/// Purity classification for optimization
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LambdaPurity {
    Pure,
    CapturesImmutable,
    CapturesMutable,
    MutatesCaptures,
    HasSideEffects,
}

/// Pattern for matching
#[derive(Debug, Clone)]
pub enum Pattern {
    /// Wildcard pattern: _
    Wildcard(Span),
    /// Literal pattern: 1, "hello", true, -5
    Literal(Expr),
    /// Identifier pattern (binds value): n
    Identifier { name: Symbol, span: Span },
}
