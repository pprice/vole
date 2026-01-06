// src/frontend/ast.rs

use crate::frontend::Span;

/// Unique identifier for symbols (interned strings)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(pub u32);

/// Unique identifier for AST nodes (expressions, statements, declarations)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct NodeId(pub u32);

/// For backwards compatibility and clarity in type maps
pub type ExprId = NodeId;

/// Type parameter declaration: T or T: Constraint
#[derive(Debug, Clone)]
pub struct TypeParam {
    pub name: Symbol,
    pub constraint: Option<TypeConstraint>,
    pub span: Span,
}

/// Constraint on a type parameter
#[derive(Debug, Clone)]
pub enum TypeConstraint {
    /// Single interface: T: Stringable
    Interface(Symbol),
    /// Union of types: T: i32 | i64
    Union(Vec<TypeExpr>),
}

/// A complete program
#[derive(Debug, Clone)]
pub struct Program {
    pub declarations: Vec<Decl>,
}

/// Top-level declarations
#[derive(Debug, Clone)]
pub enum Decl {
    Function(FuncDecl),
    Tests(TestsDecl),
    Let(LetStmt),
    Class(ClassDecl),
    Record(RecordDecl),
    Interface(InterfaceDecl),
    Implement(ImplementBlock),
    Error(ErrorDecl),
    External(ExternalBlock), // Top-level external block
}

/// Function declaration
#[derive(Debug, Clone)]
pub struct FuncDecl {
    pub name: Symbol,
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub body: Block,
    pub span: Span,
}

/// Tests block declaration
#[derive(Debug, Clone)]
pub struct TestsDecl {
    pub label: Option<String>,
    pub tests: Vec<TestCase>,
    pub span: Span,
}

/// Individual test case
#[derive(Debug, Clone)]
pub struct TestCase {
    pub name: String,
    pub body: Block,
    pub span: Span,
}

/// Function parameter
#[derive(Debug, Clone)]
pub struct Param {
    pub name: Symbol,
    pub ty: TypeExpr,
    pub span: Span,
}

/// Field definition in a class or record
#[derive(Debug, Clone)]
pub struct FieldDef {
    pub name: Symbol,
    pub ty: TypeExpr,
    pub span: Span,
}

/// Class declaration
#[derive(Debug, Clone)]
pub struct ClassDecl {
    pub name: Symbol,
    pub type_params: Vec<TypeParam>,
    pub implements: Vec<Symbol>, // Interfaces this class implements
    pub fields: Vec<FieldDef>,
    pub external: Option<ExternalBlock>, // External methods from native code
    pub methods: Vec<FuncDecl>,
    pub span: Span,
}

/// Record declaration (immutable class)
#[derive(Debug, Clone)]
pub struct RecordDecl {
    pub name: Symbol,
    pub type_params: Vec<TypeParam>,
    pub implements: Vec<Symbol>, // Interfaces this record implements
    pub fields: Vec<FieldDef>,
    pub external: Option<ExternalBlock>, // External methods from native code
    pub methods: Vec<FuncDecl>,
    pub span: Span,
}

/// Interface declaration
#[derive(Debug, Clone)]
pub struct InterfaceDecl {
    pub name: Symbol,
    pub type_params: Vec<TypeParam>,
    pub extends: Vec<Symbol>,            // Parent interfaces
    pub fields: Vec<FieldDef>,           // Required fields
    pub external: Option<ExternalBlock>, // External methods from native code
    pub methods: Vec<InterfaceMethod>,
    pub span: Span,
}

/// Method in an interface (may be abstract or have default implementation)
#[derive(Debug, Clone)]
pub struct InterfaceMethod {
    pub name: Symbol,
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub body: Option<Block>, // None = abstract, Some = default implementation
    pub span: Span,
}

/// Standalone implement block: implement Trait for Type { ... }
#[derive(Debug, Clone)]
pub struct ImplementBlock {
    pub trait_name: Option<Symbol>, // None for type extension (implement Type { ... })
    pub target_type: TypeExpr,      // The type being extended
    pub external: Option<ExternalBlock>, // External methods from native code
    pub methods: Vec<FuncDecl>,
    pub span: Span,
}

/// External block: external("provider:module") { func declarations }
#[derive(Debug, Clone)]
pub struct ExternalBlock {
    pub module_path: String,
    pub functions: Vec<ExternalFunc>,
    pub span: Span,
}

/// External function declaration
#[derive(Debug, Clone)]
pub struct ExternalFunc {
    pub native_name: Option<String>, // "string_length" or None
    pub vole_name: Symbol,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub span: Span,
}

/// Error type declaration: error Name { fields }
#[derive(Debug, Clone)]
pub struct ErrorDecl {
    pub name: Symbol,
    pub fields: Vec<FieldDef>,
    pub span: Span,
}

/// Type expression
#[derive(Debug, Clone)]
pub enum TypeExpr {
    Primitive(PrimitiveType),
    Named(Symbol),
    Array(Box<TypeExpr>),    // [i32], [string], etc.
    Iterator(Box<TypeExpr>), // Iterator<T> syntax
    Optional(Box<TypeExpr>), // T? syntax (desugars to Union with Nil)
    Union(Vec<TypeExpr>),    // A | B | C
    Nil,                     // nil type
    Done,                    // Done type (iterator termination sentinel)
    Function {
        params: Vec<TypeExpr>,
        return_type: Box<TypeExpr>,
    },
    SelfType, // Self keyword (implementing type in interface)
    /// Fallible type: fallible(T, E)
    Fallible {
        success_type: Box<TypeExpr>,
        error_type: Box<TypeExpr>,
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
    Raise(RaiseStmt),
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

/// Raise statement: raise ErrorName { fields }
#[derive(Debug, Clone)]
pub struct RaiseStmt {
    pub error_name: Symbol,
    pub fields: Vec<StructFieldInit>,
    pub span: Span,
}

/// Expressions
#[derive(Debug, Clone)]
pub struct Expr {
    pub id: NodeId,
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
    CompoundAssign(Box<CompoundAssignExpr>),
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

    /// Done literal (iterator termination sentinel)
    Done,

    /// Null coalescing: value ?? default
    NullCoalesce(Box<NullCoalesceExpr>),

    /// Type test: value is Type
    Is(Box<IsExpr>),

    /// Lambda expression: (x) => x + 1
    Lambda(Box<LambdaExpr>),

    /// Type value expression: i32, f64, string, etc.
    /// Types are first-class values with type `type`
    TypeLiteral(TypeExpr),

    /// Import expression: import "std:math"
    Import(String),

    /// Struct literal: Point { x: 10, y: 20 }
    StructLiteral(Box<StructLiteralExpr>),

    /// Field access: point.x
    FieldAccess(Box<FieldAccessExpr>),

    /// Optional chaining: obj?.field
    OptionalChain(Box<OptionalChainExpr>),

    /// Method call: point.distance()
    MethodCall(Box<MethodCallExpr>),

    /// Try expression (propagation operator)
    Try(Box<Expr>),

    /// Yield expression (generator yield)
    Yield(Box<YieldExpr>),
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
    pub target: AssignTarget,
    pub value: Expr,
}

/// Target for assignment (compound or regular)
#[derive(Debug, Clone)]
pub enum AssignTarget {
    /// Simple variable: x
    Variable(Symbol),
    /// Array index: arr[i]
    Index { object: Box<Expr>, index: Box<Expr> },
    /// Field access: obj.field
    Field {
        object: Box<Expr>,
        field: Symbol,
        field_span: Span,
    },
}

/// Compound assignment operator
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompoundOp {
    Add, // +=
    Sub, // -=
    Mul, // *=
    Div, // /=
    Mod, // %=
}

impl CompoundOp {
    /// Convert to the corresponding binary operator
    pub fn to_binary_op(self) -> BinaryOp {
        match self {
            CompoundOp::Add => BinaryOp::Add,
            CompoundOp::Sub => BinaryOp::Sub,
            CompoundOp::Mul => BinaryOp::Mul,
            CompoundOp::Div => BinaryOp::Div,
            CompoundOp::Mod => BinaryOp::Mod,
        }
    }
}

/// Compound assignment expression: x += 1, arr[i] -= 2
#[derive(Debug, Clone)]
pub struct CompoundAssignExpr {
    pub target: AssignTarget,
    pub op: CompoundOp,
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

/// Struct literal expression: Name { field: value, ... }
#[derive(Debug, Clone)]
pub struct StructLiteralExpr {
    pub name: Symbol,
    pub fields: Vec<StructFieldInit>,
}

/// Field initializer in struct literal
#[derive(Debug, Clone)]
pub struct StructFieldInit {
    pub name: Symbol,
    pub value: Expr,
    pub span: Span,
}

/// Field access expression: expr.field
#[derive(Debug, Clone)]
pub struct FieldAccessExpr {
    pub object: Expr,
    pub field: Symbol,
    pub field_span: Span,
}

/// Optional chaining expression: expr?.field
#[derive(Debug, Clone)]
pub struct OptionalChainExpr {
    pub object: Expr,
    pub field: Symbol,
    pub field_span: Span,
}

/// Method call expression: expr.method(args)
#[derive(Debug, Clone)]
pub struct MethodCallExpr {
    pub object: Expr,
    pub method: Symbol,
    pub args: Vec<Expr>,
    pub method_span: Span,
}

/// Yield expression: yield value
#[derive(Debug, Clone)]
pub struct YieldExpr {
    pub value: Expr,
    pub span: Span,
}

/// Lambda expression: (params) => body
#[derive(Debug, Clone)]
pub struct LambdaExpr {
    pub type_params: Vec<TypeParam>,
    pub params: Vec<LambdaParam>,
    pub return_type: Option<TypeExpr>,
    pub body: LambdaBody,
    pub span: Span,
    /// Captured variables from enclosing scopes (populated during semantic analysis)
    pub captures: std::cell::RefCell<Vec<Capture>>,
    /// Whether the lambda has side effects (populated during semantic analysis)
    pub has_side_effects: std::cell::Cell<bool>,
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

impl LambdaExpr {
    /// Compute the purity level of this lambda based on its captures and side effects.
    ///
    /// Returns the most restrictive purity classification:
    /// - `HasSideEffects`: Calls print/println/assert or user functions
    /// - `MutatesCaptures`: Assigns to captured variables
    /// - `CapturesMutable`: Captures mutable variables (may observe external changes)
    /// - `CapturesImmutable`: Captures exist, but none are mutable
    /// - `Pure`: No captures, no side effects
    pub fn purity(&self) -> LambdaPurity {
        if self.has_side_effects.get() {
            return LambdaPurity::HasSideEffects;
        }
        let captures = self.captures.borrow();
        if captures.iter().any(|c| c.is_mutated) {
            return LambdaPurity::MutatesCaptures;
        }
        if captures.iter().any(|c| c.is_mutable) {
            return LambdaPurity::CapturesMutable;
        }
        if !captures.is_empty() {
            return LambdaPurity::CapturesImmutable;
        }
        LambdaPurity::Pure
    }
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
    /// Type pattern: i32, string, nil, MyClass
    Type { type_expr: TypeExpr, span: Span },
    /// Val pattern: val x (compares against existing variable)
    Val { name: Symbol, span: Span },
    /// Success pattern for fallible match: success x, success, success Point { x, y }
    Success {
        inner: Option<Box<Pattern>>, // None = bare success, Some = success <pattern>
        span: Span,
    },
    /// Error pattern for fallible match: error e, error, error DivByZero, error DivByZero { msg }
    Error {
        inner: Option<Box<Pattern>>, // None = bare error, Some = error <pattern>
        span: Span,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn external_func_native_name() {
        let ef = ExternalFunc {
            native_name: Some("string_length".to_string()),
            vole_name: Symbol(1),
            params: vec![],
            return_type: None,
            span: Span::default(),
        };
        assert_eq!(ef.native_name.as_deref(), Some("string_length"));
    }

    #[test]
    fn external_func_default_name() {
        let ef = ExternalFunc {
            native_name: None,
            vole_name: Symbol(1),
            params: vec![],
            return_type: None,
            span: Span::default(),
        };
        assert!(ef.native_name.is_none());
    }
}
