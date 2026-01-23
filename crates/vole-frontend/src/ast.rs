// src/frontend/ast.rs

use crate::Span;

/// Unique identifier for symbols (interned strings)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(pub u32);

/// Unique identifier for AST nodes (expressions, statements, declarations)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct NodeId(pub u32);

impl std::fmt::Display for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "node#{}", self.0)
    }
}

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
    /// Interface constraints: T: Stringable or T: Hashable + Eq
    Interface(Vec<Symbol>),
    /// Union of types: T: i32 | i64
    Union(Vec<TypeExpr>),
    /// Structural constraint: T: { name: string, func get() -> i32 }
    Structural {
        fields: Vec<StructuralField>,
        methods: Vec<StructuralMethod>,
    },
}

/// A complete program
#[derive(Debug, Clone)]
pub struct Program {
    pub declarations: Vec<Decl>,
    /// The next available node ID (one past the highest ID used).
    /// Used by transforms that need to create new AST nodes.
    pub next_node_id: u32,
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
    pub body: FuncBody,
    pub span: Span,
}

/// Function body - either a block or a single expression
#[derive(Debug, Clone)]
pub enum FuncBody {
    /// Block body: `{ statements }`
    Block(Block),
    /// Expression body: `=> expr`
    Expr(Box<Expr>),
}

/// Tests block declaration
#[derive(Debug, Clone)]
pub struct TestsDecl {
    pub label: Option<String>,
    /// Scoped declarations (func, let, record, etc.) - must come before tests
    pub decls: Vec<Decl>,
    pub tests: Vec<TestCase>,
    pub span: Span,
}

/// Individual test case
#[derive(Debug, Clone)]
pub struct TestCase {
    pub name: String,
    pub body: FuncBody,
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
    pub implements: Vec<TypeExpr>, // Interfaces this class implements (may include generics)
    pub fields: Vec<FieldDef>,
    pub external: Option<ExternalBlock>, // External methods from native code
    pub methods: Vec<FuncDecl>,
    pub statics: Option<StaticsBlock>, // Static methods
    pub span: Span,
}

/// Record declaration (immutable class)
#[derive(Debug, Clone)]
pub struct RecordDecl {
    pub name: Symbol,
    pub type_params: Vec<TypeParam>,
    pub implements: Vec<TypeExpr>, // Interfaces this record implements (may include generics)
    pub fields: Vec<FieldDef>,
    pub external: Option<ExternalBlock>, // External methods from native code
    pub methods: Vec<FuncDecl>,
    pub statics: Option<StaticsBlock>, // Static methods
    pub span: Span,
}

/// Interface declaration
#[derive(Debug, Clone)]
pub struct InterfaceDecl {
    pub name: Symbol,
    pub type_params: Vec<TypeParam>,
    pub extends: Vec<Symbol>,                // Parent interfaces
    pub fields: Vec<FieldDef>,               // Required fields
    pub external_blocks: Vec<ExternalBlock>, // External methods from native code (multiple allowed)
    pub methods: Vec<InterfaceMethod>,
    pub statics: Option<StaticsBlock>, // Static methods
    pub span: Span,
}

/// Method in an interface (may be abstract or have default implementation)
#[derive(Debug, Clone)]
pub struct InterfaceMethod {
    pub name: Symbol,
    pub type_params: Vec<TypeParam>,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub body: Option<FuncBody>, // None = abstract, Some = default implementation (block or expr)
    pub is_default: bool,       // true if marked with 'default' keyword
    pub span: Span,
}

/// Standalone implement block: implement Trait for Type { ... }
#[derive(Debug, Clone)]
pub struct ImplementBlock {
    pub trait_type: Option<TypeExpr>, // None for type extension (implement Type { ... })
    pub target_type: TypeExpr,        // The type being extended
    pub external: Option<ExternalBlock>, // External methods from native code
    pub methods: Vec<FuncDecl>,
    pub statics: Option<StaticsBlock>, // Static methods
    pub span: Span,
}

/// External block: external("provider:module") { func declarations }
#[derive(Debug, Clone)]
pub struct ExternalBlock {
    pub module_path: String,
    pub functions: Vec<ExternalFunc>,
    pub is_default: bool, // true if marked with 'default' keyword (interface default methods)
    pub span: Span,
}

/// Statics block: statics { func declarations, external blocks }
/// Contains static methods that are called on the type, not on instances
#[derive(Debug, Clone)]
pub struct StaticsBlock {
    pub methods: Vec<InterfaceMethod>, // Static methods (may have bodies or be abstract)
    pub external_blocks: Vec<ExternalBlock>, // External static methods
    pub span: Span,
}

/// External function declaration
#[derive(Debug, Clone)]
pub struct ExternalFunc {
    pub native_name: Option<String>, // "string_length" or None
    pub vole_name: Symbol,
    pub type_params: Vec<TypeParam>, // Generic type params for type-erased external functions
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

/// A field in a structural type constraint: { name: string, age: i32 }
#[derive(Debug, Clone)]
pub struct StructuralField {
    pub name: Symbol,
    pub ty: TypeExpr,
    pub span: Span,
}

/// A method in a structural type constraint: { func get() -> i32 }
#[derive(Debug, Clone)]
pub struct StructuralMethod {
    pub name: Symbol,
    pub params: Vec<TypeExpr>,
    pub return_type: TypeExpr,
    pub span: Span,
}

/// Type expression
#[derive(Debug, Clone)]
pub enum TypeExpr {
    Primitive(PrimitiveType),
    Named(Symbol),
    Array(Box<TypeExpr>),       // [i32], [string], etc.
    Optional(Box<TypeExpr>),    // T? syntax (desugars to Union with Nil)
    Union(Vec<TypeExpr>),       // A | B | C
    Combination(Vec<TypeExpr>), // A + B + C (must satisfy all constraints)
    Nil,                        // nil type
    Done,                       // Done type (iterator termination sentinel)
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
    /// Generic type application: Box<i64>, Map<string, i64>
    Generic {
        name: Symbol,
        args: Vec<TypeExpr>,
    },
    /// Tuple type: [K, V], [A, B, C] - heterogeneous fixed-size collection
    Tuple(Vec<TypeExpr>),
    /// Fixed-size array: [T; 10] - homogeneous fixed-size array
    FixedArray {
        element: Box<TypeExpr>,
        size: usize,
    },
    /// Structural type: { name: string, func get() -> i32 }
    Structural {
        fields: Vec<StructuralField>,
        methods: Vec<StructuralMethod>,
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
    LetTuple(LetTupleStmt),
    Expr(ExprStmt),
    While(WhileStmt),
    For(ForStmt),
    If(IfStmt),
    Break(Span),
    Continue(Span),
    Return(ReturnStmt),
    Raise(RaiseStmt),
}

impl Stmt {
    /// Get the span of this statement
    pub fn span(&self) -> Span {
        match self {
            Stmt::Let(s) => s.span,
            Stmt::LetTuple(s) => s.span,
            Stmt::Expr(s) => s.span,
            Stmt::While(s) => s.span,
            Stmt::For(s) => s.span,
            Stmt::If(s) => s.span,
            Stmt::Break(span) => *span,
            Stmt::Continue(span) => *span,
            Stmt::Return(s) => s.span,
            Stmt::Raise(s) => s.span,
        }
    }
}

/// Initializer for let bindings - either a value expression or a type alias
#[derive(Debug, Clone)]
pub enum LetInit {
    /// Regular value expression: let x = 42
    Expr(Expr),
    /// Type alias: let Numeric = i32 | i64
    TypeAlias(TypeExpr),
}

impl LetInit {
    /// Returns the expression if this is a value init, None for type aliases
    pub fn as_expr(&self) -> Option<&Expr> {
        match self {
            LetInit::Expr(e) => Some(e),
            LetInit::TypeAlias(_) => None,
        }
    }
}

/// Let binding: let x = expr or let mut x = expr
#[derive(Debug, Clone)]
pub struct LetStmt {
    pub name: Symbol,
    pub ty: Option<TypeExpr>,
    pub mutable: bool,
    pub init: LetInit,
    pub span: Span,
}

/// Tuple destructuring: let [a, b] = expr
#[derive(Debug, Clone)]
pub struct LetTupleStmt {
    pub pattern: Pattern,
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

impl Expr {
    /// Returns true if this expression is a literal value (int, float, bool, string, nil)
    pub fn is_literal(&self) -> bool {
        matches!(
            self.kind,
            ExprKind::IntLiteral(_)
                | ExprKind::FloatLiteral(_)
                | ExprKind::BoolLiteral(_)
                | ExprKind::StringLiteral(_)
                | ExprKind::Nil
        )
    }
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

    /// Repeat literal: [0; 10] - creates fixed-size array with repeated value
    RepeatLiteral {
        element: Box<Expr>,
        count: usize,
    },

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

    /// Block expression: { stmts; trailing_expr }
    Block(Box<BlockExpr>),

    /// If expression: if cond { then } else { else }
    If(Box<IfExpr>),
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
    pub type_args: Vec<TypeExpr>,
    pub fields: Vec<StructFieldInit>,
}

/// Field initializer in struct literal
#[derive(Debug, Clone)]
pub struct StructFieldInit {
    pub name: Symbol,
    pub value: Expr,
    pub span: Span,
    /// Whether this field init used shorthand syntax (e.g., `{ x }` instead of `{ x: x }`)
    pub shorthand: bool,
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
    pub type_args: Vec<TypeExpr>,
    pub args: Vec<Expr>,
    pub method_span: Span,
}

/// Yield expression: yield value
#[derive(Debug, Clone)]
pub struct YieldExpr {
    pub value: Expr,
    pub span: Span,
}

/// Block expression: { stmts; trailing_expr }
/// Evaluates to the trailing expression if present, otherwise void/nil
#[derive(Debug, Clone)]
pub struct BlockExpr {
    pub stmts: Vec<Stmt>,
    pub trailing_expr: Option<Expr>,
    pub span: Span,
}

/// If expression: if cond { then_expr } else { else_expr }
/// Both branches evaluate to values of the same type
#[derive(Debug, Clone)]
pub struct IfExpr {
    pub condition: Expr,
    pub then_branch: Expr,
    pub else_branch: Option<Expr>,
    pub span: Span,
}

/// Lambda expression: (params) => body
#[derive(Debug, Clone)]
pub struct LambdaExpr {
    pub type_params: Vec<TypeParam>,
    pub params: Vec<LambdaParam>,
    pub return_type: Option<TypeExpr>,
    pub body: FuncBody,
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

/// Field binding for record destructuring: x or x: alias
#[derive(Debug, Clone)]
pub struct RecordFieldPattern {
    /// The field name in the record
    pub field_name: Symbol,
    /// The variable to bind (same as field_name if no rename)
    pub binding: Symbol,
    pub span: Span,
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
    /// Tuple destructuring pattern: [a, b, c]
    Tuple { elements: Vec<Pattern>, span: Span },
    /// Record destructuring pattern: { x, y } or TypeName { x, y }
    Record {
        /// Optional type name for typed patterns in match arms (e.g., Point in `Point { x, y }`)
        type_name: Option<Symbol>,
        fields: Vec<RecordFieldPattern>,
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
            type_params: vec![],
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
            type_params: vec![],
            params: vec![],
            return_type: None,
            span: Span::default(),
        };
        assert!(ef.native_name.is_none());
    }
}
