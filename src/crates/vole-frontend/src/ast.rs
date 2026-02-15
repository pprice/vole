// src/frontend/ast.rs

use crate::Span;

/// Unique identifier for symbols (interned strings)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(u32);

impl Symbol {
    /// The unknown/fallback symbol (index 0).
    pub const UNKNOWN: Self = Self(0);

    /// Create a Symbol from a raw index. Only the interner should use this.
    pub(crate) fn new(index: u32) -> Self {
        Self(index)
    }

    /// Return the underlying index.
    pub fn index(self) -> u32 {
        self.0
    }

    /// Create a synthetic symbol with a high-bit index that won't collide
    /// with user symbols. Used for synthetic type parameters.
    pub fn synthetic(offset: u32) -> Self {
        Self(0x8000_0000 + offset)
    }

    /// Create a Symbol with an arbitrary index in test code.
    #[cfg(any(test, feature = "testing"))]
    pub fn new_for_test(index: u32) -> Self {
        Self(index)
    }
}

/// Unique identifier for AST nodes (expressions, statements, declarations)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct NodeId(u32);

impl NodeId {
    /// Create a NodeId from a raw index. Only the parser and code generators should use this.
    pub fn new(index: u32) -> Self {
        Self(index)
    }

    /// Return the underlying index.
    pub fn index(self) -> u32 {
        self.0
    }

    /// Create a NodeId with an arbitrary index in test code.
    #[cfg(any(test, feature = "testing"))]
    pub fn new_for_test(index: u32) -> Self {
        Self(index)
    }
}

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

/// An interface in a constraint, optionally with type arguments.
/// E.g., `Stringable` or `Producer<T>`.
#[derive(Debug, Clone)]
pub struct ConstraintInterface {
    pub name: Symbol,
    pub type_args: Vec<TypeExpr>,
}

/// Constraint on a type parameter
#[derive(Debug, Clone)]
pub enum TypeConstraint {
    /// Interface constraints: T: Stringable or T: Hashable + Eq or T: Producer<U>
    Interface(Vec<ConstraintInterface>),
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
    LetTuple(LetTupleStmt), // Top-level destructuring: let { a, b } = import "..."
    Class(ClassDecl),

    Struct(StructDecl),
    Interface(InterfaceDecl),
    Implement(ImplementBlock),
    Error(ErrorDecl),
    Sentinel(SentinelDecl),
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
    /// Scoped declarations (func, let, class, etc.) and nested tests blocks
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
    pub default_value: Option<Box<Expr>>,
    pub span: Span,
}

/// Field definition in a class
#[derive(Debug, Clone)]
pub struct FieldDef {
    pub name: Symbol,
    pub ty: TypeExpr,
    pub default_value: Option<Box<Expr>>,
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

/// Struct declaration (stack-allocated value type with C-ABI-compatible layout)
#[derive(Debug, Clone)]
pub struct StructDecl {
    pub name: Symbol,
    pub type_params: Vec<TypeParam>,
    pub fields: Vec<FieldDef>,
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

/// Type mapping entry for generic external functions.
/// Maps a concrete type to an intrinsic key.
/// Example: `f32 => "f32_sqrt"` maps f32 to the "f32_sqrt" intrinsic.
#[derive(Debug, Clone)]
pub struct TypeMapping {
    pub type_expr: TypeExpr,
    pub intrinsic_key: String,
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
    /// Type-to-intrinsic mappings for generic external functions.
    /// Each mapping specifies which intrinsic key to use for a concrete type.
    /// Example: `where { f32 => "f32_sqrt", f64 => "f64_sqrt" }`
    pub type_mappings: Option<Vec<TypeMapping>>,
    pub span: Span,
}

/// Error type declaration: error Name { fields }
#[derive(Debug, Clone)]
pub struct ErrorDecl {
    pub name: Symbol,
    pub fields: Vec<FieldDef>,
    pub span: Span,
}

/// Sentinel type declaration: sentinel Name
/// Body-less declaration for unique marker types (e.g., Done, None).
#[derive(Debug, Clone)]
pub struct SentinelDecl {
    pub name: Symbol,
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

/// Type expression with source location
#[derive(Debug, Clone)]
pub struct TypeExpr {
    pub kind: TypeExprKind,
    pub span: Span,
}

impl TypeExpr {
    /// Create a new TypeExpr with a kind and span.
    pub fn new(kind: TypeExprKind, span: Span) -> Self {
        Self { kind, span }
    }

    /// Create a synthetic TypeExpr with a default (zero) span.
    /// Used for compiler-generated type expressions that have no source location.
    pub fn synthetic(kind: TypeExprKind) -> Self {
        Self {
            kind,
            span: Span::default(),
        }
    }
}

/// The kind of a type expression
#[derive(Debug, Clone)]
pub enum TypeExprKind {
    Primitive(PrimitiveType),
    Named(Symbol),
    Array(Box<TypeExpr>),       // [i32], [string], etc.
    Optional(Box<TypeExpr>),    // T? syntax (desugars to Union with Nil)
    Union(Vec<TypeExpr>),       // A | B | C
    Combination(Vec<TypeExpr>), // A + B + C (must satisfy all constraints)
    Handle,                     // handle type (opaque native pointer)
    Never,                      // never type (bottom type - no values)
    Unknown,                    // unknown type (top type - any value)
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
    /// Qualified path: mod.Interface or mod.Interface<T>
    /// Used for implement blocks with module-qualified interface names.
    QualifiedPath {
        /// Path segments: [mod, Interface] for mod.Interface
        segments: Vec<Symbol>,
        /// Optional type arguments for generic interfaces
        args: Vec<TypeExpr>,
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
    /// Returns true if this expression is a literal value (int, float, bool, string)
    pub fn is_literal(&self) -> bool {
        matches!(
            self.kind,
            ExprKind::IntLiteral(..)
                | ExprKind::FloatLiteral(..)
                | ExprKind::BoolLiteral(_)
                | ExprKind::StringLiteral(_)
        )
    }

    /// Returns true if this expression can be compiled using the `select` instruction.
    ///
    /// Selectable expressions are pure (no side effects) and don't involve:
    /// - Function/method calls (might have side effects)
    /// - Assignments
    /// - Statements (only pure expressions)
    /// - Nested control flow (if/when/match)
    ///
    /// Used to optimize simple conditionals like `if cond then a else b`.
    pub fn is_selectable(&self) -> bool {
        match &self.kind {
            // Literals are always selectable
            ExprKind::IntLiteral(..)
            | ExprKind::FloatLiteral(..)
            | ExprKind::BoolLiteral(_)
            | ExprKind::StringLiteral(_) => true,

            // Simple identifier lookups are selectable
            ExprKind::Identifier(_) => true,

            // Grouping preserves selectability
            ExprKind::Grouping(inner) => inner.is_selectable(),

            // Binary ops on selectable operands (arithmetic, comparison, etc.)
            // Div and Mod can trap on division by zero, so they are NOT selectable
            // (select evaluates both arms eagerly, which would trigger the trap)
            ExprKind::Binary(bin) => {
                !matches!(bin.op, BinaryOp::Div | BinaryOp::Mod)
                    && bin.left.is_selectable()
                    && bin.right.is_selectable()
            }

            // Unary ops on selectable operand
            ExprKind::Unary(un) => un.operand.is_selectable(),

            // Tuple/array literals with all selectable elements
            ExprKind::ArrayLiteral(elements) => elements.iter().all(|e| e.is_selectable()),

            // Repeat literals with selectable element
            ExprKind::RepeatLiteral { element, .. } => element.is_selectable(),

            // Index on selectable object (no side effects from read)
            ExprKind::Index(idx) => idx.object.is_selectable() && idx.index.is_selectable(),

            // Field access on selectable object
            ExprKind::FieldAccess(fa) => fa.object.is_selectable(),

            // Block expressions are selectable if they have no statements and
            // their trailing expression (if any) is selectable
            // This handles `{ expr }` blocks used in if-else branches
            ExprKind::Block(block) => {
                block.stmts.is_empty()
                    && block
                        .trailing_expr
                        .as_ref()
                        .is_some_and(|e| e.is_selectable())
            }

            // NOT selectable: function calls, method calls, assignments, control flow
            ExprKind::Call(_)
            | ExprKind::MethodCall(_)
            | ExprKind::Assign(_)
            | ExprKind::CompoundAssign(_)
            | ExprKind::If(_)
            | ExprKind::When(_)
            | ExprKind::Match(_)
            | ExprKind::Lambda(_)
            | ExprKind::Try(_)
            | ExprKind::NullCoalesce(_)
            | ExprKind::OptionalChain(_)
            | ExprKind::Is(_)
            | ExprKind::InterpolatedString(_)
            | ExprKind::Range(_)
            | ExprKind::StructLiteral(_)
            | ExprKind::TypeLiteral(_)
            | ExprKind::Import(_)
            | ExprKind::Yield(_)
            | ExprKind::Unreachable => false,
        }
    }
}

/// Typed numeric literal suffix (e.g., `_u8`, `_f32`)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NumericSuffix {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    I128,
    F32,
    F64,
}

impl NumericSuffix {
    /// Parse a suffix string (without the leading underscore) into a NumericSuffix.
    pub fn parse(s: &str) -> Option<NumericSuffix> {
        match s {
            "u8" => Some(NumericSuffix::U8),
            "u16" => Some(NumericSuffix::U16),
            "u32" => Some(NumericSuffix::U32),
            "u64" => Some(NumericSuffix::U64),
            "i8" => Some(NumericSuffix::I8),
            "i16" => Some(NumericSuffix::I16),
            "i32" => Some(NumericSuffix::I32),
            "i64" => Some(NumericSuffix::I64),
            "i128" => Some(NumericSuffix::I128),
            "f32" => Some(NumericSuffix::F32),
            "f64" => Some(NumericSuffix::F64),
            _ => None,
        }
    }

    /// Whether this is a float suffix (f32, f64).
    pub fn is_float(self) -> bool {
        matches!(self, NumericSuffix::F32 | NumericSuffix::F64)
    }

    /// Whether this is an integer suffix (u8..u64, i8..i64).
    pub fn is_integer(self) -> bool {
        !self.is_float()
    }

    /// The suffix as a string (e.g., "u8", "f32").
    pub fn as_str(self) -> &'static str {
        match self {
            NumericSuffix::U8 => "u8",
            NumericSuffix::U16 => "u16",
            NumericSuffix::U32 => "u32",
            NumericSuffix::U64 => "u64",
            NumericSuffix::I8 => "i8",
            NumericSuffix::I16 => "i16",
            NumericSuffix::I32 => "i32",
            NumericSuffix::I64 => "i64",
            NumericSuffix::I128 => "i128",
            NumericSuffix::F32 => "f32",
            NumericSuffix::F64 => "f64",
        }
    }

    /// Convert to the corresponding PrimitiveType.
    pub fn to_primitive_type(self) -> PrimitiveType {
        match self {
            NumericSuffix::U8 => PrimitiveType::U8,
            NumericSuffix::U16 => PrimitiveType::U16,
            NumericSuffix::U32 => PrimitiveType::U32,
            NumericSuffix::U64 => PrimitiveType::U64,
            NumericSuffix::I8 => PrimitiveType::I8,
            NumericSuffix::I16 => PrimitiveType::I16,
            NumericSuffix::I32 => PrimitiveType::I32,
            NumericSuffix::I64 => PrimitiveType::I64,
            NumericSuffix::I128 => PrimitiveType::I128,
            NumericSuffix::F32 => PrimitiveType::F32,
            NumericSuffix::F64 => PrimitiveType::F64,
        }
    }
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    // Literals
    IntLiteral(i64, Option<NumericSuffix>),
    FloatLiteral(f64, Option<NumericSuffix>),
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

    /// Unreachable expression (never type / bottom type)
    Unreachable,

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

    /// When expression (subject-less conditional chains)
    /// Syntax: `when { cond1 => result1, cond2 => result2, _ => default }`
    When(Box<WhenExpr>),
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
    /// Discard pattern: _ = expr
    Discard,
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
    pub id: NodeId,
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
    pub span: Span,
}

/// When expression (subject-less conditional chains)
/// Syntax: `when { cond1 => result1, cond2 => result2, _ => default }`
#[derive(Debug, Clone)]
pub struct WhenExpr {
    pub arms: Vec<WhenArm>,
    pub span: Span,
}

/// A single arm in a when expression
#[derive(Debug, Clone)]
pub struct WhenArm {
    /// The condition (None for wildcard `_` arm which always matches)
    pub condition: Option<Expr>,
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

/// Struct literal expression: Name { field: value, ... } or mod.Name { field: value, ... }
#[derive(Debug, Clone)]
pub struct StructLiteralExpr {
    /// Path segments for the type name: [Name] or [mod, Name]
    pub path: Vec<Symbol>,
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
}

/// Lambda parameter (may have inferred type)
#[derive(Debug, Clone)]
pub struct LambdaParam {
    pub name: Symbol,
    pub ty: Option<TypeExpr>,
    pub default_value: Option<Box<Expr>>,
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
pub struct Pattern {
    pub id: NodeId,
    pub kind: PatternKind,
    pub span: Span,
}

/// Pattern kind - the different forms a pattern can take
#[derive(Debug, Clone)]
pub enum PatternKind {
    /// Wildcard pattern: _
    Wildcard,
    /// Literal pattern: 1, "hello", true, -5
    Literal(Expr),
    /// Identifier pattern (binds value): n
    Identifier { name: Symbol },
    /// Type pattern: i32, string, nil, MyClass
    Type { type_expr: TypeExpr },
    /// Val pattern: val x (compares against existing variable)
    Val { name: Symbol },
    /// Success pattern for fallible match: success x, success, success Point { x, y }
    Success {
        inner: Option<Box<Pattern>>, // None = bare success, Some = success <pattern>
    },
    /// Error pattern for fallible match: error e, error, error DivByZero, error DivByZero { msg }
    Error {
        inner: Option<Box<Pattern>>, // None = bare error, Some = error <pattern>
    },
    /// Tuple destructuring pattern: [a, b, c]
    Tuple { elements: Vec<Pattern> },
    /// Record destructuring pattern: { x, y } or TypeName { x, y }
    Record {
        /// Optional type expression for typed patterns in match arms
        /// (e.g., `Point` or `MapEntry<K, V>` in `Point { x, y }` / `MapEntry<K, V> { key }`)
        type_name: Option<TypeExpr>,
        fields: Vec<RecordFieldPattern>,
    },
}

// Compile-time Send + Sync assertions for key AST types.
//
// These assertions verify that AST types can be safely shared across threads,
// enabling future parallel compilation pipelines.
#[allow(dead_code)]
const _: () = {
    fn assert_send<T: Send>() {}
    fn assert_sync<T: Sync>() {}
    fn check() {
        assert_send::<Program>();
        assert_send::<Expr>();
        assert_send::<ExprKind>();
        assert_send::<LambdaExpr>();
        assert_send::<Stmt>();
        assert_send::<Decl>();
        assert_send::<Block>();
        assert_send::<Pattern>();
        assert_send::<TypeExpr>();
        assert_send::<TypeExprKind>();
        assert_sync::<Program>();
        assert_sync::<Expr>();
        assert_sync::<ExprKind>();
        assert_sync::<LambdaExpr>();
        assert_sync::<Stmt>();
        assert_sync::<Decl>();
        assert_sync::<Block>();
        assert_sync::<Pattern>();
        assert_sync::<TypeExpr>();
    }
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn external_func_native_name() {
        let ef = ExternalFunc {
            native_name: Some("string_length".to_string()),
            vole_name: Symbol::new_for_test(1),
            type_params: vec![],
            params: vec![],
            return_type: None,
            type_mappings: None,
            span: Span::default(),
        };
        assert_eq!(ef.native_name.as_deref(), Some("string_length"));
    }

    #[test]
    fn external_func_default_name() {
        let ef = ExternalFunc {
            native_name: None,
            vole_name: Symbol::new_for_test(1),
            type_params: vec![],
            params: vec![],
            return_type: None,
            type_mappings: None,
            span: Span::default(),
        };
        assert!(ef.native_name.is_none());
    }
}
