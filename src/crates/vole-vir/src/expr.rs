// expr.rs
//
// VIR expression nodes and their supporting types.

use vole_frontend::Expr;
use vole_identity::{FunctionId, Symbol, TypeDefId, TypeId};

use crate::calls::CallTarget;
use crate::func::VirBody;
use crate::refs::VirRef;
use crate::stmt::VirStmt;

// ---------------------------------------------------------------------------
// VirExpr — the central expression enum
// ---------------------------------------------------------------------------

/// A single VIR expression.
///
/// Every variant carries enough information for codegen to emit instructions
/// without consulting sema.  During the incremental migration, the `Ast`
/// escape-hatch lets us lower one expression kind at a time while the rest
/// pass through as raw AST nodes.
#[derive(Debug, Clone)]
pub enum VirExpr {
    // -- Literals -----------------------------------------------------------
    /// Integer literal that fits in 64 bits (i8..i64, u8..u64).
    IntLiteral { value: i64, ty: TypeId },

    /// Wide integer literal (i128) stored as two 64-bit halves.
    WideLiteral { low: u64, high: u64, ty: TypeId },

    /// Floating-point literal (f32 or f64).
    FloatLiteral { value: f64, ty: TypeId },

    /// Boolean literal.
    BoolLiteral(bool),

    /// Interned string literal.
    StringLiteral(Symbol),

    /// The `nil` literal.
    NilLiteral,

    /// Array literal with a homogeneous element type.
    ArrayLiteral {
        elements: Vec<VirRef>,
        elem_ty: TypeId,
    },

    // -- Construction -------------------------------------------------------
    /// Value-type struct construction.
    StructLiteral {
        type_def: TypeDefId,
        fields: Vec<(Symbol, VirRef)>,
    },

    /// Reference-counted class instance creation.
    ClassInstance {
        type_def: TypeDefId,
        fields: Vec<(Symbol, VirRef)>,
    },

    // -- Operators ----------------------------------------------------------
    /// Binary arithmetic, comparison, or logical operation.
    BinaryOp {
        op: VirBinOp,
        lhs: VirRef,
        rhs: VirRef,
        ty: TypeId,
    },

    /// Unary operation (negation, logical/bitwise not).
    UnaryOp {
        op: VirUnOp,
        operand: VirRef,
        ty: TypeId,
    },

    /// String concatenation of two or more parts.
    StringConcat { parts: Vec<VirRef> },

    // -- Calls --------------------------------------------------------------
    /// Function or method call.
    Call {
        target: CallTarget,
        args: Vec<VirRef>,
        ty: TypeId,
    },

    // -- Field access -------------------------------------------------------
    /// Load a field from a struct or class instance.
    FieldLoad {
        object: VirRef,
        field: Symbol,
        storage: FieldStorage,
        ty: TypeId,
    },

    /// Store a value into a field of a struct or class instance.
    FieldStore {
        object: VirRef,
        field: Symbol,
        storage: FieldStorage,
        value: VirRef,
    },

    // -- Reference counting -------------------------------------------------
    /// Increment the reference count of a value.
    RcInc { value: VirRef },

    /// Decrement the reference count of a value.
    RcDec { value: VirRef },

    /// Transfer ownership of a reference-counted value (consume without
    /// decrement).
    RcMove { value: VirRef },

    // -- Coercion -----------------------------------------------------------
    /// Type coercion (numeric widening, boxing, iterator wrapping, etc.).
    Coerce {
        value: VirRef,
        from: TypeId,
        to: TypeId,
        kind: CoerceKind,
    },

    // -- Control flow -------------------------------------------------------
    /// Conditional expression (if/else).
    If {
        cond: VirRef,
        then_body: VirBody,
        else_body: Option<VirBody>,
        ty: TypeId,
    },

    /// Pattern match expression.
    Match {
        scrutinee: VirRef,
        arms: Vec<VirMatchArm>,
        ty: TypeId,
    },

    /// Block expression with an optional trailing value.
    Block {
        stmts: Vec<VirStmt>,
        trailing: Option<VirRef>,
        ty: TypeId,
    },

    // -- Type operations ----------------------------------------------------
    /// Type-check (`x is T`). The `result` field encodes the sema decision
    /// so codegen never re-derives it.
    IsCheck {
        value: VirRef,
        result: IsCheckResult,
        ty: TypeId,
    },

    /// Type cast (`x as T`).
    AsCast {
        value: VirRef,
        target_ty: TypeId,
        kind: AsCastKind,
    },

    // -- Reflection ---------------------------------------------------------
    /// Meta-access (`T.@meta` or `val.@meta`).
    MetaAccess { kind: VirMetaKind, ty: TypeId },

    // -- Variables -----------------------------------------------------------
    /// Load a local variable.
    LocalLoad { name: Symbol, ty: TypeId },

    /// Store into a local variable.
    LocalStore { name: Symbol, value: VirRef },

    // -- Lambda -------------------------------------------------------------
    /// Lambda / closure expression.
    Lambda {
        func_id: FunctionId,
        captures: Vec<VirCapture>,
        ty: TypeId,
    },

    // -- Escape hatch -------------------------------------------------------
    /// An AST expression that has not yet been lowered to VIR.
    ///
    /// `ty` is the sema-computed type so codegen can still make layout
    /// decisions without reaching back into the node map.
    Ast { expr: Box<Expr>, ty: TypeId },
}

// ---------------------------------------------------------------------------
// Supporting types
// ---------------------------------------------------------------------------

/// Binary operator in VIR.
///
/// VIR defines its own operator enum (rather than reusing the AST's) so that
/// desugaring and lowering can introduce operators that have no surface syntax.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VirBinOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    // Comparison
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,

    // Logical
    And,
    Or,

    // Bitwise
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

/// Unary operator in VIR.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VirUnOp {
    /// Arithmetic negation (`-x`).
    Neg,
    /// Logical not (`!x`).
    Not,
    /// Bitwise not (`~x`).
    BitNot,
}

/// Describes the physical storage location of a struct/class field.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FieldStorage {
    /// Field stored inline at the given byte offset.
    Direct { offset: u32 },
    /// Field stored on the heap, accessed through a pointer at the given
    /// byte offset.
    Heap { offset: u32 },
}

/// The kind of type coercion to perform.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CoerceKind {
    /// Widen a smaller integer to a larger one (e.g. i32 -> i64).
    IntExtend,
    /// Truncate a larger integer to a smaller one (e.g. i64 -> i32).
    IntTruncate,
    /// Convert an integer to a float (e.g. i64 -> f64).
    IntToFloat,
    /// Convert a float to an integer (e.g. f64 -> i64).
    FloatToInt,
    /// Widen a smaller float to a larger one (e.g. f32 -> f64).
    FloatExtend,
    /// Truncate a larger float to a smaller one (e.g. f64 -> f32).
    FloatTruncate,
    /// Box a value behind a pointer (for interface coercion).
    Box,
    /// Unbox a pointer back to a concrete value.
    Unbox,
    /// Wrap a concrete iterator into a `RuntimeIterator`.
    IteratorWrap,
}

/// A single arm of a `Match` expression.
#[derive(Debug, Clone)]
pub struct VirMatchArm {
    /// The pattern to match against.
    pub pattern: VirPattern,
    /// Optional guard expression (`when cond`).
    pub guard: Option<VirRef>,
    /// The body to execute if the pattern matches.
    pub body: VirBody,
    /// The type of the arm's result expression.
    pub ty: TypeId,
}

/// A pattern in a `Match` arm.
///
/// Stub: only the `Ast` escape hatch is available for now. Concrete pattern
/// variants will be added as match lowering is migrated to VIR.
#[derive(Debug, Clone)]
pub enum VirPattern {
    /// Escape hatch: a pattern that has not yet been lowered.
    Ast { expr: Box<Expr> },
}

/// Whether an `as` cast is checked or unchecked.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AsCastKind {
    /// Runtime-checked cast (traps on failure).
    Checked,
    /// Unchecked cast (undefined behavior on failure).
    Unchecked,
}

/// The kind of `.@meta` access.
#[derive(Debug, Clone)]
pub enum VirMetaKind {
    /// Static meta: the type is known at compile time.
    Static { type_def: TypeDefId },
    /// Dynamic meta: the value's type is only known at runtime (interface
    /// dispatch through vtable slot 0).
    Dynamic { value: VirRef },
}

/// A captured variable in a lambda / closure.
#[derive(Debug, Clone)]
pub struct VirCapture {
    /// The name of the captured variable.
    pub name: Symbol,
    /// The type of the captured variable.
    pub ty: TypeId,
    /// Whether the variable is captured by reference (true) or by value
    /// (false).
    pub by_ref: bool,
}

/// Result of an `is` type-check, pre-computed by sema.
///
/// VIR defines its own copy of this enum (rather than depending on vole-sema)
/// to keep the VIR crate dependency-light and avoid circular dependencies.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IsCheckResult {
    /// The check always succeeds (e.g. `x is Int` when x is `Int`).
    AlwaysTrue,
    /// The check always fails (e.g. `x is Int` when x is `String`).
    AlwaysFalse,
    /// Runtime check needed: compare against this union variant tag.
    CheckTag(u32),
    /// Runtime check needed for unknown type: compare against this type's
    /// runtime tag.  The `TypeId` indicates what type we are checking for.
    CheckUnknown(TypeId),
}
