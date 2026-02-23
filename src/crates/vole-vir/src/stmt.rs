// stmt.rs
//
// VIR statement nodes.

use vole_frontend::Stmt;
use vole_identity::{Symbol, TypeId};

use crate::expr::FieldStorage;
use crate::func::VirBody;
use crate::refs::VirRef;

// ---------------------------------------------------------------------------
// VirStmt — the central statement enum
// ---------------------------------------------------------------------------

/// A single VIR statement.
///
/// Like `VirExpr`, the `Ast` variant is a temporary escape hatch for
/// statements that have not yet been lowered from the AST.
///
/// Note: there is no `If` variant — Vole's `if/else` is an expression, so
/// conditional logic lives in [`VirExpr::If`] wrapped in `VirStmt::Expr`.
#[derive(Debug, Clone)]
pub enum VirStmt {
    // -- Bindings -----------------------------------------------------------
    /// Local variable binding (`let x = ...`).
    Let {
        name: Symbol,
        value: VirRef,
        mutable: bool,
        ty: TypeId,
    },

    /// Tuple destructuring (`let (a, b) = ...`).
    LetTuple {
        names: Vec<Symbol>,
        value: VirRef,
        types: Vec<TypeId>,
    },

    // -- Assignment ---------------------------------------------------------
    /// Assignment to a local, field, or index target.
    Assign { target: AssignTarget, value: VirRef },

    // -- Expression as statement --------------------------------------------
    /// An expression used as a statement (its value is discarded).
    Expr { value: VirRef },

    // -- Loops --------------------------------------------------------------
    /// While loop.
    While { cond: VirRef, body: VirBody },

    /// For loop (iterating over a range, array, string, or runtime iterator).
    For(VirFor),

    // -- Control flow -------------------------------------------------------
    /// Return from the enclosing function.
    Return { value: Option<VirRef> },

    /// Break out of the enclosing loop.
    Break,

    /// Continue to the next iteration of the enclosing loop.
    Continue,

    /// Raise an error value.
    Raise { value: VirRef },

    // -- Reference counting (statement form) --------------------------------
    /// Increment the reference count of a value (fire-and-forget).
    RcInc { value: VirRef },

    /// Decrement the reference count of a value (fire-and-forget).
    RcDec { value: VirRef },

    // -- Escape hatch -------------------------------------------------------
    /// An AST statement not yet lowered to VIR.
    Ast { stmt: Box<Stmt> },
}

// ---------------------------------------------------------------------------
// Supporting types
// ---------------------------------------------------------------------------

/// The target of an assignment statement.
#[derive(Debug, Clone)]
pub enum AssignTarget {
    /// Assign to a local variable.
    Local(Symbol),

    /// Assign to a field of a struct or class instance.
    Field {
        object: VirRef,
        field: Symbol,
        storage: FieldStorage,
    },

    /// Assign to an array element by index.
    Index { array: VirRef, index: VirRef },
}

/// A for-loop in VIR.
///
/// VIR collapses sema's six `IterableKind` variants down to four
/// [`VirIterKind`] variants — `CustomIterator`, `CustomIterable`, and
/// `IteratorInterface` all become [`VirIterKind::RuntimeIterator`].
#[derive(Debug, Clone)]
pub struct VirFor {
    /// The loop variable name.
    pub var_name: Symbol,
    /// The type of the loop variable.
    pub var_type: TypeId,
    /// The iterable expression.
    pub iterable: VirRef,
    /// The loop body.
    pub body: VirBody,
    /// What kind of iteration to perform.
    pub kind: VirIterKind,
}

/// The iteration strategy for a `VirFor` loop.
///
/// Sema distinguishes six `IterableKind` variants; VIR collapses them to four.
/// `CustomIterator`, `CustomIterable`, and `IteratorInterface` all map to
/// `RuntimeIterator` because they share the same codegen path (call `.next()`
/// on a `RuntimeIterator` value).
#[derive(Debug, Clone)]
pub enum VirIterKind {
    /// Iterate over a numeric range.
    Range,

    /// Iterate over an array with the given element type.
    Array { elem_type: TypeId },

    /// Iterate over the characters of a string.
    String,

    /// Iterate via a `RuntimeIterator` with the given element type.
    ///
    /// This covers sema's `CustomIterator`, `CustomIterable`, and
    /// `IteratorInterface` variants — all use the same `.next()` protocol
    /// at runtime.
    RuntimeIterator { elem_type: TypeId },
}
