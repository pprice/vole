// stmt.rs
//
// VIR statement nodes.

use vole_frontend::Stmt;
use vole_identity::{Symbol, TypeId};
use vole_sema::UnionStorageKind;

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

    /// Raise an error value (early return with error propagation).
    ///
    /// `error_name` identifies the error variant (for tag lookup and type
    /// resolution).  `fields` are the named field initializers, already
    /// lowered to VIR expressions.  The function's return type (available
    /// in codegen via `self.return_type`) provides the fallible type
    /// context needed to compute the error tag and payload layout.
    Raise {
        error_name: Symbol,
        fields: Vec<(Symbol, VirRef)>,
    },

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
/// VIR collapses sema's six `IterableKind` variants down to five
/// [`VirIterKind`] variants.  The loop body for all RuntimeIterator-based
/// kinds shares the same `iter_next` protocol; they differ only in how
/// the RuntimeIterator value is obtained (setup phase).
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
/// Sema distinguishes six `IterableKind` variants; VIR maps them to five
/// `VirIterKind` variants.  `IteratorInterface` and `CustomIterator` are
/// kept separate because their setup differs (interface wrapping vs
/// boxing + wrapping), while `CustomIterable` has its own variant because
/// codegen must call `.iter()` before wrapping.
#[derive(Debug, Clone)]
pub enum VirIterKind {
    /// Iterate over a numeric range.
    Range,

    /// Iterate over an array with the given element type.
    Array {
        elem_type: TypeId,
        /// Union storage annotation for arrays of union-typed elements.
        /// Codegen needs this to decode element values correctly.
        union_storage: Option<UnionStorageKind>,
    },

    /// Iterate over the characters of a string.
    String,

    /// Iterate via an `Iterator<T>` interface or `RuntimeIterator` value.
    ///
    /// The compiled iterable may be a direct `RuntimeIterator` (pass through)
    /// or an `Iterator<T>` interface (needs `InterfaceIter` wrapping).
    /// Codegen inspects the compiled value's type to choose the path.
    IteratorInterface { elem_type: TypeId },

    /// Iterate via a concrete class implementing `Iterator<T>`.
    ///
    /// Codegen boxes to `Iterator<T>` interface, then wraps via `InterfaceIter`.
    CustomIterator { elem_type: TypeId },

    /// Iterate via a concrete class implementing `Iterable<T>`.
    ///
    /// Codegen calls `.iter()` to get `Iterator<T>`, then wraps via
    /// `InterfaceIter`.
    CustomIterable { elem_type: TypeId },
}
