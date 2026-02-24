// stmt.rs
//
// VIR statement nodes.

use vole_identity::{ModuleId, Symbol, TypeId, UnionStorageKind};

use crate::expr::FieldStorage;
use crate::func::VirBody;
use crate::refs::VirRef;

// ---------------------------------------------------------------------------
// VirStmt — the central statement enum
// ---------------------------------------------------------------------------

/// A single VIR statement.
///
/// All AST statement kinds are fully lowered to typed VIR nodes.
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

    /// Tuple destructuring (`let [a, b] = ...`, `let { x, y } = ...`).
    ///
    /// The pattern is fully lowered to VIR-native `VirDestructurePattern`
    /// during AST-to-VIR lowering.  The `init_ty` is the sema-computed
    /// type of the init expression, used by codegen for layout resolution.
    LetTuple {
        pattern: VirDestructurePattern,
        value: VirRef,
        init_ty: TypeId,
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

    // -- No-op ---------------------------------------------------------------
    /// A no-op statement (e.g. type aliases that produce no runtime code).
    Noop,
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

// ---------------------------------------------------------------------------
// LetTuple destructuring patterns
// ---------------------------------------------------------------------------

/// A destructuring pattern for `LetTuple` statements.
///
/// This is a simpler subset of `VirPattern` (used for match arms) that
/// covers only the patterns valid in `let` destructuring: binding,
/// wildcard, nested tuple, record (struct/class), and module.
///
/// All type information is pre-resolved during lowering so codegen
/// reads decisions rather than consulting the `TypeArena`.
#[derive(Debug, Clone)]
pub enum VirDestructurePattern {
    /// Bind a variable: `a`.
    Bind { name: Symbol, ty: TypeId },

    /// Wildcard: `_` — matches but binds nothing.
    Wildcard,

    /// Tuple or fixed-array destructuring: `[a, b, c]`.
    ///
    /// Each element carries its pre-resolved type from
    /// `TypeArena::unwrap_tuple` or `unwrap_fixed_array`.
    Tuple {
        elements: Vec<VirDestructureElement>,
        kind: DestructureTupleKind,
    },

    /// Record (struct/class) destructuring: `let { x, y } = point`.
    ///
    /// Field slots and types are pre-resolved from `EntityRegistry`.
    /// `is_struct` distinguishes flat struct layout from heap class layout.
    Record {
        fields: Vec<VirDestructureField>,
        source_ty: TypeId,
        is_struct: bool,
    },

    /// Module destructuring: `let { A, B } = import "mod"`.
    ///
    /// Module bindings are compile-time only (no runtime code generated).
    /// Each binding maps an export name to a local binding symbol.
    Module {
        bindings: Vec<VirModuleBinding>,
        module_id: ModuleId,
    },
}

/// The kind of tuple-like destructuring.
#[derive(Debug, Clone, Copy)]
pub enum DestructureTupleKind {
    /// True tuple: element types may differ.
    Tuple,
    /// Fixed-size array: all elements share the same type.
    FixedArray { elem_ty: TypeId },
}

/// A single element in a tuple destructure pattern.
#[derive(Debug, Clone)]
pub struct VirDestructureElement {
    /// The nested pattern for this element.
    pub pattern: VirDestructurePattern,
    /// Pre-resolved element type.
    pub ty: TypeId,
}

/// A single field binding in a record destructure pattern.
#[derive(Debug, Clone)]
pub struct VirDestructureField {
    /// The field name in the type definition.
    pub field_name: Symbol,
    /// The variable name to bind (may differ via rename syntax `x: alias`).
    pub binding: Symbol,
    /// Pre-resolved field slot index from `EntityRegistry`.
    pub slot: u32,
    /// Pre-resolved field type from `EntityRegistry`.
    pub ty: TypeId,
}

/// A single binding in a module destructure pattern.
#[derive(Debug, Clone)]
pub struct VirModuleBinding {
    /// The export name in the module.
    pub export_name: Symbol,
    /// The local binding name (may differ from export name).
    pub binding: Symbol,
    /// The export's type.
    pub export_ty: TypeId,
}
