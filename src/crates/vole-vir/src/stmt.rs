// stmt.rs
//
// VIR statement nodes.

use vole_identity::{ModuleId, NameId, Symbol, UnionStorageKind, VirTypeId};

use crate::expr::{CoerceKind, FieldStorage};
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
        ty: VirTypeId,
        vir_ty: VirTypeId,
        /// Pre-computed storage classification for the binding type.
        /// Codegen reads this instead of querying `TypeArena` at compile time.
        storage: LetStorageHint,
        /// The explicit type annotation on the binding, if present.
        ///
        /// `Some(type)` when the let has an annotation (e.g. `let x: i64 = ...`);
        /// `None` for untyped lets.  Codegen uses this for MethodCall inits
        /// where the codegen-computed return type may differ from sema's
        /// expression type.
        declared_type: Option<VirTypeId>,
        /// Whether the init expression's type is a struct, requiring a
        /// value-copy to maintain value semantics.  Pre-computed during VIR
        /// lowering so codegen reads a decision instead of querying
        /// `vir_query_is_struct_v()`.
        needs_struct_copy: bool,
        /// Pre-computed coercion kind for the init expression, determined
        /// during VIR lowering when the declared type differs from the init
        /// type.  Codegen passes this hint to `coerce_to_type_hinted()` to
        /// skip the 6-way type detection in `coerce_to_type_detected()`.
        ///
        /// `None` when no coercion is needed (same type), when the coercion
        /// is already handled by `LetStorageHint` (Union, Unknown), or when
        /// the types could not be resolved statically (generic mode).
        init_coercion: Option<CoerceKind>,
    },

    /// Tuple destructuring (`let [a, b] = ...`, `let { x, y } = ...`).
    ///
    /// The pattern is fully lowered to VIR-native `VirDestructurePattern`
    /// during AST-to-VIR lowering.  The `init_ty` is the sema-computed
    /// type of the init expression, used by codegen for layout resolution.
    LetTuple {
        pattern: VirDestructurePattern,
        value: VirRef,
        init_ty: VirTypeId,
        vir_init_ty: VirTypeId,
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
    Return {
        value: Option<VirRef>,
        /// Pre-computed calling convention for the return value.
        /// Codegen reads this instead of querying `TypeArena` at compile time.
        convention: ReturnConvention,
        /// Pre-computed coercion kind for the return value, determined during
        /// VIR lowering when the value type differs from the function's return
        /// type.  Codegen passes this hint to `coerce_to_type_hinted()` to
        /// skip re-detection.
        ///
        /// `None` when no coercion is needed or when the convention already
        /// handles the coercion (InterfaceBox, UnknownBox, Union, Fallible).
        return_coercion: Option<CoerceKind>,
    },

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
    ///
    /// `cleanup` describes the RC strategy for this value's type.
    RcInc {
        value: VirRef,
        cleanup: crate::expr::VirRcCleanup,
    },

    /// Decrement the reference count of a value (fire-and-forget).
    ///
    /// `cleanup` describes the RC strategy for this value's type.
    RcDec {
        value: VirRef,
        cleanup: crate::expr::VirRcCleanup,
    },

    // -- No-op ---------------------------------------------------------------
    /// A no-op statement (e.g. type aliases that produce no runtime code).
    Noop,
}

// ---------------------------------------------------------------------------
// Supporting types
// ---------------------------------------------------------------------------

/// Storage classification for a `let` binding, pre-computed during sema
/// lowering so codegen reads a decision rather than querying `TypeArena`.
///
/// Mirrors the classification in codegen's `coerce_let_init`:
/// - `Unknown` → box init to `TaggedValue`
/// - `Union` → stack-allocate tag + payload buffer
/// - `Interface` → interface boxing (post-coerce phase)
/// - `Numeric` → widen/narrow to target numeric type
/// - `Scalar` → direct value, no special treatment
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LetStorageHint {
    /// The binding type is `unknown` — init values of other types are boxed
    /// to `TaggedValue`.
    Unknown,
    /// The binding type is a union — init values are wrapped with a tag and
    /// stored in a stack-allocated union buffer.
    ///
    /// When `tag_hint` is `Some`, the variant tag, RC state, and coercion
    /// target were pre-computed during sema lowering; codegen reads these
    /// instead of re-deriving them from the type arena at compile time.
    ///
    /// `None` means the tag could not be determined statically (e.g. the
    /// init expression is already a union, is a type parameter, or the
    /// lowering ran in generic mode).
    ///
    /// `init_is_union` is `true` when the init expression's type is itself
    /// a union — codegen should pass the value through without wrapping.
    /// Pre-computed during VIR lowering so codegen reads a decision instead
    /// of querying `vir_query_is_union_v(init.type_id)`.
    Union {
        tag_hint: Option<UnionTagHint>,
        init_is_union: bool,
    },
    /// The binding type is an interface — concrete values are boxed to an
    /// interface pointer (vtable + data).
    Interface,
    /// The init expression is a `RuntimeIterator` assigned to an
    /// interface-typed binding.  Codegen passes the value through without
    /// boxing because `RuntimeIterator` implements `Iterator` dispatch
    /// directly via `runtime_iterator_method`.
    RuntimeIterator,
    /// The binding type is numeric — init values may need widening or
    /// narrowing (e.g. `i32 → i64`, `f32 → f64`).
    Numeric,
    /// Scalar / pass-through — no special storage treatment.
    Scalar,
}

/// Pre-computed union variant tag metadata, determined during sema lowering.
///
/// Codegen stores the `tag` byte at offset 0 of the union buffer and the
/// `is_rc` flag at offset 1 (IS_RC_OFFSET), without querying the type arena
/// to match the value type against the union's variant list.
///
/// `variant_type` is the resolved variant type from the union; codegen uses
/// it to derive the Cranelift target type for integer widening/narrowing of
/// the payload value (same logic as `find_union_variant_tag`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnionTagHint {
    /// Variant index in the union's variant list (the tag byte stored at
    /// offset 0).
    pub tag: u8,
    /// Whether the matched variant type is RC-managed (needs cleanup).
    /// Stored at IS_RC_OFFSET in the union buffer.
    pub is_rc: bool,
    /// The resolved variant type from the union's variant list.
    ///
    /// Codegen uses this to determine whether integer coercion (sextend /
    /// ireduce) is needed between the init value and the union payload slot.
    pub variant_type: VirTypeId,
}

/// Pre-computed return convention for `VirStmt::Return`, determined during
/// VIR lowering based on the enclosing function's return type.
///
/// Mirrors the 7-way dispatch in codegen's `emit_return_value`:
/// - `InterfaceBox` → box the value to an interface pointer
/// - `UnknownBox` → box the value to `TaggedValue`
/// - `Fallible` → multi-register return `(tag, payload)`
/// - `WideFallible` → 3-register return `(tag, low, high)` for i128 success
/// - `Struct` → struct return (codegen determines small vs sret from type)
/// - `Union` → wrap value with union tag
/// - `Scalar` → plain value return
/// - `Void` → no return value
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ReturnConvention {
    /// No return value (void function or bare `return`).
    Void,
    /// Return type is an interface — value must be boxed to interface pointer.
    InterfaceBox,
    /// Return type is `unknown` — value must be boxed to `TaggedValue`.
    UnknownBox,
    /// Return type is fallible — multi-register `(tag, payload)`.
    Fallible,
    /// Return type is fallible with wide (i128) success — `(tag, low, high)`.
    WideFallible,
    /// Return type is a struct — codegen determines small (register) vs sret
    /// (stack pointer) based on the flat slot count.
    Struct,
    /// Return type is a union — value wrapped with tag.
    Union,
    /// Scalar / plain value return.
    Scalar,
    /// Return type is not yet resolved (e.g., contains type parameters that
    /// sema monomorphization hasn't fully substituted).  Codegen falls back to
    /// the old type-query dispatch when it encounters this variant.
    Unresolved,
}

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
    pub var_type: VirTypeId,
    /// VIR type of the loop variable.
    pub vir_var_type: VirTypeId,
    /// The iterable expression.
    pub iterable: VirRef,
    /// The loop body.
    pub body: VirBody,
    /// What kind of iteration to perform.
    pub kind: VirIterKind,
}

/// The iteration strategy for a `VirFor` loop.
///
/// Sema distinguishes six `IterableKind` variants; VIR maps them to seven
/// `VirIterKind` variants.  The sema `IteratorInterface` kind is split
/// into `RuntimeIterator` (direct pass-through) and `IteratorInterface`
/// (needs `InterfaceIter` wrapping) so codegen reads the decision rather
/// than re-detecting the iterator type.
#[derive(Debug, Clone)]
pub enum VirIterKind {
    /// Iterate over a numeric range.
    Range,

    /// Iterate over an array with the given element type.
    Array {
        elem_type: VirTypeId,
        vir_elem_type: VirTypeId,
        /// Union storage annotation for arrays of union-typed elements.
        /// Codegen needs this to decode element values correctly.
        union_storage: Option<UnionStorageKind>,
    },

    /// Iterate over the characters of a string.
    String,

    /// Iterate via a direct `RuntimeIterator` value (pass-through).
    ///
    /// The iterable is already a `RuntimeIterator<T>` — codegen enters the
    /// iter-next loop directly without any wrapping or boxing.
    RuntimeIterator {
        elem_type: VirTypeId,
        vir_elem_type: VirTypeId,
    },

    /// Iterate via an `Iterator<T>` interface value.
    ///
    /// The iterable is a boxed `Iterator<T>` interface pointer.  Codegen
    /// wraps it via `InterfaceIter` into a `RuntimeIterator` before entering
    /// the iter-next loop.
    IteratorInterface {
        elem_type: VirTypeId,
        vir_elem_type: VirTypeId,
    },

    /// Iterate via a concrete class implementing `Iterator<T>`.
    ///
    /// Codegen boxes to `Iterator<T>` interface, then wraps via `InterfaceIter`.
    CustomIterator {
        elem_type: VirTypeId,
        vir_elem_type: VirTypeId,
        /// The `Iterator<T>` interface type, pre-resolved by sema.
        ///
        /// Eliminates codegen's need to reconstruct `Iterator<elem_type>`
        /// via `vir_query_lookup_interface_v()`.
        iterator_interface_type: VirTypeId,
    },

    /// Iterate via a concrete class implementing `Iterable<T>`.
    ///
    /// Codegen calls `.iter()` to get `Iterator<T>`, then wraps via
    /// `InterfaceIter`.
    CustomIterable {
        elem_type: VirTypeId,
        vir_elem_type: VirTypeId,
        /// The `Iterator<T>` interface type, pre-resolved by sema.
        ///
        /// Used as the return type of the `.iter()` call and eliminates
        /// codegen's need to reconstruct `Iterator<elem_type>`.
        iterator_interface_type: VirTypeId,
        /// The iterable class's type name, pre-resolved by sema.
        ///
        /// Together with `iter_method_name_id`, eliminates codegen's
        /// string-based lookup of the `.iter()` method.
        iter_type_name_id: NameId,
        /// The `iter` method's NameId, pre-resolved by sema.
        iter_method_name_id: NameId,
    },

    /// Placeholder for generic lowering mode.
    ///
    /// Used when the iterable expression has a bare type-parameter type and
    /// sema cannot determine the iteration strategy.  Resolved to a concrete
    /// variant during VIR monomorphization.
    Generic {
        elem_type: VirTypeId,
        vir_elem_type: VirTypeId,
    },
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
    Bind {
        name: Symbol,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

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
    /// Each field carries a `FieldStorage` annotation so codegen dispatches
    /// struct (flat) vs class (heap) field extraction without type queries.
    Record {
        fields: Vec<VirDestructureField>,
        source_ty: VirTypeId,
        vir_source_ty: VirTypeId,
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
    FixedArray {
        elem_ty: VirTypeId,
        vir_elem_ty: VirTypeId,
    },
}

/// A single element in a tuple destructure pattern.
#[derive(Debug, Clone)]
pub struct VirDestructureElement {
    /// The nested pattern for this element.
    pub pattern: VirDestructurePattern,
    /// Pre-resolved element type.
    pub ty: VirTypeId,
    /// VIR type of the element.
    pub vir_ty: VirTypeId,
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
    pub ty: VirTypeId,
    /// VIR type of the field.
    pub vir_ty: VirTypeId,
    /// Pre-resolved storage dispatch for this field.
    ///
    /// `Direct { slot }` for struct fields (stack-allocated, loaded via offset),
    /// `Heap { slot }` for class fields (runtime field access),
    /// `ByName` for generic templates or unresolved types.
    pub storage: FieldStorage,
}

/// A single binding in a module destructure pattern.
#[derive(Debug, Clone)]
pub struct VirModuleBinding {
    /// The export name in the module.
    pub export_name: Symbol,
    /// The local binding name (may differ from export name).
    pub binding: Symbol,
    /// The export's type.
    pub export_ty: VirTypeId,
    /// VIR type of the export.
    pub vir_export_ty: VirTypeId,
}
