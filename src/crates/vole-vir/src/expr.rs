// expr.rs
//
// VIR expression nodes and their supporting types.

use vole_identity::{
    MethodId, ModuleId, NameId, NodeId, StringConversion, Symbol, TypeDefId, UnionStorageKind,
    VirTypeId,
};

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
/// without consulting sema.  All AST expression kinds are fully lowered to
/// typed VIR nodes.
#[derive(Debug, Clone)]
pub enum VirExpr {
    // -- Literals -----------------------------------------------------------
    /// Integer literal that fits in 64 bits (i8..i64, u8..u64).
    IntLiteral {
        value: i64,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    /// Wide integer literal (i128) stored as two 64-bit halves.
    WideLiteral {
        low: u64,
        high: u64,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    /// Floating-point literal (f32 or f64).
    FloatLiteral {
        value: f64,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    /// Boolean literal.
    BoolLiteral(bool),

    /// Interned string literal.
    StringLiteral(Symbol),

    /// The `nil` literal.
    NilLiteral,

    /// Unreachable expression (never type / bottom type).
    ///
    /// Emits a trap instruction with file:line info if reached at runtime.
    Unreachable { line: u32 },

    /// Import expression — compile-time module value placeholder.
    ///
    /// At runtime this is just a zero value; actual function calls go through
    /// the method resolution mechanism.
    Import { ty: VirTypeId, vir_ty: VirTypeId },

    /// Type literal used as a runtime value — always an error if reached.
    TypeLiteral,

    /// Range expression (`start..end` or `start..=end`).
    ///
    /// For inclusive ranges, codegen adds 1 to `end` so the runtime iterator
    /// uses exclusive-end semantics internally.
    Range {
        start: VirRef,
        end: VirRef,
        inclusive: bool,
    },

    /// Array literal `[a, b, c]`.
    ///
    /// `ty` is the overall inferred type (array or tuple) from sema.
    /// Codegen uses `unwrap_array(ty)` / `unwrap_tuple(ty)` to dispatch
    /// between dynamic array (heap) and tuple (stack) construction paths.
    ArrayLiteral {
        elements: Vec<VirRef>,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    /// Repeat literal `[value; count]` — fixed-size array with repeated value.
    ///
    /// `ty` is the sema-inferred fixed-array type (e.g. `[i64; 4]`).
    /// Codegen allocates a stack slot and stores the element at each position.
    RepeatLiteral {
        element: VirRef,
        count: usize,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    // -- Construction -------------------------------------------------------
    /// Value-type struct construction (stack-allocated).
    ///
    /// `type_def` is the resolved `TypeDefId` from the entity registry.
    /// `ty` is the sema-inferred result type (may include generic args).
    /// `fields` are the explicitly provided field initializers; omitted default
    /// fields are compiled via `VirProgram::field_default_inits`.
    StructLiteral {
        type_def: TypeDefId,
        fields: Vec<(Symbol, VirRef)>,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    /// Reference-counted class instance creation (heap-allocated).
    ///
    /// `type_def` is the resolved `TypeDefId` from the entity registry.
    /// `ty` is the sema-inferred result type (may include generic args).
    /// `fields` are the explicitly provided field initializers; omitted default
    /// fields are compiled via `VirProgram::field_default_inits`.
    ///
    /// `field_coercions` is a parallel vec of pre-computed coercion hints for
    /// each field in `fields`.  Codegen reads these instead of querying
    /// `vir_query_is_interface_v()` at compile time.  Empty when lowered in
    /// generic mode (codegen falls back to type queries).
    ClassInstance {
        type_def: TypeDefId,
        fields: Vec<(Symbol, VirRef)>,
        field_coercions: Vec<FieldCoercionHint>,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    // -- Operators ----------------------------------------------------------
    /// Binary arithmetic, comparison, or logical operation.
    BinaryOp {
        op: VirBinOp,
        lhs: VirRef,
        rhs: VirRef,
        ty: VirTypeId,
        vir_ty: VirTypeId,
        /// Source line for panic messages (division by zero, overflow).
        line: u32,
        /// Pre-computed: the left operand's type is optional (`T?`).
        ///
        /// Used by Eq/Ne comparisons to dispatch to the nil-comparison path
        /// without querying `vir_query_is_optional_v()` at codegen time.
        /// Set during VIR lowering; re-derived after monomorphization.
        lhs_is_optional: bool,
        /// Pre-computed: the right operand's type is optional (`T?`).
        ///
        /// Symmetric with `lhs_is_optional`.
        rhs_is_optional: bool,
        /// Pre-computed: the left operand's type is an unsigned integer.
        ///
        /// Used by Div, Mod, Shr, and comparison operations to select
        /// unsigned Cranelift instructions (`udiv`, `ushr`, unsigned `icmp`)
        /// without querying `VirTypeId::is_unsigned_int()` at codegen time.
        /// Set during VIR lowering; re-derived after monomorphization.
        lhs_is_unsigned: bool,
    },

    /// Unary operation (negation, logical/bitwise not).
    UnaryOp {
        op: VirUnOp,
        operand: VirRef,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    /// String concatenation of two or more parts.
    StringConcat { parts: Vec<VirRef> },

    /// Interpolated string with conversion annotations per part.
    ///
    /// Each part is either a literal string or an expression with an
    /// associated `StringConversion` that tells codegen how to turn the
    /// value into a string.  Single-part interpolations preserve the
    /// borrowed/owned lifecycle of the original expression.
    InterpolatedString { parts: Vec<VirStringPart> },

    // -- Calls --------------------------------------------------------------
    /// Function or method call.
    Call {
        target: CallTarget,
        args: Vec<VirRef>,
        ty: VirTypeId,
        vir_ty: VirTypeId,
        /// Pre-computed: the result type is fallible (`T!E`).
        ///
        /// Used by lambda call result handling to dispatch to the
        /// tag+payload reconstruction path without querying
        /// `vir_query_is_fallible()` at codegen time.
        /// Set during VIR lowering; re-derived after monomorphization.
        result_is_fallible: bool,
    },

    /// Method call on a receiver object.
    ///
    /// Method dispatch has 6+ paths (direct, implemented, interface,
    /// default, functional-interface, static) plus builtin and iterator
    /// specialisations.  `dispatch` carries all sema-resolved routing metadata
    /// needed for VIR-native codegen dispatch.
    ///
    /// The receiver and arguments are pre-lowered to VIR refs.  Codegen
    /// consumes `dispatch` directly; `node_id` is retained only as a legacy
    /// compatibility field for non-dispatch uses.
    MethodCall {
        receiver: VirRef,
        method: Symbol,
        args: Vec<VirRef>,
        dispatch: VirMethodDispatchMeta,
        node_id: NodeId,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    // -- Field access -------------------------------------------------------
    /// Load a field from a struct or class instance.
    FieldLoad {
        object: VirRef,
        field: Symbol,
        storage: FieldStorage,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    /// Store a value into a field of a struct or class instance.
    FieldStore {
        object: VirRef,
        field: Symbol,
        storage: FieldStorage,
        value: VirRef,
    },

    // -- Indexing -----------------------------------------------------------
    /// Index read: `obj[idx]` for tuple, fixed array, or dynamic array.
    ///
    /// Codegen dispatches on the object type (tuple, fixed array, dynamic
    /// array) to select the right read strategy.  `union_storage` carries
    /// the sema-annotated `UnionStorageKind` for dynamic arrays whose
    /// element type is a union.
    Index {
        object: VirRef,
        index: VirRef,
        ty: VirTypeId,
        vir_ty: VirTypeId,
        union_storage: Option<UnionStorageKind>,
    },

    /// Index write: `obj[idx] = val` for fixed or dynamic array.
    ///
    /// Codegen dispatches on the object type to select fixed-array (bounds
    /// check + direct store) or dynamic-array (runtime `ArraySet` call).
    IndexStore {
        object: VirRef,
        index: VirRef,
        value: VirRef,
        union_storage: Option<UnionStorageKind>,
    },

    // -- Reference counting -------------------------------------------------
    /// Increment the reference count of a value.
    ///
    /// `cleanup` describes the RC strategy for this value's type.  Codegen
    /// reads this instead of querying the type arena to determine whether
    /// special handling is needed (interface fat-pointer extraction, unknown
    /// heap cleanup, etc.).
    RcInc {
        value: VirRef,
        cleanup: VirRcCleanup,
    },

    /// Decrement the reference count of a value.
    ///
    /// `cleanup` describes the RC strategy for this value's type.  Codegen
    /// reads this instead of querying the type arena.
    RcDec {
        value: VirRef,
        cleanup: VirRcCleanup,
    },

    /// Transfer ownership of a reference-counted value (consume without
    /// decrement).
    RcMove { value: VirRef },

    // -- Coercion -----------------------------------------------------------
    /// Type coercion (numeric widening, boxing, iterator wrapping, etc.).
    Coerce {
        value: VirRef,
        from: VirTypeId,
        to: VirTypeId,
        vir_from: VirTypeId,
        vir_to: VirTypeId,
        kind: CoerceKind,
    },

    // -- Control flow -------------------------------------------------------
    /// Conditional expression (if/else).
    If {
        cond: VirRef,
        then_body: VirBody,
        else_body: Option<VirBody>,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    /// Pattern match expression.
    ///
    /// `result_is_union` indicates whether the match result type (`vir_ty`)
    /// is a union, pre-computed during VIR lowering so codegen reads a
    /// decision instead of querying `vir_query_is_union_v(result_vir_ty)`.
    /// Used for union reconstruction of arm results and array literal
    /// variant disambiguation.
    Match {
        scrutinee: VirRef,
        arms: Vec<VirMatchArm>,
        ty: VirTypeId,
        vir_ty: VirTypeId,
        result_is_union: bool,
    },

    /// Block expression with an optional trailing value.
    Block {
        stmts: Vec<VirStmt>,
        trailing: Option<VirRef>,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    // -- Type operations ----------------------------------------------------
    /// Type-check (`x is T`). The `result` field encodes the sema decision
    /// so codegen never re-derives it.
    IsCheck {
        value: VirRef,
        result: IsCheckResult,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    /// Type cast (`x as T`).
    ///
    /// `kind` is `Checked` (as?) or `Unchecked` (as!).
    /// `result` carries the sema-computed `IsCheckResult` so codegen
    /// knows whether to emit a tag check, unknown check, or static result.
    AsCast {
        value: VirRef,
        target_ty: VirTypeId,
        vir_target_ty: VirTypeId,
        kind: AsCastKind,
        result: IsCheckResult,
    },

    // -- Reflection ---------------------------------------------------------
    /// Meta-access (`T.@meta` or `val.@meta`).
    MetaAccess {
        kind: VirMetaKind,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    // -- Variables -----------------------------------------------------------
    /// Load a local variable.
    LocalLoad {
        name: Symbol,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    /// Store into a local variable.
    LocalStore { name: Symbol, value: VirRef },

    // -- Lambda -------------------------------------------------------------
    /// Lambda / closure expression.
    ///
    /// `params` are the parameter names in declaration order; individual
    /// parameter types are derived by codegen from the function type `ty`
    /// via `TypeArena::unwrap_function`.
    ///
    /// `body` is the lowered VIR body (statements + optional trailing
    /// expression).
    ///
    /// `captures` list the variables captured from the enclosing scope by
    /// name; codegen resolves their runtime values and types from the
    /// enclosing compilation context.
    ///
    /// `ty` is the sema-computed function type `(P1, P2, ...) -> R`.
    Lambda {
        params: Vec<Symbol>,
        body: VirBody,
        captures: Vec<VirCapture>,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    // -- Null / optional operations -----------------------------------------
    /// Null coalesce expression (`value ?? default`).
    ///
    /// Checks whether `value` is nil; if so, evaluates and returns `default`,
    /// otherwise returns the unwrapped non-nil payload.  `inner_type` is the
    /// non-nil result type (e.g. `T` from `T | nil`); codegen uses it to
    /// determine whether the result path is scalar or union.
    NullCoalesce {
        value: VirRef,
        default: VirRef,
        inner_type: VirTypeId,
        vir_inner_type: VirTypeId,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    /// Optional chain field access (`obj?.field`).
    ///
    /// Checks whether `object` is nil; if so, produces nil wrapped in the
    /// result type.  Otherwise extracts the inner value and loads the field.
    /// `ty` is the overall expression type (e.g. `string | nil`), used for
    /// constructing the merge block and nil branch.
    OptionalChain {
        object: VirRef,
        field: Symbol,
        inner_type: VirTypeId,
        vir_inner_type: VirTypeId,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    /// Optional chain method call (`obj?.method(args)`).
    ///
    /// Like `OptionalChain` but the body is a method call instead of a
    /// field load.  The method receiver, name, and arguments are
    /// pre-lowered to VIR refs.  `dispatch` carries sema-resolved method
    /// routing metadata; `call_node_id` is retained as a legacy field for
    /// non-dispatch compatibility paths.
    /// `ty` is the overall expression type (e.g. `string | nil`).
    OptionalMethodCall {
        object: VirRef,
        method: Symbol,
        method_args: Vec<VirRef>,
        dispatch: VirMethodDispatchMeta,
        call_node_id: NodeId,
        inner_type: VirTypeId,
        vir_inner_type: VirTypeId,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    /// Try / error propagation (`expr?`).
    ///
    /// Evaluates the fallible expression; on success, unwraps and returns
    /// the success payload.  On error, propagates via early return using
    /// the fallible return convention (tag + payload registers).
    Try {
        value: VirRef,
        success_type: VirTypeId,
        vir_success_type: VirTypeId,
    },

    // -- Generator ----------------------------------------------------------
    /// Yield expression inside a generator body.
    ///
    /// Suspends the coroutine and passes `value` to the iterator consumer.
    /// Always produces a void/zero result (yield is used in statement
    /// position).
    Yield { value: VirRef },
}

impl VirExpr {
    /// Returns `true` if this is a void-typed `If` expression.
    ///
    /// Void-typed if expressions originate from lowered `IfStmt`s (statement-
    /// level if/else) and should NOT be treated as trailing value-producing
    /// expressions in function bodies.
    pub fn is_void_if(&self) -> bool {
        matches!(self, VirExpr::If { ty, .. } if *ty == VirTypeId::VOID)
    }
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
///
/// `Direct` and `Heap` are resolved during VIR lowering for concrete
/// (non-generic) types.  Generic templates emit `ByName`; the monomorph
/// rederive pass resolves them to concrete storage after type substitution.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FieldStorage {
    /// Field stored inline on the stack (value-type struct).
    ///
    /// `slot` is the logical field index in the struct's field list.
    /// Codegen converts to byte offset via `struct_field_byte_offset`.
    Direct { slot: u32 },
    /// Field stored on the heap, accessed through a runtime call
    /// (reference-counted class instance).
    ///
    /// `slot` is the physical slot index accounting for wide types
    /// (i128/f128 fields occupy 2 consecutive slots).
    Heap { slot: u32 },
    /// Module field access — resolved to a module constant or export.
    ///
    /// Carries the `ModuleId` so codegen can dispatch module field access
    /// without needing to recover the module identity from the VirTypeId.
    Module { module_id: ModuleId },
    /// Unresolved storage — emitted for generic function templates where
    /// the object type contains type parameters.  Must be resolved before
    /// codegen via the monomorph rederive pass.
    ByName,
}

/// Per-field coercion hint for struct/class construction, pre-computed
/// during VIR lowering so codegen reads a decision instead of querying
/// `vir_query_is_interface_v()` / `vir_query_is_unknown_v()` etc.
///
/// Parallel to `LetStorageHint` for let bindings — tells codegen what
/// coercion (if any) is needed when storing an init value into a field.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FieldCoercionHint {
    /// No coercion needed — value type matches field type.
    None,
    /// Box concrete value to interface fat pointer.
    InterfaceBox,
    /// Copy existing interface fat pointer (value is already an interface).
    InterfaceCopy,
    /// Unresolved — used in generic templates where the field or value
    /// type contains type parameters.  Codegen falls back to type queries.
    Unresolved,
}

/// RC cleanup strategy for a value, pre-computed during VIR lowering.
///
/// Tells codegen how to emit `rc_inc` / `rc_dec` calls for a value
/// without querying the type arena at compile time.
///
/// This covers the per-value RC operations (`VirExpr::RcInc` /
/// `VirExpr::RcDec` / `VirStmt::RcInc` / `VirStmt::RcDec`).  Scope-level
/// cleanup (drop flags, union tag checks) is a separate system.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VirRcCleanup {
    /// No RC action needed (primitive, struct, void, etc.).
    None,

    /// Simple `rc_inc` / `rc_dec` call on the value directly.
    ///
    /// Applies to: String, Array, Class instance, Function/closure,
    /// Handle, RuntimeIterator.
    SimpleDecRef,

    /// The value is an interface fat pointer `[data_ptr, vtable_ptr]`.
    ///
    /// Codegen must load the data word at offset 0 before calling
    /// `rc_inc` / `rc_dec` on it.
    InterfaceDecRef,

    /// The value is `unknown`-typed (heap-allocated `TaggedValue`).
    ///
    /// Codegen calls `unknown_heap_cleanup` (for dec) or `rc_inc` on
    /// the boxed value (for inc) instead of the plain `rc_dec` / `rc_inc`.
    UnknownHeapCleanup,

    /// Unresolved — used in generic templates where the value type
    /// contains type parameters.  Codegen falls back to arena queries.
    Unresolved,
}

impl VirRcCleanup {
    /// Returns `true` if this cleanup strategy requires any RC action.
    pub fn needs_action(&self) -> bool {
        !matches!(self, VirRcCleanup::None)
    }
}

/// The kind of type coercion to perform.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
    /// Box a value as an interface type.
    ///
    /// Carries the pre-decomposed interface target: the `TypeDefId` of the
    /// interface and its generic type arguments.  Codegen uses these to
    /// generate vtables without re-querying the type arena.
    InterfaceBox {
        interface_type_def: TypeDefId,
        interface_type_args: Vec<VirTypeId>,
    },
    /// Unbox an interface pointer back to the concrete value.
    Unbox,
    /// Wrap a concrete iterator into a `RuntimeIterator`.
    ///
    /// Carries the pre-resolved element type and the `Iterator<elem>`
    /// interface type so codegen can box + wrap without arena queries.
    IteratorWrap {
        elem_type: VirTypeId,
        interface_type: VirTypeId,
    },
}

/// Sema-independent dispatch kind annotation for VIR method calls.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VirMethodDispatchKind {
    /// Module-scoped function call dispatch.
    Module { module_id: ModuleId },
    /// Built-in method dispatch.
    Builtin,
    /// Array push special-case dispatch.
    ArrayPush,
    /// Standard method dispatch path.
    Standard,
}

/// Method-receiver coercion hints for VIR method dispatch.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VirMethodReceiverCoercion {
    /// Receiver should be boxed to `Iterator<T>` then wrapped as
    /// `RuntimeIterator<T>` before dispatch.
    IteratorWrap {
        elem_type: VirTypeId,
        vir_elem_type: VirTypeId,
    },
}

/// External/native method information used by VIR method dispatch.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VirExternalMethodInfo {
    pub module_path: NameId,
    pub native_name: NameId,
}

/// Sema-independent resolved method descriptor for VIR method dispatch.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VirResolvedMethod {
    Direct {
        type_def_id: Option<TypeDefId>,
        func_type_id: VirTypeId,
        vir_func_type_id: VirTypeId,
        return_type_id: VirTypeId,
        vir_return_type_id: VirTypeId,
        method_id: Option<MethodId>,
    },
    Implemented {
        type_def_id: Option<TypeDefId>,
        func_type_id: VirTypeId,
        vir_func_type_id: VirTypeId,
        return_type_id: VirTypeId,
        vir_return_type_id: VirTypeId,
        is_builtin: bool,
        external_info: Option<VirExternalMethodInfo>,
        concrete_return_hint: Option<VirTypeId>,
        vir_concrete_return_hint: Option<VirTypeId>,
    },
    FunctionalInterface {
        func_type_id: VirTypeId,
        vir_func_type_id: VirTypeId,
        return_type_id: VirTypeId,
        vir_return_type_id: VirTypeId,
    },
    DefaultMethod {
        type_def_id: Option<TypeDefId>,
        interface_type_def_id: TypeDefId,
        func_type_id: VirTypeId,
        vir_func_type_id: VirTypeId,
        return_type_id: VirTypeId,
        vir_return_type_id: VirTypeId,
        external_info: Option<VirExternalMethodInfo>,
    },
    InterfaceMethod {
        interface_type_def_id: TypeDefId,
        func_type_id: VirTypeId,
        vir_func_type_id: VirTypeId,
        return_type_id: VirTypeId,
        vir_return_type_id: VirTypeId,
        method_index: u32,
    },
    Static {
        type_def_id: TypeDefId,
        method_id: MethodId,
        func_type_id: VirTypeId,
        vir_func_type_id: VirTypeId,
        return_type_id: VirTypeId,
        vir_return_type_id: VirTypeId,
    },
}

impl VirResolvedMethod {
    pub fn func_type_id(&self) -> VirTypeId {
        match self {
            VirResolvedMethod::Direct { func_type_id, .. }
            | VirResolvedMethod::Implemented { func_type_id, .. }
            | VirResolvedMethod::FunctionalInterface { func_type_id, .. }
            | VirResolvedMethod::DefaultMethod { func_type_id, .. }
            | VirResolvedMethod::InterfaceMethod { func_type_id, .. }
            | VirResolvedMethod::Static { func_type_id, .. } => *func_type_id,
        }
    }

    pub fn return_type_id(&self) -> VirTypeId {
        match self {
            VirResolvedMethod::Direct { return_type_id, .. }
            | VirResolvedMethod::Implemented { return_type_id, .. }
            | VirResolvedMethod::FunctionalInterface { return_type_id, .. }
            | VirResolvedMethod::DefaultMethod { return_type_id, .. }
            | VirResolvedMethod::InterfaceMethod { return_type_id, .. }
            | VirResolvedMethod::Static { return_type_id, .. } => *return_type_id,
        }
    }

    pub fn method_id(&self) -> Option<MethodId> {
        match self {
            VirResolvedMethod::Direct { method_id, .. } => *method_id,
            VirResolvedMethod::Static { method_id, .. } => Some(*method_id),
            VirResolvedMethod::Implemented { .. }
            | VirResolvedMethod::FunctionalInterface { .. }
            | VirResolvedMethod::DefaultMethod { .. }
            | VirResolvedMethod::InterfaceMethod { .. } => None,
        }
    }

    pub fn type_def_id(&self) -> Option<TypeDefId> {
        match self {
            VirResolvedMethod::Direct { type_def_id, .. } => *type_def_id,
            VirResolvedMethod::Implemented { type_def_id, .. } => *type_def_id,
            VirResolvedMethod::DefaultMethod { type_def_id, .. } => *type_def_id,
            VirResolvedMethod::Static { type_def_id, .. } => Some(*type_def_id),
            VirResolvedMethod::InterfaceMethod {
                interface_type_def_id,
                ..
            } => Some(*interface_type_def_id),
            VirResolvedMethod::FunctionalInterface { .. } => None,
        }
    }

    pub fn external_info(&self) -> Option<VirExternalMethodInfo> {
        match self {
            VirResolvedMethod::Implemented { external_info, .. }
            | VirResolvedMethod::DefaultMethod { external_info, .. } => *external_info,
            VirResolvedMethod::Direct { .. }
            | VirResolvedMethod::FunctionalInterface { .. }
            | VirResolvedMethod::InterfaceMethod { .. }
            | VirResolvedMethod::Static { .. } => None,
        }
    }

    pub fn concrete_return_hint(&self) -> Option<VirTypeId> {
        match self {
            VirResolvedMethod::Implemented {
                concrete_return_hint,
                ..
            } => *concrete_return_hint,
            VirResolvedMethod::Direct { .. }
            | VirResolvedMethod::FunctionalInterface { .. }
            | VirResolvedMethod::DefaultMethod { .. }
            | VirResolvedMethod::InterfaceMethod { .. }
            | VirResolvedMethod::Static { .. } => None,
        }
    }

    pub fn is_builtin(&self) -> bool {
        matches!(
            self,
            VirResolvedMethod::Implemented {
                is_builtin: true,
                ..
            }
        )
    }

    pub fn method_index(&self) -> Option<u32> {
        match self {
            VirResolvedMethod::InterfaceMethod { method_index, .. } => Some(*method_index),
            VirResolvedMethod::Direct { .. }
            | VirResolvedMethod::Implemented { .. }
            | VirResolvedMethod::FunctionalInterface { .. }
            | VirResolvedMethod::DefaultMethod { .. }
            | VirResolvedMethod::Static { .. } => None,
        }
    }

    pub fn default_interface_type_def_id(&self) -> Option<TypeDefId> {
        match self {
            VirResolvedMethod::DefaultMethod {
                interface_type_def_id,
                ..
            } => Some(*interface_type_def_id),
            VirResolvedMethod::Direct { .. }
            | VirResolvedMethod::Implemented { .. }
            | VirResolvedMethod::FunctionalInterface { .. }
            | VirResolvedMethod::InterfaceMethod { .. }
            | VirResolvedMethod::Static { .. } => None,
        }
    }

    pub fn is_interface_method(&self) -> bool {
        matches!(self, VirResolvedMethod::InterfaceMethod { .. })
    }
}

/// Generic function monomorph key carried by VIR method metadata.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VirFunctionMonomorphKey {
    pub func_name: NameId,
    pub type_keys: Vec<VirTypeId>,
    pub vir_type_keys: Vec<VirTypeId>,
}

/// Generic class-method monomorph key carried by VIR method metadata.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VirClassMethodMonomorphKey {
    pub class_name: NameId,
    pub method_name: NameId,
    pub type_keys: Vec<VirTypeId>,
    pub vir_type_keys: Vec<VirTypeId>,
}

/// Generic static-method monomorph key carried by VIR method metadata.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VirStaticMethodMonomorphKey {
    pub class_name: NameId,
    pub method_name: NameId,
    pub class_type_keys: Vec<VirTypeId>,
    pub vir_class_type_keys: Vec<VirTypeId>,
    pub method_type_keys: Vec<VirTypeId>,
    pub vir_method_type_keys: Vec<VirTypeId>,
}

/// Dispatch metadata carried on VIR method-call expressions.
///
/// This is the NodeId-free contract for method-dispatch inputs that were
/// previously fetched ad-hoc from sema maps during codegen.
#[derive(Debug, Clone, Default)]
pub struct VirMethodDispatchMeta {
    pub dispatch_kind: Option<VirMethodDispatchKind>,
    pub receiver_coercion: Option<VirMethodReceiverCoercion>,
    pub resolved_method: Option<VirResolvedMethod>,
    pub generic_monomorph: Option<VirFunctionMonomorphKey>,
    pub substituted_return_type: Option<VirTypeId>,
    pub vir_substituted_return_type: Option<VirTypeId>,
    pub resolved_call_args: Option<Vec<Option<usize>>>,
    pub class_method_generic: Option<VirClassMethodMonomorphKey>,
    pub static_method_generic: Option<VirStaticMethodMonomorphKey>,
    /// Pre-computed: the receiver's type is an interface.
    ///
    /// Used by codegen to decide whether `InterfaceMethod` dispatch from sema
    /// should be trusted (receiver truly is an interface) or overridden
    /// (receiver is a concrete type implementing the interface, so vtable
    /// dispatch is wrong).  Set during VIR lowering; re-derived after
    /// monomorphization when type parameters become concrete.
    pub receiver_is_interface: bool,
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
    pub ty: VirTypeId,
    /// VIR type of the arm's result expression.
    pub vir_ty: VirTypeId,
}

/// A pattern in a `Match` arm.
///
/// Simple patterns (Wildcard, Binding, TypeCheck, Literal, Val) are fully
/// lowered to VIR.  Fallible patterns (Success, Error) are lowered to VIR
/// with pre-resolved type information.  Tuple patterns are fully lowered
/// with pre-resolved element types.  Record patterns are fully lowered
/// with pre-resolved type check results, field slots, and struct/class
/// discrimination.
#[derive(Debug, Clone)]
pub enum VirPattern {
    /// Wildcard pattern (`_`): always matches, binds nothing.
    Wildcard,

    /// Binding pattern: binds the scrutinee to a local variable.
    ///
    /// `ty` is the scrutinee's type at the point of binding (used by codegen
    /// to declare the variable with the right Cranelift type).
    Binding {
        name: Symbol,
        ty: VirTypeId,
        vir_ty: VirTypeId,
    },

    /// Type-check pattern: tests the scrutinee against a type.
    ///
    /// `result` is the sema-computed `IsCheckResult` (may be stale after
    /// monomorphization).  `tested_type` is the target type so codegen can
    /// recompute the result via `compute_is_check_result` when substitutions
    /// are active.
    ///
    /// `binding` is present for identifier-as-type patterns (e.g. `n` in a
    /// union match where sema recognizes `n` as a type name) that should
    /// also bind the narrowed value after the check succeeds.
    TypeCheck {
        result: IsCheckResult,
        tested_type: VirTypeId,
        vir_tested_type: VirTypeId,
        binding: Option<(Symbol, VirTypeId, VirTypeId)>,
    },

    /// Literal pattern: compares the scrutinee against a pre-lowered literal.
    ///
    /// `value` is the lowered VIR expression for the literal (e.g.
    /// `VirExpr::IntLiteral`, `VirExpr::StringLiteral`).
    /// `scrutinee_ty` is the scrutinee's type, needed for selecting the
    /// correct equality comparison (integer, float, string).
    Literal {
        value: VirRef,
        scrutinee_ty: VirTypeId,
        vir_scrutinee_ty: VirTypeId,
    },

    /// Val pattern (`val x`): compares the scrutinee against an existing
    /// variable's value.
    Val { name: Symbol },

    /// Success pattern for fallible match: `success x`, `success`, etc.
    ///
    /// Checks the fallible tag against `FALLIBLE_SUCCESS_TAG`.  If an inner
    /// pattern is present, extracts the success payload and binds it.
    /// `success_type` is pre-resolved from `TypeArena::unwrap_fallible`.
    Success {
        inner: Option<Box<VirPattern>>,
        success_type: VirTypeId,
        vir_success_type: VirTypeId,
    },

    /// Error pattern for fallible match: `error`, `error e`, `error DivByZero`,
    /// `error DivByZero { msg }`.
    ///
    /// The `kind` sub-enum encodes which of the four error sub-paths applies,
    /// with all type/tag information pre-resolved during lowering.
    Error { kind: VirErrorPatternKind },

    /// Tuple destructuring pattern: `[a, b, c]`.
    ///
    /// Each element binding carries the nested pattern, its position in the
    /// tuple, and its pre-resolved element type from `TypeArena::unwrap_tuple`.
    /// Layout offsets (byte offsets, Cranelift types) are NOT pre-computed
    /// because they depend on Cranelift type sizes — codegen calls
    /// `tuple_layout()` and `cranelift_types()` at instruction selection time.
    Tuple { bindings: Vec<VirTupleBinding> },

    /// Record (struct/class) destructuring pattern: `Point { x, y }` or `{ name, age }`.
    ///
    /// `type_check` is present for typed patterns (e.g. `Point { x, y }` in a union
    /// match), where a type check must pass before fields can be extracted.
    /// `None` for anonymous record patterns (`{ x, y }`).
    ///
    /// `tested_type` is the target type for monomorphized recomputation of the
    /// type check result (parallel to `VirPattern::TypeCheck::tested_type`).
    ///
    /// `source_ty` is the narrowed type of the record after union payload extraction
    /// (e.g. `Point` rather than `Point | Circle`).  Codegen uses this for field lookups.
    ///
    /// `is_union_payload` indicates whether the scrutinee is a union and the pattern
    /// variant type must be extracted from offset 8 before field access.
    ///
    /// `is_struct` distinguishes struct (flat field load via `struct_field_load`)
    /// from class (instance field load via `get_instance_field`).
    ///
    /// `fields` lists the field bindings to extract, each with a pre-resolved
    /// field slot and type from `EntityRegistry`.
    Record {
        type_check: Option<IsCheckResult>,
        tested_type: Option<VirTypeId>,
        vir_tested_type: Option<VirTypeId>,
        fields: Vec<VirRecordFieldBinding>,
        source_ty: VirTypeId,
        vir_source_ty: VirTypeId,
        is_union_payload: bool,
        is_struct: bool,
    },
}

/// The sub-kind of an error pattern, pre-resolved during lowering.
///
/// Error patterns have four forms with increasing complexity:
/// 1. Bare `error` — matches any error (tag != SUCCESS)
/// 2. `error e` (catch-all) — matches any error and binds the payload
/// 3. `error SpecificType` — matches a specific error type by pre-computed tag
/// 4. `error SpecificType { field, ... }` — specific type with field destructuring
#[derive(Debug, Clone)]
pub enum VirErrorPatternKind {
    /// Bare `error` pattern: matches any error (tag != SUCCESS).
    Bare,

    /// Catch-all error with binding: `error e`.
    ///
    /// Matches any error and binds the error payload to `name`.
    /// `error_ty` is the fallible's error type for payload extraction.
    CatchAll {
        name: Symbol,
        error_ty: VirTypeId,
        vir_error_ty: VirTypeId,
    },

    /// Specific error type match: `error DivByZero`.
    ///
    /// `error_tag` is the pre-computed tag value for the error type within
    /// the fallible's error union.
    Specific { error_tag: i64 },

    /// Specific error type with record destructuring: `error Overflow { value, max }`.
    ///
    /// `error_tag` is the pre-computed tag value.  `type_def` is the error
    /// type's `TypeDefId` for field layout resolution.  `fields` lists the
    /// field bindings to extract from the error payload.
    SpecificRecord {
        error_tag: i64,
        type_def: TypeDefId,
        fields: Vec<VirErrorFieldBinding>,
    },
}

/// A single field binding in an error record destructure pattern.
///
/// Maps a field name (from the source pattern) to a binding name
/// (the variable name in the match arm body).
#[derive(Debug, Clone)]
pub struct VirErrorFieldBinding {
    /// The field name in the error type definition.
    pub field_name: Symbol,
    /// The variable name to bind the field value to.
    pub binding: Symbol,
}

/// A single element binding in a tuple destructure pattern.
///
/// Maps a nested pattern (typically `Binding` or `Wildcard`) to its
/// position in the tuple and its pre-resolved element type.
#[derive(Debug, Clone)]
pub struct VirTupleBinding {
    /// The nested pattern for this element (e.g. `Binding` for `x`,
    /// `Wildcard` for `_`).
    pub pattern: VirPattern,
    /// Zero-based position of this element in the tuple.
    pub element_index: usize,
    /// The element type, pre-resolved from `TypeArena::unwrap_tuple`.
    pub ty: VirTypeId,
    /// VIR type of the element.
    pub vir_ty: VirTypeId,
}

/// A single field binding in a record destructure pattern.
///
/// Maps a field name (from the type definition) to a binding name (the variable
/// name in the match arm body), with pre-resolved field slot index and type.
#[derive(Debug, Clone)]
pub struct VirRecordFieldBinding {
    /// The field name in the type definition.
    pub field_name: Symbol,
    /// The variable name to bind the field value to (may differ via rename syntax).
    pub binding_name: Symbol,
    /// Pre-resolved field slot index from `EntityRegistry`.
    pub field_slot: u32,
    /// Pre-resolved field type from `EntityRegistry`.
    pub ty: VirTypeId,
    /// VIR type of the field.
    pub vir_ty: VirTypeId,
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
    ///
    /// `object` is present when the access was on a value expression
    /// (e.g. `val.@meta` where `val: Point`) so codegen can re-derive the
    /// TypeDefId in monomorphized contexts.  `None` when the access was on
    /// a type name (e.g. `Point.@meta`).
    Static {
        type_def: TypeDefId,
        object: Option<VirRef>,
    },
    /// Dynamic meta: the value's type is only known at runtime (interface
    /// dispatch through vtable slot 0).
    Dynamic { value: VirRef },
    /// Type parameter meta: the reflected type is a generic type parameter.
    ///
    /// Codegen resolves this at monomorphization time by looking up the
    /// concrete type from substitutions and dispatching to the static or
    /// dynamic path.
    TypeParam { name_id: NameId, value: VirRef },
}

/// RC classification for a captured variable in a closure.
///
/// Models the three capture-kind flags used by the closure runtime:
///   - `None` (0): value type, no RC management
///   - `Rc` (1): simple RC type (string, array, function, class) —
///     `rc_inc` / `rc_dec` on the value directly
///   - `Unresolved`: type is unknown or generic — codegen falls back to
///     computing from the resolved type at compile time
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VirCaptureRcKind {
    /// No RC management needed (primitive, struct, void, interface, handle,
    /// iterator, etc.).
    None,
    /// Simple RC type eligible for capture management (string, array,
    /// function, class).  The closure runtime calls `rc_inc` on capture
    /// and `rc_dec` on drop for this value.
    Rc,
    /// Type is unknown or contains generic parameters — codegen falls
    /// back to computing RC state from the resolved type.
    Unresolved,
}

/// A captured variable in a lambda / closure.
#[derive(Debug, Clone)]
pub struct VirCapture {
    /// The name of the captured variable.
    pub name: Symbol,
    /// The type of the captured variable.
    pub ty: VirTypeId,
    /// VIR type of the captured variable.
    pub vir_ty: VirTypeId,
    /// Whether the variable is captured by reference (true) or by value
    /// (false).
    pub by_ref: bool,
    /// Pre-classified RC kind for this capture.
    ///
    /// Set to `Unresolved` during initial lowering (capture types are
    /// unknown) and reclassified by the rederive pass after
    /// monomorphization resolves concrete types.  Codegen reads this
    /// directly instead of re-computing from the capture type.
    pub rc_kind: VirCaptureRcKind,
}

/// A single part of an interpolated string.
///
/// Literal parts become static strings at compile time.  Expression parts
/// carry the sema-annotated `StringConversion` so codegen knows how to
/// convert the value to a string without re-detecting types.
#[derive(Debug, Clone)]
pub enum VirStringPart {
    /// A literal string fragment (e.g. the `"hello "` in `"hello {x}"`).
    Literal(Symbol),
    /// An expression with its string-conversion strategy.
    Expr {
        value: VirRef,
        conversion: StringConversion,
    },
}

// Re-export from vole-identity — canonical definition lives there.
// Locally aliased as `IsCheckResult` to minimise churn within the VIR crate.
pub use vole_identity::VirIsCheckResult as IsCheckResult;
