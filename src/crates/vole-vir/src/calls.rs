// calls.rs
//
// Call target descriptors for VIR function calls.

use vole_identity::{FunctionId, MethodId, MonomorphKey, NodeId, Symbol, TypeDefId, VirTypeId};

use crate::intrinsics::IntrinsicKey;

/// The target of a function or method call in VIR.
///
/// Codegen uses this to select the correct calling convention and linkage.
#[derive(Debug, Clone)]
pub enum CallTarget {
    /// A direct call to a known function.
    Direct { function_id: FunctionId },

    /// Virtual dispatch through a vtable slot (receiver is in the call's args).
    VtableMethod { slot: usize },

    /// A built-in method on a primitive type (array, string, range).
    BuiltinMethod { method: BuiltinMethod },

    /// A compiler intrinsic, identified by a typed `IntrinsicKey`.
    Intrinsic { key: IntrinsicKey, line: u32 },

    /// A runtime intrinsic (calls into `vole-runtime`), identified by a typed
    /// `IntrinsicKey`.  Codegen resolves to the appropriate `RuntimeKey`.
    IntrinsicRuntime { key: IntrinsicKey },

    /// Lambda / closure invocation.  The closure value is the first element
    /// of the call's `args`.
    Lambda,

    /// A call to a local variable that holds a closure/function value.
    ///
    /// Emitted when VIR lowering detects that the callee identifier is a
    /// local variable with a function type (not a declared function).
    /// Codegen loads the variable from `vars`, extracts the function pointer
    /// from the closure struct, and emits an indirect call.
    ClosureVariable {
        /// The variable name symbol (used to look up the Cranelift `Variable`).
        var_name: Symbol,
        /// The VIR function type of the closure (e.g. `(i64) -> string`).
        vir_type: VirTypeId,
        /// Pre-resolved named-argument reordering mapping from sema.
        resolved_call_args: Option<Vec<Option<usize>>>,
        /// Lambda parameter defaults from sema.
        lambda_defaults: Option<LambdaDefaultsInfo>,
    },

    /// A call to a captured closure variable from an enclosing scope.
    ///
    /// Emitted when VIR lowering detects that the callee identifier is a
    /// captured variable with a function type.  Codegen loads the capture
    /// from the closure environment, extracts the function pointer, and
    /// emits an indirect call.
    CapturedClosure {
        /// The capture name symbol (used to look up the capture binding).
        var_name: Symbol,
        /// The VIR function type of the closure (e.g. `(i64) -> string`).
        vir_type: VirTypeId,
        /// Pre-resolved named-argument reordering mapping from sema.
        resolved_call_args: Option<Vec<Option<usize>>>,
        /// Lambda parameter defaults from sema.
        lambda_defaults: Option<LambdaDefaultsInfo>,
    },

    /// A call to a local variable that holds a functional interface value.
    ///
    /// Emitted when VIR lowering detects that the callee identifier is a
    /// local variable whose type is a single-method interface (a "functional
    /// interface").  Codegen loads the variable, performs vtable dispatch on
    /// the interface's single method.
    FunctionalInterface {
        /// The variable name symbol (used to look up the Cranelift `Variable`).
        var_name: Symbol,
        /// The VIR type of the variable (the interface type, not the method's
        /// function type).
        vir_type: VirTypeId,
        /// The `TypeDefId` of the interface (for vtable/method lookup).
        interface_type_def_id: TypeDefId,
        /// The `MethodId` of the single callable method on the interface.
        method_id: MethodId,
    },

    /// A call to a global variable that holds a closure/function or functional
    /// interface value.
    ///
    /// Emitted when VIR lowering detects that the callee identifier is a
    /// global variable (not a locally-scoped variable or declared function).
    /// Codegen compiles the global's VIR initializer, then dispatches as
    /// either a closure call or a functional interface call depending on the
    /// global's declared type.
    GlobalClosure {
        /// The global variable name symbol.
        var_name: Symbol,
        /// Pre-resolved named-argument reordering mapping from sema.
        resolved_call_args: Option<Vec<Option<usize>>>,
        /// Lambda parameter defaults from sema.
        lambda_defaults: Option<LambdaDefaultsInfo>,
        /// MonomorphKey for generic function calls through the global.
        monomorph_key: Option<MonomorphKey>,
    },

    /// A call to a native (FFI) function.
    Native {
        module_path: Symbol,
        native_name: Symbol,
        abi: NativeAbi,
    },

    /// A call to a generic function with (possibly abstract) type arguments.
    ///
    /// Emitted during generic VIR lowering when a generic function body calls
    /// another generic function with type args that may include type parameters.
    /// Must be resolved to a concrete `CallTarget` during VIR monomorphization
    /// before codegen.
    GenericCall {
        function_id: FunctionId,
        type_args: Vec<VirTypeId>,
    },

    /// A direct call to a VIR-monomorphized function by its index in
    /// `VirProgram.functions`.
    ///
    /// Produced by the VIR monomorphization post-pass when resolving
    /// `GenericCall` targets.  Unlike `Direct`, this does not require an
    /// entity registry lookup — the function index points directly into the
    /// VIR function array.
    VirDirect { function_index: usize },

    /// A call that could not be fully classified during VIR lowering.
    ///
    /// Lowering classifies many call patterns into concrete `CallTarget`
    /// variants (Direct, Native, Intrinsic, ClosureVariable, CapturedClosure,
    /// FunctionalInterface, GlobalClosure, GenericCall).  The following
    /// cases still produce Unresolved:
    ///
    /// - Functions with default parameters, struct returns, interface/union
    ///   params, or generator return types (rejected by `try_resolve_function_id`)
    /// - Test-scoped local functions (not in the main name table)
    /// - Sema-fallback monomorphized calls (not in VIR instance index)
    /// - All calls in generic templates (resolved during VIR monomorphization
    ///   or kept as Unresolved for codegen's sema-fallback path)
    ///
    /// Codegen resolves these into concrete call paths using the same
    /// dispatch logic as the `call_dispatch()` method.
    ///
    /// The VIR `args` on the parent `VirExpr::Call` carry the lowered
    /// arguments; codegen compiles them via `ArgSource::Vir` and threads
    /// them through each dispatch path.
    Unresolved {
        /// The callee identifier symbol.
        callee_sym: Symbol,
        /// NodeId of the call expression (for NodeMap lookups: monomorph key,
        /// lambda defaults, intrinsic key, etc.).
        call_node_id: NodeId,
        /// Source line for error messages (assert, panic).
        line: u32,
        /// Pre-resolved named-argument reordering mapping from sema.
        ///
        /// `mapping[i] = Some(j)` means arg_source[j] fills parameter slot i.
        /// `mapping[i] = None` means slot i uses its default value.
        /// `None` when all arguments are positional.
        resolved_call_args: Option<Vec<Option<usize>>>,
        /// Lambda parameter defaults from sema.
        ///
        /// Present when the callee is a closure whose lambda definition has
        /// default parameter values.  Codegen uses this to compile fallback
        /// values for omitted arguments.
        lambda_defaults: Option<LambdaDefaultsInfo>,
        /// MonomorphKey for generic function calls.
        ///
        /// Copied from `NodeMap::get_generic` during VIR lowering so codegen
        /// can resolve monomorphized callees without touching the NodeMap.
        /// `None` for non-generic calls.
        monomorph_key: Option<MonomorphKey>,
    },
}

/// Lambda parameter default info carried on VIR call nodes.
///
/// When a closure is called with fewer arguments than parameters, defaults
/// are compiled from the lambda body.  VIR lowering copies this from
/// `NodeMap::get_lambda_defaults` so codegen can read it without touching
/// the NodeMap.
#[derive(Debug, Clone, Copy)]
pub struct LambdaDefaultsInfo {
    /// Number of required parameters (those without defaults).
    pub required_params: usize,
    /// NodeId of the lambda expression (for locating default expressions).
    pub lambda_node_id: NodeId,
}

/// ABI convention for native (FFI) calls.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NativeAbi {
    /// Standard C-ABI call returning a single scalar.
    Simple,
    /// The native function returns a struct via an out-pointer (sret).
    StructReturn { field_count: usize },
}

/// Built-in methods on arrays, strings, and ranges.
///
/// These are methods that codegen handles directly (via runtime calls or
/// compiler intrinsics) rather than dispatching through user-defined
/// function bodies.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BuiltinMethod {
    // -- Array methods ------------------------------------------------------
    /// `[T].length` — returns the number of elements.
    ArrayLength,
    /// `[T].iter()` — creates a `RuntimeIterator` over the array.
    ArrayIter,
    /// `[T].push(value)` — appends an element (separate dispatch kind in
    /// sema, but included here for completeness).
    ArrayPush,

    // -- String methods -----------------------------------------------------
    /// `string.length` — returns the byte length.
    StringLength,
    /// `string.iter()` — creates a character iterator.
    StringIter,

    // -- Range methods ------------------------------------------------------
    /// `range.iter()` — creates a `RuntimeIterator` over the range.
    RangeIter,

    // -- Iterator pipeline methods ------------------------------------------
    // These are dispatched through RuntimeIterator's external bindings in
    // codegen, but are enumerated here so VIR can name them without strings.
    /// `iter.map(f)` — lazy transform.
    IterMap,
    /// `iter.filter(f)` — lazy predicate filter.
    IterFilter,
    /// `iter.flat_map(f)` — lazy flatMap.
    IterFlatMap,
    /// `iter.filter_map(f)` — lazy filter + map.
    IterFilterMap,
    /// `iter.take(n)` — take first N elements.
    IterTake,
    /// `iter.skip(n)` — skip first N elements.
    IterSkip,
    /// `iter.reverse()` — reverse the iterator.
    IterReverse,
    /// `iter.sorted()` — sort the iterator.
    IterSorted,
    /// `iter.unique()` — deduplicate.
    IterUnique,
    /// `iter.chain(other)` — concatenate two iterators.
    IterChain,
    /// `iter.flatten()` — flatten nested iterators.
    IterFlatten,
    /// `iter.enumerate()` — yield `(index, element)` pairs.
    IterEnumerate,
    /// `iter.zip(other)` — zip two iterators.
    IterZip,
    /// `iter.chunks(n)` — yield fixed-size chunks.
    IterChunks,
    /// `iter.windows(n)` — yield sliding windows.
    IterWindows,

    // -- Iterator terminal methods ------------------------------------------
    /// `iter.collect()` — materialize into an array.
    IterCollect,
    /// `iter.count()` — count elements.
    IterCount,
    /// `iter.any(f)` — short-circuit boolean test.
    IterAny,
    /// `iter.all(f)` — short-circuit boolean test.
    IterAll,
    /// `iter.for_each(f)` — consume all elements.
    IterForEach,
    /// `iter.sum()` — sum elements.
    IterSum,
    /// `iter.reduce(f)` — fold without initial value.
    IterReduce,
    /// `iter.first()` — first element (optional).
    IterFirst,
    /// `iter.last()` — last element (optional).
    IterLast,
    /// `iter.nth(n)` — nth element (optional).
    IterNth,
    /// `iter.find(f)` — first matching element (optional).
    IterFind,
    /// `iter.next()` — advance and return next element.
    IterNext,
}
