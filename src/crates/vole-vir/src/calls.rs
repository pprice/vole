// calls.rs
//
// Call target descriptors for VIR function calls.

use vole_identity::{FunctionId, NodeId, Symbol, VirTypeId};

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
    Intrinsic { key: IntrinsicKey },

    /// A runtime intrinsic (calls into `vole-runtime`), identified by a typed
    /// `IntrinsicKey`.  Codegen resolves to the appropriate `RuntimeKey`.
    IntrinsicRuntime { key: IntrinsicKey },

    /// Lambda / closure invocation.  The closure value is the first element
    /// of the call's `args`.
    Lambda,

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
    /// Lowering can see the callee symbol and NodeMap annotations but lacks
    /// access to the function registry, variable table, and module context
    /// needed for full dispatch.  Codegen resolves these into concrete call
    /// paths using the same dispatch logic as the `call_dispatch()` method.
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
    },
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
