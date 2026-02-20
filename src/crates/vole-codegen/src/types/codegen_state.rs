// types/codegen_state.rs
//
// Grouped codegen lookup tables - created once per Compiler, read-only after pass 1.

use rustc_hash::FxHashMap;
use std::cell::{Cell, RefCell};

use vole_identity::{NameId, TypeDefId};
use vole_runtime::NativeRegistry;
use vole_sema::type_arena::TypeId;

use crate::FunctionKey;
use crate::interfaces::InterfaceVtableRegistry;
use crate::intrinsics::IntrinsicsRegistry;

use super::TypeMetadata;

/// Type metadata lookup map.
///
/// Keyed by TypeDefId for stable cross-interner identity.
/// Also maintains a secondary NameId -> TypeDefId index for O(1) lookup
/// by NameId (used by vtable dispatch to resolve types across interners).
pub(crate) struct TypeMetadataMap {
    /// Primary map: TypeDefId -> TypeMetadata
    entries: FxHashMap<TypeDefId, TypeMetadata>,
    /// Secondary index: NameId -> TypeDefId for cross-interner lookups
    name_id_index: FxHashMap<NameId, TypeDefId>,
}

impl TypeMetadataMap {
    /// Create a new empty TypeMetadataMap.
    pub fn new() -> Self {
        Self {
            entries: FxHashMap::default(),
            name_id_index: FxHashMap::default(),
        }
    }

    /// Insert type metadata, also updating the NameId secondary index.
    pub fn insert_with_name_id(
        &mut self,
        type_def_id: TypeDefId,
        name_id: NameId,
        metadata: TypeMetadata,
    ) {
        self.name_id_index.insert(name_id, type_def_id);
        self.entries.insert(type_def_id, metadata);
    }

    /// Look up TypeMetadata by NameId using the secondary index (O(1)).
    pub fn get_by_name_id(&self, name_id: NameId) -> Option<&TypeMetadata> {
        let type_def_id = self.name_id_index.get(&name_id)?;
        self.entries.get(type_def_id)
    }
}

impl std::ops::Deref for TypeMetadataMap {
    type Target = FxHashMap<TypeDefId, TypeMetadata>;

    fn deref(&self) -> &Self::Target {
        &self.entries
    }
}

impl Default for TypeMetadataMap {
    fn default() -> Self {
        Self::new()
    }
}

/// Key for monomorphized generic class type_id cache.
/// Combines the base class TypeDefId with concrete type arguments.
type MonoTypeKey = (TypeDefId, Vec<TypeId>);

/// Grouped codegen lookup tables.
///
/// Created once in `Compiler::new`, populated during pass 1 (declarations),
/// then effectively read-only during pass 2 (compilation).
///
/// Fields using interior mutability (RefCell, Cell) can be mutated through
/// shared references during compilation.
pub(crate) struct CodegenState {
    /// Class metadata for struct literals, field access, and method calls.
    pub type_metadata: TypeMetadataMap,
    /// Unified method function key lookup: (type_name_id, method_name_id) -> FunctionKey
    /// Uses NameId for both to ensure stable lookup across different analyzer instances.
    pub method_func_keys: FxHashMap<(NameId, NameId), FunctionKey>,
    /// Array Iterable default method keys: (method_name_id, elem_type_id) -> FunctionKey
    /// Used for `[T].count()`, `[T].map()`, etc. which are compiled per element type.
    /// Since `method_func_keys` maps a single key to one FunctionKey, array Iterable methods
    /// use a separate map keyed on (method_name_id, concrete_elem_type_id).
    pub array_iterable_func_keys: FxHashMap<(NameId, TypeId), FunctionKey>,
    /// Interface vtable registry (uses interior mutability)
    pub interface_vtables: RefCell<InterfaceVtableRegistry>,
    /// Registry of native functions for external method calls
    pub native_registry: NativeRegistry,
    /// Registry of compiler intrinsics (e.g., f64.nan(), f32.infinity())
    pub intrinsics_registry: IntrinsicsRegistry,
    /// Counter for generating unique lambda names (interior mutability)
    pub lambda_counter: Cell<usize>,
    /// Cache of runtime type_ids for monomorphized generic class instances.
    /// Maps (base TypeDefId, concrete type args) -> runtime type_id.
    /// When a generic class like `Wrapper<Tag>` is instantiated, we register
    /// a new runtime type_id with field type tags based on the concrete types,
    /// so that instance_drop can properly rc_dec RC-typed fields.
    pub mono_type_ids: RefCell<FxHashMap<MonoTypeKey, u32>>,
    /// Reverse mapping from native function pointer address to JIT symbol name.
    /// Used to devirtualize `call_indirect` with constant function pointers into
    /// direct `call` instructions. Built from both `LINKABLE_RUNTIME_SYMBOLS` and
    /// native stdlib functions registered in the `NativeRegistry`.
    pub ptr_to_symbol: FxHashMap<usize, String>,
}

impl CodegenState {
    /// Create a new CodegenState with empty lookup tables.
    pub fn new(native_registry: NativeRegistry) -> Self {
        // Build the reverse map from function pointer to symbol name.
        // Start with LINKABLE_RUNTIME_SYMBOLS (static names), then add
        // native stdlib functions (generated names like "native_std_math__sin").
        let mut ptr_to_symbol = crate::runtime_registry::build_ptr_to_symbol_map();
        for (symbol_name, ptr) in native_registry.all_function_ptrs() {
            ptr_to_symbol.entry(ptr as usize).or_insert(symbol_name);
        }

        Self {
            type_metadata: TypeMetadataMap::new(),
            method_func_keys: FxHashMap::default(),
            array_iterable_func_keys: FxHashMap::default(),
            interface_vtables: RefCell::new(InterfaceVtableRegistry::new()),
            native_registry,
            intrinsics_registry: IntrinsicsRegistry::new(),
            lambda_counter: Cell::new(0),
            mono_type_ids: RefCell::new(FxHashMap::default()),
            ptr_to_symbol,
        }
    }
}
