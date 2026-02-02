// types/codegen_state.rs
//
// Grouped codegen lookup tables - created once per Compiler, read-only after pass 1.

use rustc_hash::FxHashMap;
use std::cell::{Cell, RefCell};

use vole_identity::{NameId, TypeDefId};
use vole_runtime::NativeRegistry;
use vole_sema::type_arena::TypeId;

use crate::FunctionKey;
use crate::interface_vtable::InterfaceVtableRegistry;
use crate::intrinsics::IntrinsicsRegistry;

use super::TypeMetadata;

/// Type metadata lookup map.
/// Keyed by TypeDefId for stable cross-interner identity.
pub type TypeMetadataMap = FxHashMap<TypeDefId, TypeMetadata>;

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
pub struct CodegenState {
    /// Class metadata for struct literals, field access, and method calls.
    pub type_metadata: TypeMetadataMap,
    /// Unified method function key lookup: (type_name_id, method_name_id) -> FunctionKey
    /// Uses NameId for both to ensure stable lookup across different analyzer instances.
    pub method_func_keys: FxHashMap<(NameId, NameId), FunctionKey>,
    /// Interface vtable registry (uses interior mutability)
    pub interface_vtables: RefCell<InterfaceVtableRegistry>,
    /// Registry of native functions for external method calls
    pub native_registry: NativeRegistry,
    /// Registry of compiler intrinsics (e.g., f64.nan(), f32.infinity())
    pub intrinsics_registry: IntrinsicsRegistry,
    /// Counter for generating unique lambda names (interior mutability)
    pub lambda_counter: Cell<usize>,
    /// Counter for dynamically allocated monomorphized type_ids (interior mutability).
    /// Initialized from `Compiler::next_type_id` after pass 1 completes.
    pub mono_type_id_counter: Cell<u32>,
    /// Cache of runtime type_ids for monomorphized generic class instances.
    /// Maps (base TypeDefId, concrete type args) -> runtime type_id.
    /// When a generic class like `Wrapper<Tag>` is instantiated, we register
    /// a new runtime type_id with field type tags based on the concrete types,
    /// so that instance_drop can properly rc_dec RC-typed fields.
    pub mono_type_ids: RefCell<FxHashMap<MonoTypeKey, u32>>,
}

impl CodegenState {
    /// Create a new CodegenState with empty lookup tables.
    pub fn new(native_registry: NativeRegistry) -> Self {
        Self {
            type_metadata: FxHashMap::default(),
            method_func_keys: FxHashMap::default(),
            interface_vtables: RefCell::new(InterfaceVtableRegistry::new()),
            native_registry,
            intrinsics_registry: IntrinsicsRegistry::new(),
            lambda_counter: Cell::new(0),
            mono_type_id_counter: Cell::new(0),
            mono_type_ids: RefCell::new(FxHashMap::default()),
        }
    }
}
