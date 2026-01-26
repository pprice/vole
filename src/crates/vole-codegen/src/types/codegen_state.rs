// types/codegen_state.rs
//
// Grouped codegen lookup tables - created once per Compiler, read-only after pass 1.

use rustc_hash::FxHashMap;
use std::cell::{Cell, RefCell};

use vole_identity::{NameId, TypeDefId};
use vole_runtime::NativeRegistry;

use crate::FunctionKey;
use crate::interface_vtable::InterfaceVtableRegistry;
use crate::intrinsics::IntrinsicsRegistry;

use super::TypeMetadata;

/// Type metadata lookup map.
/// Keyed by TypeDefId for stable cross-interner identity.
pub type TypeMetadataMap = FxHashMap<TypeDefId, TypeMetadata>;

/// Grouped codegen lookup tables.
///
/// Created once in `Compiler::new`, populated during pass 1 (declarations),
/// then effectively read-only during pass 2 (compilation).
///
/// Fields using interior mutability (RefCell, Cell) can be mutated through
/// shared references during compilation.
pub struct CodegenState {
    /// Class and record metadata for struct literals, field access, and method calls.
    pub type_metadata: TypeMetadataMap,
    /// Unified method function key lookup: (TypeDefId, method_name) -> FunctionKey
    pub method_func_keys: FxHashMap<(TypeDefId, NameId), FunctionKey>,
    /// Interface vtable registry (uses interior mutability)
    pub interface_vtables: RefCell<InterfaceVtableRegistry>,
    /// Registry of native functions for external method calls
    pub native_registry: NativeRegistry,
    /// Registry of compiler intrinsics (e.g., f64.nan(), f32.infinity())
    pub intrinsics_registry: IntrinsicsRegistry,
    /// Counter for generating unique lambda names (interior mutability)
    pub lambda_counter: Cell<usize>,
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
        }
    }
}
