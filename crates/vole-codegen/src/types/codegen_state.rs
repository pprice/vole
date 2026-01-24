// types/codegen_state.rs
//
// Grouped codegen lookup tables - created once per Compiler, read-only after pass 1.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use vole_identity::{NameId, TypeDefId};
use vole_runtime::NativeRegistry;
use vole_sema::implement_registry::ImplTypeId;

use crate::FunctionKey;
use crate::interface_vtable::InterfaceVtableRegistry;

use super::{MethodInfo, TypeMetadata};

/// Type metadata lookup map.
/// Keyed by TypeDefId for stable cross-interner identity.
pub type TypeMetadataMap = HashMap<TypeDefId, TypeMetadata>;

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
    /// This replaces impl_method_infos, static_method_infos, and TypeMetadata.method_infos.
    pub method_func_keys: HashMap<(TypeDefId, NameId), FunctionKey>,
    /// Implement block method info for primitive and named types
    /// DEPRECATED: Use method_func_keys instead. Will be removed.
    pub impl_method_infos: HashMap<(ImplTypeId, NameId), MethodInfo>,
    /// Static method info keyed by (TypeDefId, method_name)
    /// DEPRECATED: Use method_func_keys instead. Will be removed.
    pub static_method_infos: HashMap<(TypeDefId, NameId), MethodInfo>,
    /// Interface vtable registry (uses interior mutability)
    pub interface_vtables: RefCell<InterfaceVtableRegistry>,
    /// Registry of native functions for external method calls
    pub native_registry: NativeRegistry,
    /// Counter for generating unique lambda names (interior mutability)
    pub lambda_counter: Cell<usize>,
}

impl CodegenState {
    /// Create a new CodegenState with empty lookup tables.
    pub fn new(native_registry: NativeRegistry) -> Self {
        Self {
            type_metadata: HashMap::new(),
            method_func_keys: HashMap::new(),
            impl_method_infos: HashMap::new(),
            static_method_infos: HashMap::new(),
            interface_vtables: RefCell::new(InterfaceVtableRegistry::new()),
            native_registry,
            lambda_counter: Cell::new(0),
        }
    }
}
