// types/codegen_state.rs
//
// Grouped codegen lookup tables - created once per Compiler, read-only after pass 1.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use vole_frontend::Symbol;
use vole_identity::{NameId, TypeDefId};
use vole_runtime::NativeRegistry;
use vole_sema::implement_registry::ImplTypeId;

use crate::interface_vtable::InterfaceVtableRegistry;

use super::{MethodInfo, TypeMetadata};

/// Grouped codegen lookup tables.
///
/// Created once in `Compiler::new`, populated during pass 1 (declarations),
/// then effectively read-only during pass 2 (compilation).
///
/// Fields using interior mutability (RefCell, Cell) can be mutated through
/// shared references during compilation.
pub struct CodegenState {
    /// Class and record metadata for struct literals, field access, and method calls
    pub type_metadata: HashMap<Symbol, TypeMetadata>,
    /// Implement block method info for primitive and named types
    pub impl_method_infos: HashMap<(ImplTypeId, NameId), MethodInfo>,
    /// Static method info keyed by (TypeDefId, method_name)
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
            impl_method_infos: HashMap::new(),
            static_method_infos: HashMap::new(),
            interface_vtables: RefCell::new(InterfaceVtableRegistry::new()),
            native_registry,
            lambda_counter: Cell::new(0),
        }
    }
}
