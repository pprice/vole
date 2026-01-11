// src/codegen/compiler/mod.rs
mod impls;
mod program;
mod signatures;
mod state;
mod type_registry;

use std::collections::HashMap;

use cranelift::prelude::types as clif_types;

use crate::codegen::types::{MethodInfo, TypeMetadata};
use std::cell::RefCell;

use crate::codegen::{
    FunctionRegistry, JitContext, RuntimeFn, interface_vtable::InterfaceVtableRegistry,
};
use crate::commands::common::AnalyzedProgram;
use crate::frontend::{LetStmt, Symbol};
use crate::identity::{NameId, TypeDefId};
use crate::runtime::NativeRegistry;
use crate::sema::{ProgramQuery, TypeId};

pub use state::{ControlFlowCtx, TestInfo};

/// Compiler for generating Cranelift IR from AST
pub struct Compiler<'a> {
    jit: &'a mut JitContext,
    /// Reference to analyzed program (types, methods, etc.)
    analyzed: &'a AnalyzedProgram,
    pointer_type: clif_types::Type,
    tests: Vec<TestInfo>,
    /// Global variable declarations (let statements at module level)
    globals: Vec<LetStmt>,
    /// Counter for generating unique lambda names
    lambda_counter: usize,
    /// NameIds for declared test functions by index
    test_name_ids: Vec<NameId>,
    /// Class and record metadata: name -> TypeMetadata
    type_metadata: HashMap<Symbol, TypeMetadata>,
    /// Implement block method info keyed by (TypeId, method)
    impl_method_infos: HashMap<(TypeId, NameId), MethodInfo>,
    /// Static method info keyed by (TypeDefId, method_name)
    static_method_infos: HashMap<(TypeDefId, NameId), MethodInfo>,
    /// Interface vtable registry for interface-typed values
    interface_vtables: RefCell<InterfaceVtableRegistry>,
    /// Next type ID to assign
    next_type_id: u32,
    /// Opaque function identities and return types
    func_registry: FunctionRegistry,
    /// Registry of native functions for external method calls
    native_registry: NativeRegistry,
}

impl<'a> Compiler<'a> {
    pub fn new(jit: &'a mut JitContext, analyzed: &'a AnalyzedProgram) -> Self {
        let pointer_type = jit.pointer_type();

        // Initialize native registry with stdlib functions
        let mut native_registry = NativeRegistry::new();
        crate::runtime::stdlib::register_stdlib(&mut native_registry);

        let mut func_registry = FunctionRegistry::new(analyzed.name_table.clone());
        for runtime in RuntimeFn::ALL {
            if let Some(func_id) = jit.func_ids.get(runtime.name()) {
                let key = func_registry.intern_runtime(*runtime);
                func_registry.set_func_id(key, *func_id);
            }
        }

        Self {
            jit,
            analyzed,
            pointer_type,
            tests: Vec::new(),
            globals: Vec::new(),
            lambda_counter: 0,
            test_name_ids: Vec::new(),
            type_metadata: HashMap::new(),
            impl_method_infos: HashMap::new(),
            static_method_infos: HashMap::new(),
            interface_vtables: RefCell::new(InterfaceVtableRegistry::new()),
            next_type_id: 0,
            func_registry,
            native_registry,
        }
    }

    /// Get a query interface for the analyzed program
    fn query(&self) -> ProgramQuery<'_> {
        self.analyzed.query()
    }

    /// Intern a qualified function name (encapsulates borrow of interner + func_registry)
    fn intern_func(&mut self, module: crate::identity::ModuleId, segments: &[Symbol]) -> crate::codegen::FunctionKey {
        self.func_registry.intern_qualified(module, segments, &self.analyzed.interner)
    }

    /// Intern a function name with a NameId prefix (for implement block methods)
    fn intern_func_prefixed(&mut self, prefix: NameId, method: Symbol) -> crate::codegen::FunctionKey {
        self.func_registry.intern_with_prefix(prefix, method, &self.analyzed.interner)
    }

    /// Resolve a Symbol to a string (owned, for use across mutable operations)
    fn resolve_symbol(&self, sym: Symbol) -> String {
        self.analyzed.interner.resolve(sym).to_string()
    }

    /// Look up the "self" keyword symbol
    fn lookup_self_symbol(&self) -> Option<Symbol> {
        self.analyzed.interner.lookup("self")
    }

    /// Look up a method NameId by Symbol
    fn method_name_id(&self, name: Symbol) -> Option<NameId> {
        self.query().method_name_id(name)
    }

    /// Get TypeId from a Type (wraps TypeId::from_type with entity_registry.type_table)
    fn type_id_from_type(&self, ty: &crate::sema::Type) -> Option<TypeId> {
        TypeId::from_type(ty, &self.analyzed.entity_registry.type_table)
    }

    /// Set the source file path for error reporting.
    /// The string is stored in the JitContext so it lives as long as the JIT code.
    pub fn set_source_file(&mut self, file: &str) {
        self.jit.set_source_file(file);
    }

    /// Get the source file pointer and length from the JitContext.
    fn source_file_ptr(&self) -> (*const u8, usize) {
        self.jit.source_file_ptr()
    }

    /// Get the source file as a string for TestInfo metadata.
    fn source_file_str(&self) -> String {
        let (ptr, len) = self.jit.source_file_ptr();
        if ptr.is_null() || len == 0 {
            String::new()
        } else {
            unsafe {
                std::str::from_utf8_unchecked(std::slice::from_raw_parts(ptr, len)).to_string()
            }
        }
    }

    /// Take the compiled test metadata, leaving an empty vec
    pub fn take_tests(&mut self) -> Vec<TestInfo> {
        std::mem::take(&mut self.tests)
    }
}

#[cfg(test)]
mod tests;
