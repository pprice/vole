// src/codegen/compiler/mod.rs
pub(crate) mod common;
mod impls;
mod program;
mod signatures;
mod state;
mod type_registry;

pub use signatures::{SelfParam, TypeResolver};

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use cranelift::prelude::types as clif_types;

use crate::types::{MethodInfo, TypeMetadata};

use crate::AnalyzedProgram;
use crate::{FunctionRegistry, JitContext, RuntimeFn, interface_vtable::InterfaceVtableRegistry};
use vole_frontend::{Expr, Interner, Symbol};
use vole_identity::{NameId, TypeDefId};
use vole_runtime::NativeRegistry;
use vole_sema::{ImplTypeId, ProgramQuery, type_arena::TypeId};

pub use state::{ControlFlowCtx, TestInfo};

/// Compiler for generating Cranelift IR from AST
pub struct Compiler<'a> {
    jit: &'a mut JitContext,
    /// Reference to analyzed program (types, methods, etc.)
    analyzed: &'a AnalyzedProgram,
    pointer_type: clif_types::Type,
    tests: Vec<TestInfo>,
    /// Global variable initializer expressions keyed by name
    global_inits: HashMap<Symbol, Expr>,
    /// Counter for generating unique lambda names
    lambda_counter: usize,
    /// NameIds for declared test functions by index
    test_name_ids: Vec<NameId>,
    /// Class and record metadata: name -> TypeMetadata
    type_metadata: HashMap<Symbol, TypeMetadata>,
    /// Implement block method info keyed by (ImplTypeId, method)
    impl_method_infos: HashMap<(ImplTypeId, NameId), MethodInfo>,
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
        vole_runtime::stdlib::register_stdlib(&mut native_registry);

        let mut func_registry = FunctionRegistry::new(Rc::clone(&analyzed.name_table));
        for runtime in RuntimeFn::ALL {
            // Runtime functions are in imported_func_ids (Import linkage)
            if let Some(func_id) = jit.imported_func_ids.get(runtime.name()) {
                let key = func_registry.intern_runtime(*runtime);
                func_registry.set_func_id(key, *func_id);
            }
        }

        Self {
            jit,
            analyzed,
            pointer_type,
            tests: Vec::new(),
            global_inits: HashMap::new(),
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

    /// Get a TypeCtx for type resolution functions
    fn type_ctx(&self) -> crate::types::TypeCtx<'_> {
        crate::types::TypeCtx::new(self.query(), self.pointer_type)
    }

    /// Get a TypeCtx with a custom interner (for module programs)
    fn type_ctx_with_interner<'b>(&'b self, interner: &'b Interner) -> crate::types::TypeCtx<'b> {
        use vole_sema::ProgramQuery;
        let query = ProgramQuery::new(
            &self.analyzed.entity_registry,
            &self.analyzed.expression_data,
            &self.analyzed.name_table,
            interner,
            &self.analyzed.implement_registry,
            &self.analyzed.module_programs,
            &self.analyzed.type_arena,
        );
        crate::types::TypeCtx::new(query, self.pointer_type)
    }

    /// Intern a qualified function name (encapsulates borrow of interner + func_registry)
    fn intern_func(
        &mut self,
        module: vole_identity::ModuleId,
        segments: &[Symbol],
    ) -> crate::FunctionKey {
        self.func_registry
            .intern_qualified(module, segments, &self.analyzed.interner)
    }

    /// Intern a function name with a NameId prefix (for implement block methods)
    fn intern_func_prefixed(&mut self, prefix: NameId, method: Symbol) -> crate::FunctionKey {
        self.func_registry
            .intern_with_prefix(prefix, method, &self.analyzed.interner)
    }

    /// Resolve a Symbol to a string (owned, for use across mutable operations)
    fn resolve_symbol(&self, sym: Symbol) -> String {
        self.analyzed.interner.resolve(sym).to_string()
    }

    /// Get the "self" keyword symbol (panics if not interned - should never happen)
    fn self_symbol(&self) -> Symbol {
        self.analyzed
            .interner
            .lookup("self")
            .expect("'self' keyword should always be interned")
    }

    /// Look up a method NameId by Symbol (panics if not found)
    fn method_name_id(&self, name: Symbol) -> NameId {
        self.query().method_name_id(name)
    }

    /// Get ImplTypeId from a TypeId
    fn impl_type_id_from_type_id(&self, ty: TypeId) -> Option<ImplTypeId> {
        ImplTypeId::from_type_id(
            ty,
            &self.analyzed.type_arena.borrow(),
            &self.analyzed.entity_registry,
        )
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
