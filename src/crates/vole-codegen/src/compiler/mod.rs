// src/codegen/compiler/mod.rs

/// Macro to construct CompileEnv from Compiler fields.
/// This is a macro (not a method) to allow field-level borrowing,
/// which lets the borrow checker see that CompileEnv uses different
/// fields than CodegenCtx.
macro_rules! compile_env {
    ($self:expr, $source_file_ptr:expr) => {
        crate::types::CompileEnv {
            analyzed: $self.analyzed,
            state: &$self.state,
            interner: &$self.analyzed.interner,
            global_inits: &$self.global_inits,
            source_file_ptr: $source_file_ptr,
            current_module: None,
            global_module_bindings: &$self.global_module_bindings,
        }
    };
    // Module variant with custom interner, global_inits, and module_id
    ($self:expr, $interner:expr, $global_inits:expr, $source_file_ptr:expr, $module_id:expr) => {
        crate::types::CompileEnv {
            analyzed: $self.analyzed,
            state: &$self.state,
            interner: $interner,
            global_inits: $global_inits,
            source_file_ptr: $source_file_ptr,
            current_module: Some($module_id),
            global_module_bindings: &$self.global_module_bindings,
        }
    };
}

pub(crate) mod common;
mod impls;
mod program;
mod signatures;
mod state;
mod type_registry;

pub use signatures::SelfParam;

use std::rc::Rc;

use rustc_hash::FxHashMap;

use cranelift::prelude::types as clif_types;

use crate::context::ModuleExportBinding;
use crate::types::CodegenState;

use crate::AnalyzedProgram;
use crate::{FunctionKey, FunctionRegistry, JitContext, RuntimeFn};
use vole_frontend::{Expr, Symbol};
use vole_identity::{ModuleId, NameId};
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
    global_inits: FxHashMap<Symbol, Expr>,
    /// FunctionKeys for declared test functions by index
    test_func_keys: Vec<FunctionKey>,
    /// Codegen lookup tables (type_metadata, method_infos, vtables, etc.)
    state: CodegenState,
    /// Next type ID to assign
    next_type_id: u32,
    /// Opaque function identities and return types
    func_registry: FunctionRegistry,
    /// Global module bindings from top-level destructuring imports
    /// local_name -> (module_id, export_name, type_id)
    global_module_bindings: FxHashMap<Symbol, ModuleExportBinding>,
}

impl<'a> Compiler<'a> {
    pub fn new(jit: &'a mut JitContext, analyzed: &'a AnalyzedProgram) -> Self {
        let pointer_type = jit.pointer_type();

        // Initialize native registry with stdlib functions
        let mut native_registry = NativeRegistry::new();
        vole_runtime::stdlib::register_stdlib(&mut native_registry);

        let mut func_registry = FunctionRegistry::new(Rc::clone(analyzed.name_table_ref()));
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
            global_inits: FxHashMap::default(),
            test_func_keys: Vec::new(),
            state: CodegenState::new(native_registry),
            next_type_id: 0,
            func_registry,
            global_module_bindings: FxHashMap::default(),
        }
    }

    /// Get a query interface for the analyzed program
    fn query(&self) -> ProgramQuery<'_> {
        self.analyzed.query()
    }

    /// Get the module ID for the program being compiled.
    /// This may differ from main_module() when using a shared cache with multiple programs.
    fn program_module(&self) -> ModuleId {
        self.analyzed.module_id
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
            self.analyzed.type_arena(),
            self.analyzed.entity_registry(),
        )
    }

    /// Check if a function (by NameId) is an external function.
    ///
    /// External functions are registered by their short name in the implement registry.
    /// This helper encapsulates the pattern of extracting the short name and checking
    /// the registry.
    ///
    /// Note: This uses string-based lookup internally. A future improvement would be
    /// to add NameId-based indexing to the implement registry.
    fn is_external_func(&self, name_id: NameId) -> bool {
        self.analyzed
            .name_table()
            .last_segment_str(name_id)
            .map(|short_name| {
                let registry = self.analyzed.implement_registry();
                // Check both regular external functions and generic external functions with type mappings
                registry.get_external_func(&short_name).is_some()
                    || registry.get_generic_external(&short_name).is_some()
            })
            .unwrap_or(false)
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

    /// Define a function and clear the JIT context.
    /// This is the common teardown after function compilation.
    fn finalize_function(&mut self, func_id: cranelift_module::FuncId) -> Result<(), String> {
        self.jit.define_function(func_id)?;
        self.jit.clear();
        Ok(())
    }
}
