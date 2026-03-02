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
            interner: $self.analyzed.interner(),
            source_file_ptr: $source_file_ptr,
            global_module_bindings: &$self.global_module_bindings,
        }
    };
    // Module variant with custom interner.
    ($self:expr, $interner:expr, $source_file_ptr:expr) => {
        crate::types::CompileEnv {
            analyzed: $self.analyzed,
            state: &$self.state,
            interner: $interner,
            source_file_ptr: $source_file_ptr,
            global_module_bindings: &$self.global_module_bindings,
        }
    };
}

pub(crate) mod common;
mod compile_tests;
mod impl_dispatch;
mod impl_monomorph;
mod impls;
mod monomorphization;
mod program;
mod signatures;
mod state;
mod type_registry;

pub use signatures::{SelfParam, VirSelfParam};

/// Mode for function declaration in JIT.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DeclareMode {
    /// Declare function for local compilation (Linkage::Export)
    Declare,
    /// Import pre-compiled function (Linkage::Import)
    Import,
}

use rustc_hash::{FxHashMap, FxHashSet};

use cranelift::prelude::types as clif_types;
use cranelift_module::FuncId;

use crate::context::ModuleExportBinding;
use crate::errors::CodegenResult;
use crate::types::CodegenState;

use crate::AnalyzedProgram;
use crate::types::PendingMonomorph;
use crate::{FunctionKey, FunctionRegistry, JitContext, RuntimeKey};
use vole_frontend::Symbol;
use vole_identity::VirTypeId;
use vole_identity::{ModuleId, NameId, TypeDefId, TypeId};
use vole_runtime::NativeRegistry;

pub use state::TestInfo;

/// Compiler for generating Cranelift IR from AST
pub struct Compiler<'a> {
    jit: &'a mut JitContext,
    /// Reference to analyzed program (types, methods, etc.)
    analyzed: &'a AnalyzedProgram,
    pointer_type: clif_types::Type,
    tests: Vec<TestInfo>,
    /// FunctionKeys for declared test functions by index
    test_func_keys: Vec<FunctionKey>,
    /// Codegen lookup tables (type_metadata, method_infos, vtables, etc.)
    state: CodegenState,
    /// Opaque function identities and return types
    func_registry: FunctionRegistry,
    /// Global module bindings from top-level destructuring imports
    /// local_name -> (module_id, export_name, type_id)
    global_module_bindings: FxHashMap<Symbol, ModuleExportBinding>,
    /// When true, skip compilation of `Decl::Tests` blocks.
    /// Set by `vole run` to avoid codegen cost for tests in production.
    skip_tests: bool,
    /// Track which JIT functions have already been defined.
    /// Prevents DuplicateDefinition errors when the same method is provided
    /// by multiple implement blocks (e.g., `implement IFace26 for Class30`
    /// and `implement IFace25 for Class30` both providing `method137`).
    defined_functions: FxHashSet<FuncId>,
    /// Monomorphs lazily declared on demand during expression compilation.
    /// These have been declared (assigned a FuncId) but their bodies have not
    /// yet been compiled. Drained by the fixpoint loop after each compilation phase.
    pending_monomorphs: Vec<PendingMonomorph>,
    /// Combined monomorph cache size at last abstract expansion.
    /// Used to early-exit when caches haven't grown.
    last_expansion_cache_size: usize,
}

impl<'a> Compiler<'a> {
    pub fn new(jit: &'a mut JitContext, analyzed: &'a AnalyzedProgram) -> Self {
        let pointer_type = jit.pointer_type();

        // Initialize native registry with stdlib functions
        let mut native_registry = NativeRegistry::new();
        vole_runtime::stdlib::register_stdlib(&mut native_registry);

        let mut func_registry = FunctionRegistry::new(analyzed.name_table_rc());
        for runtime in RuntimeKey::ALL {
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
            test_func_keys: Vec::new(),
            state: CodegenState::new(native_registry),
            func_registry,
            global_module_bindings: FxHashMap::default(),
            skip_tests: false,
            defined_functions: FxHashSet::default(),
            pending_monomorphs: Vec::new(),
            last_expansion_cache_size: 0,
        }
    }

    /// Get the VIR type table for `VirTypeId`-based queries.
    #[inline]
    fn vir_type_table(&self) -> &vole_vir::type_table::VirTypeTable {
        &self.analyzed.vir_program().type_table
    }

    /// Get the module ID for the program being compiled.
    /// This may differ from main_module() when using a shared cache with multiple programs.
    fn program_module(&self) -> ModuleId {
        self.analyzed.module_id()
    }

    /// Convert a `VirTypeId` to sema `TypeId` (boundary helper).
    ///
    /// Uses the VirTypeTable reverse mapping — no arena access.
    #[allow(dead_code)]
    #[inline]
    fn sema_type_id(&self, vir_ty: VirTypeId) -> TypeId {
        let lossy = crate::types::vir_conversions::vir_to_sema_type_id_lossy(vir_ty);
        if lossy != TypeId::UNKNOWN || vir_ty == VirTypeId::UNKNOWN {
            return lossy;
        }
        self.vir_type_table()
            .lookup_vir_type_id(vir_ty)
            .unwrap_or(TypeId::UNKNOWN)
    }

    /// Get the "self" keyword symbol (panics if not interned - should never happen)
    fn self_symbol(&self) -> Symbol {
        self.analyzed
            .interner()
            .lookup("self")
            .expect("INTERNAL: 'self' keyword not interned")
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
                // Check both regular external functions and generic external functions with type mappings
                self.analyzed.external_func_by_name(&short_name).is_some()
                    || self
                        .analyzed
                        .generic_external_by_name(&short_name)
                        .is_some()
            })
            .unwrap_or(false)
    }

    /// Set the source file path for error reporting.
    /// The string is stored in the JitContext so it lives as long as the JIT code.
    pub fn set_source_file(&mut self, file: &str) {
        self.jit.set_source_file(file);
    }

    /// Set whether to skip compilation of tests blocks.
    /// When true, `Decl::Tests` is ignored during code generation.
    pub fn set_skip_tests(&mut self, skip: bool) {
        self.skip_tests = skip;
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
            // SAFETY: `source_file_ptr()` returns a pointer and length derived from a Rust
            // `String` (set via `JitContext::set_source_file`). The pointer remains valid
            // because the `JitContext` (and its `source_file` field) outlives this call.
            let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };
            std::str::from_utf8(bytes)
                .unwrap_or("<invalid utf-8>")
                .to_string()
        }
    }

    /// Take the compiled test metadata, leaving an empty vec
    pub fn take_tests(&mut self) -> Vec<TestInfo> {
        std::mem::take(&mut self.tests)
    }

    /// Define a function and clear the JIT context.
    /// This is the common teardown after function compilation.
    /// Silently skips if the function was already defined (e.g., from overlapping
    /// implement blocks), preventing DuplicateDefinition errors from Cranelift.
    fn finalize_function(&mut self, func_id: FuncId) -> CodegenResult<()> {
        if !self.defined_functions.insert(func_id) {
            // Already defined (e.g., same method from overlapping implement blocks).
            // Clear the context without defining to avoid DuplicateDefinition error.
            self.jit.clear();
            return Ok(());
        }
        self.jit.define_function(func_id)?;
        self.jit.clear();
        Ok(())
    }

    /// Declare or import a function given its NameId.
    ///
    /// This helper consolidates the common pattern of:
    /// 1. Looking up the semantic FunctionId from NameId
    /// 2. Building the Cranelift signature
    /// 3. Declaring/importing the function in the JIT
    /// 4. Registering the func_id and return_type in func_registry
    ///
    /// Returns `Some(func_key)` if successful, `None` if the function wasn't found
    /// in the entity registry.
    fn declare_function_by_name_id(
        &mut self,
        name_id: NameId,
        display_name: &str,
        mode: DeclareMode,
    ) -> Option<FunctionKey> {
        // Look up semantic FunctionId from NameId
        let semantic_func_id = self.analyzed.function_id_by_name_id(name_id)?;

        // Build signature from pre-resolved types
        let sig = self.build_signature_for_function(semantic_func_id);

        // Declare or import the function
        let jit_func_id = match mode {
            DeclareMode::Declare => self.jit.declare_function(display_name, &sig),
            DeclareMode::Import => self.jit.import_function(display_name, &sig),
        };

        // Intern the function key and register func_id
        let func_key = self.func_registry.intern_name_id(name_id);
        self.func_registry.set_func_id(func_key, jit_func_id);

        // Record return type from pre-resolved signature
        let return_type_id = self
            .analyzed
            .function_def(semantic_func_id)
            .sema_return_type;
        self.func_registry.set_return_type(func_key, return_type_id);

        Some(func_key)
    }

    // =====================================================================
    // VIR query wrappers (Phase 3a migration)
    //
    // These mirror the `vir_query_*` helpers on `CodegenCtx`, providing a
    // single call-site abstraction over VirTypeTable queries.
    // Compiler-level code (registration, signature building) uses these
    // instead of raw type-table calls.
    // =====================================================================

    /// Sema `TypeId` → `VirTypeId` translation.
    /// Consults the `type_id_to_vir` mapping populated during VIR lowering
    /// and the post-lowering sweep.
    #[inline]
    fn vir_lookup(&self, type_id: TypeId) -> VirTypeId {
        let lookup = self.vir_type_table().lookup_type_id(type_id);
        debug_assert!(
            lookup.is_some(),
            "TypeId({}) has no VirTypeId mapping — was it missed by the sweep?",
            type_id.raw(),
        );
        lookup.unwrap_or(VirTypeId::UNKNOWN)
    }

    /// Look up an existing array type by element `TypeId` via VirTypeTable.
    #[inline]
    fn vir_query_lookup_array(&self, elem: TypeId) -> Option<TypeId> {
        self.vir_type_table().lookup_array_sema(elem)
    }

    /// Return all concrete element types for which a RuntimeIterator exists.
    #[inline]
    fn vir_query_all_concrete_runtime_iterator_elem_types(&self) -> Vec<TypeId> {
        self.vir_type_table()
            .all_concrete_runtime_iterator_elem_types_sema()
    }

    /// Unwrap a type parameter `VirTypeId` to its `NameId` via VirTypeTable.
    #[allow(dead_code)]
    #[inline]
    fn vir_query_unwrap_type_param_v(&self, vir_ty: VirTypeId) -> Option<NameId> {
        crate::types::vir_conversions::vir_unwrap_type_param(vir_ty, self.vir_type_table())
    }

    /// Unwrap a type parameter to its `NameId` via VirTypeTable.
    #[inline]
    fn vir_query_unwrap_type_param(&self, type_id: TypeId) -> Option<NameId> {
        self.vir_query_unwrap_type_param_v(self.vir_lookup(type_id))
    }

    /// Unwrap a function `VirTypeId` to `(params, return_type)` via VirTypeTable.
    #[allow(dead_code)]
    #[inline]
    fn vir_query_unwrap_function_v(
        &self,
        vir_ty: VirTypeId,
    ) -> Option<(Vec<VirTypeId>, VirTypeId)> {
        crate::types::vir_conversions::vir_unwrap_function(vir_ty, self.vir_type_table())
            .map(|(params, ret)| (params.to_vec(), ret))
    }

    /// Look up the result of substituting type parameters in a type via VirTypeTable.
    ///
    /// Falls back to arena for compound types that were not lowered into the
    /// VIR type table (e.g., cross-module Self parameters in interface default
    /// methods).
    #[inline]
    fn vir_query_lookup_substitute(
        &self,
        ty: TypeId,
        subs: &FxHashMap<NameId, TypeId>,
    ) -> Option<TypeId> {
        self.vir_type_table()
            .lookup_substitute(ty, subs)
            .or_else(|| self.analyzed.type_arena().lookup_substitute(ty, subs))
    }

    /// Access the pre-interned primitive types.
    ///
    /// Primitive `TypeId`s are compile-time constants — no arena query needed.
    #[inline]
    fn vir_query_primitives(&self) -> vole_sema::type_arena::PrimitiveTypes {
        vole_sema::type_arena::PrimitiveTypes::CONST
    }

    /// Look up an existing runtime iterator type by element `TypeId` via VirTypeTable.
    #[inline]
    fn vir_query_lookup_runtime_iterator(&self, elem: TypeId) -> Option<TypeId> {
        self.vir_type_table().lookup_runtime_iterator_sema(elem)
    }

    /// Unwrap a fallible `VirTypeId` to `(success, errors)` via VirTypeTable.
    #[allow(dead_code)]
    #[inline]
    fn vir_query_unwrap_fallible_v(
        &self,
        vir_ty: VirTypeId,
    ) -> Option<(VirTypeId, Vec<VirTypeId>)> {
        crate::types::vir_conversions::vir_unwrap_fallible(vir_ty, self.vir_type_table())
            .map(|(success, errors)| (success, errors.to_vec()))
    }

    /// Unwrap a fallible sema `TypeId` to `(success, errors)` via VirTypeTable.
    #[inline]
    fn vir_query_unwrap_fallible(&self, type_id: TypeId) -> Option<(VirTypeId, Vec<VirTypeId>)> {
        self.vir_query_unwrap_fallible_v(self.vir_lookup(type_id))
    }

    /// Unwrap a class `VirTypeId` to `(TypeDefId, type_args)` via VirTypeTable.
    #[allow(dead_code)]
    #[inline]
    fn vir_query_unwrap_class_v(&self, vir_ty: VirTypeId) -> Option<(TypeDefId, Vec<VirTypeId>)> {
        crate::types::vir_conversions::vir_unwrap_class(vir_ty, self.vir_type_table())
            .map(|(def, args)| (def, args.to_vec()))
    }

    /// Unwrap a class type to `(TypeDefId, type_args)` via VirTypeTable.
    #[inline]
    fn vir_query_unwrap_class(&self, type_id: TypeId) -> Option<(TypeDefId, Vec<VirTypeId>)> {
        self.vir_query_unwrap_class_v(self.vir_lookup(type_id))
    }

    /// Unwrap a struct `VirTypeId` to `(TypeDefId, type_args)` via VirTypeTable.
    #[allow(dead_code)]
    #[inline]
    fn vir_query_unwrap_struct_v(&self, vir_ty: VirTypeId) -> Option<(TypeDefId, Vec<VirTypeId>)> {
        crate::types::vir_conversions::vir_unwrap_struct(vir_ty, self.vir_type_table())
            .map(|(def, args)| (def, args.to_vec()))
    }

    /// Unwrap a struct type to `(TypeDefId, type_args)` via VirTypeTable.
    #[inline]
    fn vir_query_unwrap_struct(&self, type_id: TypeId) -> Option<(TypeDefId, Vec<VirTypeId>)> {
        self.vir_query_unwrap_struct_v(self.vir_lookup(type_id))
    }

    /// Unwrap an interface `VirTypeId` to `(TypeDefId, type_args)` via VirTypeTable.
    #[allow(dead_code)]
    #[inline]
    fn vir_query_unwrap_interface_v(
        &self,
        vir_ty: VirTypeId,
    ) -> Option<(TypeDefId, Vec<VirTypeId>)> {
        crate::types::vir_conversions::vir_unwrap_interface(vir_ty, self.vir_type_table())
            .map(|(def, args)| (def, args.to_vec()))
    }

    /// Unwrap an array `VirTypeId` to its element `VirTypeId` via VirTypeTable.
    #[allow(dead_code)]
    #[inline]
    fn vir_query_unwrap_array_v(&self, vir_ty: VirTypeId) -> Option<VirTypeId> {
        crate::types::vir_conversions::vir_unwrap_array(vir_ty, self.vir_type_table())
    }

    /// Unwrap a fixed array `VirTypeId` to `(elem, len)` via VirTypeTable.
    #[allow(dead_code)]
    #[inline]
    fn vir_query_unwrap_fixed_array_v(&self, vir_ty: VirTypeId) -> Option<(VirTypeId, usize)> {
        crate::types::vir_conversions::vir_unwrap_fixed_array(vir_ty, self.vir_type_table())
            .map(|(elem, len)| (elem, len as usize))
    }

    /// Unwrap a tuple `VirTypeId` to its element `VirTypeId`s via VirTypeTable.
    #[allow(dead_code)]
    #[inline]
    fn vir_query_unwrap_tuple_v(&self, vir_ty: VirTypeId) -> Option<Vec<VirTypeId>> {
        crate::types::vir_conversions::vir_unwrap_tuple(vir_ty, self.vir_type_table())
            .map(|v| v.to_vec())
    }

    /// Unwrap a union `VirTypeId` to its variant `VirTypeId`s via VirTypeTable.
    ///
    /// Also handles `VirType::Optional { inner }`, expanding it to a two-element
    /// vector matching the sema arena's sorted variant order.
    #[allow(dead_code)]
    fn vir_query_unwrap_union_v(&self, vir_ty: VirTypeId) -> Option<Vec<VirTypeId>> {
        let table = self.vir_type_table();
        match table.get(vir_ty) {
            vole_vir::VirType::Union { variants } => Some(variants.to_vec()),
            vole_vir::VirType::Optional { inner } => Some(table.expand_optional_variants(*inner)),
            _ => None,
        }
    }

    /// Check if a `VirTypeId` contains any type parameter anywhere in its structure
    /// via VirTypeTable.
    #[allow(dead_code)]
    #[inline]
    fn vir_query_contains_type_param_v(&self, vir_ty: VirTypeId) -> bool {
        crate::types::vir_conversions::vir_contains_type_param(vir_ty, self.vir_type_table())
    }

    /// Check if a type contains any type parameter anywhere in its structure
    /// via VirTypeTable.
    #[inline]
    fn vir_query_contains_type_param(&self, type_id: TypeId) -> bool {
        self.vir_query_contains_type_param_v(self.vir_lookup(type_id))
    }

    /// Map a `VirTypeId` to its Cranelift type via VirTypeTable.
    #[allow(dead_code)]
    #[inline]
    fn vir_query_type_to_cranelift_v(&self, vir_ty: VirTypeId) -> clif_types::Type {
        // Sentinel types are always i8 (zero-field struct tag). VIR maps them
        // as Struct, which would incorrectly resolve to ptr_type.
        if crate::types::vir_conversions::vir_is_sentinel(vir_ty, self.vir_type_table()) {
            return clif_types::I8;
        }
        let ptr = self.pointer_type;
        crate::types::vir_conversions::vir_type_to_cranelift(vir_ty, self.vir_type_table(), ptr)
    }

    /// Map a sema `TypeId` to its Cranelift type via VirTypeTable.
    #[inline]
    fn vir_query_type_to_cranelift(&self, type_id: TypeId) -> clif_types::Type {
        self.vir_query_type_to_cranelift_v(self.vir_lookup(type_id))
    }
}
