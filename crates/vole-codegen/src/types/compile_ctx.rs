// types/compile_ctx.rs
//
// Legacy CompileCtx - being migrated to split contexts.
// This struct bundles too many concerns and is being incrementally replaced.

use cranelift::prelude::Type;
use cranelift_jit::JITModule;
use cranelift_module::Module;
use rustc_hash::FxHashMap;
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;

use crate::AnalyzedProgram;
use crate::FunctionRegistry;
use vole_frontend::{Expr, Interner, NodeId, Symbol};
use vole_identity::TypeDefId;
use vole_identity::{NameId, Resolver};
use vole_runtime::NativeRegistry;
use vole_sema::generic::MonomorphCache;
use vole_sema::implement_registry::ImplTypeId;
use vole_sema::type_arena::{TypeArena, TypeId};
use vole_sema::{EntityRegistry, ProgramQuery, ResolverEntityExt};

use super::{FunctionCtx, MethodInfo, TypeCtx, TypeMetadata};

/// Context for compiling expressions and statements.
///
/// # Deprecation Notice
///
/// **This struct is deprecated and being migrated to split contexts.**
/// Use the following instead:
/// - [`TypeCtx`] for read-only program queries (arena, interner, name table)
/// - [`CodegenCtx`] for mutable JIT infrastructure (module, func registry)
/// - [`FunctionCtx`] for per-function state (return type, substitutions)
/// - [`GlobalCtx`] for shared read-only registries
/// - [`Cg`](crate::context::Cg) wraps all the above for function body compilation
///
/// ## Migration Guide
///
/// 1. Replace `CompileCtx { ... }` construction with `CtxFactory` methods
/// 2. Use `Cg::new_split()` instead of `Cg::new()` with CompileCtx
/// 3. Access fields via the appropriate split context
///
/// Once all call sites are migrated, this struct will be removed.
///
/// Note: `arena`, `pointer_type`, and `monomorph_cache` are derived from `analyzed`
/// via accessor methods rather than stored as separate fields.
#[allow(dead_code)]
pub(crate) struct CompileCtx<'a> {
    /// Analyzed program containing expr_types, method_resolutions, etc.
    pub analyzed: &'a AnalyzedProgram,
    /// Interner for symbol resolution (may differ from analyzed.interner for module code)
    pub interner: &'a Interner,
    pub module: &'a mut JITModule,
    pub func_registry: &'a mut FunctionRegistry,
    pub source_file_ptr: (*const u8, usize),
    /// Global variable initializer expressions keyed by name
    pub global_inits: &'a HashMap<Symbol, Expr>,
    /// Counter for generating unique lambda names (interior mutability)
    pub lambda_counter: &'a Cell<usize>,
    /// Class and record metadata for struct literals, field access, and method calls
    pub type_metadata: &'a HashMap<Symbol, TypeMetadata>,
    /// Implement block method info for primitive and named types
    pub impl_method_infos: &'a HashMap<(ImplTypeId, NameId), MethodInfo>,
    /// Static method info keyed by (TypeDefId, method_name)
    pub static_method_infos: &'a HashMap<(TypeDefId, NameId), MethodInfo>,
    /// Interface vtable registry (interface + concrete type -> data id)
    pub interface_vtables: &'a RefCell<crate::interface_vtable::InterfaceVtableRegistry>,
    /// Current function's return type (needed for raise statements in fallible functions)
    pub current_function_return_type: Option<TypeId>,
    /// Registry of native functions for external method calls
    pub native_registry: &'a NativeRegistry,
    /// Current module path when compiling module code (e.g., "std:math")
    /// None when compiling main program code
    pub current_module: Option<&'a str>,
    /// Type substitutions for monomorphized class method compilation
    /// Maps type param NameId -> concrete TypeId (interned for O(1) equality)
    pub type_substitutions: Option<&'a HashMap<NameId, TypeId>>,
    /// Cache for substituted types (avoids repeated HashMap conversion and arena mutations)
    /// Only populated when type_substitutions is Some
    pub substitution_cache: RefCell<HashMap<TypeId, TypeId>>,
}

#[allow(dead_code)]
impl<'a> CompileCtx<'a> {
    /// Get a query interface for the analyzed program
    #[inline]
    pub fn query(&self) -> ProgramQuery<'_> {
        self.analyzed.query()
    }

    /// Borrow the type arena (derived from analyzed)
    #[inline]
    pub fn arena(&self) -> std::cell::Ref<'_, TypeArena> {
        self.analyzed.type_arena()
    }

    /// Get the arena Rc (for functions that need the raw Rc<RefCell<TypeArena>>)
    #[inline]
    pub fn arena_rc(&self) -> &Rc<RefCell<TypeArena>> {
        self.analyzed.type_arena_ref()
    }

    /// Get an update interface for arena mutations.
    /// Centralizes all borrow_mut() calls for cleaner code.
    #[inline]
    pub fn update(&self) -> vole_sema::ProgramUpdate<'_> {
        vole_sema::ProgramUpdate::new(self.analyzed.type_arena_ref())
    }

    /// Get the pointer type (derived from module target config)
    #[inline]
    pub fn ptr_type(&self) -> Type {
        self.module.target_config().pointer_type()
    }

    /// Get the monomorph cache (derived from analyzed)
    #[inline]
    pub fn monomorph_cache(&self) -> &MonomorphCache {
        &self.analyzed.entity_registry().monomorph_cache
    }

    /// Get the interner (API-compatible with CodegenCtx)
    #[inline]
    pub fn interner(&self) -> &'a Interner {
        self.interner
    }

    /// Get the entity registry.
    #[inline]
    pub fn registry(&self) -> &'a EntityRegistry {
        self.analyzed.entity_registry()
    }

    /// Substitute type parameters with concrete types using TypeId directly.
    /// Uses a cache to avoid repeated HashMap conversion and arena mutations.
    pub fn substitute_type_id(&self, ty: TypeId) -> TypeId {
        if let Some(substitutions) = self.type_substitutions {
            // Check cache first
            if let Some(&cached) = self.substitution_cache.borrow().get(&ty) {
                return cached;
            }
            // Convert std HashMap to FxHashMap for arena compatibility
            let subs: FxHashMap<NameId, TypeId> =
                substitutions.iter().map(|(&k, &v)| (k, v)).collect();
            let result = self.update().substitute(ty, &subs);
            // Cache the result
            self.substitution_cache.borrow_mut().insert(ty, result);
            result
        } else {
            ty
        }
    }

    /// Resolve a type via the resolution chain (primitive → module → builtin).
    /// This replaces calling resolver().resolve_type() which had lifetime issues.
    pub fn resolve_type(&self, sym: Symbol) -> Option<TypeDefId> {
        let name_table = self.analyzed.name_table();
        let module_id = self
            .current_module
            .and_then(|path| name_table.module_id_if_known(path))
            .unwrap_or_else(|| name_table.main_module());
        let resolver = Resolver::new(self.interner, &name_table, module_id, &[]);
        resolver.resolve_type(sym, self.analyzed.entity_registry())
    }

    /// Resolve a type by string name, with fallback to interface/class short name search.
    /// This replaces calling resolver().resolve_type_str_or_interface() which had lifetime issues.
    pub fn resolve_type_str_or_interface(&self, name: &str) -> Option<TypeDefId> {
        let name_table = self.analyzed.name_table();
        let module_id = self
            .current_module
            .and_then(|path| name_table.module_id_if_known(path))
            .unwrap_or_else(|| name_table.main_module());
        let resolver = Resolver::new(self.interner, &name_table, module_id, &[]);
        resolver.resolve_type_str_or_interface(name, self.analyzed.entity_registry())
    }

    /// Look up expression type, checking module-specific expr_types if compiling module code.
    /// Returns the interned TypeId handle.
    pub fn get_expr_type(&self, node_id: &NodeId) -> Option<TypeId> {
        // When compiling module code, NodeIds are relative to that module's program
        // Use module-specific expr_types if available
        if let Some(module_path) = self.current_module
            && let Some(module_types) = self.analyzed.query().expr_data().module_types(module_path)
            && let Some(ty) = module_types.get(node_id)
        {
            return Some(*ty);
        }
        // Fall back to main program expr_types via query interface
        self.analyzed.query().type_of(*node_id)
    }

    /// Get the substituted return type for a generic method call, if one was computed by sema.
    /// This avoids codegen having to recompute type substitution for generic method calls.
    pub fn get_substituted_return_type(&self, node_id: &NodeId) -> Option<TypeId> {
        self.analyzed
            .query()
            .expr_data()
            .get_substituted_return_type(*node_id)
    }

    // ========== Extraction methods for incremental migration ==========
    // These methods are used during incremental migration to the new context system.

    /// Extract a FunctionCtx from this CompileCtx.
    /// Used during incremental migration to the new context system.
    pub fn function_ctx(&self) -> FunctionCtx<'a> {
        let module_id = self
            .current_module
            .and_then(|path| self.analyzed.name_table().module_id_if_known(path));
        FunctionCtx {
            return_type: self.current_function_return_type,
            current_module: module_id,
            substitutions: self.type_substitutions,
            substitution_cache: RefCell::new(HashMap::new()),
        }
    }

    /// Extract a TypeCtx from this CompileCtx.
    /// Used during incremental migration to the new context system.
    pub fn type_ctx(&self) -> TypeCtx<'_> {
        TypeCtx::new(self.query(), self.ptr_type())
    }

    // ========== Delegation methods for incremental migration ==========

    /// Get the current module path.
    /// Delegation method for migrating to FunctionCtx.
    #[inline]
    pub fn module_path(&self) -> Option<&'a str> {
        self.current_module
    }

    // ========== GlobalCtx delegation methods ==========
    // These methods provide access to fields that will move to GlobalCtx.

    /// Get source file pointer for error reporting.
    #[inline]
    pub fn source_file(&self) -> (*const u8, usize) {
        self.source_file_ptr
    }

    /// Get global variable initializer by name.
    #[inline]
    pub fn global_init(&self, name: Symbol) -> Option<&Expr> {
        self.global_inits.get(&name)
    }

    /// Get current lambda counter and increment it (returns value before increment).
    #[inline]
    pub fn next_lambda_id(&self) -> usize {
        let id = self.lambda_counter.get();
        self.lambda_counter.set(id + 1);
        id
    }

    // ========== Registry field delegation methods ==========
    // These provide read access to lookup tables used during codegen.
    // Allow dead_code until all callers are migrated.

    /// Get native function registry for external calls.
    #[inline]
    pub fn native_funcs(&self) -> &'a NativeRegistry {
        self.native_registry
    }

    /// Get impl method info map.
    #[inline]
    pub fn impl_methods(&self) -> &'a HashMap<(ImplTypeId, NameId), MethodInfo> {
        self.impl_method_infos
    }

    /// Get type metadata map.
    #[inline]
    pub fn type_meta(&self) -> &'a HashMap<Symbol, TypeMetadata> {
        self.type_metadata
    }

    // ========== Core CodegenCtx field delegation methods ==========
    // These provide access to the mutable JIT infrastructure.

    /// Get mutable reference to JIT module.
    #[inline]
    pub fn jit_module(&mut self) -> &mut JITModule {
        self.module
    }

    /// Get mutable reference to function registry.
    #[inline]
    pub fn funcs(&mut self) -> &mut FunctionRegistry {
        self.func_registry
    }

    /// Create a JitCtx by reborrowing fields from CompileCtx.
    ///
    /// This is a transition helper for migrating from CompileCtx to JitCtx.
    /// The returned JitCtx has a lifetime tied to the mutable borrow of self.
    #[inline]
    pub fn as_codegen_ctx(&mut self) -> super::CodegenCtx<'_> {
        super::CodegenCtx::new(self.module, self.func_registry)
    }
}

impl<'a> crate::vtable_ctx::VtableCtx for CompileCtx<'a> {
    fn analyzed(&self) -> &AnalyzedProgram {
        self.analyzed
    }

    fn arena(&self) -> std::cell::Ref<'_, TypeArena> {
        self.analyzed.type_arena()
    }

    fn arena_rc(&self) -> &Rc<RefCell<TypeArena>> {
        self.analyzed.type_arena_ref()
    }

    fn registry(&self) -> &EntityRegistry {
        self.analyzed.entity_registry()
    }

    fn interner(&self) -> &Interner {
        self.interner
    }

    fn query(&self) -> ProgramQuery<'_> {
        self.analyzed.query()
    }

    fn update(&self) -> vole_sema::ProgramUpdate<'_> {
        vole_sema::ProgramUpdate::new(self.analyzed.type_arena_ref())
    }

    fn ptr_type(&self) -> Type {
        self.module.target_config().pointer_type()
    }

    fn jit_module(&mut self) -> &mut JITModule {
        self.module
    }

    fn funcs(&mut self) -> &mut FunctionRegistry {
        self.func_registry
    }

    fn resolve_type_str_or_interface(&self, name: &str) -> Option<TypeDefId> {
        let name_table = self.analyzed.name_table();
        let module_id = self
            .current_module
            .and_then(|path| name_table.module_id_if_known(path))
            .unwrap_or_else(|| name_table.main_module());
        let resolver = Resolver::new(self.interner, &name_table, module_id, &[]);
        resolver.resolve_type_str_or_interface(name, self.analyzed.entity_registry())
    }

    fn native_registry(&self) -> &NativeRegistry {
        self.native_registry
    }

    fn interface_vtables(&self) -> &RefCell<crate::interface_vtable::InterfaceVtableRegistry> {
        self.interface_vtables
    }

    fn type_metadata(&self) -> &HashMap<Symbol, TypeMetadata> {
        self.type_metadata
    }

    fn impl_method_infos(&self) -> &HashMap<(ImplTypeId, NameId), MethodInfo> {
        self.impl_method_infos
    }
}
