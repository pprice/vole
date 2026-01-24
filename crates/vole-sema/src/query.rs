//! Query interface for analyzed programs.
//!
//! ProgramQuery provides a clean API for querying type information,
//! method resolutions, and other analysis results. It encapsulates
//! access to multiple internal structures, reducing boilerplate in codegen.

use rustc_hash::FxHashMap;

use std::cell::RefCell;
use std::rc::Rc;

use crate::entity_defs::{FieldDef, GlobalDef, Implementation, MethodDef, TypeDef};
use crate::entity_registry::EntityRegistry;
use crate::expression_data::ExpressionData;
use crate::generic::{MonomorphCache, MonomorphInstance, MonomorphKey, StaticMethodMonomorphKey};
use crate::implement_registry::{ExternalMethodInfo, ImplementRegistry};
use crate::resolution::ResolvedMethod;
use crate::type_arena::{TypeArena, TypeId};
use vole_frontend::{Expr, Interner, NodeId, Program, Span, Symbol};
use vole_identity::{FieldId, MethodId, ModuleId, NameId, NameTable, Resolver, TypeDefId};

use crate::resolve::ResolverEntityExt;

/// Query interface for accessing analyzed program data.
///
/// Provides a unified API for type queries, method resolution lookups,
/// name resolution, and other analysis results. Designed to reduce
/// boilerplate in codegen by encapsulating common multi-step lookups.
pub struct ProgramQuery<'a> {
    registry: &'a EntityRegistry,
    expr_data: &'a ExpressionData,
    name_table: &'a Rc<RefCell<NameTable>>,
    interner: &'a Interner,
    implement_registry: &'a ImplementRegistry,
    module_programs: &'a FxHashMap<String, (Program, Interner)>,
    type_arena: &'a Rc<RefCell<TypeArena>>,
}

impl<'a> ProgramQuery<'a> {
    /// Create a new query interface
    pub fn new(
        registry: &'a EntityRegistry,
        expr_data: &'a ExpressionData,
        name_table: &'a Rc<RefCell<NameTable>>,
        interner: &'a Interner,
        implement_registry: &'a ImplementRegistry,
        module_programs: &'a FxHashMap<String, (Program, Interner)>,
        type_arena: &'a Rc<RefCell<TypeArena>>,
    ) -> Self {
        Self {
            registry,
            expr_data,
            name_table,
            interner,
            implement_registry,
            module_programs,
            type_arena,
        }
    }

    // =========================================================================
    // Expression queries
    // =========================================================================

    /// Get the type of an expression by its NodeId (returns interned TypeId handle).
    #[must_use]
    pub fn type_of(&self, node: NodeId) -> Option<TypeId> {
        self.expr_data.get_type(node)
    }

    /// Get the resolved method at a call site
    #[must_use]
    pub fn method_at(&self, node: NodeId) -> Option<&'a ResolvedMethod> {
        self.expr_data.get_method(node)
    }

    /// Get the resolved method at a call site, checking module-specific resolutions first
    #[must_use]
    pub fn method_at_in_module(
        &self,
        node: NodeId,
        current_module: Option<&str>,
    ) -> Option<&'a ResolvedMethod> {
        self.expr_data.get_method_in_module(node, current_module)
    }

    /// Get the monomorphization key for a generic call
    #[must_use]
    pub fn monomorph_for(&self, node: NodeId) -> Option<&'a MonomorphKey> {
        self.expr_data.get_generic(node)
    }

    /// Get the monomorphization key for a generic static method call
    #[must_use]
    pub fn static_method_generic_at(&self, node: NodeId) -> Option<&'a StaticMethodMonomorphKey> {
        self.expr_data.get_static_method_generic(node)
    }

    /// Get the closure function type for a scoped function by its declaration span.
    /// Scoped functions (in test blocks) are compiled as closures, and sema pre-computes
    /// their function types so codegen doesn't need to create them.
    #[must_use]
    pub fn scoped_function_type(&self, span: Span) -> Option<TypeId> {
        self.expr_data.get_scoped_function_type(span)
    }

    // =========================================================================
    // Name resolution (high-frequency in codegen)
    // =========================================================================

    /// Get the main module ID
    pub fn main_module(&self) -> ModuleId {
        self.name_table.borrow().main_module()
    }

    /// Display a NameId as a qualified string (e.g., "module::Type::method")
    pub fn display_name(&self, name_id: NameId) -> String {
        self.name_table.borrow().display(name_id)
    }

    /// Resolve a Symbol to its string representation
    pub fn resolve_symbol(&self, sym: Symbol) -> &'a str {
        self.interner.resolve(sym)
    }

    /// Look up a Symbol in the interner (panics if not found)
    pub fn symbol(&self, s: &str) -> Symbol {
        self.interner
            .lookup(s)
            .unwrap_or_else(|| panic!("symbol '{}' not interned", s))
    }

    /// Look up a Symbol in the interner, returning None if not found
    #[must_use]
    pub fn try_symbol(&self, s: &str) -> Option<Symbol> {
        self.interner.lookup(s)
    }

    /// Convert Symbols to a NameId in the given module (panics if not found)
    pub fn name_id(&self, module: ModuleId, segments: &[Symbol]) -> NameId {
        self.name_table
            .borrow()
            .name_id(module, segments, self.interner)
            .unwrap_or_else(|| {
                let names: Vec<_> = segments.iter().map(|s| self.interner.resolve(*s)).collect();
                panic!("name_id not found for {:?} in module {:?}", names, module)
            })
    }

    /// Convert Symbols to a NameId in the given module, returning None if not found
    #[must_use]
    pub fn try_name_id(&self, module: ModuleId, segments: &[Symbol]) -> Option<NameId> {
        self.name_table
            .borrow()
            .name_id(module, segments, self.interner)
    }

    /// Convert a single Symbol to a NameId in the main module (panics if not found)
    pub fn name_id_in_main(&self, sym: Symbol) -> NameId {
        self.name_id(self.main_module(), &[sym])
    }

    /// Convert a single Symbol to a NameId in the main module, returning None if not found
    #[must_use]
    pub fn try_name_id_in_main(&self, sym: Symbol) -> Option<NameId> {
        self.try_name_id(self.main_module(), &[sym])
    }

    /// Get the module path for a module ID
    pub fn module_path(&self, module: ModuleId) -> String {
        self.name_table.borrow().module_path(module).to_string()
    }

    /// Look up a module ID by path, returning None if not found
    #[must_use]
    pub fn module_id_if_known(&self, path: &str) -> Option<ModuleId> {
        self.name_table.borrow().module_id_if_known(path)
    }

    /// Look up a module ID by path, falling back to main module if not found
    pub fn module_id_or_main(&self, path: &str) -> ModuleId {
        self.name_table
            .borrow()
            .module_id_if_known(path)
            .unwrap_or_else(|| self.main_module())
    }

    /// Get the last segment of a NameId as a string
    #[must_use]
    pub fn last_segment(&self, name_id: NameId) -> Option<String> {
        self.name_table.borrow().last_segment_str(name_id)
    }

    // =========================================================================
    // Type queries
    // =========================================================================

    /// Get a type definition by ID
    pub fn get_type(&self, type_id: TypeDefId) -> &'a TypeDef {
        self.registry.get_type(type_id)
    }

    /// Look up a TypeDefId by its NameId (panics if not found)
    pub fn type_def_id(&self, name_id: NameId) -> TypeDefId {
        self.registry
            .type_by_name(name_id)
            .unwrap_or_else(|| panic!("type not found for name_id {:?}", name_id))
    }

    /// Look up a TypeDefId by its NameId, returning None if not found
    #[must_use]
    pub fn try_type_def_id(&self, name_id: NameId) -> Option<TypeDefId> {
        self.registry.type_by_name(name_id)
    }

    /// Resolve a Symbol to a TypeDefId using the full resolution chain.
    /// This follows the same resolution path as sema:
    /// 1. Primitives
    /// 2. Current module definitions
    /// 3. Explicit imports
    /// 4. Builtin module (stdlib types)
    /// 5. Interface/class fallback (for prelude types like Set, Map)
    #[must_use]
    pub fn resolve_type_def(&self, module: ModuleId, sym: Symbol) -> Option<TypeDefId> {
        let name_table = self.name_table.borrow();
        let resolver = Resolver::new(self.interner, &name_table, module, &[]);
        resolver.resolve_type_or_interface(sym, self.registry)
    }

    /// Resolve a type name string to a TypeDefId using the full resolution chain.
    #[must_use]
    pub fn resolve_type_def_by_str(&self, module: ModuleId, name: &str) -> Option<TypeDefId> {
        let name_table = self.name_table.borrow();
        let resolver = Resolver::new(self.interner, &name_table, module, &[]);
        resolver.resolve_type_str_or_interface(name, self.registry)
    }

    /// Resolve a type alias to its underlying type.
    /// Returns None if the type is not an alias or has no aliased_type.
    #[must_use]
    pub fn resolve_alias(&self, type_id: TypeDefId) -> Option<TypeId> {
        self.registry.get_type(type_id).aliased_type
    }

    /// Get all interface implementations for a type
    pub fn implementations_of(&self, type_id: TypeDefId) -> &'a [Implementation] {
        &self.registry.get_type(type_id).implements
    }

    /// Get all interface TypeDefIds that a type implements
    pub fn implemented_interfaces(&self, type_id: TypeDefId) -> Vec<TypeDefId> {
        self.registry.get_implemented_interfaces(type_id)
    }

    /// Check if a type is a functional interface (single abstract method).
    /// Returns the single method's ID if it's a functional interface.
    #[must_use]
    pub fn is_functional_interface(&self, type_id: TypeDefId) -> Option<MethodId> {
        self.registry.is_functional(type_id)
    }

    /// Get the NameId for a type definition
    pub fn type_name_id(&self, type_id: TypeDefId) -> NameId {
        self.registry.get_type(type_id).name_id
    }

    /// Get the short name of a type (last segment only)
    #[must_use]
    pub fn type_short_name(&self, type_id: TypeDefId) -> Option<String> {
        let name_id = self.registry.get_type(type_id).name_id;
        self.name_table.borrow().last_segment_str(name_id)
    }

    // =========================================================================
    // Field queries
    // =========================================================================

    /// Get a field definition by ID
    pub fn get_field(&self, field_id: FieldId) -> &'a FieldDef {
        self.registry.get_field(field_id)
    }

    /// Iterate over fields on a type
    pub fn fields_on_type(&self, type_id: TypeDefId) -> impl Iterator<Item = FieldId> + 'a {
        self.registry.fields_on_type(type_id)
    }

    /// Get the type of a field
    pub fn field_type(&self, field_id: FieldId) -> TypeId {
        self.registry.get_field(field_id).ty
    }

    // =========================================================================
    // Method queries
    // =========================================================================

    /// Get a method definition by ID
    pub fn get_method(&self, method_id: MethodId) -> &'a MethodDef {
        self.registry.get_method(method_id)
    }

    /// Get the display name of a method
    pub fn method_display_name(&self, method_id: MethodId) -> String {
        let method = self.registry.get_method(method_id);
        self.name_table.borrow().display(method.name_id)
    }

    /// Find a method on a type by its short name
    #[must_use]
    pub fn find_method(&self, type_id: TypeDefId, name_id: NameId) -> Option<MethodId> {
        self.registry.find_method_on_type(type_id, name_id)
    }

    /// Resolve a method on a type, checking inherited methods too
    #[must_use]
    pub fn resolve_method(&self, type_id: TypeDefId, method_name: NameId) -> Option<MethodId> {
        self.registry.resolve_method(type_id, method_name)
    }

    /// Get the external binding for a method (if any)
    #[must_use]
    pub fn method_external_binding(&self, method_id: MethodId) -> Option<&'a ExternalMethodInfo> {
        self.registry.get_external_binding(method_id)
    }

    /// Look up a method NameId by Symbol (panics if not found)
    pub fn method_name_id(&self, name: Symbol) -> NameId {
        use vole_identity::NamerLookup;
        let name_table = self.name_table.borrow();
        let namer = NamerLookup::new(&name_table, self.interner);
        namer.method(name).unwrap_or_else(|| {
            panic!(
                "method name_id not found for '{}'",
                self.interner.resolve(name)
            )
        })
    }

    /// Look up a method NameId by Symbol, returning None if not found
    #[must_use]
    pub fn try_method_name_id(&self, name: Symbol) -> Option<NameId> {
        use vole_identity::NamerLookup;
        let name_table = self.name_table.borrow();
        let namer = NamerLookup::new(&name_table, self.interner);
        namer.method(name)
    }

    /// Look up a method NameId by string name (panics if not found)
    pub fn method_name_id_by_str(&self, name_str: &str) -> NameId {
        let name_table = self.name_table.borrow();
        vole_identity::method_name_id_by_str(&name_table, self.interner, name_str)
            .unwrap_or_else(|| panic!("method name_id not found for '{}'", name_str))
    }

    /// Look up a method NameId by string name, returning None if not found
    #[must_use]
    pub fn try_method_name_id_by_str(&self, name_str: &str) -> Option<NameId> {
        let name_table = self.name_table.borrow();
        vole_identity::method_name_id_by_str(&name_table, self.interner, name_str)
    }

    /// Look up a function NameId by Symbol (panics if not found)
    pub fn function_name_id(&self, module: ModuleId, name: Symbol) -> NameId {
        use vole_identity::NamerLookup;
        let name_table = self.name_table.borrow();
        let namer = NamerLookup::new(&name_table, self.interner);
        namer.function(module, name).unwrap_or_else(|| {
            panic!(
                "function name_id not found for '{}'",
                self.interner.resolve(name)
            )
        })
    }

    /// Look up a function NameId by Symbol, returning None if not found
    #[must_use]
    pub fn try_function_name_id(&self, module: ModuleId, name: Symbol) -> Option<NameId> {
        use vole_identity::NamerLookup;
        let name_table = self.name_table.borrow();
        let namer = NamerLookup::new(&name_table, self.interner);
        namer.function(module, name)
    }

    /// Get a function's return type from entity_registry
    #[must_use]
    pub fn function_return_type(&self, module: ModuleId, name: Symbol) -> Option<TypeId> {
        let name_id = self.try_function_name_id(module, name)?;
        let func_id = self.registry.function_by_name(name_id)?;
        let func_def = self.registry.get_function(func_id);
        Some(func_def.signature.return_type_id)
    }

    /// Get a function's default parameter expressions and required param count.
    /// Returns (required_params, param_defaults) where param_defaults[i] is Some
    /// if parameter i has a default value.
    #[must_use]
    pub fn function_param_defaults(
        &self,
        module: ModuleId,
        name: Symbol,
    ) -> Option<(usize, &[Option<Box<Expr>>])> {
        let name_id = self.try_function_name_id(module, name)?;
        let func_id = self.registry.function_by_name(name_id)?;
        let func_def = self.registry.get_function(func_id);
        Some((func_def.required_params, &func_def.param_defaults))
    }

    /// Get a function's default parameter expressions by NameId.
    /// Returns (required_params, param_defaults) where param_defaults[i] is Some
    /// if parameter i has a default value.
    #[must_use]
    pub fn function_param_defaults_by_name_id(
        &self,
        name_id: NameId,
    ) -> Option<(usize, &[Option<Box<Expr>>])> {
        let func_id = self.registry.function_by_name(name_id)?;
        let func_def = self.registry.get_function(func_id);
        Some((func_def.required_params, &func_def.param_defaults))
    }

    /// Get a method's return type from entity_registry
    #[must_use]
    pub fn method_return_type(&self, type_name: Symbol, method_name: Symbol) -> Option<TypeId> {
        use vole_identity::NamerLookup;
        let name_table = self.name_table.borrow();
        let namer = NamerLookup::new(&name_table, self.interner);
        let type_name_id = namer.function(self.main_module(), type_name)?;
        let type_def_id = self.registry.type_by_name(type_name_id)?;
        let method_name_id = self.method_name_id(method_name);
        let method_id = self
            .registry
            .find_method_on_type(type_def_id, method_name_id)?;
        let method_def = self.registry.get_method(method_id);
        // Get return type from arena via signature_id
        let arena = self.type_arena.borrow();
        let (_, ret, _) = arena.unwrap_function(method_def.signature_id)?;
        Some(ret)
    }

    /// Get a method's return type by TypeDefId and method NameId.
    /// More efficient for codegen which already has these IDs.
    #[must_use]
    pub fn method_return_type_by_id(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<TypeId> {
        let method_id = self
            .registry
            .find_method_on_type(type_def_id, method_name_id)?;
        let method_def = self.registry.get_method(method_id);
        let arena = self.type_arena.borrow();
        let (_, ret, _) = arena.unwrap_function(method_def.signature_id)?;
        Some(ret)
    }

    /// Get a static method's return type by TypeDefId and method NameId.
    #[must_use]
    pub fn static_method_return_type_by_id(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<TypeId> {
        let method_id = self
            .registry
            .find_static_method_on_type(type_def_id, method_name_id)?;
        let method_def = self.registry.get_method(method_id);
        let arena = self.type_arena.borrow();
        let (_, ret, _) = arena.unwrap_function(method_def.signature_id)?;
        Some(ret)
    }

    // =========================================================================
    // Well-known type checks
    // =========================================================================

    /// Check if a NameId refers to the Iterator interface
    #[must_use]
    pub fn is_iterator(&self, name_id: NameId) -> bool {
        let name_table = self.name_table.borrow();
        self.registry
            .type_by_name(name_id)
            .is_some_and(|id| name_table.well_known.is_iterator_type_def(id))
    }

    /// Check if a NameId refers to the Iterable interface
    #[must_use]
    pub fn is_iterable(&self, name_id: NameId) -> bool {
        let name_table = self.name_table.borrow();
        self.registry
            .type_by_name(name_id)
            .is_some_and(|id| name_table.well_known.is_iterable_type_def(id))
    }

    // =========================================================================
    // Monomorphization
    // =========================================================================

    /// Iterate over all monomorphized function instances
    pub fn monomorph_instances(
        &self,
    ) -> impl Iterator<Item = (&'a MonomorphKey, &'a MonomorphInstance)> {
        self.registry.monomorph_cache.instances()
    }

    /// Look up a specific monomorphized instance
    #[must_use]
    pub fn get_monomorph(&self, key: &MonomorphKey) -> Option<&'a MonomorphInstance> {
        self.registry.monomorph_cache.get(key)
    }

    /// Get the monomorph cache reference (for CompileCtx creation)
    pub fn monomorph_cache(&self) -> &'a MonomorphCache {
        &self.registry.monomorph_cache
    }

    // =========================================================================
    // External function lookups
    // =========================================================================

    /// Get external function info by name (for builtin calls)
    #[must_use]
    pub fn get_external_func(&self, name: &str) -> Option<&'a ExternalMethodInfo> {
        self.implement_registry.get_external_func(name)
    }

    // =========================================================================
    // Global variable lookups
    // =========================================================================

    /// Get a global variable definition by its NameId
    #[must_use]
    pub fn global(&self, name_id: NameId) -> Option<&'a GlobalDef> {
        let id = self.registry.global_by_name(name_id)?;
        Some(self.registry.get_global(id))
    }

    /// Get the type of a global variable by its NameId
    #[must_use]
    pub fn global_type(&self, name_id: NameId) -> Option<TypeId> {
        self.global(name_id).map(|g| g.type_id)
    }

    // =========================================================================
    // Escape hatches (for edge cases not covered by query methods)
    // =========================================================================

    /// Get direct access to the entity registry for advanced queries
    pub fn registry(&self) -> &'a EntityRegistry {
        self.registry
    }

    /// Get direct access to expression data for advanced queries
    pub fn expr_data(&self) -> &'a ExpressionData {
        self.expr_data
    }

    /// Get direct access to the name table Rc for advanced queries
    pub fn name_table_rc(&self) -> &'a Rc<RefCell<NameTable>> {
        self.name_table
    }

    /// Get direct access to the interner for advanced queries
    pub fn interner(&self) -> &'a Interner {
        self.interner
    }

    /// Get direct access to the implement registry for advanced queries
    pub fn implement_registry(&self) -> &'a ImplementRegistry {
        self.implement_registry
    }

    /// Get the type arena for direct type queries
    pub fn arena(&self) -> &'a Rc<RefCell<TypeArena>> {
        self.type_arena
    }

    // =========================================================================
    // Module programs
    // =========================================================================

    /// Get the paths of all imported module programs
    pub fn module_paths(&self) -> impl Iterator<Item = &'a str> {
        self.module_programs.keys().map(String::as_str)
    }

    /// Get a module program and its interner by path
    #[must_use]
    pub fn module_program(&self, path: &str) -> Option<(&'a Program, &'a Interner)> {
        self.module_programs
            .get(path)
            .map(|(prog, int)| (prog, int))
    }
}
