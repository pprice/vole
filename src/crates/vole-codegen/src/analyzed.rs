// analyzed.rs
//! Result of parsing and analyzing a source file.

use rustc_hash::FxHashMap;
use std::collections::HashSet;
use std::rc::Rc;

use crate::entity_view::EntityView;
use vole_frontend::{Interner, Program, Symbol};
use vole_identity::{
    FieldId, FunctionId, MethodId, ModuleId, NameId, NameTable, NamerLookup, Span, TypeDefId,
};
use vole_sema::lowering::{LowerVirProgramArgs, lower_vir_program};
use vole_sema::{AnalysisOutput, ImplementRegistry, NodeMap, TypeArena};
use vole_vir::{VirBody, VirEntityMetadata, VirFunction, VirProgram};

/// Result of parsing and analyzing a source file.
pub struct AnalyzedProgram {
    program: Program,
    interner: Rc<Interner>,
    /// All expression-level metadata (types, method resolutions, generic calls).
    /// Vec-backed per-node store, keyed by `NodeId`.
    node_map: NodeMap,
    /// Virtual module IDs for tests blocks. Maps tests block span to its virtual ModuleId.
    /// Keyed by Span (not NodeId), so stored separately from NodeId-keyed NodeMap.
    tests_virtual_modules: FxHashMap<Span, ModuleId>,
    /// Parsed module programs for compiling pure Vole functions
    module_programs: FxHashMap<String, (Program, Rc<Interner>)>,
    /// Type arena (Rc-shared, immutable during codegen).
    types: Rc<TypeArena>,
    /// Name table (Rc-shared, immutable during codegen).
    names: Rc<NameTable>,
    /// The module ID for the main program (may differ from main_module when using shared cache)
    module_id: ModuleId,
    /// Module paths that had sema errors. Codegen should skip compiling
    /// function bodies for these modules to avoid INVALID type IDs.
    modules_with_errors: HashSet<String>,
    /// All VIR data: functions, tests, global inits, type table, and lookup maps.
    ///
    /// This is the single entry point for all VIR data produced during lowering.
    /// Codegen accesses VIR through this struct rather than individual fields.
    vir_program: VirProgram,
    /// Codegen-local metadata view for implement-registry lookups.
    ///
    /// Populated once during `from_analysis`; all implement helpers read
    /// from this view instead of `Rc<ImplementRegistry>`.
    implement_view: ImplementView,
    /// Codegen-local metadata view for entity-registry lookups.
    ///
    /// Populated once during `from_analysis`; all entity helpers read
    /// from this view instead of `Rc<EntityRegistry>`.
    entity_view: EntityView,
}

/// Codegen-local external binding payload from implement-registry lookups.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ExternalMethodInfoRef {
    pub module_path: NameId,
    pub native_name: NameId,
}

impl From<vole_sema::implement_registry::ExternalMethodInfo> for ExternalMethodInfoRef {
    fn from(value: vole_sema::implement_registry::ExternalMethodInfo) -> Self {
        Self {
            module_path: value.module_path,
            native_name: value.native_name,
        }
    }
}

/// Codegen-local mapping kind for generic external dispatch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GenericTypeMappingKind {
    Exact(vole_sema::type_arena::TypeId),
    Default,
}

impl From<&vole_sema::implement_registry::TypeMappingKind> for GenericTypeMappingKind {
    fn from(value: &vole_sema::implement_registry::TypeMappingKind) -> Self {
        match value {
            vole_sema::implement_registry::TypeMappingKind::Exact(type_id) => Self::Exact(*type_id),
            vole_sema::implement_registry::TypeMappingKind::Default => Self::Default,
        }
    }
}

/// Codegen-local where-mapping entry for generic external dispatch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GenericTypeMappingEntry {
    pub kind: GenericTypeMappingKind,
    pub intrinsic_key: String,
}

impl From<&vole_sema::implement_registry::TypeMappingEntry> for GenericTypeMappingEntry {
    fn from(value: &vole_sema::implement_registry::TypeMappingEntry) -> Self {
        Self {
            kind: GenericTypeMappingKind::from(&value.kind),
            intrinsic_key: value.intrinsic_key.clone(),
        }
    }
}

/// Codegen-local generic external metadata payload.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GenericExternalInfoRef {
    pub module_path: NameId,
    pub type_mappings: Vec<GenericTypeMappingEntry>,
}

impl From<&vole_sema::implement_registry::GenericExternalInfo> for GenericExternalInfoRef {
    fn from(value: &vole_sema::implement_registry::GenericExternalInfo) -> Self {
        Self {
            module_path: value.module_path,
            type_mappings: value
                .type_mappings
                .iter()
                .map(GenericTypeMappingEntry::from)
                .collect(),
        }
    }
}

/// Codegen-local implement-method payload used by dispatch paths.
#[derive(Debug, Clone)]
pub(crate) struct MethodImplRef {
    pub func_type: vole_sema::types::FunctionType,
    pub external_info: Option<ExternalMethodInfoRef>,
}

impl From<&vole_sema::implement_registry::MethodImpl> for MethodImplRef {
    fn from(value: &vole_sema::implement_registry::MethodImpl) -> Self {
        Self {
            func_type: value.func_type.clone(),
            external_info: value.external_info.map(ExternalMethodInfoRef::from),
        }
    }
}

/// Codegen-local metadata view for implement-registry data.
///
/// Populated once during `from_analysis` from the sema `ImplementRegistry`.
/// All helpers on `AnalyzedProgram` that previously read `Rc<ImplementRegistry>`
/// now read from this view instead.
pub(crate) struct ImplementView {
    /// External function info by short name (e.g. "print").
    external_funcs: FxHashMap<String, ExternalMethodInfoRef>,
    /// Generic external function info by short name.
    generic_externals: FxHashMap<String, GenericExternalInfoRef>,
    /// Generic external method info by (defining type, method name).
    generic_external_methods: FxHashMap<(TypeDefId, NameId), GenericExternalInfoRef>,
    /// Implement-block method bindings by (type name key, method name).
    methods: FxHashMap<(NameId, NameId), MethodImplRef>,
}

impl ImplementView {
    /// Build a codegen-local view by materializing all entries from an `ImplementRegistry`.
    fn from_registry(registry: &ImplementRegistry) -> Self {
        use vole_sema::implement_registry::ImplTypeId;

        let external_funcs = registry
            .external_func_entries()
            .map(|(name, info)| (name.to_string(), ExternalMethodInfoRef::from(*info)))
            .collect();

        let generic_externals = registry
            .generic_external_entries()
            .map(|(name, info)| (name.to_string(), GenericExternalInfoRef::from(info)))
            .collect();

        let generic_external_methods = registry
            .generic_external_method_entries()
            .map(|(key, info)| {
                (
                    (key.type_def_id, key.method_name),
                    GenericExternalInfoRef::from(info),
                )
            })
            .collect();

        let methods = registry
            .method_entries()
            .map(|(key, method_impl)| {
                let type_name_id = ImplTypeId::name_id(key.type_id);
                (
                    (type_name_id, key.method_name),
                    MethodImplRef::from(method_impl),
                )
            })
            .collect();

        Self {
            external_funcs,
            generic_externals,
            generic_external_methods,
            methods,
        }
    }
}

/// Codegen-local method binding payload for per-type method dispatch.
#[derive(Debug, Clone)]
pub(crate) struct MethodBindingRef {
    pub func_type: vole_sema::types::FunctionType,
    pub external_info: Option<ExternalMethodInfoRef>,
}

impl From<&vole_sema::entity_defs::MethodBinding> for MethodBindingRef {
    fn from(value: &vole_sema::entity_defs::MethodBinding) -> Self {
        Self {
            func_type: value.func_type.clone(),
            external_info: value.external_info.map(ExternalMethodInfoRef::from),
        }
    }
}

impl AnalyzedProgram {
    /// Construct AnalyzedProgram from parsed program and analysis output.
    ///
    /// When the CompilationDb has a single owner (non-cached path), unwraps it
    /// directly. When shared (cached path, where module cache holds a reference),
    /// creates a CodegenDb that shares all data via Rc (O(1), zero cloning).
    pub fn from_analysis(program: Program, mut interner: Interner, output: AnalysisOutput) -> Self {
        let AnalysisOutput {
            node_map,
            tests_virtual_modules,
            module_programs,
            db: output_db,
            module_id,
            modules_with_errors,
            generic_vir_functions,
            generic_vir_type_table,
        } = output;

        let db = match Rc::try_unwrap(output_db) {
            // Non-cached path: sole owner, move data directly (zero-cost)
            Ok(compilation_db) => compilation_db.into_codegen(),
            // Cached path: share Rc-wrapped fields instead of cloning entire CompilationDb
            Err(rc) => rc.to_codegen_shared(),
        };
        let lowering_output = lower_vir_program(LowerVirProgramArgs {
            program: &program,
            interner: &mut interner,
            names: &db.names,
            entities: &db.entities,
            type_arena: &db.types,
            node_map: &node_map,
            tests_virtual_modules: &tests_virtual_modules,
            module_programs,
            module_id,
            modules_with_errors: &modules_with_errors,
            generic_vir_functions,
            generic_vir_type_table,
        });
        let module_programs = lowering_output.module_programs;
        let vir_program = lowering_output.vir_program;
        let implement_view = ImplementView::from_registry(&db.implements);
        let entity_view = EntityView::from_registry(&db.entities, &db.names);
        Self {
            program,
            interner: Rc::new(interner),
            node_map,
            tests_virtual_modules,
            module_programs,
            types: db.types,
            names: db.names,
            module_id,
            modules_with_errors,
            vir_program,
            implement_view,
            entity_view,
        }
    }

    /// Get read-only access to the name table
    pub(crate) fn name_table(&self) -> &NameTable {
        &self.names
    }

    /// Get read-only access to the analyzed root program AST.
    pub fn program(&self) -> &Program {
        &self.program
    }

    /// Get read-only access to the interner.
    pub(crate) fn interner(&self) -> &Interner {
        &self.interner
    }

    /// Clone the interner Rc for APIs that need shared ownership.
    pub(crate) fn interner_rc(&self) -> Rc<Interner> {
        Rc::clone(&self.interner)
    }

    /// Get read-only access to the node map.
    pub(crate) fn node_map(&self) -> &NodeMap {
        &self.node_map
    }

    /// Get the main/root module ID for this analyzed program.
    pub fn module_id(&self) -> ModuleId {
        self.module_id
    }

    /// Get read-only access to parsed module programs and their interners.
    pub fn module_programs(&self) -> &FxHashMap<String, (Program, Rc<Interner>)> {
        &self.module_programs
    }

    /// Get read-only access to module paths that had sema errors.
    pub(crate) fn modules_with_errors(&self) -> &HashSet<String> {
        &self.modules_with_errors
    }

    /// Get read-only access to the lowered VIR program.
    pub fn vir_program(&self) -> &VirProgram {
        &self.vir_program
    }

    /// Get read-only access to the VIR entity metadata.
    ///
    /// This is the VIR-native replacement for `EntityView` type/field/method
    /// queries.  Proxy methods on `AnalyzedProgram` are progressively
    /// migrated from `entity_view` to this accessor.
    fn entity_metadata(&self) -> &VirEntityMetadata {
        self.vir_program.entity_metadata()
    }

    /// Get a reference to the name table Rc (borrowed, no clone)
    pub(crate) fn name_table_ref(&self) -> &Rc<NameTable> {
        &self.names
    }

    /// Get read-only access to the type arena
    pub(crate) fn type_arena(&self) -> &TypeArena {
        &self.types
    }

    /// Resolve the EntityRegistry NameId used for all array implement dispatch.
    pub(crate) fn array_type_name_id(&self) -> Option<NameId> {
        self.entity_view.array_name_id()
    }

    /// Resolve a type's canonical entity NameId from its TypeDefId.
    pub(crate) fn entity_type_name_id(&self, type_def_id: TypeDefId) -> NameId {
        self.entity_metadata()
            .type_name_id(type_def_id)
            .unwrap_or_else(|| {
                panic!(
                    "entity_type_name_id: type def {:?} not in VirEntityMetadata",
                    type_def_id
                )
            })
    }

    /// Resolve a sema TypeDef by ID.
    pub(crate) fn type_def(&self, type_def_id: TypeDefId) -> &vole_sema::entity_defs::TypeDef {
        self.entity_view.get_type(type_def_id)
    }

    /// Query-compatible alias for resolving a sema TypeDef by ID.
    pub(crate) fn get_type(&self, type_def_id: TypeDefId) -> &vole_sema::entity_defs::TypeDef {
        self.type_def(type_def_id)
    }

    /// Resolve a sema FieldDef by ID.
    pub(crate) fn field_def(&self, field_id: FieldId) -> &vole_sema::entity_defs::FieldDef {
        self.entity_view.get_field(field_id)
    }

    /// Query-compatible alias for resolving a sema FieldDef by ID.
    pub(crate) fn get_field(&self, field_id: FieldId) -> &vole_sema::entity_defs::FieldDef {
        self.field_def(field_id)
    }

    /// Resolve a sema FunctionDef by ID.
    pub(crate) fn function_def(
        &self,
        function_id: FunctionId,
    ) -> &vole_sema::entity_defs::FunctionDef {
        self.entity_view.get_function(function_id)
    }

    /// Query-compatible alias for resolving a sema FunctionDef by ID.
    pub(crate) fn get_function(
        &self,
        function_id: FunctionId,
    ) -> &vole_sema::entity_defs::FunctionDef {
        self.function_def(function_id)
    }

    /// Resolve a sema MethodDef by ID.
    pub(crate) fn method_def(&self, method_id: MethodId) -> &vole_sema::entity_defs::MethodDef {
        self.entity_view.get_method(method_id)
    }

    /// Query-compatible alias for resolving a sema MethodDef by ID.
    pub(crate) fn get_method(&self, method_id: MethodId) -> &vole_sema::entity_defs::MethodDef {
        self.method_def(method_id)
    }

    /// Return the sema signature TypeId for a method.
    pub(crate) fn method_signature_id(&self, method_id: MethodId) -> vole_sema::type_arena::TypeId {
        self.entity_view.get_method(method_id).signature_id
    }

    /// Return all field IDs declared on a type definition.
    pub(crate) fn fields_on_type(
        &self,
        type_def_id: TypeDefId,
    ) -> impl Iterator<Item = FieldId> + '_ {
        self.entity_metadata()
            .fields_on_type(type_def_id)
            .unwrap_or(&[])
            .iter()
            .copied()
    }

    /// Return true when a global is present for the given NameId.
    pub(crate) fn has_global(&self, name_id: NameId) -> bool {
        self.entity_view.global_by_name(name_id).is_some()
    }

    /// Resolve a NameId to display form (e.g. module::Type::method).
    pub(crate) fn display_name(&self, name_id: NameId) -> String {
        self.names.display(name_id)
    }

    /// Resolve a symbol in the main-program interner.
    pub(crate) fn resolve_symbol(&self, sym: Symbol) -> &str {
        self.interner.resolve(sym)
    }

    /// Resolve a NameId to its last segment.
    pub(crate) fn last_segment(&self, name_id: NameId) -> Option<String> {
        self.names.last_segment_str(name_id)
    }

    /// Resolve type definition by NameId.
    pub(crate) fn try_type_def_id(&self, name_id: NameId) -> Option<TypeDefId> {
        self.entity_view.type_by_name(name_id)
    }

    /// Resolve method NameId by Symbol.
    pub(crate) fn try_method_name_id(&self, name: Symbol) -> Option<NameId> {
        let namer = NamerLookup::new(self.name_table(), self.interner());
        namer.method(name)
    }

    /// Resolve method NameId by short string.
    pub(crate) fn try_method_name_id_by_str(&self, name_str: &str) -> Option<NameId> {
        vole_identity::method_name_id_by_str(self.name_table(), self.interner(), name_str)
    }

    /// Resolve NameId by module and symbol segments using the main interner.
    pub(crate) fn try_name_id(&self, module_id: ModuleId, segments: &[Symbol]) -> Option<NameId> {
        self.names.name_id(module_id, segments, self.interner())
    }

    /// Query-compatible alias for resolving NameId by module and symbol segments.
    pub(crate) fn name_id(&self, module_id: ModuleId, segments: &[Symbol]) -> NameId {
        self.try_name_id(module_id, segments).unwrap_or_else(|| {
            panic!(
                "name_id not found for segments {:?} in {:?}",
                segments, module_id
            )
        })
    }

    /// Resolve NameId by module and symbol segments with an explicit interner.
    pub(crate) fn try_name_id_with_interner(
        &self,
        module_id: ModuleId,
        segments: &[Symbol],
        interner: &Interner,
    ) -> Option<NameId> {
        self.names.name_id(module_id, segments, interner)
    }

    /// Resolve method NameId by short string, panicking when missing.
    pub(crate) fn method_name_id_by_str(&self, name_str: &str) -> NameId {
        self.try_method_name_id_by_str(name_str)
            .unwrap_or_else(|| panic!("method name_id not found for '{}'", name_str))
    }

    /// Resolve function NameId by module and Symbol.
    pub(crate) fn try_function_name_id(&self, module_id: ModuleId, name: Symbol) -> Option<NameId> {
        let namer = NamerLookup::new(self.name_table(), self.interner());
        namer.function(module_id, name)
    }

    /// Resolve semantic FunctionId by NameId.
    pub(crate) fn function_id_by_name_id(&self, name_id: NameId) -> Option<FunctionId> {
        self.entity_view.function_by_name(name_id)
    }

    /// Resolve semantic FunctionId by module and Symbol.
    pub(crate) fn function_id(&self, module_id: ModuleId, name: Symbol) -> Option<FunctionId> {
        let name_id = self.try_function_name_id(module_id, name)?;
        self.function_id_by_name_id(name_id)
    }

    /// Resolve a string type name in a module context.
    pub(crate) fn resolve_type_def_by_str(
        &self,
        module_id: ModuleId,
        name: &str,
    ) -> Option<TypeDefId> {
        self.entity_view.resolve_type_def_by_str(
            self.interner(),
            self.name_table(),
            module_id,
            name,
        )
    }

    /// Return sentinel base type for a sentinel TypeDef, when present.
    pub(crate) fn sentinel_base_type(
        &self,
        type_def_id: TypeDefId,
    ) -> Option<vole_sema::type_arena::TypeId> {
        self.entity_view.get_type(type_def_id).base_type_id
    }

    /// Return whether a type definition is a sentinel.
    pub(crate) fn is_sentinel_type(&self, type_def_id: TypeDefId) -> bool {
        self.entity_type_is_sentinel(type_def_id)
    }

    /// Return whether a type definition is an interface.
    pub(crate) fn is_interface_type(&self, type_def_id: TypeDefId) -> bool {
        self.entity_metadata()
            .type_def_kind(type_def_id)
            .is_some_and(|k| k.is_interface())
    }

    /// Return interface method binding return type, when a binding exists.
    pub(crate) fn method_binding_return_type(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<vole_sema::type_arena::TypeId> {
        self.entity_view
            .find_method_binding(type_def_id, method_name_id)
            .map(|binding| binding.func_type.return_type_id)
    }

    /// Return interface method binding metadata, when a binding exists.
    pub(crate) fn method_binding(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodBindingRef> {
        self.entity_view
            .find_method_binding(type_def_id, method_name_id)
            .map(MethodBindingRef::from)
    }

    /// Find a method on a type by method NameId.
    pub(crate) fn find_method(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId> {
        self.entity_metadata()
            .find_method_on_type(type_def_id, method_name_id)
    }

    /// Return direct method IDs declared on a type definition.
    pub(crate) fn type_methods(&self, type_def_id: TypeDefId) -> Vec<MethodId> {
        self.entity_metadata()
            .methods_on_type(type_def_id)
            .map(|s| s.to_vec())
            .unwrap_or_default()
    }

    /// Build interface type-parameter substitutions for a concrete implementation.
    pub(crate) fn interface_impl_type_param_subs(
        &self,
        implementing_type_id: TypeDefId,
        interface_id: TypeDefId,
    ) -> FxHashMap<NameId, vole_sema::type_arena::TypeId> {
        let type_params = self.entity_type_params(interface_id);
        let type_args = self
            .entity_view
            .implementation_type_args(implementing_type_id, interface_id);
        type_params
            .into_iter()
            .zip(type_args.iter().copied())
            .collect()
    }

    /// Find a static method on a type by method NameId.
    pub(crate) fn find_static_method(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId> {
        self.entity_metadata()
            .find_static_method_on_type(type_def_id, method_name_id)
    }

    /// Get the full NameId for a semantic method.
    pub(crate) fn method_full_name(&self, method_id: MethodId) -> NameId {
        self.entity_metadata()
            .method_full_name_id(method_id)
            .unwrap_or_else(|| {
                panic!(
                    "method_full_name: method {:?} not in VirEntityMetadata",
                    method_id
                )
            })
    }

    /// Return all interfaces implemented by a type definition.
    pub(crate) fn implemented_interfaces(&self, type_def_id: TypeDefId) -> Vec<TypeDefId> {
        self.entity_metadata().implemented_interfaces(type_def_id)
    }

    /// Return external binding metadata for a method, when available.
    pub(crate) fn method_external_binding(
        &self,
        method_id: MethodId,
    ) -> Option<ExternalMethodInfoRef> {
        self.entity_view.method_external_binding(method_id)
    }

    /// Return true when all methods on a type are external-only.
    pub(crate) fn is_external_only(&self, type_def_id: TypeDefId) -> bool {
        self.entity_view.is_external_only(type_def_id)
    }

    /// Return resolved method metadata for a call node.
    pub(crate) fn method_at(
        &self,
        node_id: vole_identity::NodeId,
    ) -> Option<&vole_sema::ResolvedMethod> {
        self.node_map.get_method(node_id)
    }

    /// Return monomorph key metadata for a call node.
    pub(crate) fn monomorph_for(
        &self,
        node_id: vole_identity::NodeId,
    ) -> Option<&vole_sema::generic::MonomorphKey> {
        self.node_map.get_generic(node_id)
    }

    /// Return static-method monomorph key metadata for a call node.
    pub(crate) fn static_method_generic_at(
        &self,
        node_id: vole_identity::NodeId,
    ) -> Option<&vole_sema::generic::StaticMethodMonomorphKey> {
        self.node_map.get_static_method_generic(node_id)
    }

    /// Return the single abstract method for functional interfaces.
    pub(crate) fn is_functional_interface(&self, type_def_id: TypeDefId) -> Option<MethodId> {
        self.entity_metadata().is_functional(type_def_id)
    }

    /// Resolve virtual module ID for a tests block span.
    pub(crate) fn tests_virtual_module(&self, span: Span) -> Option<ModuleId> {
        self.tests_virtual_modules.get(&span).copied()
    }

    /// Resolve function NameId by module and Symbol, panicking when missing.
    pub(crate) fn function_name_id(&self, module_id: ModuleId, name: Symbol) -> NameId {
        self.try_function_name_id(module_id, name)
            .unwrap_or_else(|| {
                panic!(
                    "function name_id not found for '{}'",
                    self.resolve_symbol(name)
                )
            })
    }

    /// Return function parameter TypeIds by FunctionId.
    pub(crate) fn function_param_type_ids(
        &self,
        func_id: FunctionId,
    ) -> Vec<vole_sema::type_arena::TypeId> {
        self.entity_view
            .get_function(func_id)
            .signature
            .params_id
            .to_vec()
    }

    /// Return global declared TypeId by NameId.
    pub(crate) fn global_type_id(&self, name_id: NameId) -> Option<vole_sema::type_arena::TypeId> {
        let global_id = self.entity_view.global_by_name(name_id)?;
        Some(self.entity_view.get_global(global_id).type_id)
    }

    /// Return module ID for a path, falling back to main module.
    pub(crate) fn module_id_or_main(&self, path: &str) -> ModuleId {
        self.names
            .module_id_if_known(path)
            .unwrap_or_else(|| self.names.main_module())
    }

    /// Return module ID when known for a path.
    pub(crate) fn module_id_if_known(&self, path: &str) -> Option<ModuleId> {
        self.names.module_id_if_known(path)
    }

    /// Return known imported module paths.
    pub(crate) fn module_paths(&self) -> Vec<String> {
        self.module_programs.keys().cloned().collect()
    }

    /// Return whether a function parameter has a default expression.
    pub(crate) fn has_function_default_expr(&self, func_id: FunctionId, param_idx: usize) -> bool {
        self.entity_view
            .get_function(func_id)
            .param_defaults
            .get(param_idx)
            .is_some_and(|opt| opt.is_some())
    }

    /// Return whether a method parameter has a default expression.
    pub(crate) fn has_method_default_expr(&self, method_id: MethodId, param_idx: usize) -> bool {
        self.entity_view
            .get_method(method_id)
            .param_defaults
            .get(param_idx)
            .is_some_and(|opt| opt.is_some())
    }

    /// Return imported-module interner for a module ID, when available.
    pub(crate) fn module_interner(&self, module_id: ModuleId) -> Option<&Interner> {
        let module_path = self.names.module_path(module_id);
        self.module_programs
            .get(module_path)
            .map(|(_, interner)| &**interner)
    }

    /// Return whether a type definition is marked as an annotation type.
    pub(crate) fn type_is_annotation(&self, type_def_id: TypeDefId) -> bool {
        self.entity_metadata().is_annotation(type_def_id)
    }

    /// Return interface method IDs in deterministic slot order.
    pub(crate) fn interface_method_ids_ordered(
        &self,
        interface_type_def_id: TypeDefId,
    ) -> Vec<MethodId> {
        self.entity_metadata()
            .interface_methods_ordered(interface_type_def_id)
    }

    /// Return all field IDs declared on a type definition.
    pub(crate) fn entity_field_ids_on_type(&self, type_def_id: TypeDefId) -> Vec<FieldId> {
        self.entity_metadata()
            .fields_on_type(type_def_id)
            .map(|s| s.to_vec())
            .unwrap_or_default()
    }

    /// Return the semantic field type for a field ID.
    pub(crate) fn entity_field_type(&self, field_id: FieldId) -> vole_sema::type_arena::TypeId {
        self.entity_view.get_field(field_id).ty
    }

    /// Return declared type parameter NameIds for a type definition.
    pub(crate) fn entity_type_params(&self, type_def_id: TypeDefId) -> Vec<NameId> {
        self.entity_metadata()
            .type_params(type_def_id)
            .map(|s| s.to_vec())
            .unwrap_or_default()
    }

    /// Return generic field types metadata for a type definition, if present.
    pub(crate) fn entity_generic_field_types(
        &self,
        type_def_id: TypeDefId,
    ) -> Option<Vec<vole_sema::type_arena::TypeId>> {
        self.entity_view
            .get_type(type_def_id)
            .generic_info
            .as_ref()
            .map(|g| g.field_types.clone())
    }

    /// Return whether a type definition is a sentinel type.
    pub(crate) fn entity_type_is_sentinel(&self, type_def_id: TypeDefId) -> bool {
        self.entity_metadata()
            .type_def_kind(type_def_id)
            .is_some_and(|k| k.is_sentinel())
    }

    /// Find a type by its short (last-segment) name in the entity view.
    pub(crate) fn type_by_short_name(&self, short_name: &str) -> Option<TypeDefId> {
        self.entity_view.type_by_short_name(short_name)
    }

    /// Look up external function binding metadata by short function name.
    pub(crate) fn external_func_by_name(&self, name: &str) -> Option<ExternalMethodInfoRef> {
        self.implement_view.external_funcs.get(name).copied()
    }

    /// Look up generic external function metadata by short function name.
    pub(crate) fn generic_external_by_name(&self, name: &str) -> Option<GenericExternalInfoRef> {
        self.implement_view.generic_externals.get(name).cloned()
    }

    /// Look up generic external method metadata by defining type and method name.
    pub(crate) fn generic_external_method(
        &self,
        type_def_id: TypeDefId,
        method_name: NameId,
    ) -> Option<GenericExternalInfoRef> {
        self.implement_view
            .generic_external_methods
            .get(&(type_def_id, method_name))
            .cloned()
    }

    /// Get the free-function monomorph cache.
    pub(crate) fn monomorph_cache(&self) -> &vole_sema::generic::MonomorphCache {
        self.entity_view.monomorph_cache()
    }

    /// Get the class-method monomorph cache.
    pub(crate) fn class_method_monomorph_cache(
        &self,
    ) -> &vole_sema::generic::ClassMethodMonomorphCache {
        self.entity_view.class_method_monomorph_cache()
    }

    /// Get the static-method monomorph cache.
    pub(crate) fn static_method_monomorph_cache(
        &self,
    ) -> &vole_sema::generic::StaticMethodMonomorphCache {
        self.entity_view.static_method_monomorph_cache()
    }

    /// Render a short human-readable type name for diagnostics/debug output.
    pub(crate) fn display_type_id_short(&self, type_id: vole_sema::type_arena::TypeId) -> String {
        vole_sema::type_display::display_type_id_short(
            type_id,
            self.type_arena(),
            self.name_table(),
            &self.entity_view,
        )
    }

    /// Resolve the implement-registry type key NameId for a concrete sema TypeId.
    pub(crate) fn impl_type_name_id_from_type_id(
        &self,
        type_id: vole_sema::type_arena::TypeId,
    ) -> Option<NameId> {
        self.entity_view
            .impl_type_name_id_from_type_id(type_id, self.type_arena())
    }

    /// Look up an implement-registry method by concrete type-name key.
    pub(crate) fn implement_method_by_name(
        &self,
        type_name_id: NameId,
        method_name_id: NameId,
    ) -> Option<MethodImplRef> {
        self.implement_view
            .methods
            .get(&(type_name_id, method_name_id))
            .cloned()
    }

    /// Resolve and look up an implement-registry method from a sema TypeId.
    pub(crate) fn implement_method_for_type(
        &self,
        type_id: vole_sema::type_arena::TypeId,
        method_name_id: NameId,
    ) -> Option<(NameId, MethodImplRef)> {
        let type_name_id = self.impl_type_name_id_from_type_id(type_id)?;
        let method_impl = self.implement_method_by_name(type_name_id, method_name_id)?;
        Some((type_name_id, method_impl))
    }

    /// Look up a VIR function by its monomorphized mangled NameId.
    /// Returns `None` if no VIR function was lowered for this instance.
    pub(crate) fn get_vir_monomorph(&self, mangled_name_id: NameId) -> Option<&VirFunction> {
        self.vir_program.get_monomorph(mangled_name_id)
    }

    /// Look up a VIR function by its semantic FunctionId.
    /// Returns `None` if no VIR function was lowered for this function.
    pub(crate) fn get_vir_function(&self, func_id: FunctionId) -> Option<&VirFunction> {
        self.vir_program.get_function(func_id)
    }

    /// Look up a VIR function by its semantic MethodId.
    /// Returns `None` if no VIR function was lowered for this method.
    pub(crate) fn get_vir_method(&self, method_id: MethodId) -> Option<&VirFunction> {
        self.vir_program.get_method(method_id)
    }

    /// Return whether a VIR function belongs to the given module.
    pub fn vir_function_in_module(&self, func: &VirFunction, module_id: ModuleId) -> bool {
        if let Some(method_id) = func.method_id {
            let method_def = self.get_method(method_id);
            self.get_type(method_def.defining_type).module == module_id
        } else {
            self.get_function(func.id).module == module_id
        }
    }

    /// Look up a VIR test body by the test case's span.
    /// Returns `None` if no VIR body was lowered for this test.
    pub(crate) fn get_vir_test(&self, span: Span) -> Option<&VirBody> {
        self.vir_program.get_test(span)
    }
}
