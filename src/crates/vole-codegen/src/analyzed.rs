// analyzed.rs
//! Result of parsing and analyzing a source file.

use rustc_hash::FxHashMap;
use std::collections::HashSet;
use std::rc::Rc;

use crate::analyzed_lowering_facade::{LowerVirProgramArgs, lower_vir_program};
use crate::analyzed_lowering_lookup::LoweringEntityLookup;
use vole_frontend::{Decl, Interner, Program, Symbol};
use vole_identity::{
    FieldId, FunctionId, MethodId, ModuleId, NameId, NameTable, NamerLookup, Span, TypeDefId,
};
use vole_sema::{AnalysisOutput, EntityRegistry, ImplementRegistry, NodeMap, TypeArena};
use vole_vir::type_table::VirTypeTable;
use vole_vir::{VirBody, VirFunction, VirProgram, VirTest};

use vole_sema::vir_lower::{lower_stmts, lower_test_body};

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
    /// Entity registry (Rc-shared, immutable during codegen).
    entities: Rc<EntityRegistry>,
    /// Implement registry (Rc-shared, immutable during codegen).
    implements: Rc<ImplementRegistry>,
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
        Self {
            program,
            interner: Rc::new(interner),
            node_map,
            tests_virtual_modules,
            module_programs,
            types: db.types,
            entities: db.entities,
            implements: db.implements,
            names: db.names,
            module_id,
            modules_with_errors,
            vir_program,
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
        self.entities.array_name_id()
    }

    /// Resolve a type's canonical entity NameId from its TypeDefId.
    pub(crate) fn entity_type_name_id(&self, type_def_id: TypeDefId) -> NameId {
        self.entities.name_id(type_def_id)
    }

    /// Resolve a sema TypeDef by ID.
    pub(crate) fn type_def(&self, type_def_id: TypeDefId) -> &vole_sema::entity_defs::TypeDef {
        self.entities.get_type(type_def_id)
    }

    /// Query-compatible alias for resolving a sema TypeDef by ID.
    pub(crate) fn get_type(&self, type_def_id: TypeDefId) -> &vole_sema::entity_defs::TypeDef {
        self.type_def(type_def_id)
    }

    /// Resolve a sema FieldDef by ID.
    pub(crate) fn field_def(&self, field_id: FieldId) -> &vole_sema::entity_defs::FieldDef {
        self.entities.get_field(field_id)
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
        self.entities.get_function(function_id)
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
        self.entities.get_method(method_id)
    }

    /// Query-compatible alias for resolving a sema MethodDef by ID.
    pub(crate) fn get_method(&self, method_id: MethodId) -> &vole_sema::entity_defs::MethodDef {
        self.method_def(method_id)
    }

    /// Return the sema signature TypeId for a method.
    pub(crate) fn method_signature_id(&self, method_id: MethodId) -> vole_sema::type_arena::TypeId {
        self.entities.get_method(method_id).signature_id
    }

    /// Return all field IDs declared on a type definition.
    pub(crate) fn fields_on_type(
        &self,
        type_def_id: TypeDefId,
    ) -> impl Iterator<Item = FieldId> + '_ {
        self.entities.fields_on_type(type_def_id)
    }

    /// Return true when a global is present for the given NameId.
    pub(crate) fn has_global(&self, name_id: NameId) -> bool {
        self.entities.global_by_name(name_id).is_some()
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
        self.entities.type_by_name(name_id)
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
        self.entities.function_by_name(name_id)
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
        vole_sema::query::resolve_type_def_by_str(
            self.interner(),
            self.name_table(),
            &self.entities,
            module_id,
            name,
        )
    }

    /// Return sentinel base type for a sentinel TypeDef, when present.
    pub(crate) fn sentinel_base_type(
        &self,
        type_def_id: TypeDefId,
    ) -> Option<vole_sema::type_arena::TypeId> {
        self.entities.get_type(type_def_id).base_type_id
    }

    /// Return whether a type definition is a sentinel.
    pub(crate) fn is_sentinel_type(&self, type_def_id: TypeDefId) -> bool {
        self.entity_type_is_sentinel(type_def_id)
    }

    /// Return whether a type definition is a struct (not class/interface/sentinel).
    pub(crate) fn is_struct_type(&self, type_def_id: TypeDefId) -> bool {
        self.entities.get_type(type_def_id).kind == vole_sema::entity_defs::TypeDefKind::Struct
    }

    /// Return whether a type definition is an interface.
    pub(crate) fn is_interface_type(&self, type_def_id: TypeDefId) -> bool {
        self.entities.get_type(type_def_id).kind == vole_sema::entity_defs::TypeDefKind::Interface
    }

    /// Return whether a type definition is an alias.
    pub(crate) fn is_alias_type(&self, type_def_id: TypeDefId) -> bool {
        self.entities.get_type(type_def_id).kind == vole_sema::entity_defs::TypeDefKind::Alias
    }

    /// Return aliased arena TypeId for alias types.
    pub(crate) fn aliased_type(
        &self,
        type_def_id: TypeDefId,
    ) -> Option<vole_sema::type_arena::TypeId> {
        self.entities.get_type(type_def_id).aliased_type
    }

    /// Return whether a type definition is an error type.
    pub(crate) fn is_error_type(&self, type_def_id: TypeDefId) -> bool {
        self.entities.get_type(type_def_id).kind == vole_sema::entity_defs::TypeDefKind::ErrorType
    }

    /// Return whether an error type has additional error_info payload.
    pub(crate) fn is_error_type_with_info(&self, type_def_id: TypeDefId) -> bool {
        let type_def = self.entities.get_type(type_def_id);
        type_def.kind == vole_sema::entity_defs::TypeDefKind::ErrorType
            && type_def.error_info.is_some()
    }

    /// Return interface method binding return type, when a binding exists.
    pub(crate) fn method_binding_return_type(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<vole_sema::type_arena::TypeId> {
        self.entities
            .find_method_binding(type_def_id, method_name_id)
            .map(|binding| binding.func_type.return_type_id)
    }

    /// Return interface method binding metadata, when a binding exists.
    pub(crate) fn method_binding(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodBindingRef> {
        self.entities
            .find_method_binding(type_def_id, method_name_id)
            .map(MethodBindingRef::from)
    }

    /// Find a method on a type by method NameId.
    pub(crate) fn find_method(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId> {
        self.entities
            .find_method_on_type(type_def_id, method_name_id)
    }

    /// Return direct method IDs declared on a type definition.
    pub(crate) fn type_methods(&self, type_def_id: TypeDefId) -> Vec<MethodId> {
        self.entities.methods_on_type(type_def_id)
    }

    /// Build interface type-parameter substitutions for a concrete implementation.
    pub(crate) fn interface_impl_type_param_subs(
        &self,
        implementing_type_id: TypeDefId,
        interface_id: TypeDefId,
    ) -> FxHashMap<NameId, vole_sema::type_arena::TypeId> {
        let type_params = self.entities.type_params(interface_id);
        let type_args = self
            .entities
            .get_implementation_type_args(implementing_type_id, interface_id);
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
        self.entities
            .find_static_method_on_type(type_def_id, method_name_id)
    }

    /// Get the full NameId for a semantic method.
    pub(crate) fn method_full_name(&self, method_id: MethodId) -> NameId {
        self.entities.method_full_name(method_id)
    }

    /// Return all interfaces implemented by a type definition.
    pub(crate) fn implemented_interfaces(&self, type_def_id: TypeDefId) -> Vec<TypeDefId> {
        self.entities.get_implemented_interfaces(type_def_id)
    }

    /// Return external binding metadata for a method, when available.
    pub(crate) fn method_external_binding(
        &self,
        method_id: MethodId,
    ) -> Option<ExternalMethodInfoRef> {
        self.entities
            .get_external_binding(method_id)
            .map(|info| ExternalMethodInfoRef {
                module_path: info.module_path,
                native_name: info.native_name,
            })
    }

    /// Return true when all methods on a type are external-only.
    pub(crate) fn is_external_only(&self, type_def_id: TypeDefId) -> bool {
        self.entities.is_external_only(type_def_id)
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

    /// Return class-method monomorph key metadata for a call node.
    pub(crate) fn class_method_generic_at(
        &self,
        node_id: vole_identity::NodeId,
    ) -> Option<&vole_sema::generic::ClassMethodMonomorphKey> {
        self.node_map.get_class_method_generic(node_id)
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
        self.entities.is_functional(type_def_id)
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
        self.entities
            .get_function(func_id)
            .signature
            .params_id
            .to_vec()
    }

    /// Return global declared TypeId by NameId.
    pub(crate) fn global_type_id(&self, name_id: NameId) -> Option<vole_sema::type_arena::TypeId> {
        let global_id = self.entities.global_by_name(name_id)?;
        Some(self.entities.get_global(global_id).type_id)
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
        self.entities
            .function_default_expr(func_id, param_idx)
            .is_some()
    }

    /// Return whether a method parameter has a default expression.
    pub(crate) fn has_method_default_expr(&self, method_id: MethodId, param_idx: usize) -> bool {
        self.entities
            .method_default_expr(method_id, param_idx)
            .is_some()
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
        self.entities.get_type(type_def_id).is_annotation
    }

    /// Return interface method IDs in deterministic slot order.
    pub(crate) fn interface_method_ids_ordered(
        &self,
        interface_type_def_id: TypeDefId,
    ) -> Vec<MethodId> {
        self.entities
            .interface_methods_ordered(interface_type_def_id)
    }

    /// Return all field IDs declared on a type definition.
    pub(crate) fn entity_field_ids_on_type(&self, type_def_id: TypeDefId) -> Vec<FieldId> {
        self.entities.fields_on_type(type_def_id).collect()
    }

    /// Return the semantic field type for a field ID.
    pub(crate) fn entity_field_type(&self, field_id: FieldId) -> vole_sema::type_arena::TypeId {
        self.entities.get_field(field_id).ty
    }

    /// Return declared type parameter NameIds for a type definition.
    pub(crate) fn entity_type_params(&self, type_def_id: TypeDefId) -> Vec<NameId> {
        self.entities.type_params(type_def_id)
    }

    /// Return generic field types metadata for a type definition, if present.
    pub(crate) fn entity_generic_field_types(
        &self,
        type_def_id: TypeDefId,
    ) -> Option<Vec<vole_sema::type_arena::TypeId>> {
        self.entities
            .get_type(type_def_id)
            .generic_info
            .as_ref()
            .map(|g| g.field_types.clone())
    }

    /// Return whether a type definition is a sentinel type.
    pub(crate) fn entity_type_is_sentinel(&self, type_def_id: TypeDefId) -> bool {
        self.entities.get_type(type_def_id).kind.is_sentinel()
    }

    /// Find a type by its short (last-segment) name in the entity registry.
    pub(crate) fn type_by_short_name(&self, short_name: &str) -> Option<TypeDefId> {
        self.entities
            .type_by_short_name(short_name, self.name_table())
    }

    /// Look up external function binding metadata by short function name.
    pub(crate) fn external_func_by_name(&self, name: &str) -> Option<ExternalMethodInfoRef> {
        self.implements
            .get_external_func(name)
            .copied()
            .map(ExternalMethodInfoRef::from)
    }

    /// Look up generic external function metadata by short function name.
    pub(crate) fn generic_external_by_name(&self, name: &str) -> Option<GenericExternalInfoRef> {
        self.implements
            .get_generic_external(name)
            .map(GenericExternalInfoRef::from)
    }

    /// Look up generic external method metadata by defining type and method name.
    pub(crate) fn generic_external_method(
        &self,
        type_def_id: TypeDefId,
        method_name: NameId,
    ) -> Option<GenericExternalInfoRef> {
        self.implements
            .get_generic_external_method(type_def_id, method_name)
            .map(GenericExternalInfoRef::from)
    }

    /// Get the free-function monomorph cache.
    pub(crate) fn monomorph_cache(&self) -> &vole_sema::generic::MonomorphCache {
        &self.entities.monomorph_cache
    }

    /// Get the class-method monomorph cache.
    pub(crate) fn class_method_monomorph_cache(
        &self,
    ) -> &vole_sema::generic::ClassMethodMonomorphCache {
        &self.entities.class_method_monomorph_cache
    }

    /// Get the static-method monomorph cache.
    pub(crate) fn static_method_monomorph_cache(
        &self,
    ) -> &vole_sema::generic::StaticMethodMonomorphCache {
        &self.entities.static_method_monomorph_cache
    }

    /// Render a short human-readable type name for diagnostics/debug output.
    pub(crate) fn display_type_id_short(&self, type_id: vole_sema::type_arena::TypeId) -> String {
        vole_sema::type_display::display_type_id_short(
            type_id,
            self.type_arena(),
            self.name_table(),
            &self.entities,
        )
    }

    /// Resolve the implement-registry type key NameId for a concrete sema TypeId.
    pub(crate) fn impl_type_name_id_from_type_id(
        &self,
        type_id: vole_sema::type_arena::TypeId,
    ) -> Option<NameId> {
        ImplementRegistry::type_name_id_for_type(type_id, self.type_arena(), &self.entities)
    }

    /// Look up an implement-registry method by concrete type-name key.
    pub(crate) fn implement_method_by_name(
        &self,
        type_name_id: NameId,
        method_name_id: NameId,
    ) -> Option<MethodImplRef> {
        self.implements
            .get_method_by_name(type_name_id, method_name_id)
            .map(MethodImplRef::from)
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

/// Build a lookup map from monomorphized mangled NameId to VirFunction index.
///
/// Only includes VIR functions that have a `mangled_name_id` set (i.e.,
/// monomorphized instances).  Non-generic functions are not indexed here
/// because they are compiled via the normal (non-monomorph) path.
pub(crate) fn build_vir_monomorph_map(vir_functions: &[VirFunction]) -> FxHashMap<NameId, usize> {
    let mut map = FxHashMap::default();
    for (idx, vf) in vir_functions.iter().enumerate() {
        if let Some(name_id) = vf.mangled_name_id {
            map.insert(name_id, idx);
        }
    }
    map
}

/// Build a lookup map from semantic FunctionId to VirFunction index.
///
/// Only includes non-monomorphized functions (those without a `mangled_name_id`).
/// Monomorphized instances are looked up via `vir_monomorph_map` instead.
pub(crate) fn build_vir_function_map(
    vir_functions: &[VirFunction],
) -> FxHashMap<FunctionId, usize> {
    let mut map = FxHashMap::default();
    for (idx, vf) in vir_functions.iter().enumerate() {
        if vf.mangled_name_id.is_none() && vf.method_id.is_none() {
            map.insert(vf.id, idx);
        }
    }
    map
}

/// Build a lookup map from semantic MethodId to VirFunction index.
///
/// Only includes VIR functions that have a `method_id` set (class/struct
/// methods and static methods).
pub(crate) fn build_vir_method_map(vir_functions: &[VirFunction]) -> FxHashMap<MethodId, usize> {
    let mut map = FxHashMap::default();
    for (idx, vf) in vir_functions.iter().enumerate() {
        if let Some(method_id) = vf.method_id {
            map.insert(method_id, idx);
        }
    }
    map
}

/// Lower all test function bodies in the program to VIR.
///
/// Walks the program's `Decl::Tests` blocks (including nested ones) and
/// lowers each `TestCase.body` to a `VirBody`.  Returns a map keyed by
/// the `TestCase`'s `Span` for O(1) lookup during test compilation.
pub(crate) fn lower_test_bodies(
    program: &Program,
    node_map: &NodeMap,
    interner: &mut Interner,
    type_arena: &TypeArena,
    entities: &impl LoweringEntityLookup,
    names: &NameTable,
    type_table: &mut VirTypeTable,
) -> Vec<VirTest> {
    let mut tests = Vec::new();
    for decl in &program.declarations {
        if let Decl::Tests(tests_decl) = decl {
            lower_tests_decl_bodies(
                tests_decl, node_map, interner, type_arena, entities, names, &mut tests, type_table,
            );
        }
    }
    tests
}

/// Recursively lower test bodies from a single `TestsDecl`.
#[allow(clippy::too_many_arguments)]
fn lower_tests_decl_bodies(
    tests_decl: &vole_frontend::ast::TestsDecl,
    node_map: &NodeMap,
    interner: &mut Interner,
    type_arena: &TypeArena,
    entities: &impl LoweringEntityLookup,
    names: &NameTable,
    tests: &mut Vec<VirTest>,
    type_table: &mut VirTypeTable,
) {
    let scoped_let_stmts: Vec<vole_frontend::Stmt> = tests_decl
        .decls
        .iter()
        .filter_map(|decl| match decl {
            Decl::Let(let_stmt) => Some(vole_frontend::Stmt::Let(let_stmt.clone())),
            Decl::LetTuple(let_tuple) => Some(vole_frontend::Stmt::LetTuple(let_tuple.clone())),
            _ => None,
        })
        .collect();
    let scoped_let_vir_stmts = if scoped_let_stmts.is_empty() {
        Vec::new()
    } else {
        let mut ctx = vole_sema::vir_lower::LoweringCtx {
            node_map,
            interner,
            type_arena,
            entities: entities.as_entity_registry(),
            name_table: names,
            type_table,
            generic: false,
        };
        lower_stmts(&scoped_let_stmts, &mut ctx).stmts
    };

    for test in &tests_decl.tests {
        let mut vir_body = lower_test_body(
            &test.body,
            node_map,
            interner,
            type_arena,
            entities.as_entity_registry(),
            names,
            type_table,
        );
        if !scoped_let_vir_stmts.is_empty() {
            vir_body
                .stmts
                .splice(0..0, scoped_let_vir_stmts.iter().cloned());
        }
        tests.push(VirTest {
            name: test.name.clone(),
            body: vir_body,
            span: test.span,
        });
    }
    // Recurse into nested tests blocks
    for decl in &tests_decl.decls {
        if let Decl::Tests(nested) = decl {
            lower_tests_decl_bodies(
                nested, node_map, interner, type_arena, entities, names, tests, type_table,
            );
        }
    }
}

/// Build generic VIR storage with VirTypeId remapping.
///
/// Like `build_generic_vir_storage` but applies a VirTypeId remapping to
/// each generic function template.  This is needed because generic templates
/// are lowered with their own type table (in sema Pass 2a) and their
/// VirTypeIds must be translated to the program's main type table.
pub(crate) fn build_generic_vir_storage_remapped(
    pairs: Vec<(NameId, VirFunction)>,
    type_remap: &FxHashMap<vole_identity::VirTypeId, vole_identity::VirTypeId>,
) -> (Vec<VirFunction>, FxHashMap<NameId, usize>) {
    let ctx = vole_vir::RewriteCtx::new(type_remap.clone());
    let mut map = FxHashMap::default();
    let mut functions = Vec::with_capacity(pairs.len());
    for (name_id, vir) in pairs {
        let idx = functions.len();
        map.insert(name_id, idx);
        functions.push(vole_vir::rewrite_function(&vir, &ctx));
    }
    (functions, map)
}

/// Run VIR monomorphization for free-function generics.
///
/// Converts sema monomorph cache entries into VIR `MonomorphInstance` seeds,
/// builds a temporary `VirProgram`, runs VIR monomorphization with those
/// seeds, and merges the produced concrete functions back into the working
/// `vir_functions` vec and `type_table`.
///
/// Returns the set of `FunctionId`s for generic functions that were
/// successfully monomorphized -- `lower_monomorphized_instances` should skip
/// all sema cache entries whose `original_name` resolves to one of these.
#[allow(clippy::too_many_arguments)]
pub(crate) fn run_early_vir_monomorphize(
    vir_functions: &mut Vec<VirFunction>,
    generic_vir_functions: &[VirFunction],
    generic_vir_map: &FxHashMap<NameId, usize>,
    type_table: &mut VirTypeTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
) -> HashSet<FunctionId> {
    use vole_sema::vir_lower::type_translate::translate_type_id;

    let mut handled = HashSet::new();

    // Build seeds from the sema monomorph cache.
    let mut seeds: Vec<vole_vir::MonomorphInstance> = Vec::new();
    let mut seed_mangled_names: FxHashMap<vole_vir::MonomorphInstance, NameId> =
        FxHashMap::default();
    for sema_instance in entities.monomorph_instances() {
        let Some(func_id) = entities.function_by_name(sema_instance.original_name) else {
            continue;
        };
        // Find the generic VIR template to get the type param order.
        let template = generic_vir_functions.iter().find(|f| f.id == func_id);
        let Some(template) = template else {
            // No generic VIR template — can't VIR-monomorphize this one.
            continue;
        };

        // Convert sema substitutions to ordered VIR type args.
        let mut type_args = Vec::with_capacity(template.type_params.len());
        let mut all_resolved = true;
        for &param_name in &template.type_params {
            if let Some(&sema_ty) = sema_instance.substitutions.get(&param_name) {
                let vir_ty = translate_type_id(type_table, sema_ty, type_arena);
                type_args.push(vir_ty);
            } else {
                // Substitution missing for this param — skip this instance.
                all_resolved = false;
                break;
            }
        }
        if !all_resolved {
            continue;
        }

        let seed = vole_vir::MonomorphInstance {
            function_id: func_id,
            type_args,
        };
        seed_mangled_names.insert(seed.clone(), sema_instance.mangled_name);
        seeds.push(seed);
    }

    if seeds.is_empty() {
        return handled;
    }

    // Build a temporary VirProgram for VIR monomorphization.
    let mut temp_program = VirProgram {
        type_table: std::mem::take(type_table),
        functions: std::mem::take(vir_functions),
        monomorph_map: FxHashMap::default(),
        function_map: FxHashMap::default(),
        method_map: FxHashMap::default(),
        generic_functions: generic_vir_functions.to_vec(),
        generic_map: generic_vir_map.clone(),
        tests: Vec::new(),
        global_inits: FxHashMap::default(),
        module_global_inits: FxHashMap::default(),
        function_default_inits: FxHashMap::default(),
        method_default_inits: FxHashMap::default(),
        lambda_default_inits: FxHashMap::default(),
        field_default_inits: FxHashMap::default(),
        vir_monomorph_base: usize::MAX,
    };

    let mut result = vole_vir::monomorphize_with_seeds(&mut temp_program, seeds);

    for (instance, &rel_idx) in &result.instance_map {
        if let Some(&mangled_name_id) = seed_mangled_names.get(instance)
            && let Some(func) = result.functions.get_mut(rel_idx)
        {
            func.mangled_name_id = Some(mangled_name_id);
        }
    }

    if !result.functions.is_empty() {
        // Record which generic FunctionIds were handled.
        for instance in result.instance_map.keys() {
            handled.insert(instance.function_id);
        }

        // Compute the base index where new functions will be appended.
        let base_index = temp_program.functions.len();
        temp_program.vir_monomorph_base = base_index;

        // Build the absolute instance index (base + relative offset).
        let abs_index: vole_vir::InstanceIndex = result
            .instance_map
            .into_iter()
            .map(|(instance, rel_idx)| (instance, base_index + rel_idx))
            .collect();

        // Append the monomorphized functions.
        temp_program.functions.extend(result.functions);

        // Resolve GenericCall -> VirDirect in all concrete functions.
        vole_vir::resolve_generic_calls(&mut temp_program.functions, &abs_index);
    }

    // Move the (possibly updated) type_table and functions back.
    *type_table = temp_program.type_table;
    *vir_functions = temp_program.functions;

    handled
}

/// Run the VIR monomorphization pass: discover generic calls in concrete
/// functions, instantiate generic templates, and resolve call targets.
///
/// This is the final VIR monomorph pass that runs on the fully assembled
/// VirProgram.  It catches any `GenericCall` sites in concrete functions
/// (including those produced by the early VIR monomorph pass) and resolves
/// them to `VirDirect` call targets.
pub(crate) fn run_vir_monomorphize(program: &mut VirProgram) {
    let result = vole_vir::monomorphize(program);
    if result.functions.is_empty() {
        return;
    }

    // Compute the base index where new functions will be appended.
    let base_index = program.functions.len();
    // Preserve the earliest VIR monomorph base if an earlier pass already
    // appended VIR monomorphized functions (e.g. early seeded monomorphize).
    if program.vir_monomorph_base == usize::MAX {
        program.vir_monomorph_base = base_index;
    }

    // Build the absolute instance index (base + relative offset).
    let abs_index: vole_vir::InstanceIndex = result
        .instance_map
        .into_iter()
        .map(|(instance, rel_idx)| (instance, base_index + rel_idx))
        .collect();

    // Append the monomorphized functions to the program.
    program.functions.extend(result.functions);

    // Resolve GenericCall -> VirDirect in all concrete functions.
    vole_vir::resolve_generic_calls(&mut program.functions, &abs_index);
}
