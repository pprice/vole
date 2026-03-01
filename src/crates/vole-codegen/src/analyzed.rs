// analyzed.rs
//! Result of parsing and analyzing a source file.

use rustc_hash::FxHashMap;
use std::collections::HashSet;
use std::rc::Rc;

use vole_frontend::{Interner, Program, Symbol};
use vole_identity::{FieldId, FunctionId, MethodId, ModuleId, NameId, NameTable, Span, TypeDefId};
use vole_sema::lowering::{LowerVirProgramArgs, lower_vir_program};
use vole_sema::{AnalysisOutput, SemaType, TypeArena};
use vole_vir::{VirEntityMetadata, VirFunction, VirProgram};

/// Result of parsing and analyzing a source file.
pub struct AnalyzedProgram {
    /// Virtual module IDs for tests blocks. Maps tests block span to its virtual ModuleId.
    tests_virtual_modules: FxHashMap<Span, ModuleId>,
    /// Type arena (Rc-shared, immutable during codegen).
    types: Rc<TypeArena>,
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

impl From<vole_vir::VirExternalMethodInfo> for ExternalMethodInfoRef {
    fn from(value: vole_vir::VirExternalMethodInfo) -> Self {
        Self {
            module_path: value.module_path,
            native_name: value.native_name,
        }
    }
}

impl From<vole_identity::ExternalMethodInfo> for ExternalMethodInfoRef {
    fn from(value: vole_identity::ExternalMethodInfo) -> Self {
        Self {
            module_path: value.module_path,
            native_name: value.native_name,
        }
    }
}

/// Codegen-local method binding payload for per-type method dispatch.
#[derive(Debug, Clone)]
pub(crate) struct MethodBindingRef {
    pub func_type: vole_identity::FunctionType,
    pub external_info: Option<ExternalMethodInfoRef>,
}

impl From<&vole_vir::VirMethodBinding> for MethodBindingRef {
    fn from(value: &vole_vir::VirMethodBinding) -> Self {
        Self {
            func_type: value.sema_func_type.clone(),
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
            implements: &db.implements,
        });
        let mut vir_program = lowering_output.vir_program;
        // Move name resolution data into VirProgram (zero-clone for NameTable
        // via Rc::clone, single Rc::new wrap for interner).
        vir_program.interner = Rc::new(interner);
        vir_program.name_table = Rc::clone(&db.names);
        Self {
            tests_virtual_modules,
            types: db.types,
            module_id,
            modules_with_errors,
            vir_program,
        }
    }

    /// Get read-only access to the name table.
    pub(crate) fn name_table(&self) -> &NameTable {
        self.vir_program.name_table()
    }

    /// Get read-only access to the interner.
    pub(crate) fn interner(&self) -> &Interner {
        self.vir_program.interner()
    }

    /// Clone the interner Rc for APIs that need shared ownership.
    pub(crate) fn interner_rc(&self) -> Rc<Interner> {
        self.vir_program.interner_rc()
    }

    /// Get the main/root module ID for this analyzed program.
    pub fn module_id(&self) -> ModuleId {
        self.module_id
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
    /// VIR-native entity data for type, field, method, function, and global
    /// queries.  Populated during VIR lowering from sema's `EntityRegistry`.
    fn entity_metadata(&self) -> &VirEntityMetadata {
        self.vir_program.entity_metadata()
    }

    /// Clone the name table Rc for APIs that need shared ownership.
    pub(crate) fn name_table_rc(&self) -> Rc<NameTable> {
        self.vir_program.name_table_rc()
    }

    /// Get read-only access to the type arena
    pub(crate) fn type_arena(&self) -> &TypeArena {
        &self.types
    }

    /// Resolve the EntityRegistry NameId used for all array implement dispatch.
    pub(crate) fn array_type_name_id(&self) -> Option<NameId> {
        self.entity_metadata().array_name_id()
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

    /// Resolve a VIR type definition by ID.
    pub(crate) fn type_def(
        &self,
        type_def_id: TypeDefId,
    ) -> &vole_vir::entity_metadata::VirTypeDef {
        self.entity_metadata()
            .get_type_def(type_def_id)
            .unwrap_or_else(|| {
                panic!(
                    "type_def: type def {:?} not in VirEntityMetadata",
                    type_def_id
                )
            })
    }

    /// Query-compatible alias for resolving a VIR type definition by ID.
    pub(crate) fn get_type(
        &self,
        type_def_id: TypeDefId,
    ) -> &vole_vir::entity_metadata::VirTypeDef {
        self.type_def(type_def_id)
    }

    /// Resolve a VIR field definition by ID.
    pub(crate) fn field_def(&self, field_id: FieldId) -> &vole_vir::VirFieldDef {
        self.entity_metadata()
            .get_field_def(field_id)
            .unwrap_or_else(|| panic!("field_def: no VirFieldDef for {field_id:?}"))
    }

    /// Query-compatible alias for resolving a VIR field definition by ID.
    pub(crate) fn get_field(&self, field_id: FieldId) -> &vole_vir::VirFieldDef {
        self.field_def(field_id)
    }

    /// Resolve a VIR function definition by ID.
    pub(crate) fn function_def(
        &self,
        function_id: FunctionId,
    ) -> &vole_vir::entity_metadata::VirFunctionDef {
        self.entity_metadata()
            .get_function_def(function_id)
            .unwrap_or_else(|| panic!("function_def: no VirFunctionDef for {function_id:?}"))
    }

    /// Resolve a VIR method definition by ID.
    pub(crate) fn method_def(
        &self,
        method_id: MethodId,
    ) -> &vole_vir::entity_metadata::VirMethodDef {
        self.entity_metadata()
            .get_method_def(method_id)
            .unwrap_or_else(|| panic!("method_def: no VirMethodDef for {method_id:?}"))
    }

    /// Query-compatible alias for resolving a VIR method definition by ID.
    pub(crate) fn get_method(
        &self,
        method_id: MethodId,
    ) -> &vole_vir::entity_metadata::VirMethodDef {
        self.method_def(method_id)
    }

    /// Return the sema signature TypeId for a method.
    pub(crate) fn method_signature_id(&self, method_id: MethodId) -> vole_sema::type_arena::TypeId {
        self.method_def(method_id).signature_id
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
        self.entity_metadata().has_global(name_id)
    }

    /// Resolve a NameId to display form (e.g. module::Type::method).
    pub(crate) fn display_name(&self, name_id: NameId) -> String {
        self.vir_program.display_name(name_id)
    }

    /// Resolve a NameId to its last segment.
    pub(crate) fn last_segment(&self, name_id: NameId) -> Option<String> {
        self.vir_program.last_segment(name_id)
    }

    /// Resolve type definition by NameId.
    pub(crate) fn try_type_def_id(&self, name_id: NameId) -> Option<TypeDefId> {
        self.entity_metadata().type_by_name(name_id)
    }

    /// Resolve method NameId by short string.
    pub(crate) fn try_method_name_id_by_str(&self, name_str: &str) -> Option<NameId> {
        self.vir_program.try_method_name_id_by_str(name_str)
    }

    /// Resolve method NameId by short string, panicking when missing.
    pub(crate) fn method_name_id_by_str(&self, name_str: &str) -> NameId {
        self.vir_program.method_name_id_by_str(name_str)
    }

    /// Resolve semantic FunctionId by NameId.
    pub(crate) fn function_id_by_name_id(&self, name_id: NameId) -> Option<FunctionId> {
        self.entity_metadata().function_by_name(name_id)
    }

    /// Resolve a string type name in a module context.
    pub(crate) fn resolve_type_def_by_str(
        &self,
        module_id: ModuleId,
        name: &str,
    ) -> Option<TypeDefId> {
        self.entity_metadata().resolve_type_def_by_str(
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
        self.type_def(type_def_id).base_type_id
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
        self.entity_metadata()
            .find_method_binding(type_def_id, method_name_id)
            .map(|binding| binding.sema_func_type.return_type_id)
    }

    /// Return interface method binding metadata, when a binding exists.
    pub(crate) fn method_binding(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodBindingRef> {
        self.entity_metadata()
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
            .entity_metadata()
            .implementation_sema_type_args(implementing_type_id, interface_id);
        type_params
            .into_iter()
            .zip(type_args.iter().copied())
            .collect()
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

    /// Return all implement block entries (main program + all modules) that
    /// target the given type.  Used to build the set of implement-block method
    /// IDs so `compile_type_methods` can skip them (they are compiled by the
    /// implement block path instead).
    pub(crate) fn implement_blocks_for_type(
        &self,
        type_def_id: TypeDefId,
    ) -> impl Iterator<Item = &vole_vir::VirImplementBlockEntry> {
        let em = &self.vir_program().entity_metadata;
        em.implement_blocks()
            .iter()
            .chain(
                em.all_module_implement_blocks()
                    .flat_map(|(_, entries)| entries.iter()),
            )
            .filter(move |entry| entry.type_def_id == type_def_id)
    }

    /// Return external binding metadata for a method, when available.
    pub(crate) fn method_external_binding(
        &self,
        method_id: MethodId,
    ) -> Option<&vole_vir::VirExternalMethodInfo> {
        self.method_def(method_id).external_binding.as_ref()
    }

    /// Return true when all methods on a type are external-only.
    pub(crate) fn is_external_only(&self, type_def_id: TypeDefId) -> bool {
        self.entity_metadata().is_external_only(type_def_id)
    }

    /// Return the single abstract method for functional interfaces.
    pub(crate) fn is_functional_interface(&self, type_def_id: TypeDefId) -> Option<MethodId> {
        self.entity_metadata().is_functional(type_def_id)
    }

    /// Return all test-scoped virtual module IDs.
    pub(crate) fn tests_virtual_module_ids(&self) -> Vec<ModuleId> {
        self.tests_virtual_modules.values().copied().collect()
    }

    /// Resolve function NameId by module and Symbol, panicking when missing.
    pub(crate) fn function_name_id(&self, module_id: ModuleId, name: Symbol) -> NameId {
        self.vir_program.function_name_id(module_id, name)
    }

    /// Return function parameter TypeIds by FunctionId.
    pub(crate) fn function_param_type_ids(
        &self,
        func_id: FunctionId,
    ) -> Vec<vole_sema::type_arena::TypeId> {
        self.function_def(func_id).sema_param_types.clone()
    }

    /// Return global declared TypeId by NameId.
    pub(crate) fn global_type_id(&self, name_id: NameId) -> Option<vole_sema::type_arena::TypeId> {
        let global_id = self.entity_metadata().global_by_name(name_id)?;
        Some(
            self.entity_metadata()
                .get_global_def(global_id)
                .expect("global_type_id: global ID not in VirEntityMetadata")
                .sema_type_id,
        )
    }

    /// Return module ID for a path, falling back to main module.
    pub(crate) fn module_id_or_main(&self, path: &str) -> ModuleId {
        self.vir_program.module_id_or_main(path)
    }

    /// Return known imported module paths.
    pub fn module_paths(&self) -> Vec<String> {
        self.vir_program.module_paths()
    }

    /// Return whether a function parameter has a default expression.
    pub(crate) fn has_function_default_expr(&self, func_id: FunctionId, param_idx: usize) -> bool {
        self.function_def(func_id)
            .has_defaults
            .get(param_idx)
            .copied()
            .unwrap_or(false)
    }

    /// Return whether a method parameter has a default expression.
    pub(crate) fn has_method_default_expr(&self, method_id: MethodId, param_idx: usize) -> bool {
        self.method_def(method_id)
            .has_param_defaults
            .get(param_idx)
            .copied()
            .unwrap_or(false)
    }

    /// Return imported-module interner for a module ID, when available.
    pub(crate) fn module_interner(&self, module_id: ModuleId) -> Option<&Interner> {
        let module_path = self.vir_program.module_path(module_id);
        self.vir_program.module_interner(module_path)
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
    pub(crate) fn entity_field_type(&self, field_id: FieldId) -> vole_identity::TypeId {
        self.field_def(field_id).sema_type_id
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
        self.type_def(type_def_id).sema_generic_field_types.clone()
    }

    /// Return whether a type definition is a sentinel type.
    pub(crate) fn entity_type_is_sentinel(&self, type_def_id: TypeDefId) -> bool {
        self.entity_metadata()
            .type_def_kind(type_def_id)
            .is_some_and(|k| k.is_sentinel())
    }

    /// Find a type by its short (last-segment) name.
    pub(crate) fn type_by_short_name(&self, short_name: &str) -> Option<TypeDefId> {
        self.entity_metadata().type_by_short_name(short_name)
    }

    /// Look up external function binding metadata by short function name.
    pub(crate) fn external_func_by_name(
        &self,
        name: &str,
    ) -> Option<vole_vir::VirExternalFuncInfo> {
        self.vir_program.external_func_by_name(name)
    }

    /// Look up generic external function metadata by short function name.
    pub(crate) fn generic_external_by_name(
        &self,
        name: &str,
    ) -> Option<&vole_vir::VirGenericExternalInfo> {
        self.vir_program.generic_external_by_name(name)
    }

    /// Look up generic external method metadata by defining type and method name.
    pub(crate) fn generic_external_method(
        &self,
        type_def_id: TypeDefId,
        method_name: NameId,
    ) -> Option<&vole_vir::VirGenericExternalInfo> {
        self.vir_program
            .generic_external_method(type_def_id, method_name)
    }

    /// Render a short human-readable type name for diagnostics/debug output.
    pub(crate) fn display_type_id_short(&self, type_id: vole_sema::type_arena::TypeId) -> String {
        vole_sema::type_display::display_type_id_short(
            type_id,
            self.type_arena(),
            self.name_table(),
            self.vir_program.entity_metadata(),
        )
    }

    /// Resolve the implement-registry type key NameId for a concrete sema TypeId.
    ///
    /// Fast path: looks up the pre-computed `impl_type_names` map in
    /// `VirEntityMetadata` (covers primitives, Range, Handle).
    /// Fallback: inspects the `TypeArena` for Array, Class, and Struct types.
    pub(crate) fn impl_type_name_id_from_type_id(
        &self,
        type_id: vole_sema::type_arena::TypeId,
    ) -> Option<NameId> {
        let entity_metadata = self.vir_program.entity_metadata();
        // Fast path: pre-computed for primitives, Range, Handle.
        if let Some(name_id) = entity_metadata.impl_type_name(type_id) {
            return Some(name_id);
        }
        // Dynamic path: inspect the arena for Array, Class, Struct.
        match self.type_arena().get(type_id) {
            SemaType::Array(_) => entity_metadata.array_name_id(),
            SemaType::Class { type_def_id, .. } | SemaType::Struct { type_def_id, .. } => {
                entity_metadata.type_name_id(*type_def_id)
            }
            _ => None,
        }
    }

    /// Look up an implement-registry method by concrete type-name key.
    pub(crate) fn implement_method_by_name(
        &self,
        type_name_id: NameId,
        method_name_id: NameId,
    ) -> Option<&vole_vir::VirMethodImplInfo> {
        self.vir_program
            .implement_method_by_name(type_name_id, method_name_id)
    }

    /// Resolve and look up an implement-registry method from a sema TypeId.
    pub(crate) fn implement_method_for_type(
        &self,
        type_id: vole_sema::type_arena::TypeId,
        method_name_id: NameId,
    ) -> Option<(NameId, &vole_vir::VirMethodImplInfo)> {
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
            self.function_def(func.id).module == module_id
        }
    }
}
