// analyzed.rs
//! Result of parsing and analyzing a source file.

use rustc_hash::FxHashMap;
use std::collections::HashSet;
use std::rc::Rc;

use vole_frontend::{Decl, Interner, LetInit, Program, Symbol};
use vole_identity::{
    FieldId, FunctionId, MethodId, ModuleId, NameId, NameTable, NamerLookup, Span, TypeDefId,
};
use vole_sema::{
    AnalysisOutput, EntityRegistry, ImplementRegistry, NodeMap, ProgramQuery, TypeArena,
};
use vole_vir::type_table::VirTypeTable;
use vole_vir::{VirBody, VirFunction, VirProgram, VirRef, VirTest};

use vole_sema::vir_lower::{
    lower_function, lower_interface_method, lower_method, lower_monomorphized_function,
    lower_stmts, lower_test_body,
};

/// Result of parsing and analyzing a source file.
pub struct AnalyzedProgram {
    pub program: Program,
    pub interner: Rc<Interner>,
    /// All expression-level metadata (types, method resolutions, generic calls).
    /// Vec-backed per-node store, keyed by `NodeId`.
    pub node_map: NodeMap,
    /// Virtual module IDs for tests blocks. Maps tests block span to its virtual ModuleId.
    /// Keyed by Span (not NodeId), so stored separately from NodeId-keyed NodeMap.
    pub tests_virtual_modules: FxHashMap<Span, ModuleId>,
    /// Parsed module programs for compiling pure Vole functions
    pub module_programs: FxHashMap<String, (Program, Rc<Interner>)>,
    /// Type arena (Rc-shared, immutable during codegen).
    pub types: Rc<TypeArena>,
    /// Entity registry (Rc-shared, immutable during codegen).
    pub entities: Rc<EntityRegistry>,
    /// Implement registry (Rc-shared, immutable during codegen).
    pub implements: Rc<ImplementRegistry>,
    /// Name table (Rc-shared, immutable during codegen).
    pub names: Rc<NameTable>,
    /// The module ID for the main program (may differ from main_module when using shared cache)
    pub module_id: ModuleId,
    /// Module paths that had sema errors. Codegen should skip compiling
    /// function bodies for these modules to avoid INVALID type IDs.
    pub modules_with_errors: HashSet<String>,
    /// All VIR data: functions, tests, global inits, type table, and lookup maps.
    ///
    /// This is the single entry point for all VIR data produced during lowering.
    /// Codegen accesses VIR through this struct rather than individual fields.
    pub vir_program: VirProgram,
}

impl AnalyzedProgram {
    /// Construct AnalyzedProgram from parsed program and analysis output.
    ///
    /// When the CompilationDb has a single owner (non-cached path), unwraps it
    /// directly. When shared (cached path, where module cache holds a reference),
    /// creates a CodegenDb that shares all data via Rc (O(1), zero cloning).
    pub fn from_analysis(program: Program, mut interner: Interner, output: AnalysisOutput) -> Self {
        let db = match Rc::try_unwrap(output.db) {
            // Non-cached path: sole owner, move data directly (zero-cost)
            Ok(compilation_db) => compilation_db.into_codegen(),
            // Cached path: share Rc-wrapped fields instead of cloning entire CompilationDb
            Err(rc) => rc.to_codegen_shared(),
        };
        let mut module_programs = output.module_programs;
        let mut type_table = VirTypeTable::new();
        let mut vir_functions = lower_top_level_functions(
            &program,
            &mut interner,
            &db.names,
            &db.entities,
            &db.types,
            &output.node_map,
            output.module_id,
            &mut type_table,
        );
        lower_module_functions(
            &mut module_programs,
            &db.names,
            &db.entities,
            &db.types,
            &output.node_map,
            &output.modules_with_errors,
            &mut vir_functions,
            &mut type_table,
        );

        // --- VIR monomorphization ---
        //
        // Run VIR monomorph to produce concrete functions from generic
        // templates via type substitution.  This is the primary
        // monomorphization path for free functions.
        //
        // Generic VIR templates use VirTypeIds from their own type table
        // (built during sema Pass 2a).  We must merge that table into the
        // main type_table and remap all VirTypeIds in the templates so that
        // VIR monomorphization operates on a single unified type table.
        let generic_type_remap = type_table.merge_from(&output.generic_vir_type_table);
        let (generic_vir_functions, generic_vir_map) =
            build_generic_vir_storage_remapped(output.generic_vir_functions, &generic_type_remap);

        // Convert sema monomorph cache entries to VIR MonomorphInstance seeds
        // and run VIR monomorphization.  Collect which FunctionIds were handled
        // so we can skip them in the AST-based lowering fallback path.
        let vir_handled_function_ids = run_early_vir_monomorphize(
            &mut vir_functions,
            &generic_vir_functions,
            &generic_vir_map,
            &mut type_table,
            &db.entities,
            &db.types,
        );

        let generic_func_asts = build_generic_func_map(
            &program,
            &interner,
            &db.names,
            &db.entities,
            &output.tests_virtual_modules,
            output.module_id,
        );
        lower_monomorphized_instances(
            &generic_func_asts,
            &mut module_programs,
            &db.names,
            &db.entities,
            &db.types,
            &output.node_map,
            &output.modules_with_errors,
            &mut interner,
            &mut vir_functions,
            &mut type_table,
            &vir_handled_function_ids,
        );
        lower_top_level_type_methods(
            &program,
            &mut interner,
            &db.names,
            &db.entities,
            &db.types,
            &output.node_map,
            output.module_id,
            Some(&module_programs),
            &mut vir_functions,
            &mut type_table,
        );
        lower_module_type_methods(
            &mut module_programs,
            &db.names,
            &db.entities,
            &db.types,
            &output.node_map,
            &output.modules_with_errors,
            &mut vir_functions,
            &mut type_table,
        );
        lower_implement_block_methods(
            &program,
            &mut interner,
            &db.names,
            &db.entities,
            &db.types,
            &output.node_map,
            output.module_id,
            &mut vir_functions,
            &mut type_table,
        );
        lower_module_implement_block_methods(
            &mut module_programs,
            &db.names,
            &db.entities,
            &db.types,
            &output.node_map,
            &output.modules_with_errors,
            &mut vir_functions,
            &mut type_table,
        );
        lower_test_scoped_type_methods(
            &program,
            &mut interner,
            &db.names,
            &db.entities,
            &db.types,
            &output.node_map,
            &output.tests_virtual_modules,
            Some(&module_programs),
            output.module_id,
            &mut vir_functions,
            &mut type_table,
        );
        let method_monomorph_ctx = MethodMonomorphLoweringCtx {
            names: &db.names,
            entities: &db.entities,
            type_arena: &db.types,
            node_map: &output.node_map,
            modules_with_errors: &output.modules_with_errors,
        };
        let mut method_monomorph_work = MethodMonomorphLoweringWork {
            program: &program,
            interner: &mut interner,
            module_programs: &mut module_programs,
            tests_virtual_modules: &output.tests_virtual_modules,
            module_id: output.module_id,
            vir_functions: &mut vir_functions,
            type_table: &mut type_table,
        };
        lower_type_method_monomorphized_instances(
            &mut method_monomorph_work,
            &method_monomorph_ctx,
        );
        let vir_monomorph_map = build_vir_monomorph_map(&vir_functions);
        let vir_function_map = build_vir_function_map(&vir_functions);
        let vir_method_map = build_vir_method_map(&vir_functions);
        let vir_tests = lower_test_bodies(
            &program,
            &output.node_map,
            &mut interner,
            &db.types,
            &db.entities,
            &db.names,
            &mut type_table,
        );
        let vir_global_inits = lower_global_inits(
            &program,
            &mut interner,
            &output.node_map,
            &db.types,
            &db.entities,
            &db.names,
            &mut type_table,
        );
        let module_vir_global_inits = lower_module_global_inits(
            &mut module_programs,
            &db.names,
            &output.node_map,
            &db.types,
            &db.entities,
            &output.modules_with_errors,
            &mut type_table,
        );
        let mut vir_function_default_inits = lower_function_default_inits(
            &program,
            &mut interner,
            output.module_id,
            &output.tests_virtual_modules,
            &db.names,
            &db.entities,
            &output.node_map,
            &db.types,
            &mut type_table,
        );
        let module_vir_function_default_inits = lower_module_function_default_inits(
            &mut module_programs,
            &db.names,
            &db.entities,
            &output.node_map,
            &db.types,
            &output.modules_with_errors,
            &mut type_table,
        );
        vir_function_default_inits.extend(module_vir_function_default_inits);
        let mut vir_method_default_inits = lower_method_default_inits(
            &program,
            &mut interner,
            output.module_id,
            &output.tests_virtual_modules,
            &db.names,
            &db.entities,
            &output.node_map,
            &db.types,
            &mut type_table,
        );
        let module_vir_method_default_inits = lower_module_method_default_inits(
            &mut module_programs,
            &db.names,
            &db.entities,
            &output.node_map,
            &db.types,
            &output.modules_with_errors,
            &mut type_table,
        );
        vir_method_default_inits.extend(module_vir_method_default_inits);
        let vir_lambda_default_inits = lower_lambda_default_inits(
            &program,
            &mut interner,
            &mut module_programs,
            output.module_id,
            &output.tests_virtual_modules,
            &db.names,
            &db.entities,
            &output.node_map,
            &db.types,
            &output.modules_with_errors,
            &mut type_table,
        );
        let mut vir_field_default_inits = lower_field_default_inits(
            &program,
            &mut interner,
            output.module_id,
            &output.tests_virtual_modules,
            &db.names,
            &db.entities,
            &output.node_map,
            &db.types,
            &mut type_table,
        );
        let module_vir_field_default_inits = lower_module_field_default_inits(
            &mut module_programs,
            &db.names,
            &db.entities,
            &output.node_map,
            &db.types,
            &output.modules_with_errors,
            &mut type_table,
        );
        vir_field_default_inits.extend(module_vir_field_default_inits);
        let mut vir_program = VirProgram {
            type_table,
            functions: vir_functions,
            monomorph_map: vir_monomorph_map,
            function_map: vir_function_map,
            method_map: vir_method_map,
            generic_functions: generic_vir_functions,
            generic_map: generic_vir_map,
            tests: vir_tests,
            global_inits: vir_global_inits,
            module_global_inits: module_vir_global_inits,
            function_default_inits: vir_function_default_inits,
            method_default_inits: vir_method_default_inits,
            lambda_default_inits: vir_lambda_default_inits,
            field_default_inits: vir_field_default_inits,
            vir_monomorph_base: usize::MAX,
        };
        // Run VIR monomorph again on the full program to resolve any
        // GenericCall targets in concrete functions (e.g., from VIR-lowered
        // monomorphs that call other generics).  The early run above handles
        // sema-seeded instances; this run catches GenericCall sites in all
        // concrete functions.
        run_vir_monomorphize(&mut vir_program);
        Self {
            program,
            interner: Rc::new(interner),
            node_map: output.node_map,
            tests_virtual_modules: output.tests_virtual_modules,
            module_programs,
            types: db.types,
            entities: db.entities,
            implements: db.implements,
            names: db.names,
            module_id: output.module_id,
            modules_with_errors: output.modules_with_errors,
            vir_program,
        }
    }

    /// Get a query interface for accessing type information and analysis results.
    pub fn query(&self) -> ProgramQuery<'_> {
        ProgramQuery::new(
            self.entity_registry(),
            &self.node_map,
            &self.tests_virtual_modules,
            self.name_table_ref(),
            &self.interner,
            self.implement_registry(),
            &self.module_programs,
            self.type_arena(),
        )
    }

    /// Get read-only access to the name table
    pub fn name_table(&self) -> &NameTable {
        &self.names
    }

    /// Get a shared reference to the name table Rc (cloned)
    pub fn name_table_rc(&self) -> Rc<NameTable> {
        Rc::clone(self.name_table_ref())
    }

    /// Get a reference to the name table Rc (borrowed, no clone)
    pub fn name_table_ref(&self) -> &Rc<NameTable> {
        &self.names
    }

    /// Get read-only access to the type arena
    pub fn type_arena(&self) -> &TypeArena {
        &self.types
    }

    /// Get read-only access to entity registry
    pub fn entity_registry(&self) -> &EntityRegistry {
        &self.entities
    }

    /// Resolve the EntityRegistry NameId used for all array implement dispatch.
    pub fn array_type_name_id(&self) -> Option<NameId> {
        self.entity_registry().array_name_id()
    }

    /// Resolve a type's canonical entity NameId from its TypeDefId.
    pub fn entity_type_name_id(&self, type_def_id: TypeDefId) -> NameId {
        self.entity_registry().name_id(type_def_id)
    }

    /// Find a type by its short (last-segment) name in the entity registry.
    pub fn type_by_short_name(&self, short_name: &str) -> Option<TypeDefId> {
        self.entity_registry()
            .type_by_short_name(short_name, self.name_table())
    }

    /// Get read-only access to implement registry
    pub fn implement_registry(&self) -> &ImplementRegistry {
        &self.implements
    }

    /// Look up external function binding metadata by short function name.
    pub fn external_func_by_name(
        &self,
        name: &str,
    ) -> Option<&vole_sema::implement_registry::ExternalMethodInfo> {
        self.implement_registry().get_external_func(name)
    }

    /// Look up generic external function metadata by short function name.
    pub fn generic_external_by_name(
        &self,
        name: &str,
    ) -> Option<&vole_sema::implement_registry::GenericExternalInfo> {
        self.implement_registry().get_generic_external(name)
    }

    /// Look up generic external method metadata by defining type and method name.
    pub fn generic_external_method(
        &self,
        type_def_id: TypeDefId,
        method_name: NameId,
    ) -> Option<&vole_sema::implement_registry::GenericExternalInfo> {
        self.implement_registry()
            .get_generic_external_method(type_def_id, method_name)
    }

    /// Get the free-function monomorph cache.
    pub fn monomorph_cache(&self) -> &vole_sema::generic::MonomorphCache {
        &self.entity_registry().monomorph_cache
    }

    /// Get the class-method monomorph cache.
    pub fn class_method_monomorph_cache(&self) -> &vole_sema::generic::ClassMethodMonomorphCache {
        &self.entity_registry().class_method_monomorph_cache
    }

    /// Get the static-method monomorph cache.
    pub fn static_method_monomorph_cache(&self) -> &vole_sema::generic::StaticMethodMonomorphCache {
        &self.entity_registry().static_method_monomorph_cache
    }

    /// Render a short human-readable type name for diagnostics/debug output.
    pub fn display_type_id_short(&self, type_id: vole_sema::type_arena::TypeId) -> String {
        vole_sema::type_display::display_type_id_short(
            type_id,
            self.type_arena(),
            self.name_table(),
            self.entity_registry(),
        )
    }

    /// Resolve the implement-registry type key NameId for a concrete sema TypeId.
    pub fn impl_type_name_id_from_type_id(
        &self,
        type_id: vole_sema::type_arena::TypeId,
    ) -> Option<NameId> {
        ImplementRegistry::type_name_id_for_type(type_id, self.type_arena(), self.entity_registry())
    }

    /// Look up an implement-registry method by concrete type-name key.
    pub fn implement_method_by_name(
        &self,
        type_name_id: NameId,
        method_name_id: NameId,
    ) -> Option<&vole_sema::implement_registry::MethodImpl> {
        self.implement_registry()
            .get_method_by_name(type_name_id, method_name_id)
    }

    /// Resolve and look up an implement-registry method from a sema TypeId.
    pub fn implement_method_for_type(
        &self,
        type_id: vole_sema::type_arena::TypeId,
        method_name_id: NameId,
    ) -> Option<(NameId, &vole_sema::implement_registry::MethodImpl)> {
        let type_name_id = self.impl_type_name_id_from_type_id(type_id)?;
        let method_impl = self.implement_method_by_name(type_name_id, method_name_id)?;
        Some((type_name_id, method_impl))
    }

    /// Look up a VIR function by its monomorphized mangled NameId.
    /// Returns `None` if no VIR function was lowered for this instance.
    pub fn get_vir_monomorph(&self, mangled_name_id: NameId) -> Option<&VirFunction> {
        self.vir_program.get_monomorph(mangled_name_id)
    }

    /// Look up a VIR function by its semantic FunctionId.
    /// Returns `None` if no VIR function was lowered for this function.
    pub fn get_vir_function(&self, func_id: FunctionId) -> Option<&VirFunction> {
        self.vir_program.get_function(func_id)
    }

    /// Look up a VIR function by its semantic MethodId.
    /// Returns `None` if no VIR function was lowered for this method.
    pub fn get_vir_method(&self, method_id: MethodId) -> Option<&VirFunction> {
        self.vir_program.get_method(method_id)
    }

    /// Look up a generic VIR function template by its original `NameId`.
    /// Returns `None` if no generic VIR function was lowered for this name.
    pub fn get_generic_vir_function(&self, original_name: NameId) -> Option<&VirFunction> {
        self.vir_program.get_generic_function(original_name)
    }

    /// Look up a VIR test body by the test case's span.
    /// Returns `None` if no VIR body was lowered for this test.
    pub fn get_vir_test(&self, span: Span) -> Option<&VirBody> {
        self.vir_program.get_test(span)
    }
}

trait LoweringEntityLookup {
    fn function_by_name(&self, name_id: NameId) -> Option<FunctionId>;
    fn type_by_name(&self, name_id: NameId) -> Option<TypeDefId>;
    fn type_by_short_name(&self, short_name: &str, names: &NameTable) -> Option<TypeDefId>;
    fn find_method_on_type(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId>;
    fn find_static_method_on_type(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId>;
    fn as_entity_registry(&self) -> &EntityRegistry;
    fn array_name_id(&self) -> Option<NameId>;
    fn get_type(&self, type_def_id: TypeDefId) -> &vole_sema::entity_defs::TypeDef;
    fn get_function(&self, func_id: FunctionId) -> &vole_sema::entity_defs::FunctionDef;
    fn get_method(&self, method_id: MethodId) -> &vole_sema::entity_defs::MethodDef;
    fn get_implemented_interfaces(&self, type_def_id: TypeDefId) -> Vec<TypeDefId>;
    fn methods_on_type(&self, type_def_id: TypeDefId) -> Vec<MethodId>;
    fn monomorph_instances(&self) -> Vec<vole_sema::generic::MonomorphInstance>;
    fn class_method_monomorph_instances(
        &self,
    ) -> Vec<vole_sema::generic::ClassMethodMonomorphInstance>;
    fn static_method_monomorph_instances(
        &self,
    ) -> Vec<vole_sema::generic::StaticMethodMonomorphInstance>;
}

impl LoweringEntityLookup for EntityRegistry {
    fn function_by_name(&self, name_id: NameId) -> Option<FunctionId> {
        EntityRegistry::function_by_name(self, name_id)
    }

    fn type_by_name(&self, name_id: NameId) -> Option<TypeDefId> {
        EntityRegistry::type_by_name(self, name_id)
    }

    fn type_by_short_name(&self, short_name: &str, names: &NameTable) -> Option<TypeDefId> {
        EntityRegistry::type_by_short_name(self, short_name, names)
    }

    fn find_method_on_type(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId> {
        EntityRegistry::find_method_on_type(self, type_def_id, method_name_id)
    }

    fn find_static_method_on_type(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId> {
        EntityRegistry::find_static_method_on_type(self, type_def_id, method_name_id)
    }

    fn as_entity_registry(&self) -> &EntityRegistry {
        self
    }

    fn array_name_id(&self) -> Option<NameId> {
        EntityRegistry::array_name_id(self)
    }

    fn get_type(&self, type_def_id: TypeDefId) -> &vole_sema::entity_defs::TypeDef {
        EntityRegistry::get_type(self, type_def_id)
    }

    fn get_function(&self, func_id: FunctionId) -> &vole_sema::entity_defs::FunctionDef {
        EntityRegistry::get_function(self, func_id)
    }

    fn get_method(&self, method_id: MethodId) -> &vole_sema::entity_defs::MethodDef {
        EntityRegistry::get_method(self, method_id)
    }

    fn get_implemented_interfaces(&self, type_def_id: TypeDefId) -> Vec<TypeDefId> {
        EntityRegistry::get_implemented_interfaces(self, type_def_id)
    }

    fn methods_on_type(&self, type_def_id: TypeDefId) -> Vec<MethodId> {
        EntityRegistry::methods_on_type(self, type_def_id).collect()
    }

    fn monomorph_instances(&self) -> Vec<vole_sema::generic::MonomorphInstance> {
        self.monomorph_cache.collect_instances()
    }

    fn class_method_monomorph_instances(
        &self,
    ) -> Vec<vole_sema::generic::ClassMethodMonomorphInstance> {
        self.class_method_monomorph_cache.collect_instances()
    }

    fn static_method_monomorph_instances(
        &self,
    ) -> Vec<vole_sema::generic::StaticMethodMonomorphInstance> {
        self.static_method_monomorph_cache.collect_instances()
    }
}

impl<T> LoweringEntityLookup for Rc<T>
where
    T: LoweringEntityLookup + ?Sized,
{
    fn function_by_name(&self, name_id: NameId) -> Option<FunctionId> {
        (**self).function_by_name(name_id)
    }

    fn type_by_name(&self, name_id: NameId) -> Option<TypeDefId> {
        (**self).type_by_name(name_id)
    }

    fn type_by_short_name(&self, short_name: &str, names: &NameTable) -> Option<TypeDefId> {
        (**self).type_by_short_name(short_name, names)
    }

    fn find_method_on_type(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId> {
        (**self).find_method_on_type(type_def_id, method_name_id)
    }

    fn find_static_method_on_type(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId> {
        (**self).find_static_method_on_type(type_def_id, method_name_id)
    }

    fn as_entity_registry(&self) -> &EntityRegistry {
        (**self).as_entity_registry()
    }

    fn array_name_id(&self) -> Option<NameId> {
        (**self).array_name_id()
    }

    fn get_type(&self, type_def_id: TypeDefId) -> &vole_sema::entity_defs::TypeDef {
        (**self).get_type(type_def_id)
    }

    fn get_function(&self, func_id: FunctionId) -> &vole_sema::entity_defs::FunctionDef {
        (**self).get_function(func_id)
    }

    fn get_method(&self, method_id: MethodId) -> &vole_sema::entity_defs::MethodDef {
        (**self).get_method(method_id)
    }

    fn get_implemented_interfaces(&self, type_def_id: TypeDefId) -> Vec<TypeDefId> {
        (**self).get_implemented_interfaces(type_def_id)
    }

    fn methods_on_type(&self, type_def_id: TypeDefId) -> Vec<MethodId> {
        (**self).methods_on_type(type_def_id)
    }

    fn monomorph_instances(&self) -> Vec<vole_sema::generic::MonomorphInstance> {
        (**self).monomorph_instances()
    }

    fn class_method_monomorph_instances(
        &self,
    ) -> Vec<vole_sema::generic::ClassMethodMonomorphInstance> {
        (**self).class_method_monomorph_instances()
    }

    fn static_method_monomorph_instances(
        &self,
    ) -> Vec<vole_sema::generic::StaticMethodMonomorphInstance> {
        (**self).static_method_monomorph_instances()
    }
}

/// Lower global variable initializer expressions from the main program to VIR.
///
/// Iterates `Decl::Let` declarations and lowers each initializer expression
/// using `lower_expr`.  The resulting map is keyed by the binding's `Symbol`.
fn lower_global_inits(
    program: &Program,
    interner: &mut Interner,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    entities: &impl LoweringEntityLookup,
    names: &NameTable,
    type_table: &mut VirTypeTable,
) -> FxHashMap<Symbol, VirRef> {
    use vole_sema::vir_lower::LoweringCtx;
    use vole_sema::vir_lower::expr::lower_expr;

    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities: entities.as_entity_registry(),
        name_table: names,
        type_table,
        generic: false,
    };

    let mut map = FxHashMap::default();
    for decl in &program.declarations {
        if let Decl::Let(let_stmt) = decl
            && let LetInit::Expr(expr) = &let_stmt.init
        {
            // Only lower if sema analyzed the expression (has type info)
            if node_map.get_type(expr.id).is_some() {
                let vir = lower_expr(expr, &mut ctx);
                map.insert(let_stmt.name, vir);
            }
        }
    }
    map
}

/// Lower global variable initializer expressions from imported modules to VIR.
///
/// Iterates each module's `Decl::Let` declarations and lowers their
/// initializer expressions.  Returns a nested map keyed first by module path,
/// then by the binding's `Symbol`.
fn lower_module_global_inits(
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &NameTable,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    entities: &impl LoweringEntityLookup,
    modules_with_errors: &HashSet<String>,
    type_table: &mut VirTypeTable,
) -> FxHashMap<String, FxHashMap<Symbol, VirRef>> {
    use vole_sema::vir_lower::expr::lower_expr;

    let mut result = FxHashMap::default();
    for (module_path, (program, module_interner)) in module_programs.iter_mut() {
        if modules_with_errors.contains(module_path.as_str()) {
            continue;
        }
        let interner = Rc::make_mut(module_interner);
        let mut ctx = vole_sema::vir_lower::LoweringCtx {
            node_map,
            interner,
            type_arena,
            entities: entities.as_entity_registry(),
            name_table: names,
            type_table,
            generic: false,
        };

        let mut map = FxHashMap::default();
        for decl in &program.declarations {
            if let Decl::Let(let_stmt) = decl
                && let LetInit::Expr(expr) = &let_stmt.init
                && node_map.get_type(expr.id).is_some()
            {
                let vir = lower_expr(expr, &mut ctx);
                map.insert(let_stmt.name, vir);
            }
        }
        if !map.is_empty() {
            result.insert(module_path.clone(), map);
        }
    }
    result
}

/// Lower default parameter expressions for functions in the main program.
#[allow(clippy::too_many_arguments)]
fn lower_function_default_inits(
    program: &Program,
    interner: &mut Interner,
    module_id: ModuleId,
    tests_virtual_modules: &FxHashMap<Span, ModuleId>,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
) -> FxHashMap<(FunctionId, usize), VirRef> {
    let mut ctx = vole_sema::vir_lower::LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities: entities.as_entity_registry(),
        name_table: names,
        type_table,
        generic: false,
    };
    let mut map = FxHashMap::default();
    lower_function_default_inits_in_decls(
        &program.declarations,
        module_id,
        Some(tests_virtual_modules),
        names,
        entities,
        &mut ctx,
        &mut map,
    );
    map
}

/// Lower default parameter expressions for imported-module functions.
#[allow(clippy::too_many_arguments)]
fn lower_module_function_default_inits(
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    modules_with_errors: &HashSet<String>,
    type_table: &mut VirTypeTable,
) -> FxHashMap<(FunctionId, usize), VirRef> {
    let mut map = FxHashMap::default();
    for (module_path, (program, module_interner)) in module_programs.iter_mut() {
        if modules_with_errors.contains(module_path.as_str()) {
            continue;
        }
        let module_id = names
            .module_id_if_known(module_path)
            .unwrap_or_else(|| names.main_module());
        let interner = Rc::make_mut(module_interner);
        let mut ctx = vole_sema::vir_lower::LoweringCtx {
            node_map,
            interner,
            type_arena,
            entities: entities.as_entity_registry(),
            name_table: names,
            type_table,
            generic: false,
        };
        lower_function_default_inits_in_decls(
            &program.declarations,
            module_id,
            None,
            names,
            entities,
            &mut ctx,
            &mut map,
        );
    }
    map
}

/// Recursively lower function default parameter expressions in declarations.
fn lower_function_default_inits_in_decls(
    decls: &[Decl],
    module_id: ModuleId,
    tests_virtual_modules: Option<&FxHashMap<Span, ModuleId>>,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    ctx: &mut vole_sema::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<(FunctionId, usize), VirRef>,
) {
    for decl in decls {
        match decl {
            Decl::Function(func_decl) => {
                lower_function_default_params(func_decl, module_id, names, entities, ctx, map);
            }
            Decl::External(external_block) => {
                for external_func in &external_block.functions {
                    lower_external_function_default_params(
                        external_func,
                        module_id,
                        names,
                        entities,
                        ctx,
                        map,
                    );
                }
            }
            Decl::Tests(tests_decl) => {
                let tests_module_id = tests_virtual_modules
                    .and_then(|m| m.get(&tests_decl.span).copied())
                    .unwrap_or(module_id);
                lower_function_default_inits_in_decls(
                    &tests_decl.decls,
                    tests_module_id,
                    tests_virtual_modules,
                    names,
                    entities,
                    ctx,
                    map,
                );
            }
            _ => {}
        }
    }
}

/// Lower default parameter expressions for a single external function declaration.
fn lower_external_function_default_params(
    func: &vole_frontend::ast::ExternalFunc,
    module_id: ModuleId,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    ctx: &mut vole_sema::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<(FunctionId, usize), VirRef>,
) {
    use vole_sema::vir_lower::expr::lower_expr;

    let Some(name_id) = names.name_id(module_id, &[func.vole_name], ctx.interner) else {
        return;
    };
    let Some(func_id) = entities.function_by_name(name_id) else {
        return;
    };
    for (slot, param) in func.params.iter().enumerate() {
        let Some(default_expr) = param.default_value.as_ref() else {
            continue;
        };
        if ctx.node_map.get_type(default_expr.id).is_none() {
            continue;
        }
        let vir = lower_expr(default_expr, ctx);
        map.insert((func_id, slot), vir);
    }
}

/// Lower default parameter expressions for a single function declaration.
fn lower_function_default_params(
    func: &vole_frontend::ast::FuncDecl,
    module_id: ModuleId,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    ctx: &mut vole_sema::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<(FunctionId, usize), VirRef>,
) {
    use vole_sema::vir_lower::expr::lower_expr;

    let Some(name_id) = names.name_id(module_id, &[func.name], ctx.interner) else {
        return;
    };
    let Some(func_id) = entities.function_by_name(name_id) else {
        return;
    };
    for (slot, param) in func.params.iter().enumerate() {
        let Some(default_expr) = param.default_value.as_ref() else {
            continue;
        };
        if ctx.node_map.get_type(default_expr.id).is_none() {
            continue;
        }
        let vir = lower_expr(default_expr, ctx);
        map.insert((func_id, slot), vir);
    }
}

/// Lower default parameter expressions for methods in the main program.
#[allow(clippy::too_many_arguments)]
fn lower_method_default_inits(
    program: &Program,
    interner: &mut Interner,
    module_id: ModuleId,
    tests_virtual_modules: &FxHashMap<Span, ModuleId>,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
) -> FxHashMap<(MethodId, usize), VirRef> {
    let mut ctx = vole_sema::vir_lower::LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities: entities.as_entity_registry(),
        name_table: names,
        type_table,
        generic: false,
    };
    let mut map = FxHashMap::default();
    lower_method_default_inits_in_decls(
        &program.declarations,
        module_id,
        Some(tests_virtual_modules),
        names,
        entities,
        &mut ctx,
        &mut map,
    );
    map
}

/// Lower default parameter expressions for methods in imported modules.
#[allow(clippy::too_many_arguments)]
fn lower_module_method_default_inits(
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    modules_with_errors: &HashSet<String>,
    type_table: &mut VirTypeTable,
) -> FxHashMap<(MethodId, usize), VirRef> {
    let mut map = FxHashMap::default();
    for (module_path, (program, module_interner)) in module_programs.iter_mut() {
        if modules_with_errors.contains(module_path.as_str()) {
            continue;
        }
        let module_id = names
            .module_id_if_known(module_path)
            .unwrap_or_else(|| names.main_module());
        let interner = Rc::make_mut(module_interner);
        let mut ctx = vole_sema::vir_lower::LoweringCtx {
            node_map,
            interner,
            type_arena,
            entities: entities.as_entity_registry(),
            name_table: names,
            type_table,
            generic: false,
        };
        lower_method_default_inits_in_decls(
            &program.declarations,
            module_id,
            None,
            names,
            entities,
            &mut ctx,
            &mut map,
        );
    }
    map
}

/// Recursively lower method default parameter expressions in declarations.
fn lower_method_default_inits_in_decls(
    decls: &[Decl],
    module_id: ModuleId,
    tests_virtual_modules: Option<&FxHashMap<Span, ModuleId>>,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    ctx: &mut vole_sema::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<(MethodId, usize), VirRef>,
) {
    for decl in decls {
        match decl {
            Decl::Class(class_decl) => {
                lower_type_decl_method_default_inits(
                    class_decl.name,
                    &class_decl.methods,
                    class_decl.statics.as_ref(),
                    class_decl.external.as_ref().into_iter(),
                    module_id,
                    names,
                    entities,
                    ctx,
                    map,
                );
            }
            Decl::Struct(struct_decl) => {
                lower_type_decl_method_default_inits(
                    struct_decl.name,
                    &struct_decl.methods,
                    struct_decl.statics.as_ref(),
                    std::iter::empty(),
                    module_id,
                    names,
                    entities,
                    ctx,
                    map,
                );
            }
            Decl::Interface(iface_decl) => {
                lower_type_decl_method_default_inits(
                    iface_decl.name,
                    &[],
                    iface_decl.statics.as_ref(),
                    iface_decl.external_blocks.iter(),
                    module_id,
                    names,
                    entities,
                    ctx,
                    map,
                );
                lower_interface_method_decl_defaults(
                    iface_decl.name,
                    &iface_decl.methods,
                    false,
                    module_id,
                    names,
                    entities,
                    ctx,
                    map,
                );
            }
            Decl::Implement(impl_block) => {
                lower_implement_method_default_inits(
                    impl_block, module_id, names, entities, ctx, map,
                );
            }
            Decl::Tests(tests_decl) => {
                let tests_module_id = tests_virtual_modules
                    .and_then(|m| m.get(&tests_decl.span).copied())
                    .unwrap_or(module_id);
                lower_method_default_inits_in_decls(
                    &tests_decl.decls,
                    tests_module_id,
                    tests_virtual_modules,
                    names,
                    entities,
                    ctx,
                    map,
                );
            }
            _ => {}
        }
    }
}

/// Lower method default params for class/struct/interface type declarations.
#[allow(clippy::too_many_arguments)]
fn lower_type_decl_method_default_inits<'a>(
    type_name: Symbol,
    methods: &[vole_frontend::ast::FuncDecl],
    statics: Option<&vole_frontend::ast::StaticsBlock>,
    external_blocks: impl Iterator<Item = &'a vole_frontend::ast::ExternalBlock>,
    module_id: ModuleId,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    ctx: &mut vole_sema::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<(MethodId, usize), VirRef>,
) {
    let Some(type_name_id) = names.name_id(module_id, &[type_name], ctx.interner) else {
        return;
    };
    let Some(type_def_id) = entities.type_by_name(type_name_id) else {
        return;
    };

    for method in methods {
        if !method.type_params.is_empty() {
            continue;
        }
        let method_id = {
            let namer = NamerLookup::new(names, ctx.interner);
            let Some(method_name_id) = namer.method(method.name) else {
                continue;
            };
            entities.find_method_on_type(type_def_id, method_name_id)
        };
        let Some(method_id) = method_id else {
            continue;
        };
        lower_method_default_params(method_id, &method.params, ctx, map);
    }

    if let Some(statics) = statics {
        lower_interface_method_decl_defaults(
            type_name,
            &statics.methods,
            true,
            module_id,
            names,
            entities,
            ctx,
            map,
        );
        for external in &statics.external_blocks {
            lower_external_method_decl_defaults(
                type_def_id,
                &external.functions,
                true,
                names,
                ctx,
                entities,
                map,
            );
        }
    }

    for external in external_blocks {
        lower_external_method_decl_defaults(
            type_def_id,
            &external.functions,
            false,
            names,
            ctx,
            entities,
            map,
        );
    }
}

/// Lower method default params for interface-method AST nodes.
#[allow(clippy::too_many_arguments)]
fn lower_interface_method_decl_defaults(
    type_name: Symbol,
    methods: &[vole_frontend::ast::InterfaceMethod],
    is_static: bool,
    module_id: ModuleId,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    ctx: &mut vole_sema::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<(MethodId, usize), VirRef>,
) {
    let Some(type_name_id) = names.name_id(module_id, &[type_name], ctx.interner) else {
        return;
    };
    let Some(type_def_id) = entities.type_by_name(type_name_id) else {
        return;
    };
    for method in methods {
        if !method.type_params.is_empty() {
            continue;
        }
        let method_id = {
            let namer = NamerLookup::new(names, ctx.interner);
            let Some(method_name_id) = namer.method(method.name) else {
                continue;
            };
            if is_static {
                entities.find_static_method_on_type(type_def_id, method_name_id)
            } else {
                entities.find_method_on_type(type_def_id, method_name_id)
            }
        };
        let Some(method_id) = method_id else {
            continue;
        };
        lower_method_default_params(method_id, &method.params, ctx, map);
    }
}

/// Lower method default params for external-method AST nodes.
fn lower_external_method_decl_defaults(
    type_def_id: TypeDefId,
    funcs: &[vole_frontend::ast::ExternalFunc],
    is_static: bool,
    names: &NameTable,
    ctx: &mut vole_sema::vir_lower::LoweringCtx<'_>,
    entities: &impl LoweringEntityLookup,
    map: &mut FxHashMap<(MethodId, usize), VirRef>,
) {
    for func in funcs {
        if !func.type_params.is_empty() {
            continue;
        }
        let method_id = {
            let namer = NamerLookup::new(names, ctx.interner);
            let Some(method_name_id) = namer.method(func.vole_name) else {
                continue;
            };
            if is_static {
                entities.find_static_method_on_type(type_def_id, method_name_id)
            } else {
                entities.find_method_on_type(type_def_id, method_name_id)
            }
        };
        let Some(method_id) = method_id else {
            continue;
        };
        lower_method_default_params(method_id, &func.params, ctx, map);
    }
}

/// Lower method default params from an `implement` block.
fn lower_implement_method_default_inits(
    impl_block: &vole_frontend::ast::ImplementBlock,
    module_id: ModuleId,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    ctx: &mut vole_sema::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<(MethodId, usize), VirRef>,
) {
    let Some(type_def_id) = resolve_implement_target(
        &impl_block.target_type,
        ctx.interner,
        names,
        entities,
        module_id,
    ) else {
        return;
    };

    for method in &impl_block.methods {
        if !method.type_params.is_empty() {
            continue;
        }
        let method_id = {
            let namer = NamerLookup::new(names, ctx.interner);
            let Some(method_name_id) = namer.method(method.name) else {
                continue;
            };
            entities.find_method_on_type(type_def_id, method_name_id)
        };
        let Some(method_id) = method_id else {
            continue;
        };
        lower_method_default_params(method_id, &method.params, ctx, map);
    }
    if let Some(external) = impl_block.external.as_ref() {
        lower_external_method_decl_defaults(
            type_def_id,
            &external.functions,
            false,
            names,
            ctx,
            entities,
            map,
        );
    }
    if let Some(statics) = impl_block.statics.as_ref() {
        for method in &statics.methods {
            if !method.type_params.is_empty() {
                continue;
            }
            let method_id = {
                let namer = NamerLookup::new(names, ctx.interner);
                let Some(method_name_id) = namer.method(method.name) else {
                    continue;
                };
                entities.find_static_method_on_type(type_def_id, method_name_id)
            };
            let Some(method_id) = method_id else {
                continue;
            };
            lower_method_default_params(method_id, &method.params, ctx, map);
        }
        for external in &statics.external_blocks {
            lower_external_method_decl_defaults(
                type_def_id,
                &external.functions,
                true,
                names,
                ctx,
                entities,
                map,
            );
        }
    }
}

/// Lower default parameter expressions for a single method identifier.
fn lower_method_default_params(
    method_id: MethodId,
    params: &[vole_frontend::ast::Param],
    ctx: &mut vole_sema::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<(MethodId, usize), VirRef>,
) {
    use vole_sema::vir_lower::expr::lower_expr;

    for (slot, param) in params.iter().enumerate() {
        let Some(default_expr) = param.default_value.as_ref() else {
            continue;
        };
        let vir = lower_expr(default_expr, ctx);
        map.insert((method_id, slot), vir);
    }
}

/// Lower default parameter expressions for lambdas referenced by call-site
/// `LambdaDefaults` metadata.
#[allow(clippy::too_many_arguments)]
fn lower_lambda_default_inits(
    program: &Program,
    interner: &mut Interner,
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    main_module_id: ModuleId,
    tests_virtual_modules: &FxHashMap<Span, ModuleId>,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    modules_with_errors: &HashSet<String>,
    type_table: &mut VirTypeTable,
) -> FxHashMap<(vole_identity::NodeId, usize), VirRef> {
    let mut map = FxHashMap::default();
    let lambda_nodes = node_map.collect_lambda_default_nodes();
    if lambda_nodes.is_empty() {
        return map;
    }

    let mut main_module_ids = HashSet::<ModuleId>::default();
    let _ = main_module_ids.insert(main_module_id);
    let _ = main_module_ids.insert(names.main_module());
    main_module_ids.extend(tests_virtual_modules.values().copied());

    for lambda_node_id in lambda_nodes {
        if main_module_ids.contains(&lambda_node_id.module) {
            lower_single_lambda_default_init(
                lambda_node_id,
                program,
                interner,
                names,
                entities,
                node_map,
                type_arena,
                type_table,
                &mut map,
            );
            continue;
        }

        let module_path = names.module_path(lambda_node_id.module).to_string();
        if modules_with_errors.contains(&module_path) {
            continue;
        }
        let Some((module_program, module_interner)) = module_programs.get_mut(&module_path) else {
            continue;
        };
        let module_interner = Rc::make_mut(module_interner);
        lower_single_lambda_default_init(
            lambda_node_id,
            module_program,
            module_interner,
            names,
            entities,
            node_map,
            type_arena,
            type_table,
            &mut map,
        );
    }

    map
}

/// Lower default parameter expressions for a single lambda expression node.
#[allow(clippy::too_many_arguments)]
fn lower_single_lambda_default_init(
    lambda_node_id: vole_identity::NodeId,
    program: &Program,
    interner: &mut Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
    map: &mut FxHashMap<(vole_identity::NodeId, usize), VirRef>,
) {
    use crate::calls::find_lambda_in_program;
    use vole_sema::vir_lower::expr::lower_expr;

    let Some(lambda) = find_lambda_in_program(program, lambda_node_id) else {
        return;
    };

    let mut ctx = vole_sema::vir_lower::LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities: entities.as_entity_registry(),
        name_table: names,
        type_table,
        generic: false,
    };

    for (slot, param) in lambda.params.iter().enumerate() {
        let Some(default_expr) = param.default_value.as_ref() else {
            continue;
        };
        let vir = lower_expr(default_expr, &mut ctx);
        map.insert((lambda_node_id, slot), vir);
    }
}

/// Lower default field initializer expressions from main-program type declarations to VIR.
///
/// Includes declarations nested in `tests {}` blocks (using virtual test-module
/// IDs when available) so test-scoped types can use VIR default initializers.
#[allow(clippy::too_many_arguments)]
fn lower_field_default_inits(
    program: &Program,
    interner: &mut Interner,
    module_id: ModuleId,
    tests_virtual_modules: &FxHashMap<Span, ModuleId>,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    type_table: &mut VirTypeTable,
) -> FxHashMap<FieldId, VirRef> {
    use vole_sema::vir_lower::LoweringCtx;

    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities: entities.as_entity_registry(),
        name_table: names,
        type_table,
        generic: false,
    };
    let mut map = FxHashMap::default();
    lower_field_default_inits_in_decls(
        &program.declarations,
        module_id,
        Some(tests_virtual_modules),
        names,
        entities,
        &mut ctx,
        &mut map,
    );
    map
}

/// Lower default field initializer expressions from imported module type declarations to VIR.
#[allow(clippy::too_many_arguments)]
fn lower_module_field_default_inits(
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    modules_with_errors: &HashSet<String>,
    type_table: &mut VirTypeTable,
) -> FxHashMap<FieldId, VirRef> {
    let mut map = FxHashMap::default();
    for (module_path, (program, module_interner)) in module_programs.iter_mut() {
        if modules_with_errors.contains(module_path.as_str()) {
            continue;
        }
        let module_id = names
            .module_id_if_known(module_path)
            .unwrap_or_else(|| names.main_module());
        let interner = Rc::make_mut(module_interner);
        let mut ctx = vole_sema::vir_lower::LoweringCtx {
            node_map,
            interner,
            type_arena,
            entities: entities.as_entity_registry(),
            name_table: names,
            type_table,
            generic: false,
        };
        lower_field_default_inits_in_decls(
            &program.declarations,
            module_id,
            None,
            names,
            entities,
            &mut ctx,
            &mut map,
        );
    }
    map
}

/// Recursively lower default field initializer expressions in declarations.
fn lower_field_default_inits_in_decls(
    decls: &[Decl],
    module_id: ModuleId,
    tests_virtual_modules: Option<&FxHashMap<Span, ModuleId>>,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    ctx: &mut vole_sema::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<FieldId, VirRef>,
) {
    for decl in decls {
        match decl {
            Decl::Class(class_decl) => {
                lower_type_default_fields(
                    class_decl.name,
                    &class_decl.fields,
                    module_id,
                    names,
                    entities,
                    ctx,
                    map,
                );
            }
            Decl::Struct(struct_decl) => {
                lower_type_default_fields(
                    struct_decl.name,
                    &struct_decl.fields,
                    module_id,
                    names,
                    entities,
                    ctx,
                    map,
                );
            }
            Decl::Tests(tests_decl) => {
                let tests_module_id = tests_virtual_modules
                    .and_then(|m| m.get(&tests_decl.span).copied())
                    .unwrap_or(module_id);
                lower_field_default_inits_in_decls(
                    &tests_decl.decls,
                    tests_module_id,
                    tests_virtual_modules,
                    names,
                    entities,
                    ctx,
                    map,
                );
            }
            _ => {}
        }
    }
}

/// Lower default field initializers for a single class/struct declaration.
fn lower_type_default_fields(
    type_name: Symbol,
    fields: &[vole_frontend::ast::FieldDef],
    module_id: ModuleId,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    ctx: &mut vole_sema::vir_lower::LoweringCtx<'_>,
    map: &mut FxHashMap<FieldId, VirRef>,
) {
    use vole_sema::vir_lower::expr::lower_expr;

    let Some(type_name_id) = names.name_id(module_id, &[type_name], ctx.interner) else {
        return;
    };
    let Some(type_def_id) = entities.type_by_name(type_name_id) else {
        return;
    };
    let type_def = entities.get_type(type_def_id);
    for (slot, field) in fields.iter().enumerate() {
        let Some(default_expr) = field.default_value.as_ref() else {
            continue;
        };
        // Skip expressions sema never analyzed (e.g. parse/type errors).
        if ctx.node_map.get_type(default_expr.id).is_none() {
            continue;
        }
        let Some(&field_id) = type_def.fields.get(slot) else {
            continue;
        };
        let vir = lower_expr(default_expr, ctx);
        map.insert(field_id, vir);
    }
}

/// Lower top-level non-generic functions to VIR.
///
/// Iterates the program's declarations, looks up each non-generic function
/// in the entity registry, and calls `lower_function()` to produce a
/// `VirFunction`.  Generic functions and implicit generics are skipped
/// because they are monomorphized during codegen.
#[allow(clippy::too_many_arguments)]
fn lower_top_level_functions(
    program: &Program,
    interner: &mut Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    module_id: ModuleId,
    type_table: &mut VirTypeTable,
) -> Vec<VirFunction> {
    // Collect (func_decl, func_id, func_def) tuples first while interner is
    // borrowed immutably by NamerLookup, then lower with &mut interner.
    let resolved: Vec<_> = {
        let namer = NamerLookup::new(names, interner);
        program
            .declarations
            .iter()
            .filter_map(|decl| {
                let Decl::Function(func) = decl else {
                    return None;
                };
                if !func.type_params.is_empty() {
                    return None;
                }
                let name_id = namer.function(module_id, func.name)?;
                let func_id = entities.function_by_name(name_id)?;
                let func_def = entities.get_function(func_id);
                if func_def.generic_info.is_some() {
                    return None;
                }
                Some((func, func_id, func_def))
            })
            .collect()
    };

    let mut vir_functions = Vec::new();
    for (func, func_id, func_def) in resolved {
        let param_types: Vec<_> = func
            .params
            .iter()
            .zip(func_def.signature.params_id.iter())
            .map(|(p, &ty)| (p.name, ty))
            .collect();
        let display_name = interner.resolve(func.name).to_string();
        let vir = lower_function(
            func,
            func_id,
            display_name,
            &param_types,
            func_def.signature.return_type_id,
            node_map,
            interner,
            type_arena,
            entities.as_entity_registry(),
            names,
            type_table,
        );
        vir_functions.push(vir);
    }

    vir_functions
}

/// AST-based fallback for monomorphized instances not handled by VIR monomorph.
///
/// For each concrete instance in the monomorph cache, finds the generic
/// function's AST in the main program (`generic_func_asts`) or in module
/// programs and lowers it with the substituted (concrete) param and return
/// types from the instance's `func_type`.
///
/// Instances whose `original_name` resolves to a `FunctionId` in
/// `vir_handled_function_ids` are skipped -- those were already produced
/// by the VIR monomorphization pass.  The remaining instances (e.g.,
/// module-originating generics without VIR templates) are lowered here.
///
/// Debug-asserts that no `TypeId` in the output contains a type parameter.
#[allow(clippy::too_many_arguments)]
fn lower_monomorphized_instances(
    generic_func_asts: &FxHashMap<NameId, &vole_frontend::FuncDecl>,
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    modules_with_errors: &HashSet<String>,
    interner: &mut Interner,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
    vir_handled_function_ids: &HashSet<FunctionId>,
) {
    // Iterate all monomorphized instances in the cache
    for instance in entities.monomorph_instances() {
        // Skip instances already handled by VIR monomorphization.
        // VIR monomorph produced concrete functions for these via type
        // substitution on generic templates.
        if let Some(func_id) = entities.function_by_name(instance.original_name)
            && vir_handled_function_ids.contains(&func_id)
        {
            continue;
        }

        if let Some(func) = generic_func_asts.get(&instance.original_name) {
            // Found in the main program — lower with the main interner
            lower_single_monomorph(
                func,
                &instance,
                names,
                entities,
                type_arena,
                node_map,
                interner,
                vir_functions,
                type_table,
            );
            continue;
        }

        // Not in the main program — search module programs
        lower_module_monomorph(
            &instance,
            module_programs,
            names,
            entities,
            type_arena,
            node_map,
            modules_with_errors,
            vir_functions,
            type_table,
        );
    }
}

/// Shared references used while lowering class/static method monomorphs to VIR.
struct MethodMonomorphLoweringCtx<'a> {
    names: &'a NameTable,
    entities: &'a dyn LoweringEntityLookup,
    type_arena: &'a TypeArena,
    node_map: &'a NodeMap,
    modules_with_errors: &'a HashSet<String>,
}

/// Mutable state used while lowering class/static method monomorphs to VIR.
struct MethodMonomorphLoweringWork<'a> {
    program: &'a Program,
    interner: &'a mut Interner,
    module_programs: &'a mut FxHashMap<String, (Program, Rc<Interner>)>,
    tests_virtual_modules: &'a FxHashMap<Span, ModuleId>,
    module_id: ModuleId,
    vir_functions: &'a mut Vec<VirFunction>,
    type_table: &'a mut VirTypeTable,
}

/// Lower class/static method monomorph cache entries into VIR.
fn lower_type_method_monomorphized_instances(
    work: &mut MethodMonomorphLoweringWork<'_>,
    ctx: &MethodMonomorphLoweringCtx<'_>,
) {
    lower_class_method_monomorphized_instances(work, ctx);
    lower_static_method_monomorphized_instances(work, ctx);
}

/// Lower all class method monomorph instances into VIR.
///
/// Includes abstract templates (TypeParam substitutions) so expanded abstract
/// class method monomorph compilation can reuse their VIR bodies with concrete
/// substitutions.
fn lower_class_method_monomorphized_instances(
    work: &mut MethodMonomorphLoweringWork<'_>,
    ctx: &MethodMonomorphLoweringCtx<'_>,
) {
    let instances = ctx.entities.class_method_monomorph_instances();
    for instance in instances {
        // External methods are runtime calls and have no Vole body to lower.
        if instance.external_info.is_some() {
            continue;
        }

        let method_name = ctx.names.display(instance.method_name);

        if let Some(method) = find_class_method_in_decls(
            &work.program.declarations,
            instance.class_name,
            &method_name,
            work.module_id,
            work.interner,
            ctx.names,
            Some(work.tests_virtual_modules),
        ) {
            if let Some(vir) = lower_class_method_monomorph_vir(
                method,
                &instance,
                work.interner,
                ctx,
                work.type_table,
            ) {
                work.vir_functions.push(vir);
            }
            continue;
        }

        let source_module_id = ctx.names.module_of(instance.class_name);
        let source_module_path = ctx.names.module_path(source_module_id).to_string();
        if ctx.modules_with_errors.contains(&source_module_path) {
            continue;
        }
        let Some((module_program, module_interner)) =
            work.module_programs.get_mut(&source_module_path)
        else {
            continue;
        };

        if let Some(method) = find_class_method_in_decls(
            &module_program.declarations,
            instance.class_name,
            &method_name,
            source_module_id,
            module_interner.as_ref(),
            ctx.names,
            None,
        ) {
            let module_interner = Rc::make_mut(module_interner);
            if let Some(vir) = lower_class_method_monomorph_vir(
                method,
                &instance,
                module_interner,
                ctx,
                work.type_table,
            ) {
                work.vir_functions.push(vir);
            }
        }
    }
}

/// Lower all static method monomorph instances into VIR.
fn lower_static_method_monomorphized_instances(
    work: &mut MethodMonomorphLoweringWork<'_>,
    ctx: &MethodMonomorphLoweringCtx<'_>,
) {
    let instances = ctx.entities.static_method_monomorph_instances();
    for instance in instances {
        let method_name = ctx.names.display(instance.method_name);

        if let Some(method) = find_static_method_in_decls(
            &work.program.declarations,
            instance.class_name,
            &method_name,
            work.module_id,
            work.interner,
            ctx.names,
            Some(work.tests_virtual_modules),
        ) {
            if let Some(vir) = lower_static_method_monomorph_vir(
                method,
                &instance,
                work.interner,
                ctx,
                work.type_table,
            ) {
                work.vir_functions.push(vir);
            }
            continue;
        }

        let source_module_id = ctx.names.module_of(instance.class_name);
        let source_module_path = ctx.names.module_path(source_module_id).to_string();
        if ctx.modules_with_errors.contains(&source_module_path) {
            continue;
        }
        let Some((module_program, module_interner)) =
            work.module_programs.get_mut(&source_module_path)
        else {
            continue;
        };

        if let Some(method) = find_static_method_in_decls(
            &module_program.declarations,
            instance.class_name,
            &method_name,
            source_module_id,
            module_interner.as_ref(),
            ctx.names,
            None,
        ) {
            let module_interner = Rc::make_mut(module_interner);
            if let Some(vir) = lower_static_method_monomorph_vir(
                method,
                &instance,
                module_interner,
                ctx,
                work.type_table,
            ) {
                work.vir_functions.push(vir);
            }
        }
    }
}

/// Lower a single class method monomorph to a VIR function tagged by mangled name.
fn lower_class_method_monomorph_vir(
    method: &vole_frontend::FuncDecl,
    instance: &vole_sema::generic::ClassMethodMonomorphInstance,
    interner: &mut Interner,
    ctx: &MethodMonomorphLoweringCtx<'_>,
    type_table: &mut VirTypeTable,
) -> Option<VirFunction> {
    if method.params.len() != instance.func_type.params_id.len() {
        return None;
    }
    if !body_has_sema_data(&method.body, ctx.node_map) {
        return None;
    }
    let param_types: Vec<_> = method
        .params
        .iter()
        .zip(instance.func_type.params_id.iter())
        .map(|(p, &ty)| (p.name, ty))
        .collect();
    let mut vir = lower_method(
        method,
        MethodId::new(0),
        ctx.names.display(instance.mangled_name),
        &param_types,
        instance.func_type.return_type_id,
        ctx.node_map,
        interner,
        ctx.type_arena,
        ctx.entities.as_entity_registry(),
        ctx.names,
        type_table,
    );
    // Monomorphized method instances are looked up via mangled name map, not MethodId.
    vir.method_id = None;
    vir.mangled_name_id = Some(instance.mangled_name);
    Some(vir)
}

/// Lower a single static method monomorph to a VIR function tagged by mangled name.
fn lower_static_method_monomorph_vir(
    method: &vole_frontend::ast::InterfaceMethod,
    instance: &vole_sema::generic::StaticMethodMonomorphInstance,
    interner: &mut Interner,
    ctx: &MethodMonomorphLoweringCtx<'_>,
    type_table: &mut VirTypeTable,
) -> Option<VirFunction> {
    let body = method.body.as_ref()?;
    if method.params.len() != instance.func_type.params_id.len() {
        return None;
    }
    if !body_has_sema_data(body, ctx.node_map) {
        return None;
    }
    let param_types: Vec<_> = method
        .params
        .iter()
        .zip(instance.func_type.params_id.iter())
        .map(|(p, &ty)| (p.name, ty))
        .collect();
    let mut vir = lower_interface_method(
        method,
        MethodId::new(0),
        ctx.names.display(instance.mangled_name),
        &param_types,
        instance.func_type.return_type_id,
        ctx.node_map,
        interner,
        ctx.type_arena,
        ctx.entities.as_entity_registry(),
        ctx.names,
        type_table,
    )?;
    // Monomorphized method instances are looked up via mangled name map, not MethodId.
    vir.method_id = None;
    vir.mangled_name_id = Some(instance.mangled_name);
    Some(vir)
}

/// Find an instance method AST on a generic class/struct or matching implement block.
fn find_class_method_in_decls<'a>(
    decls: &'a [Decl],
    class_name_id: NameId,
    method_name: &str,
    module_id: ModuleId,
    interner: &Interner,
    names: &NameTable,
    tests_virtual_modules: Option<&FxHashMap<Span, ModuleId>>,
) -> Option<&'a vole_frontend::FuncDecl> {
    for decl in decls {
        match decl {
            Decl::Class(class) if !class.type_params.is_empty() => {
                let Some(name_id) = names.name_id(module_id, &[class.name], interner) else {
                    continue;
                };
                if name_id == class_name_id
                    && let Some(method) = class
                        .methods
                        .iter()
                        .find(|m| interner.resolve(m.name) == method_name)
                {
                    return Some(method);
                }
            }
            Decl::Struct(s) if !s.type_params.is_empty() => {
                let Some(name_id) = names.name_id(module_id, &[s.name], interner) else {
                    continue;
                };
                if name_id == class_name_id
                    && let Some(method) = s
                        .methods
                        .iter()
                        .find(|m| interner.resolve(m.name) == method_name)
                {
                    return Some(method);
                }
            }
            Decl::Implement(impl_block) => {
                use vole_frontend::TypeExprKind;
                let target_sym = match &impl_block.target_type.kind {
                    TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => {
                        Some(*sym)
                    }
                    _ => None,
                };
                let Some(target_sym) = target_sym else {
                    continue;
                };
                let Some(target_name_id) = names.name_id(module_id, &[target_sym], interner) else {
                    continue;
                };
                if target_name_id == class_name_id
                    && let Some(method) = impl_block
                        .methods
                        .iter()
                        .find(|m| interner.resolve(m.name) == method_name)
                {
                    return Some(method);
                }
            }
            Decl::Tests(tests_decl) => {
                let tests_module_id = tests_virtual_modules
                    .and_then(|m| m.get(&tests_decl.span).copied())
                    .unwrap_or(module_id);
                if let Some(method) = find_class_method_in_decls(
                    &tests_decl.decls,
                    class_name_id,
                    method_name,
                    tests_module_id,
                    interner,
                    names,
                    tests_virtual_modules,
                ) {
                    return Some(method);
                }
                if tests_module_id != module_id
                    && let Some(method) = find_class_method_in_decls(
                        &tests_decl.decls,
                        class_name_id,
                        method_name,
                        module_id,
                        interner,
                        names,
                        tests_virtual_modules,
                    )
                {
                    return Some(method);
                }
            }
            _ => {}
        }
    }
    None
}

/// Find a static method AST on a generic class/struct.
fn find_static_method_in_decls<'a>(
    decls: &'a [Decl],
    class_name_id: NameId,
    method_name: &str,
    module_id: ModuleId,
    interner: &Interner,
    names: &NameTable,
    tests_virtual_modules: Option<&FxHashMap<Span, ModuleId>>,
) -> Option<&'a vole_frontend::ast::InterfaceMethod> {
    for decl in decls {
        match decl {
            Decl::Class(class) if !class.type_params.is_empty() => {
                let Some(name_id) = names.name_id(module_id, &[class.name], interner) else {
                    continue;
                };
                if name_id == class_name_id
                    && let Some(statics) = class.statics.as_ref()
                    && let Some(method) = statics
                        .methods
                        .iter()
                        .find(|m| interner.resolve(m.name) == method_name)
                {
                    return Some(method);
                }
            }
            Decl::Struct(s) if !s.type_params.is_empty() => {
                let Some(name_id) = names.name_id(module_id, &[s.name], interner) else {
                    continue;
                };
                if name_id == class_name_id
                    && let Some(statics) = s.statics.as_ref()
                    && let Some(method) = statics
                        .methods
                        .iter()
                        .find(|m| interner.resolve(m.name) == method_name)
                {
                    return Some(method);
                }
            }
            Decl::Tests(tests_decl) => {
                let tests_module_id = tests_virtual_modules
                    .and_then(|m| m.get(&tests_decl.span).copied())
                    .unwrap_or(module_id);
                if let Some(method) = find_static_method_in_decls(
                    &tests_decl.decls,
                    class_name_id,
                    method_name,
                    tests_module_id,
                    interner,
                    names,
                    tests_virtual_modules,
                ) {
                    return Some(method);
                }
            }
            _ => {}
        }
    }
    None
}

/// Lower a single monomorphized instance whose AST is in the main program.
#[allow(clippy::too_many_arguments)]
fn lower_single_monomorph(
    func: &vole_frontend::FuncDecl,
    instance: &vole_sema::generic::MonomorphInstance,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    interner: &mut Interner,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let Some(func_id) = entities.function_by_name(instance.original_name) else {
        return;
    };
    let param_types: Vec<_> = func
        .params
        .iter()
        .zip(instance.func_type.params_id.iter())
        .map(|(p, &ty)| (p.name, ty))
        .collect();
    let mangled_name = names.display(instance.mangled_name);
    let vir = lower_monomorphized_function(
        func,
        func_id,
        mangled_name,
        &param_types,
        instance.func_type.return_type_id,
        node_map,
        type_arena,
        instance.mangled_name,
        interner,
        entities.as_entity_registry(),
        names,
        type_table,
    );
    vir_functions.push(vir);
}

/// Lower a single monomorphized instance whose AST originates from a module.
///
/// Resolves the module from `instance.original_name`, finds the generic
/// function AST in that module's program, and lowers it with the module's
/// interner.  Skips lowering if sema never analyzed the function body (i.e.,
/// the NodeMap has no entries for body nodes) — codegen falls back to the
/// AST path for those instances.
#[allow(clippy::too_many_arguments)]
fn lower_module_monomorph(
    instance: &vole_sema::generic::MonomorphInstance,
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    modules_with_errors: &HashSet<String>,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let Some(func_id) = entities.function_by_name(instance.original_name) else {
        return;
    };
    let module_id = names.module_of(instance.original_name);
    let module_path = names.module_path(module_id).to_string();
    if modules_with_errors.contains(&module_path) {
        return;
    }
    let Some((module_program, module_interner)) = module_programs.get_mut(&module_path) else {
        return;
    };
    let interner = Rc::make_mut(module_interner);

    // Find the generic function in the module by checking all function decls
    let func = module_program.declarations.iter().find_map(|decl| {
        let Decl::Function(func) = decl else {
            return None;
        };
        if func.type_params.is_empty() {
            return None;
        }
        let namer = NamerLookup::new(names, interner);
        let name_id = namer.function(module_id, func.name)?;
        if name_id == instance.original_name {
            Some(func)
        } else {
            None
        }
    });

    let Some(func) = func else { return };

    // Check if sema analyzed this function's body.  Generic function bodies
    // are skipped during initial module analysis and only analyzed later
    // during `analyze_monomorph_bodies`.  If the body was never analyzed,
    // the NodeMap won't have entries and VIR lowering would panic.
    if !body_has_sema_data(&func.body, node_map) {
        return;
    }

    let param_types: Vec<_> = func
        .params
        .iter()
        .zip(instance.func_type.params_id.iter())
        .map(|(p, &ty)| (p.name, ty))
        .collect();
    let mangled_name = names.display(instance.mangled_name);
    let vir = lower_monomorphized_function(
        func,
        func_id,
        mangled_name,
        &param_types,
        instance.func_type.return_type_id,
        node_map,
        type_arena,
        instance.mangled_name,
        interner,
        entities.as_entity_registry(),
        names,
        type_table,
    );
    vir_functions.push(vir);
}

/// Check whether sema has analyzed a function body by probing for NodeMap
/// entries.  Returns `true` if body node data exists, `false` otherwise.
///
/// Generic function bodies are skipped during initial sema analysis.  The
/// monomorph body analysis pass (`analyze_monomorph_bodies`) re-analyzes them
/// with concrete substitutions — for both main-program and module-originating
/// generics.  This check is a safety guard: if sema analysis failed to
/// populate the NodeMap for a body (e.g., due to errors), VIR lowering would
/// panic, so we skip and let codegen fall back to the AST path.
fn body_has_sema_data(body: &vole_frontend::ast::FuncBody, node_map: &NodeMap) -> bool {
    use vole_frontend::ast::FuncBody;
    match body {
        FuncBody::Expr(expr) => node_map.get_type(expr.id).is_some(),
        FuncBody::Block(block) => {
            // Check the first expression NodeId reachable from the first statement
            for stmt in &block.stmts {
                if let Some(node_id) = first_expr_node_id(stmt) {
                    return node_map.get_type(node_id).is_some();
                }
            }
            // Empty body — trivially analyzed
            true
        }
    }
}

/// Extract the first expression NodeId from a statement, if any.
fn first_expr_node_id(stmt: &vole_frontend::ast::Stmt) -> Option<vole_identity::NodeId> {
    use vole_frontend::ast::Stmt;
    match stmt {
        Stmt::Expr(s) => Some(s.expr.id),
        Stmt::Let(s) => s.init.as_expr().map(|e| e.id),
        Stmt::LetTuple(s) => Some(s.init.id),
        Stmt::If(s) => Some(s.condition.id),
        Stmt::While(s) => Some(s.condition.id),
        Stmt::For(s) => Some(s.iterable.id),
        Stmt::Return(s) => s.value.as_ref().map(|e| e.id),
        Stmt::Raise(_) => None,
        Stmt::Break(_) | Stmt::Continue(_) => None,
    }
}

/// Build a map from NameId to generic `FuncDecl` for the main program.
///
/// Includes both explicitly generic functions (those with type_params in AST)
/// and implicitly generic functions (those with generic_info in entity
/// registry, e.g. structural type params).  Recurses into `Decl::Tests`
/// blocks so that test-scoped generic functions are also available for
/// monomorphized VIR lowering.
fn build_generic_func_map<'decl>(
    program: &'decl Program,
    interner: &Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    tests_virtual_modules: &FxHashMap<Span, ModuleId>,
    module_id: ModuleId,
) -> FxHashMap<NameId, &'decl vole_frontend::FuncDecl> {
    let namer = NamerLookup::new(names, interner);
    let mut collector = GenericFuncCollector {
        namer: &namer,
        names,
        entities,
        tests_virtual_modules,
        root_module_id: module_id,
        map: FxHashMap::default(),
    };
    collector.collect(&program.declarations, module_id);
    collector.map
}

/// Collect generic function ASTs from declarations, including test-scoped
/// functions that live under virtual test modules.
struct GenericFuncCollector<'a, 'namer> {
    namer: &'namer NamerLookup<'namer>,
    names: &'namer NameTable,
    entities: &'namer dyn LoweringEntityLookup,
    tests_virtual_modules: &'namer FxHashMap<Span, ModuleId>,
    root_module_id: ModuleId,
    map: FxHashMap<NameId, &'a vole_frontend::FuncDecl>,
}

impl<'a, 'namer> GenericFuncCollector<'a, 'namer> {
    fn collect(&mut self, decls: &'a [Decl], module_id: ModuleId) {
        for decl in decls {
            match decl {
                Decl::Function(func) => {
                    // Include both explicit generics (`type_params`) and
                    // implicit generics (`generic_info`, e.g. structural constraints).
                    let module_candidates =
                        [module_id, self.root_module_id, self.names.main_module()];
                    for (idx, candidate_module) in module_candidates.into_iter().enumerate() {
                        if module_candidates[..idx].contains(&candidate_module) {
                            continue;
                        }
                        let Some(name_id) = self.namer.function(candidate_module, func.name) else {
                            continue;
                        };
                        let Some(func_id) = self.entities.function_by_name(name_id) else {
                            continue;
                        };
                        let is_generic = !func.type_params.is_empty()
                            || self.entities.get_function(func_id).generic_info.is_some();
                        if is_generic {
                            self.map.insert(name_id, func);
                        }
                    }
                }
                Decl::Tests(tests_decl) => {
                    let tests_module_id = self
                        .tests_virtual_modules
                        .get(&tests_decl.span)
                        .copied()
                        .unwrap_or(module_id);
                    self.collect(&tests_decl.decls, tests_module_id);
                }
                _ => {}
            }
        }
    }
}

/// Lower non-generic functions from imported modules to VIR.
///
/// Iterates each module's parsed program, resolves function identities through
/// the module's interner and module ID, and calls `lower_function()` for each
/// non-generic, non-implicitly-generic function.  Modules with sema errors are
/// skipped to avoid INVALID type IDs.
#[allow(clippy::too_many_arguments)]
fn lower_module_functions(
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    modules_with_errors: &HashSet<String>,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    for (module_path, (program, module_interner)) in module_programs.iter_mut() {
        if modules_with_errors.contains(module_path.as_str()) {
            continue;
        }
        let module_id = names
            .module_id_if_known(module_path)
            .unwrap_or_else(|| names.main_module());
        let interner = Rc::make_mut(module_interner);
        lower_module_program_functions(
            program,
            interner,
            names,
            entities,
            type_arena,
            node_map,
            module_id,
            vir_functions,
            type_table,
        );
    }
}

/// Lower non-generic functions from a single module program to VIR.
#[allow(clippy::too_many_arguments)]
fn lower_module_program_functions(
    program: &Program,
    interner: &mut Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    module_id: ModuleId,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let resolved: Vec<_> = {
        let namer = NamerLookup::new(names, interner);
        program
            .declarations
            .iter()
            .filter_map(|decl| {
                let Decl::Function(func) = decl else {
                    return None;
                };
                if !func.type_params.is_empty() {
                    return None;
                }
                let name_id = namer.function(module_id, func.name)?;
                let func_id = entities.function_by_name(name_id)?;
                let func_def = entities.get_function(func_id);
                if func_def.generic_info.is_some() {
                    return None;
                }
                Some((func, func_id, func_def))
            })
            .collect()
    };

    for (func, func_id, func_def) in resolved {
        let param_types: Vec<_> = func
            .params
            .iter()
            .zip(func_def.signature.params_id.iter())
            .map(|(p, &ty)| (p.name, ty))
            .collect();
        let display_name = interner.resolve(func.name).to_string();
        let vir = lower_function(
            func,
            func_id,
            display_name,
            &param_types,
            func_def.signature.return_type_id,
            node_map,
            interner,
            type_arena,
            entities.as_entity_registry(),
            names,
            type_table,
        );
        vir_functions.push(vir);
    }
}

/// Build a lookup map from monomorphized mangled NameId to VirFunction index.
///
/// Only includes VIR functions that have a `mangled_name_id` set (i.e.,
/// monomorphized instances).  Non-generic functions are not indexed here
/// because they are compiled via the normal (non-monomorph) path.
fn build_vir_monomorph_map(vir_functions: &[VirFunction]) -> FxHashMap<NameId, usize> {
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
fn build_vir_function_map(vir_functions: &[VirFunction]) -> FxHashMap<FunctionId, usize> {
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
fn build_vir_method_map(vir_functions: &[VirFunction]) -> FxHashMap<MethodId, usize> {
    let mut map = FxHashMap::default();
    for (idx, vf) in vir_functions.iter().enumerate() {
        if let Some(method_id) = vf.method_id {
            map.insert(method_id, idx);
        }
    }
    map
}

/// Lower non-generic class/struct instance methods and static methods to VIR.
///
/// Iterates the program's class and struct declarations, looks up each type's
/// methods in the entity registry, and lowers non-generic methods to VIR.
#[allow(clippy::too_many_arguments)]
fn lower_top_level_type_methods(
    program: &Program,
    interner: &mut Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    module_id: ModuleId,
    module_programs: Option<&FxHashMap<String, (Program, Rc<Interner>)>>,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    for decl in &program.declarations {
        match decl {
            Decl::Class(class) => {
                if !class.type_params.is_empty() {
                    continue;
                }
                lower_type_methods(
                    &class.methods,
                    class.statics.as_ref(),
                    class.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    module_id,
                    vir_functions,
                    type_table,
                );
                // Also lower default methods from implemented interfaces
                let direct_method_names: HashSet<String> = class
                    .methods
                    .iter()
                    .map(|m| interner.resolve(m.name).to_string())
                    .collect();
                lower_type_default_methods(
                    &direct_method_names,
                    class.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    module_id,
                    program,
                    module_programs,
                    vir_functions,
                    type_table,
                );
            }
            Decl::Struct(s) => {
                if !s.type_params.is_empty() {
                    continue;
                }
                lower_type_methods(
                    &s.methods,
                    s.statics.as_ref(),
                    s.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    module_id,
                    vir_functions,
                    type_table,
                );
                // Also lower default methods from implemented interfaces
                let direct_method_names: HashSet<String> = s
                    .methods
                    .iter()
                    .map(|m| interner.resolve(m.name).to_string())
                    .collect();
                lower_type_default_methods(
                    &direct_method_names,
                    s.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    module_id,
                    program,
                    module_programs,
                    vir_functions,
                    type_table,
                );
            }
            _ => {}
        }
    }
}

/// Lower instance methods and static methods for a single type declaration.
#[allow(clippy::too_many_arguments)]
fn lower_type_methods(
    methods: &[vole_frontend::FuncDecl],
    statics: Option<&vole_frontend::ast::StaticsBlock>,
    type_name: Symbol,
    interner: &mut Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    module_id: ModuleId,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    // Resolve all name lookups first while interner is borrowed immutably
    let (type_def_id, resolved_methods, resolved_statics) = {
        let namer = NamerLookup::new(names, interner);
        let Some(type_name_id) = names.name_id(module_id, &[type_name], interner) else {
            return;
        };
        let Some(type_def_id) = entities.type_by_name(type_name_id) else {
            return;
        };

        let resolved_methods: Vec<_> = methods
            .iter()
            .filter_map(|method| {
                if !method.type_params.is_empty() {
                    return None;
                }
                let method_name_id = namer.method(method.name)?;
                let mid = entities.find_method_on_type(type_def_id, method_name_id)?;
                let method_def = entities.get_method(mid);
                if !method_def.method_type_params.is_empty() {
                    return None;
                }
                Some((method, mid, method_def))
            })
            .collect();

        let resolved_statics: Vec<_> = statics
            .map(|s| {
                s.methods
                    .iter()
                    .filter_map(|method| {
                        if method.body.is_none() || !method.type_params.is_empty() {
                            return None;
                        }
                        let method_name_id = namer.method(method.name)?;
                        let mid =
                            entities.find_static_method_on_type(type_def_id, method_name_id)?;
                        let method_def = entities.get_method(mid);
                        if !method_def.method_type_params.is_empty() {
                            return None;
                        }
                        Some((method, mid, method_def))
                    })
                    .collect()
            })
            .unwrap_or_default();

        (type_def_id, resolved_methods, resolved_statics)
    };

    // Now lower with &mut interner (namer is dropped, no immutable borrow)
    let _ = type_def_id;
    let type_name_str = interner.resolve(type_name).to_string();

    for (method, mid, method_def) in resolved_methods {
        lower_single_method(
            method,
            mid,
            method_def,
            &type_name_str,
            interner,
            names,
            node_map,
            type_arena,
            entities,
            vir_functions,
            type_table,
        );
    }

    for (method, mid, method_def) in resolved_statics {
        let method_name_str = interner.resolve(method.name);
        let display_name = format!("{}::{}", type_name_str, method_name_str);
        let param_types: Vec<_> = method
            .params
            .iter()
            .map(|p| (p.name, vole_identity::TypeId::UNKNOWN))
            .collect();
        if let Some(vir) = lower_interface_method(
            method,
            mid,
            display_name,
            &param_types,
            method_def.signature_id,
            node_map,
            interner,
            type_arena,
            entities.as_entity_registry(),
            names,
            type_table,
        ) {
            vir_functions.push(vir);
        }
    }
}

/// Lower default methods from implemented interfaces for a class or struct.
///
/// Finds interface default methods inherited by `type_name` and lowers them to VIR.
/// Direct methods (explicitly defined on the type) are skipped since they override
/// the default. This covers default methods from the type's own `implements` clause,
/// as opposed to `lower_implement_default_methods` which covers `extend T with I` blocks.
#[allow(clippy::too_many_arguments)]
fn lower_type_default_methods(
    direct_method_names: &HashSet<String>,
    type_name: Symbol,
    interner: &mut Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    module_id: ModuleId,
    program: &Program,
    module_programs: Option<&FxHashMap<String, (Program, Rc<Interner>)>>,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    // Resolve type_def_id
    let Some(type_name_id) = names.name_id(module_id, &[type_name], interner) else {
        return;
    };
    let Some(type_def_id) = entities.type_by_name(type_name_id) else {
        return;
    };

    let type_name_str = interner.resolve(type_name).to_string();

    // Find default methods from implemented interfaces
    let default_methods =
        collect_default_method_ids(type_def_id, entities, names, direct_method_names);

    for (impl_method_id, method_name_str, interface_tdef_id) in default_methods {
        let iface_name_str = names
            .last_segment_str(entities.get_type(interface_tdef_id).name_id)
            .unwrap_or_default();
        let iface_method = find_interface_method_ast(
            &iface_name_str,
            &method_name_str,
            program,
            interner,
            module_programs,
        );
        let Some(iface_method) = iface_method else {
            continue;
        };

        let method_def = entities.get_method(impl_method_id);
        let display_name = format!("{}::{}", type_name_str, method_name_str);
        let param_types: Vec<_> = iface_method
            .params
            .iter()
            .map(|p| (p.name, vole_identity::TypeId::UNKNOWN))
            .collect();

        if let Some(vir) = lower_interface_method(
            iface_method,
            impl_method_id,
            display_name,
            &param_types,
            method_def.signature_id,
            node_map,
            interner,
            type_arena,
            entities.as_entity_registry(),
            names,
            type_table,
        ) {
            vir_functions.push(vir);
        }
    }
}

/// Lower a single instance method to VIR and push it onto the functions vec.
#[allow(clippy::too_many_arguments)]
fn lower_single_method(
    method: &vole_frontend::FuncDecl,
    method_id: MethodId,
    method_def: &vole_sema::MethodDef,
    type_name_str: &str,
    interner: &mut Interner,
    names: &NameTable,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    entities: &impl LoweringEntityLookup,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let arena_sig = method_def.signature_id;
    // We need the type arena to unwrap the signature, but we don't have it here.
    // Instead, use the AST param names + entity registry param types.
    // MethodDef doesn't store params_id directly, so we extract from signature.
    // Since we can't unwrap_function without the TypeArena, pass param names
    // paired with placeholder types (UNKNOWN).  VIR lowering embeds types from
    // sema's NodeMap, so the placeholder types are not used for codegen.
    let method_name_str = interner.resolve(method.name);
    let display_name = format!("{}::{}", type_name_str, method_name_str);

    // Create placeholder entries matching the AST params.
    let param_types: Vec<_> = method
        .params
        .iter()
        .map(|p| (p.name, vole_identity::TypeId::UNKNOWN))
        .collect();

    let vir = lower_method(
        method,
        method_id,
        display_name,
        &param_types,
        arena_sig, // return_type from entity registry
        node_map,
        interner,
        type_arena,
        entities.as_entity_registry(),
        names,
        type_table,
    );
    vir_functions.push(vir);
}

/// Lower non-generic type methods from imported modules to VIR.
///
/// Two passes: first lowers direct instance + static methods, then lowers
/// default methods from implemented interfaces.  The second pass needs
/// immutable access to `module_programs` for cross-module interface AST
/// lookup, so we collect per-type work items during the first (mutable) pass
/// and process them in a second (immutable) pass.
#[allow(clippy::too_many_arguments)]
fn lower_module_type_methods(
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    modules_with_errors: &HashSet<String>,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    // --- Pass 1: lower direct + static methods (needs &mut interner) ---
    // Also collect (module_path, type_name, direct_method_names) for pass 2.
    struct DefaultMethodWork {
        module_path: String,
        type_name: Symbol,
        direct_method_names: HashSet<String>,
    }
    let mut default_method_work: Vec<DefaultMethodWork> = Vec::new();

    for (module_path, (program, module_interner)) in module_programs.iter_mut() {
        if modules_with_errors.contains(module_path.as_str()) {
            continue;
        }
        let module_id = names
            .module_id_if_known(module_path)
            .unwrap_or_else(|| names.main_module());
        let interner = Rc::make_mut(module_interner);

        for decl in &program.declarations {
            match decl {
                Decl::Class(class) => {
                    if !class.type_params.is_empty() {
                        continue;
                    }
                    lower_type_methods(
                        &class.methods,
                        class.statics.as_ref(),
                        class.name,
                        interner,
                        names,
                        entities,
                        type_arena,
                        node_map,
                        module_id,
                        vir_functions,
                        type_table,
                    );
                    let direct_method_names: HashSet<String> = class
                        .methods
                        .iter()
                        .map(|m| interner.resolve(m.name).to_string())
                        .collect();
                    default_method_work.push(DefaultMethodWork {
                        module_path: module_path.clone(),
                        type_name: class.name,
                        direct_method_names,
                    });
                }
                Decl::Struct(s) => {
                    if !s.type_params.is_empty() {
                        continue;
                    }
                    lower_type_methods(
                        &s.methods,
                        s.statics.as_ref(),
                        s.name,
                        interner,
                        names,
                        entities,
                        type_arena,
                        node_map,
                        module_id,
                        vir_functions,
                        type_table,
                    );
                    let direct_method_names: HashSet<String> = s
                        .methods
                        .iter()
                        .map(|m| interner.resolve(m.name).to_string())
                        .collect();
                    default_method_work.push(DefaultMethodWork {
                        module_path: module_path.clone(),
                        type_name: s.name,
                        direct_method_names,
                    });
                }
                _ => {}
            }
        }
    }

    // --- Pass 2: lower default methods from interfaces (needs shared module_programs) ---
    for work in default_method_work {
        let Some((program, module_interner)) = module_programs.get_mut(&work.module_path) else {
            continue;
        };
        let module_id = names
            .module_id_if_known(&work.module_path)
            .unwrap_or_else(|| names.main_module());
        let interner = Rc::make_mut(module_interner);

        // For module types, pass only the module's own program for interface lookup.
        // Cross-module interface lookup is not available here (borrow limitation),
        // but module types typically implement interfaces defined in the same module
        // or in the stdlib (which is also in module_programs).  The implement-block
        // lowering handles cross-module cases separately.
        lower_type_default_methods(
            &work.direct_method_names,
            work.type_name,
            interner,
            names,
            entities,
            type_arena,
            node_map,
            module_id,
            program,
            None, // cross-module lookup not available in this pass
            vir_functions,
            type_table,
        );
    }
}

/// Lower type methods for classes/structs declared inside test blocks.
///
/// Test blocks can contain `Decl::Class` and `Decl::Struct` declarations that
/// are scoped to a virtual module.  This function recursively walks `Decl::Tests`
/// blocks and lowers their class/struct methods (direct + default) to VIR.
#[allow(clippy::too_many_arguments)]
fn lower_test_scoped_type_methods(
    program: &Program,
    interner: &mut Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    tests_virtual_modules: &FxHashMap<Span, ModuleId>,
    module_programs: Option<&FxHashMap<String, (Program, Rc<Interner>)>>,
    module_id: ModuleId,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    for decl in &program.declarations {
        if let Decl::Tests(tests_decl) = decl {
            lower_tests_decl_type_methods(
                tests_decl,
                program,
                interner,
                names,
                entities,
                type_arena,
                node_map,
                tests_virtual_modules,
                module_programs,
                module_id,
                vir_functions,
                type_table,
            );
        }
    }
}

/// Recursively lower type methods from a single `TestsDecl`.
#[allow(clippy::too_many_arguments)]
fn lower_tests_decl_type_methods(
    tests_decl: &vole_frontend::ast::TestsDecl,
    program: &Program,
    interner: &mut Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    tests_virtual_modules: &FxHashMap<Span, ModuleId>,
    module_programs: Option<&FxHashMap<String, (Program, Rc<Interner>)>>,
    module_id: ModuleId,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let virtual_module_id = tests_virtual_modules
        .get(&tests_decl.span)
        .copied()
        .unwrap_or_else(|| names.main_module());

    // Test-scoped functions are registered under the program's module_id (not the virtual
    // test module), so use the passed module_id for function name resolution. This must
    // match what codegen uses in compile_function (program_module = analyzed.module_id).
    let main_module_id = module_id;

    for inner_decl in &tests_decl.decls {
        match inner_decl {
            Decl::Function(func) => {
                if !func.type_params.is_empty() {
                    continue;
                }
                // Resolve the function in the main module (test-scoped functions use
                // program_module for name resolution, same as top-level functions)
                let func_id_and_def = {
                    let namer = NamerLookup::new(names, interner);
                    let name_id = namer.function(main_module_id, func.name);
                    name_id.and_then(|nid| {
                        let fid = entities.function_by_name(nid)?;
                        let fdef = entities.get_function(fid);
                        if fdef.generic_info.is_some() {
                            return None;
                        }
                        Some((fid, fdef))
                    })
                };
                if let Some((func_id, func_def)) = func_id_and_def {
                    let param_types: Vec<_> = func
                        .params
                        .iter()
                        .zip(func_def.signature.params_id.iter())
                        .map(|(p, &ty)| (p.name, ty))
                        .collect();
                    let vir = lower_function(
                        func,
                        func_id,
                        interner.resolve(func.name).to_string(),
                        &param_types,
                        func_def.signature.return_type_id,
                        node_map,
                        interner,
                        type_arena,
                        entities.as_entity_registry(),
                        names,
                        type_table,
                    );
                    vir_functions.push(vir);
                }
            }
            Decl::Class(class) => {
                if !class.type_params.is_empty() {
                    continue;
                }
                lower_type_methods(
                    &class.methods,
                    class.statics.as_ref(),
                    class.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    virtual_module_id,
                    vir_functions,
                    type_table,
                );
                let direct_method_names: HashSet<String> = class
                    .methods
                    .iter()
                    .map(|m| interner.resolve(m.name).to_string())
                    .collect();
                lower_type_default_methods(
                    &direct_method_names,
                    class.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    virtual_module_id,
                    program,
                    module_programs,
                    vir_functions,
                    type_table,
                );
            }
            Decl::Struct(s) => {
                if !s.type_params.is_empty() {
                    continue;
                }
                lower_type_methods(
                    &s.methods,
                    s.statics.as_ref(),
                    s.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    virtual_module_id,
                    vir_functions,
                    type_table,
                );
                let direct_method_names: HashSet<String> = s
                    .methods
                    .iter()
                    .map(|m| interner.resolve(m.name).to_string())
                    .collect();
                lower_type_default_methods(
                    &direct_method_names,
                    s.name,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    virtual_module_id,
                    program,
                    module_programs,
                    vir_functions,
                    type_table,
                );
            }
            Decl::Implement(impl_block) => {
                let type_def_id = resolve_implement_target(
                    &impl_block.target_type,
                    interner,
                    names,
                    entities,
                    virtual_module_id,
                );
                if let Some(type_def_id) = type_def_id {
                    lower_implement_direct_methods(
                        &impl_block.methods,
                        type_def_id,
                        interner,
                        names,
                        entities,
                        type_arena,
                        node_map,
                        vir_functions,
                        type_table,
                    );
                    if let Some(ref statics) = impl_block.statics {
                        lower_implement_static_methods(
                            statics,
                            type_def_id,
                            interner,
                            names,
                            entities,
                            type_arena,
                            node_map,
                            vir_functions,
                            type_table,
                        );
                    }
                    lower_implement_default_methods(
                        impl_block,
                        type_def_id,
                        interner,
                        names,
                        entities,
                        type_arena,
                        node_map,
                        virtual_module_id,
                        program,
                        module_programs,
                        vir_functions,
                        type_table,
                    );
                }
            }
            Decl::Tests(nested) => {
                lower_tests_decl_type_methods(
                    nested,
                    program,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    tests_virtual_modules,
                    module_programs,
                    module_id,
                    vir_functions,
                    type_table,
                );
            }
            _ => {}
        }
    }
}

/// Lower all test function bodies in the program to VIR.
///
/// Walks the program's `Decl::Tests` blocks (including nested ones) and
/// lowers each `TestCase.body` to a `VirBody`.  Returns a map keyed by
/// the `TestCase`'s `Span` for O(1) lookup during test compilation.
fn lower_test_bodies(
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

/// Lower implement block methods (direct + statics) to VIR.
///
/// Iterates `Decl::Implement` blocks in the main program, resolves each
/// method's `MethodId` from the entity registry, and lowers the body.
/// Default interface methods (not in the implement block AST) are handled
/// by [`lower_implement_default_methods`].
#[allow(clippy::too_many_arguments)]
fn lower_implement_block_methods(
    program: &Program,
    interner: &mut Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    module_id: ModuleId,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    for decl in &program.declarations {
        let Decl::Implement(impl_block) = decl else {
            continue;
        };
        lower_single_implement_block(
            impl_block,
            interner,
            names,
            entities,
            type_arena,
            node_map,
            module_id,
            program,
            vir_functions,
            type_table,
        );
    }
}

/// Lower a single implement block's direct methods and statics to VIR.
#[allow(clippy::too_many_arguments)]
fn lower_single_implement_block(
    impl_block: &vole_frontend::ast::ImplementBlock,
    interner: &mut Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    module_id: ModuleId,
    program: &Program,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let Some(type_def_id) = resolve_implement_target(
        &impl_block.target_type,
        interner,
        names,
        entities,
        module_id,
    ) else {
        return;
    };

    // Lower direct instance methods
    lower_implement_direct_methods(
        &impl_block.methods,
        type_def_id,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        vir_functions,
        type_table,
    );

    // Lower static methods
    if let Some(ref statics) = impl_block.statics {
        lower_implement_static_methods(
            statics,
            type_def_id,
            interner,
            names,
            entities,
            type_arena,
            node_map,
            vir_functions,
            type_table,
        );
    }

    // Lower interface default methods (inherited, not overridden)
    lower_implement_default_methods(
        impl_block,
        type_def_id,
        interner,
        names,
        entities,
        type_arena,
        node_map,
        module_id,
        program,
        None,
        vir_functions,
        type_table,
    );
}

/// Resolve the target type of an implement block to a `TypeDefId`.
///
/// Handles `Named`, `Generic`, `Primitive`, `Handle`, and `Array` target types.
fn resolve_implement_target(
    target_type: &vole_frontend::TypeExpr,
    interner: &Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    module_id: ModuleId,
) -> Option<TypeDefId> {
    use vole_frontend::TypeExprKind;
    match &target_type.kind {
        TypeExprKind::Named(sym) | TypeExprKind::Generic { name: sym, .. } => {
            // Try normal module-scoped lookup first (class/struct types)
            if let Some(name_id) = names.name_id(module_id, &[*sym], interner)
                && let Some(tdef) = entities.type_by_name(name_id)
            {
                return Some(tdef);
            }
            // Fall back to short-name lookup for named primitives (e.g. "range")
            let sym_str = interner.resolve(*sym);
            entities.type_by_short_name(sym_str, names)
        }
        TypeExprKind::Primitive(p) => {
            let prim_name = match p {
                vole_frontend::PrimitiveType::I8 => "i8",
                vole_frontend::PrimitiveType::I16 => "i16",
                vole_frontend::PrimitiveType::I32 => "i32",
                vole_frontend::PrimitiveType::I64 => "i64",
                vole_frontend::PrimitiveType::I128 => "i128",
                vole_frontend::PrimitiveType::U8 => "u8",
                vole_frontend::PrimitiveType::U16 => "u16",
                vole_frontend::PrimitiveType::U32 => "u32",
                vole_frontend::PrimitiveType::U64 => "u64",
                vole_frontend::PrimitiveType::F32 => "f32",
                vole_frontend::PrimitiveType::F64 => "f64",
                vole_frontend::PrimitiveType::F128 => "f128",
                vole_frontend::PrimitiveType::Bool => "bool",
                vole_frontend::PrimitiveType::String => "string",
            };
            entities.type_by_short_name(prim_name, names)
        }
        TypeExprKind::Handle => entities.type_by_short_name("handle", names),
        TypeExprKind::Array(_) => entities
            .array_name_id()
            .and_then(|n| entities.type_by_name(n)),
        _ => None,
    }
}

/// Lower direct instance methods from an implement block to VIR.
#[allow(clippy::too_many_arguments)]
fn lower_implement_direct_methods(
    methods: &[vole_frontend::FuncDecl],
    type_def_id: TypeDefId,
    interner: &mut Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let type_name_str = names
        .last_segment_str(entities.get_type(type_def_id).name_id)
        .unwrap_or_default();

    // Resolve all methods first while interner is borrowed immutably
    let resolved: Vec<_> = {
        let namer = NamerLookup::new(names, interner);
        methods
            .iter()
            .filter_map(|method| {
                if !method.type_params.is_empty() {
                    return None;
                }
                let method_name_id = namer.method(method.name)?;
                let mid = entities.find_method_on_type(type_def_id, method_name_id)?;
                let method_def = entities.get_method(mid);
                if !method_def.method_type_params.is_empty() {
                    return None;
                }
                Some((method, mid, method_def))
            })
            .collect()
    };

    for (method, mid, method_def) in resolved {
        let method_name_str = interner.resolve(method.name);
        let display_name = format!("{}::{}", type_name_str, method_name_str);
        let param_types: Vec<_> = method
            .params
            .iter()
            .map(|p| (p.name, vole_identity::TypeId::UNKNOWN))
            .collect();

        let vir = lower_method(
            method,
            mid,
            display_name,
            &param_types,
            method_def.signature_id,
            node_map,
            interner,
            type_arena,
            entities.as_entity_registry(),
            names,
            type_table,
        );
        vir_functions.push(vir);
    }
}

/// Lower static methods from an implement block's statics section to VIR.
#[allow(clippy::too_many_arguments)]
fn lower_implement_static_methods(
    statics: &vole_frontend::ast::StaticsBlock,
    type_def_id: TypeDefId,
    interner: &mut Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let type_name_str = names
        .last_segment_str(entities.get_type(type_def_id).name_id)
        .unwrap_or_default();

    let resolved: Vec<_> = {
        let namer = NamerLookup::new(names, interner);
        statics
            .methods
            .iter()
            .filter_map(|method| {
                if method.body.is_none() || !method.type_params.is_empty() {
                    return None;
                }
                let method_name_id = namer.method(method.name)?;
                let mid = entities.find_static_method_on_type(type_def_id, method_name_id)?;
                let method_def = entities.get_method(mid);
                if !method_def.method_type_params.is_empty() {
                    return None;
                }
                Some((method, mid, method_def))
            })
            .collect()
    };

    for (method, mid, method_def) in resolved {
        let method_name_str = interner.resolve(method.name);
        let display_name = format!("{}::{}", type_name_str, method_name_str);
        let param_types: Vec<_> = method
            .params
            .iter()
            .map(|p| (p.name, vole_identity::TypeId::UNKNOWN))
            .collect();
        if let Some(vir) = lower_interface_method(
            method,
            mid,
            display_name,
            &param_types,
            method_def.signature_id,
            node_map,
            interner,
            type_arena,
            entities.as_entity_registry(),
            names,
            type_table,
        ) {
            vir_functions.push(vir);
        }
    }
}

/// Lower interface default methods for an implement block.
///
/// Finds default methods from implemented interfaces that are NOT overridden
/// by the implement block's direct methods. For each such default method,
/// locates the interface's AST body and lowers it with the implementing
/// type's MethodId.
#[allow(clippy::too_many_arguments)]
fn lower_implement_default_methods(
    impl_block: &vole_frontend::ast::ImplementBlock,
    type_def_id: TypeDefId,
    interner: &mut Interner,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    _module_id: ModuleId,
    program: &Program,
    module_programs: Option<&FxHashMap<String, (Program, Rc<Interner>)>>,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    let type_name_str = names
        .last_segment_str(entities.get_type(type_def_id).name_id)
        .unwrap_or_default();

    // Collect direct method names to skip
    let direct_method_names: HashSet<String> = impl_block
        .methods
        .iter()
        .map(|m| interner.resolve(m.name).to_string())
        .collect();

    // Find default methods from implemented interfaces
    let default_methods =
        collect_default_method_ids(type_def_id, entities, names, &direct_method_names);

    for (impl_method_id, method_name_str, interface_tdef_id) in default_methods {
        // Find the interface AST method body
        let iface_name_str = names
            .last_segment_str(entities.get_type(interface_tdef_id).name_id)
            .unwrap_or_default();
        let iface_method = find_interface_method_ast(
            &iface_name_str,
            &method_name_str,
            program,
            interner,
            module_programs,
        );
        let Some(iface_method) = iface_method else {
            continue;
        };

        let method_def = entities.get_method(impl_method_id);
        let display_name = format!("{}::{}", type_name_str, method_name_str);
        let param_types: Vec<_> = iface_method
            .params
            .iter()
            .map(|p| (p.name, vole_identity::TypeId::UNKNOWN))
            .collect();

        // Use lower_interface_method since the AST is an InterfaceMethod
        if let Some(vir) = lower_interface_method(
            iface_method,
            impl_method_id,
            display_name,
            &param_types,
            method_def.signature_id,
            node_map,
            interner,
            type_arena,
            entities.as_entity_registry(),
            names,
            type_table,
        ) {
            vir_functions.push(vir);
        }
    }
}

/// Collect interface default method IDs for a type, skipping overridden ones.
///
/// Returns `(impl_method_id, method_name_str, interface_tdef_id)` tuples.
fn collect_default_method_ids(
    type_def_id: TypeDefId,
    entities: &impl LoweringEntityLookup,
    names: &NameTable,
    direct_method_names: &HashSet<String>,
) -> Vec<(MethodId, String, TypeDefId)> {
    let mut results = Vec::new();
    for interface_tdef_id in entities.get_implemented_interfaces(type_def_id) {
        // Note: we intentionally do NOT skip interfaces with abstract type params
        // (e.g. Iterable<T> on [T]). The VIR body is the same regardless of T —
        // substitutions are applied at compile time by passing `concrete_subs`.
        // Skipping abstract params would leave array Iterable default methods
        // without VIR bodies.

        for iface_method_id in entities.methods_on_type(interface_tdef_id) {
            let method_def = entities.get_method(iface_method_id);
            if !method_def.has_default || method_def.external_binding.is_some() {
                continue;
            }
            let method_name_str = names
                .last_segment_str(method_def.name_id)
                .unwrap_or_default();
            if direct_method_names.contains(&method_name_str) {
                continue;
            }
            if let Some(impl_method_id) =
                entities.find_method_on_type(type_def_id, method_def.name_id)
            {
                results.push((impl_method_id, method_name_str, interface_tdef_id));
            }
        }
    }
    results
}

/// Find an interface method's AST node by interface and method name.
///
/// Searches the main program and optionally module programs for the
/// interface declaration, then finds the default method with a body.
fn find_interface_method_ast<'a>(
    interface_name: &str,
    method_name: &str,
    program: &'a Program,
    interner: &Interner,
    module_programs: Option<&'a FxHashMap<String, (Program, Rc<Interner>)>>,
) -> Option<&'a vole_frontend::ast::InterfaceMethod> {
    // Search main program using the main interner
    for decl in &program.declarations {
        if let Decl::Interface(iface) = decl {
            if interner.resolve(iface.name) != interface_name {
                continue;
            }
            for method in &iface.methods {
                if interner.resolve(method.name) == method_name && method.body.is_some() {
                    return Some(method);
                }
            }
        }
    }

    // Search module programs using their interners
    if let Some(module_programs) = module_programs {
        for (program, module_interner) in module_programs.values() {
            for decl in &program.declarations {
                if let Decl::Interface(iface) = decl {
                    if module_interner.resolve(iface.name) != interface_name {
                        continue;
                    }
                    for method in &iface.methods {
                        if module_interner.resolve(method.name) == method_name
                            && method.body.is_some()
                        {
                            return Some(method);
                        }
                    }
                }
            }
        }
    }

    None
}

/// Lower implement block methods from imported modules to VIR.
///
/// Two passes: first lowers direct instance + static methods, then lowers
/// default methods from implemented interfaces.  The second pass needs
/// immutable access to `module_programs` for cross-module interface AST
/// lookup, so we collect per-block work items during the first pass.
#[allow(clippy::too_many_arguments)]
fn lower_module_implement_block_methods(
    module_programs: &mut FxHashMap<String, (Program, Rc<Interner>)>,
    names: &NameTable,
    entities: &impl LoweringEntityLookup,
    type_arena: &TypeArena,
    node_map: &NodeMap,
    modules_with_errors: &HashSet<String>,
    vir_functions: &mut Vec<VirFunction>,
    type_table: &mut VirTypeTable,
) {
    // --- Pass 1: lower direct + static methods, collect default method work items ---
    struct ImplDefaultWork {
        module_path: String,
        /// Index of the Decl::Implement within the module's declarations.
        impl_decl_index: usize,
        type_def_id: TypeDefId,
    }
    let mut default_work: Vec<ImplDefaultWork> = Vec::new();

    for (module_path, (program, module_interner)) in module_programs.iter_mut() {
        if modules_with_errors.contains(module_path.as_str()) {
            continue;
        }
        let module_id = names
            .module_id_if_known(module_path)
            .unwrap_or_else(|| names.main_module());
        let interner = Rc::make_mut(module_interner);

        for (decl_idx, decl) in program.declarations.iter().enumerate() {
            let Decl::Implement(impl_block) = decl else {
                continue;
            };
            let Some(type_def_id) = resolve_implement_target(
                &impl_block.target_type,
                interner,
                names,
                entities,
                module_id,
            ) else {
                continue;
            };

            lower_implement_direct_methods(
                &impl_block.methods,
                type_def_id,
                interner,
                names,
                entities,
                type_arena,
                node_map,
                vir_functions,
                type_table,
            );

            if let Some(ref statics) = impl_block.statics {
                lower_implement_static_methods(
                    statics,
                    type_def_id,
                    interner,
                    names,
                    entities,
                    type_arena,
                    node_map,
                    vir_functions,
                    type_table,
                );
            }

            default_work.push(ImplDefaultWork {
                module_path: module_path.clone(),
                impl_decl_index: decl_idx,
                type_def_id,
            });
        }
    }

    // --- Pass 2: lower default methods from interfaces ---
    // We need both &mut Interner (for the current module) and &module_programs
    // (for cross-module interface AST lookup). Clone the Rc<Interner> so we can
    // borrow module_programs immutably while mutating our own copy.
    for work in default_work {
        let module_id = names
            .module_id_if_known(&work.module_path)
            .unwrap_or_else(|| names.main_module());

        // Clone the Rc<Interner> so we can mutate it independently
        let Some((program, module_interner_rc)) = module_programs.get(&work.module_path) else {
            continue;
        };
        let mut interner_clone = (**module_interner_rc).clone();

        // Re-extract the implement block from the known index
        let Decl::Implement(impl_block) = &program.declarations[work.impl_decl_index] else {
            continue;
        };

        lower_implement_default_methods(
            impl_block,
            work.type_def_id,
            &mut interner_clone,
            names,
            entities,
            type_arena,
            node_map,
            module_id,
            program,
            Some(module_programs),
            vir_functions,
            type_table,
        );
    }
}

/// Build generic VIR storage with VirTypeId remapping.
///
/// Like `build_generic_vir_storage` but applies a VirTypeId remapping to
/// each generic function template.  This is needed because generic templates
/// are lowered with their own type table (in sema Pass 2a) and their
/// VirTypeIds must be translated to the program's main type table.
fn build_generic_vir_storage_remapped(
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
fn run_early_vir_monomorphize(
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
fn run_vir_monomorphize(program: &mut VirProgram) {
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
