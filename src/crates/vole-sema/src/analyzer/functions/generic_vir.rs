// src/sema/analyzer/functions/generic_vir.rs
//! Pass 2a: Analyze generic function bodies with abstract type params and
//! lower them to VIR templates.
//!
//! The NodeMap entries used for lowering contain abstract TypeParam types
//! (identity substitutions), not concrete types from any specific instance.
//!
//! The resulting `VirFunction` templates preserve `VirType::Param` for type
//! parameters and are consumed by the VIR monomorph pass
//! (`vole_vir::monomorph`) which produces concrete instantiations via type
//! substitution.

use super::super::*;
use vole_vir::func::VirFunction;
use vole_vir::type_table::VirTypeTable;

impl Analyzer {
    /// Analyze generic function bodies with identity substitutions and lower
    /// each to a VIR template.
    ///
    /// For each generic function in the main program:
    /// 1. Analyzes the body with abstract TypeParam types (identity subs)
    /// 2. Immediately lowers to VIR with `generic: true` mode
    /// 3. Collects `(original_name, VirFunction)` pairs
    ///
    /// Returns the collected generic VIR functions.  These are stored in
    /// `AnalysisOutput.generic_vir_functions` and later moved into
    /// `AnalyzedProgram.generic_vir_functions`.
    pub(in crate::analyzer) fn lower_generic_bodies_to_vir(
        &mut self,
        program: &Program,
        interner: &Interner,
    ) -> (Vec<(NameId, VirFunction)>, VirTypeTable) {
        let mut generic_func_asts: FxHashMap<NameId, &FuncDecl> = FxHashMap::default();
        self.collect_generic_func_asts(&program.declarations, interner, &mut generic_func_asts);

        // Snapshot the monomorph cache keys that exist BEFORE generic analysis.
        // Pass 2 may have already created entries with TypeParam keys (from class
        // method body checking); those must be preserved for Pass 2.5 propagation.
        let pre_existing_keys: HashSet<MonomorphKey> = self
            .entity_registry()
            .monomorph_cache
            .instances()
            .map(|(k, _)| k.clone())
            .collect();

        let entries: Vec<_> = generic_func_asts.into_iter().collect();
        let mut results = Vec::new();

        // Use a shared type table across all generic templates so that
        // VirTypeIds are consistent and can be consumed by VIR monomorphization
        // (which needs a single type table for substitution/rewriting).
        let mut shared_type_table = VirTypeTable::new();

        for (name_id, func) in entries {
            if let Some(vir) =
                self.analyze_and_lower_generic(name_id, func, interner, &mut shared_type_table)
            {
                results.push((name_id, vir));
            }
        }

        // Clean up: remove monomorph cache entries that were newly created
        // during generic analysis AND whose type_keys contain TypeParam types.
        // These identity-substitution entries are not valid concrete instances
        // and would pollute the monomorph cache consumed by VIR monomorph and
        // codegen lowering.  Pre-existing entries (from Pass 2) are preserved
        // because Pass 2.5 needs them for propagation.
        self.purge_new_type_param_monomorph_entries(&pre_existing_keys);

        (results, shared_type_table)
    }

    /// Analyze a single generic function body with identity substitutions,
    /// then lower it to a VIR template.
    ///
    /// Returns `None` if the function lacks `GenericInfo` or if analysis fails.
    fn analyze_and_lower_generic(
        &mut self,
        name_id: NameId,
        func: &FuncDecl,
        interner: &Interner,
        shared_type_table: &mut VirTypeTable,
    ) -> Option<VirFunction> {
        let (func_id, generic_info) = {
            let registry = self.entity_registry();
            let fid = registry.function_by_name(name_id)?;
            let info = registry.get_function(fid).generic_info.clone()?;
            (fid, info)
        };

        let substitutions = self.build_identity_substitutions(&generic_info);

        // Analyze the body with identity substitutions (populates NodeMap
        // with abstract TypeParam types).  Suppress diagnostics: generic
        // body analysis may produce errors for type-parameter-dependent
        // operations that are only valid with concrete types.
        let saved_errors = std::mem::take(&mut self.diagnostics.errors);
        let saved_warnings = std::mem::take(&mut self.diagnostics.warnings);
        self.analyze_monomorph_body(func, &substitutions, interner);
        let generic_errors = self.diagnostics.errors.len();
        self.diagnostics.errors = saved_errors;
        self.diagnostics.warnings = saved_warnings;

        // If the generic body analysis produced errors, the NodeMap entries
        // may be incomplete.  Skip VIR lowering for this function.
        if generic_errors > 0 {
            return None;
        }

        // Immediately lower to VIR while NodeMap has abstract types.
        let vir =
            self.lower_analyzed_generic(func, func_id, &generic_info, interner, shared_type_table);

        Some(vir)
    }

    /// Build identity substitutions: each type param maps to its own
    /// `TypeParam(name_id)` type, so `arena.substitute()` is a no-op.
    fn build_identity_substitutions(
        &mut self,
        generic_info: &GenericFuncInfo,
    ) -> FxHashMap<NameId, ArenaTypeId> {
        let mut subs = FxHashMap::default();
        for tp in &generic_info.type_params {
            // `type_param` returns the existing interned TypeId or creates one.
            let param_type_id = self.type_arena_mut().type_param(tp.name_id);
            subs.insert(tp.name_id, param_type_id);
        }
        subs
    }

    /// Remove monomorph cache entries that were newly created during generic
    /// analysis AND whose keys contain TypeParam types.
    ///
    /// During generic body analysis with identity substitutions, calls to
    /// other generic functions create monomorph instances keyed by TypeParam
    /// types (e.g., `MonomorphKey { type_keys: [TypeParam(T)] }`).  These
    /// are not valid concrete instances and must be removed so they don't
    /// pollute the cache consumed by VIR monomorphization and codegen lowering.
    ///
    /// Pre-existing entries (created during Pass 2) are preserved because
    /// Pass 2.5 (propagate_class_method_monomorphs) needs them.
    fn purge_new_type_param_monomorph_entries(
        &mut self,
        pre_existing_keys: &HashSet<MonomorphKey>,
    ) {
        let type_arena = self.type_arena();
        self.entity_registry_mut().monomorph_cache.retain(|key, _| {
            // Keep all pre-existing entries.
            if pre_existing_keys.contains(key) {
                return true;
            }
            // Remove newly added entries with TypeParam type keys.
            !key.type_keys
                .iter()
                .any(|&tk| type_arena.contains_type_param(tk))
        });
    }

    /// Lower an analyzed generic function body to a VIR template.
    fn lower_analyzed_generic(
        &mut self,
        func: &FuncDecl,
        func_id: vole_identity::FunctionId,
        generic_info: &GenericFuncInfo,
        interner: &Interner,
        shared_type_table: &mut VirTypeTable,
    ) -> VirFunction {
        let param_types: Vec<_> = func
            .params
            .iter()
            .zip(generic_info.param_types.iter())
            .map(|(p, &ty)| (p.name, ty))
            .collect();

        let display_name = interner.resolve(func.name).to_string();

        // Clone the interner for VIR lowering (the lowering may intern
        // new string literals, requiring &mut Interner).
        let mut lowering_interner = interner.clone();

        let node_map = &self.results.node_map;
        let type_arena = self.type_arena();
        let entities = self.entity_registry();
        let names = self.name_table();

        let type_param_names: Vec<_> = generic_info
            .type_params
            .iter()
            .map(|tp| tp.name_id)
            .collect();

        crate::vir_lower::lower_generic_function(
            func,
            func_id,
            display_name,
            &param_types,
            generic_info.return_type,
            node_map,
            &mut lowering_interner,
            &type_arena,
            &entities,
            &names,
            shared_type_table,
            &type_param_names,
        )
    }
}
