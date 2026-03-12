// vir_lower/mod.rs
//
// AST-to-VIR lowering.
//
// Walks the AST and lowers all expression and statement kinds to typed VIR
// nodes.  Every `ExprKind` variant maps to a concrete `VirExpr` variant
// (no escape hatches). Method calls carry explicit VIR dispatch metadata.
// All pattern kinds (including Record) are fully lowered to concrete
// `VirPattern` variants.

pub mod expr;
mod pattern;
pub mod stmt;
pub mod type_translate;

#[cfg(test)]
mod tests;

use rustc_hash::{FxHashMap, FxHashSet};
use vole_frontend::ast::{FuncBody, FuncDecl, InterfaceMethod};
use vole_identity::{
    FunctionId, Interner, MethodId, ModuleId, NameId, NameTable, NodeId, Symbol, TypeDefId, TypeId,
    VirTypeId,
};

use crate::implement_registry::ImplementRegistry;
use crate::node_map::NodeMap;
use crate::{EntityRegistry, TypeArena};

use vole_vir::calls::{CallTarget, NativeAbi};
use vole_vir::func::{ReturnAbi, VirBody, VirFunction};
use vole_vir::intrinsics::IntrinsicKey;
use vole_vir::type_table::VirTypeTable;

use self::expr::lower_expr;
use self::stmt::lower_stmt;
use self::type_translate::translate_type_id;

/// Cross-module and prelude call resolution context.
///
/// Bundles pre-computed data that `resolve_callee_function` needs for
/// resolving calls to functions outside the current module.
pub struct CrossModuleCtx {
    /// Destructured import bindings: local symbol → (source ModuleId, export Symbol).
    pub module_bindings: FxHashMap<Symbol, (ModuleId, Symbol)>,
    /// Module IDs of prelude modules (paths starting with `std:prelude/`).
    pub prelude_module_ids: Vec<ModuleId>,
}

impl CrossModuleCtx {
    /// Create an empty context (no cross-module or prelude resolution).
    pub fn empty() -> Self {
        Self {
            module_bindings: FxHashMap::default(),
            prelude_module_ids: Vec::new(),
        }
    }
}

/// Shared lowering context threaded through all lowering helpers.
///
/// Bundles the sema outputs needed during AST-to-VIR lowering:
/// - `node_map`: per-node sema annotations (types, dispatch info, etc.)
/// - `interner`: string interning (mutable for new literals)
/// - `type_arena`: type resolution (unwrap_union, unwrap_fallible, etc.)
/// - `entities`: entity lookups (field info, error types, etc.)
/// - `name_table`: name resolution (last_segment_str for error tag matching)
/// - `type_table`: VIR type interning table (populated during lowering)
/// - `module_id`: the module being lowered (for resolving callee symbols)
pub struct LoweringCtx<'a> {
    pub node_map: &'a NodeMap,
    pub interner: &'a mut Interner,
    pub type_arena: &'a TypeArena,
    pub entities: &'a EntityRegistry,
    pub name_table: &'a NameTable,
    pub type_table: &'a mut VirTypeTable,
    /// The module whose body is being lowered.
    ///
    /// Used by call resolution to convert callee symbols to `NameId`
    /// via `NameTable::name_id(module_id, &[sym], interner)`.
    pub module_id: ModuleId,
    /// When `true`, NodeMap lookups that would normally panic on missing
    /// entries instead produce placeholder/generic values.  Used when
    /// lowering generic function bodies where sema decision data may be
    /// absent for type-parameter-dependent expressions.
    ///
    /// Default: `false` (concrete mode — existing strict behaviour).
    pub generic: bool,
    /// The return type of the enclosing function.
    ///
    /// Used to pre-compute the `ReturnConvention` on `VirStmt::Return`
    /// nodes.  `VOID` for test bodies and void-returning functions.
    pub func_return_type: TypeId,
    /// Captured variable names for the function body currently being lowered.
    ///
    /// When lowering a lambda body, this is populated with the lambda's
    /// capture names from `LambdaAnalysis`.  Used by call lowering to
    /// distinguish `CallTarget::ClosureVariable` (local variable with
    /// function type) from `CallTarget::CapturedClosure` (captured variable
    /// with function type).
    ///
    /// Empty for top-level function bodies (no captures).
    pub captures: FxHashSet<Symbol>,

    /// Cross-module and prelude call resolution context.
    ///
    /// Used by `resolve_callee_function` to resolve calls to functions
    /// outside the current module (destructured imports, prelude functions)
    /// to `CallTarget::Direct` without falling through to codegen's
    /// `call_dispatch()`.
    pub cross_module: &'a CrossModuleCtx,

    /// Implement registry for external function lookups.
    ///
    /// Used by `resolve_callee_target` to look up external (FFI) function
    /// metadata (module path, native name) when `FunctionDef.is_external`
    /// is true, enabling `CallTarget::Native` emission during VIR lowering.
    pub implements: &'a ImplementRegistry,
}

impl LoweringCtx<'_> {
    /// Translate a sema `TypeId` to a `VirTypeId`, interning into the type table.
    pub fn translate(&mut self, type_id: TypeId) -> VirTypeId {
        translate_type_id(self.type_table, type_id, self.type_arena)
    }

    /// Translate a `TypeId` to a `VirTypeId` for VIR node annotations.
    ///
    /// Returns `VirTypeId::UNKNOWN` for sema-internal types (Module,
    /// Placeholder, Invalid) that have no VirTypeTable representation.
    pub fn compat_ty(&mut self, type_id: TypeId) -> VirTypeId {
        self.translate(type_id)
    }

    // -- Call resolution helpers ---------------------------------------------

    /// Try to resolve a callee `Symbol` to a `CallTarget`.
    ///
    /// Resolution proceeds through three stages:
    /// 1. Same-module: look up `(module_id, callee_sym)` in the name table.
    /// 2. Cross-module: if the callee is a destructured import binding,
    ///    look it up in the source module's namespace.
    /// 3. Prelude: try each prelude module's namespace.
    ///
    /// Returns:
    /// - `CallTarget::Direct` for non-external direct functions
    /// - `CallTarget::Native` for FFI external functions
    /// - `CallTarget::Intrinsic` for compiler-intrinsic external functions
    /// - `None` when the symbol doesn't map to a directly-callable
    ///   function (e.g. lambdas, closures, builtins, generics).
    pub fn resolve_callee_target(&mut self, callee_sym: Symbol) -> Option<CallTarget> {
        // Guard: if the symbol can't be resolved (e.g. UNKNOWN in tests),
        // bail early to avoid panicking in name_table.name_id().
        // Convert to owned String to avoid holding a borrow on interner
        // while try_resolve_call_target needs &mut self for interning.
        let callee_name = self.interner.try_resolve(callee_sym)?.to_string();

        // Stage 1: same-module lookup.
        let name_id = self
            .name_table
            .name_id(self.module_id, &[callee_sym], self.interner);
        if let Some(name_id) = name_id
            && let Some(target) = self.try_resolve_call_target(name_id, &callee_name)
        {
            return Some(target);
        }

        // Stage 2: cross-module lookup via destructured import bindings.
        if let Some(&(source_module_id, _export_sym)) =
            self.cross_module.module_bindings.get(&callee_sym)
        {
            // Look up the function in the source module's namespace using
            // the callee name string (cross-interner safe via name_id_raw).
            if let Some(source_name_id) = self
                .name_table
                .name_id_raw(source_module_id, &[&callee_name])
                && let Some(target) = self.try_resolve_call_target(source_name_id, &callee_name)
            {
                return Some(target);
            }
        }

        // Stage 3: prelude module lookup.
        for &prelude_module_id in &self.cross_module.prelude_module_ids {
            if let Some(prelude_name_id) = self
                .name_table
                .name_id_raw(prelude_module_id, &[&callee_name])
                && let Some(target) = self.try_resolve_call_target(prelude_name_id, &callee_name)
            {
                return Some(target);
            }
        }

        None
    }

    /// Try to resolve a callee `Symbol` to a `FunctionId` (direct calls only).
    ///
    /// Resolution proceeds through three stages:
    /// 1. Same-module: look up `(module_id, callee_sym)` in the name table.
    /// 2. Cross-module: if the callee is a destructured import binding,
    ///    look it up in the source module's namespace.
    /// 3. Prelude: try each prelude module's namespace.
    ///
    /// Returns `None` when the symbol doesn't map to a directly-callable
    /// function (e.g. lambdas, closures, builtins, generics, FFI).
    pub fn resolve_callee_function(&self, callee_sym: Symbol) -> Option<FunctionId> {
        // Guard: if the symbol can't be resolved (e.g. UNKNOWN in tests),
        // bail early to avoid panicking in name_table.name_id().
        let callee_name = self.interner.try_resolve(callee_sym)?;

        // Stage 1: same-module lookup.
        let name_id = self
            .name_table
            .name_id(self.module_id, &[callee_sym], self.interner);
        if let Some(name_id) = name_id
            && let Some(func_id) = self.try_resolve_function_id(name_id)
        {
            return Some(func_id);
        }

        // Stage 2: cross-module lookup via destructured import bindings.
        if let Some(&(source_module_id, _export_sym)) =
            self.cross_module.module_bindings.get(&callee_sym)
        {
            // Look up the function in the source module's namespace using
            // the callee name string (cross-interner safe via name_id_raw).
            if let Some(source_name_id) = self
                .name_table
                .name_id_raw(source_module_id, &[callee_name])
                && let Some(func_id) = self.try_resolve_function_id(source_name_id)
            {
                return Some(func_id);
            }
        }

        // Stage 3: prelude module lookup.
        for &prelude_module_id in &self.cross_module.prelude_module_ids {
            if let Some(prelude_name_id) = self
                .name_table
                .name_id_raw(prelude_module_id, &[callee_name])
                && let Some(func_id) = self.try_resolve_function_id(prelude_name_id)
            {
                return Some(func_id);
            }
        }

        None
    }

    /// Try to resolve a `NameId` to a `CallTarget`.
    ///
    /// Returns:
    /// - `CallTarget::Direct` for non-external direct functions
    /// - `CallTarget::Native` or `CallTarget::Intrinsic` for external functions
    /// - `None` for functions that need special codegen handling
    ///   (generics).
    fn try_resolve_call_target(
        &mut self,
        name_id: NameId,
        callee_name: &str,
    ) -> Option<CallTarget> {
        let func_id = self.entities.function_by_name(name_id)?;
        let func_def = self.entities.get_function(func_id);
        // Only resolve non-generic functions — generic calls use GenericCall.
        if func_def.generic_info.is_some() {
            return None;
        }
        // External (FFI) functions: look up the native function info from
        // the implement registry and emit CallTarget::Native or Intrinsic.
        // Use the original function name (full_name_id) for lookup, since
        // the callee may be an import alias (e.g., `sqrt as squareRoot`).
        if func_def.is_external {
            let original_name = self
                .name_table
                .last_segment_str(func_def.full_name_id)
                .unwrap_or_else(|| callee_name.to_string());
            return self.resolve_external_call_target(&original_name);
        }
        // Interface/union parameters are handled by codegen's
        // compile_vir_args_coerced(), which coerces each argument
        // against the callee's declared parameter type (interface
        // boxing, union wrapping).
        Some(CallTarget::Direct {
            function_id: func_id,
        })
    }

    /// Resolve an external (FFI) function to a `CallTarget::Native` or
    /// `CallTarget::Intrinsic`.
    ///
    /// Looks up the external function info from the implement registry by
    /// short name.  If the module path is "vole:compiler_intrinsic", the
    /// function is a compiler intrinsic and is emitted as
    /// `CallTarget::Intrinsic`.  Otherwise, it is emitted as
    /// `CallTarget::Native` with the module path and native name interned
    /// as `Symbol`s.
    fn resolve_external_call_target(&mut self, callee_name: &str) -> Option<CallTarget> {
        let ext_info = self.implements.get_external_func(callee_name)?;
        let module_path_str = self
            .name_table
            .last_segment_str(ext_info.module_path)
            .unwrap_or_default();
        let native_name_str = self
            .name_table
            .last_segment_str(ext_info.native_name)
            .unwrap_or_default();

        // Compiler intrinsics (e.g., panic) are emitted as Intrinsic.
        if module_path_str == "vole:compiler_intrinsic" {
            let key = IntrinsicKey::try_from_name(&native_name_str)?;
            return Some(CallTarget::Intrinsic { key, line: 0 });
        }

        // Regular FFI external functions → CallTarget::Native.
        let module_path_sym = self.interner.intern(&module_path_str);
        let native_name_sym = self.interner.intern(&native_name_str);
        Some(CallTarget::Native {
            module_path: module_path_sym,
            native_name: native_name_sym,
            abi: NativeAbi::Simple,
        })
    }

    /// Try to resolve a generic external function call to a `CallTarget`.
    ///
    /// When a call has a `MonomorphKey` (concrete type arguments) and the
    /// callee is a generic external function registered in the implement
    /// registry, this resolves it to either:
    /// - `CallTarget::Intrinsic` (compiler intrinsic via type mapping)
    /// - `CallTarget::Native` (regular FFI via type mapping)
    ///
    /// The concrete types from `sema_type_keys` (raw TypeIds from NodeMap's
    /// MonomorphKey) are matched against the type mappings to determine the
    /// intrinsic key.
    ///
    /// Returns `None` when the callee isn't a generic external, or when
    /// the type mapping doesn't resolve to a known intrinsic.
    pub fn resolve_generic_external_callee(
        &mut self,
        callee_sym: Symbol,
        sema_type_keys: &[VirTypeId],
        line: u32,
    ) -> Option<CallTarget> {
        let callee_name = self.interner.try_resolve(callee_sym)?.to_string();

        // Look up the function across same-module, cross-module, and prelude
        // namespaces to check if it's a generic external.
        let name_id = self.find_generic_external_name_id(callee_sym, &callee_name)?;
        let func_id = self.entities.function_by_name(name_id)?;
        let func_def = self.entities.get_function(func_id);
        if !func_def.is_external || func_def.generic_info.is_none() {
            return None;
        }

        // Look up the generic external info using the original function name
        // (not the alias), since the implement registry uses original names.
        let original_name = self
            .name_table
            .last_segment_str(func_def.full_name_id)
            .unwrap_or_else(|| callee_name.clone());
        let generic_ext = self.implements.get_generic_external(&original_name)?;
        let module_path_str = self
            .name_table
            .last_segment_str(generic_ext.module_path)
            .unwrap_or_default();

        // Resolve the intrinsic key from the concrete types in the monomorph key.
        let intrinsic_key = match resolve_intrinsic_key_from_type_mappings(
            &generic_ext.type_mappings,
            sema_type_keys,
            self.type_arena,
            self.name_table,
            self.entities,
        ) {
            Ok(key) => key,
            Err(WhereMapError::Ambiguous { matches }) => {
                let message = format!(
                    "{}: ambiguous where mapping; \
                     multiple exact arms match concrete substitutions: {}",
                    callee_name,
                    matches.join(", ")
                );
                return Some(CallTarget::CompileError { message });
            }
            Err(WhereMapError::Missing { concrete_types }) => {
                let message = format!(
                    "{}: no where mapping arm for concrete type(s): {}",
                    callee_name,
                    concrete_types.join(", ")
                );
                return Some(CallTarget::CompileError { message });
            }
        };

        // Try to classify as a compiler intrinsic first.
        if let Some(key) = IntrinsicKey::try_from_name(&intrinsic_key) {
            return Some(CallTarget::Intrinsic { key, line });
        }

        // Fall back to a Native call — the intrinsic_key IS the native
        // function name in the runtime module.
        let module_path_sym = self.interner.intern(&module_path_str);
        let native_name_sym = self.interner.intern(&intrinsic_key);
        Some(CallTarget::Native {
            module_path: module_path_sym,
            native_name: native_name_sym,
            abi: NativeAbi::Simple,
        })
    }

    /// Find the `NameId` for a callee that might be a generic external function.
    ///
    /// Searches same-module, cross-module, and prelude namespaces, returning
    /// the first match.  Used by `resolve_generic_external_callee`.
    fn find_generic_external_name_id(
        &self,
        callee_sym: Symbol,
        callee_name: &str,
    ) -> Option<NameId> {
        // Stage 1: same-module.
        if let Some(name_id) = self
            .name_table
            .name_id(self.module_id, &[callee_sym], self.interner)
        {
            return Some(name_id);
        }
        // Stage 2: cross-module.
        if let Some(&(source_module_id, _)) = self.cross_module.module_bindings.get(&callee_sym)
            && let Some(name_id) = self
                .name_table
                .name_id_raw(source_module_id, &[callee_name])
        {
            return Some(name_id);
        }
        // Stage 3: prelude.
        for &prelude_module_id in &self.cross_module.prelude_module_ids {
            if let Some(name_id) = self
                .name_table
                .name_id_raw(prelude_module_id, &[callee_name])
            {
                return Some(name_id);
            }
        }
        None
    }

    /// Check whether a `FunctionId` (looked up by `NameId`) is eligible for
    /// `CallTarget::Direct` emission.
    ///
    /// Returns `None` for functions that need special codegen handling
    /// (generics, FFI).
    fn try_resolve_function_id(&self, name_id: NameId) -> Option<FunctionId> {
        let func_id = self.entities.function_by_name(name_id)?;
        let func_def = self.entities.get_function(func_id);
        // Only resolve non-generic functions — generic calls use GenericCall.
        if func_def.generic_info.is_some() {
            return None;
        }
        // Skip external (FFI) functions — they are resolved by
        // resolve_callee_target() which emits Native or Intrinsic targets.
        if func_def.is_external {
            return None;
        }
        // Interface/union parameters are handled by codegen's
        // compile_vir_args_coerced(), which coerces each argument
        // against the callee's declared parameter type.
        Some(func_id)
    }

    // -- Tolerant NodeMap query helpers -------------------------------------
    //
    // In generic mode (`self.generic == true`), these helpers return a
    // placeholder value instead of panicking when sema decision data is
    // missing.  In concrete mode they panic exactly as before.

    /// Get the `IsCheckResult` for a node, with a tolerant fallback in
    /// generic mode.
    ///
    /// Concrete mode: panics if missing (existing behaviour).
    /// Generic mode: returns `CheckUnknown(UNKNOWN)` if missing.
    pub fn require_is_check_result(&mut self, node_id: NodeId, line: u32) -> crate::IsCheckResult {
        match self.node_map.get_is_check_result(node_id) {
            Some(result) => result,
            None if self.generic => crate::IsCheckResult::CheckUnknown(TypeId::UNKNOWN),
            None => panic!(
                "VIR lower: missing sema is_check_result for NodeId {node_id:?} (line {line})"
            ),
        }
    }

    /// Get the `MetaAccessKind` for a node, with a tolerant fallback in
    /// generic mode.
    ///
    /// Concrete mode: panics if missing (existing behaviour).
    /// Generic mode: returns `Dynamic` as a safe placeholder.
    pub fn require_meta_access(
        &self,
        node_id: NodeId,
        line: u32,
    ) -> crate::node_map::MetaAccessKind {
        match self.node_map.get_meta_access(node_id) {
            Some(kind) => kind,
            None if self.generic => crate::node_map::MetaAccessKind::Dynamic,
            None => {
                panic!("VIR lower: missing sema meta_access for NodeId {node_id:?} (line {line})")
            }
        }
    }

    /// Get the `OptionalChainInfo` for a node, with a tolerant fallback
    /// in generic mode.
    ///
    /// Concrete mode: panics if missing.
    /// Generic mode: returns a minimal placeholder with UNKNOWN types.
    pub fn require_optional_chain(
        &self,
        node_id: NodeId,
        line: u32,
    ) -> crate::node_map::OptionalChainInfo {
        match self.node_map.get_optional_chain(node_id) {
            Some(info) => info.clone(),
            None if self.generic => crate::node_map::OptionalChainInfo {
                object_type: TypeId::UNKNOWN,
                inner_type: TypeId::UNKNOWN,
                result_type: TypeId::UNKNOWN,
                kind: crate::node_map::OptionalChainKind::FieldAccess {
                    field: Symbol::UNKNOWN,
                },
            },
            None => panic!(
                "VIR lower: missing sema optional_chain for NodeId {node_id:?} (line {line})"
            ),
        }
    }

    /// Resolve the field storage dispatch for a field access.
    ///
    /// Given the object's sema type and the field name (as a `Symbol`),
    /// returns:
    /// - `FieldStorage::Direct { slot }` for struct fields (logical slot index)
    /// - `FieldStorage::Heap { slot }` for class fields (physical slot,
    ///   accounting for wide types)
    /// - `FieldStorage::ByName` for modules, unknown types, or generic templates
    pub fn resolve_field_storage(
        &self,
        object_type: TypeId,
        field: Symbol,
    ) -> vole_vir::expr::FieldStorage {
        use vole_vir::expr::FieldStorage;

        // Generic templates can't resolve storage — type params are abstract.
        if self.generic {
            return FieldStorage::ByName;
        }

        let field_name = self.interner.resolve(field);

        // Struct types are generally value-type, stack-allocated (Direct storage).
        // Exception: annotation structs (@annotation) may be heap-allocated via
        // InstanceNew (e.g. retrieved from FieldMeta.annotations array after an
        // `is` check), so their fields use Heap storage to match class instance layout.
        if let Some((type_def_id, type_args)) = self.type_arena.unwrap_struct(object_type) {
            let is_annotation = self.entities.get_type(type_def_id).is_annotation;
            if is_annotation {
                return self
                    .resolve_class_field_slot(type_def_id, type_args, field_name)
                    .map_or(FieldStorage::ByName, |slot| FieldStorage::Heap {
                        slot: slot as u32,
                    });
            }
            return self
                .resolve_struct_field_slot(type_def_id, type_args, field_name)
                .map_or(FieldStorage::ByName, |slot| FieldStorage::Direct {
                    slot: slot as u32,
                });
        }

        // Try class (reference-counted, heap-allocated).
        if let Some((type_def_id, type_args)) = self.type_arena.unwrap_class(object_type) {
            return self
                .resolve_class_field_slot(type_def_id, type_args, field_name)
                .map_or(FieldStorage::ByName, |slot| FieldStorage::Heap {
                    slot: slot as u32,
                });
        }

        // Module types carry the ModuleId for codegen dispatch.
        if let crate::SemaType::Module(interned) = self.type_arena.get(object_type) {
            return FieldStorage::Module {
                module_id: interned.module_id,
            };
        }

        // Interface or other type — codegen handles separately.
        FieldStorage::ByName
    }

    /// Resolve the logical field slot for a struct field.
    ///
    /// Returns the field's index in the struct's field list (0-based).
    fn resolve_struct_field_slot(
        &self,
        type_def_id: TypeDefId,
        _type_args: &crate::type_arena::TypeIdVec,
        field_name: &str,
    ) -> Option<usize> {
        let type_def = self.entities.get_type(type_def_id);
        let generic_info = type_def.generic_info.as_ref()?;
        generic_info.field_index_by_name(field_name, self.name_table)
    }

    /// Resolve the physical slot for a class field, accounting for wide
    /// types (i128/f128) that occupy 2 consecutive slots.
    fn resolve_class_field_slot(
        &self,
        type_def_id: TypeDefId,
        type_args: &crate::type_arena::TypeIdVec,
        field_name: &str,
    ) -> Option<usize> {
        let type_def = self.entities.get_type(type_def_id);
        let generic_info = type_def.generic_info.as_ref()?;

        // Build substitution map for generic classes.
        let subs: FxHashMap<NameId, TypeId> = type_def
            .type_params
            .iter()
            .zip(type_args.iter())
            .map(|(&param, &arg)| (param, arg))
            .collect();

        let mut physical_slot = 0usize;
        for (idx, field_name_id) in generic_info.field_names.iter().enumerate() {
            let name = self.name_table.last_segment_str(*field_name_id);
            if name.as_deref() == Some(field_name) {
                return Some(physical_slot);
            }
            // Advance physical slot: wide types use 2 slots.
            let ft = generic_info.field_types[idx];
            let resolved_ft = if !subs.is_empty() {
                self.type_arena.lookup_substitute(ft, &subs).unwrap_or(ft)
            } else {
                ft
            };
            physical_slot += if is_wide_sema_type(resolved_ft) { 2 } else { 1 };
        }
        None
    }

    /// Get the `StructLiteralInfo` for a node, with a tolerant fallback.
    ///
    /// Returns a placeholder with a zeroed `TypeDefId` and `is_class = false`
    /// when the info is missing.  This can happen in two situations:
    ///
    /// 1. **Generic mode** — the template was never fully analyzed.
    /// 2. **Concrete mode** — sema returned early (e.g. the method body was
    ///    never type-checked because the method wasn't found in the implement
    ///    registry).  A sema error was already reported, so VIR lowering
    ///    should emit a best-effort placeholder instead of panicking.
    pub fn require_struct_literal_info(
        &self,
        node_id: NodeId,
        _line: u32,
    ) -> crate::node_map::StructLiteralInfo {
        self.node_map.get_struct_literal_info(node_id).unwrap_or(
            crate::node_map::StructLiteralInfo {
                type_def_id: TypeDefId::new(0),
                is_class: false,
            },
        )
    }
}

/// Lower a single function declaration into a `VirFunction`.
///
/// `func_id`, `name`, `param_types`, and `return_type` come from the sema
/// entity registry — they are resolved during semantic analysis and passed
/// in by the caller (the compilation pipeline).
///
/// `node_map` is used by expression lowering to look up sema-computed types,
/// is-check results, optional chain info, and other annotations.
///
/// `type_arena` and `entities` are threaded into the lowering context for
/// future use by pattern lowering.
#[expect(clippy::too_many_arguments)]
pub fn lower_function(
    func: &FuncDecl,
    func_id: FunctionId,
    name: String,
    param_types: &[(Symbol, TypeId)],
    return_type: TypeId,
    node_map: &NodeMap,
    interner: &mut Interner,
    type_arena: &TypeArena,
    entities: &EntityRegistry,
    name_table: &NameTable,
    type_table: &mut VirTypeTable,
    module_id: ModuleId,
    cross_module: &CrossModuleCtx,
    implements: &ImplementRegistry,
) -> VirFunction {
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
        type_table,
        module_id,
        generic: false,
        func_return_type: return_type,
        captures: FxHashSet::default(),
        cross_module,
        implements,
    };
    let params = param_types
        .iter()
        .map(|(s, t)| {
            let vir_ty = ctx.translate(*t);
            (*s, vir_ty, vir_ty)
        })
        .collect();
    let vir_return_type = ctx.translate(return_type);
    let return_abi = ReturnAbi::classify(vir_return_type, ctx.type_table);
    let body = lower_func_body(&func.body, &mut ctx);
    VirFunction {
        id: func_id,
        name,
        params,
        return_type: vir_return_type,
        vir_return_type,
        return_abi,
        body,
        mangled_name_id: None,
        method_id: None,
        type_params: Vec::new(),
    }
}

/// Lower a monomorphized function instance into a `VirFunction`.
///
/// Like [`lower_function`], but for a generic function that has been
/// instantiated with concrete type arguments.  The caller provides
/// already-substituted `param_types` and `return_type` from the
/// `MonomorphInstance`'s `func_type`.
///
/// In debug builds, asserts that no `TypeId` in the output still
/// contains a type parameter — all types must be concrete after
/// monomorphization.
#[expect(clippy::too_many_arguments)]
pub fn lower_monomorphized_function(
    func: &FuncDecl,
    func_id: FunctionId,
    name: String,
    param_types: &[(Symbol, TypeId)],
    return_type: TypeId,
    node_map: &NodeMap,
    type_arena: &TypeArena,
    mangled_name_id: NameId,
    interner: &mut Interner,
    entities: &EntityRegistry,
    name_table: &NameTable,
    type_table: &mut VirTypeTable,
    module_id: ModuleId,
    cross_module: &CrossModuleCtx,
    implements: &ImplementRegistry,
) -> VirFunction {
    assert_concrete_types(param_types, return_type, type_arena, &name);
    let mut vir = lower_function(
        func,
        func_id,
        name,
        param_types,
        return_type,
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
        type_table,
        module_id,
        cross_module,
        implements,
    );
    vir.mangled_name_id = Some(mangled_name_id);
    vir
}

/// Lower a class/struct method (instance or static) into a `VirFunction`.
///
/// Similar to [`lower_function`] but associates a `MethodId` instead of
/// using the `FunctionId` for lookup.  The `func_id` is a dummy value
/// (methods don't have a `FunctionId` in the entity registry); the real
/// identity is carried by `method_id`.
#[expect(clippy::too_many_arguments)]
pub fn lower_method(
    func: &FuncDecl,
    method_id: MethodId,
    name: String,
    param_types: &[(Symbol, TypeId)],
    return_type: TypeId,
    node_map: &NodeMap,
    interner: &mut Interner,
    type_arena: &TypeArena,
    entities: &EntityRegistry,
    name_table: &NameTable,
    type_table: &mut VirTypeTable,
    module_id: ModuleId,
    cross_module: &CrossModuleCtx,
    implements: &ImplementRegistry,
) -> VirFunction {
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
        type_table,
        module_id,
        generic: false,
        func_return_type: return_type,
        captures: FxHashSet::default(),
        cross_module,
        implements,
    };
    let params = param_types
        .iter()
        .map(|(s, t)| {
            let vir_ty = ctx.translate(*t);
            (*s, vir_ty, vir_ty)
        })
        .collect();
    let vir_return_type = ctx.translate(return_type);
    let return_abi = ReturnAbi::classify(vir_return_type, ctx.type_table);
    let body = lower_func_body(&func.body, &mut ctx);
    VirFunction {
        id: FunctionId::new(0), // dummy — methods use method_id for lookup
        name,
        params,
        return_type: vir_return_type,
        vir_return_type,
        return_abi,
        body,
        mangled_name_id: None,
        method_id: Some(method_id),
        type_params: Vec::new(),
    }
}

/// Lower an interface method (default method with a body) into a `VirFunction`.
///
/// Interface methods use `InterfaceMethod` AST nodes (which have an optional
/// body) rather than `FuncDecl`.  Only methods with a body should be lowered.
#[expect(clippy::too_many_arguments)]
pub fn lower_interface_method(
    method: &InterfaceMethod,
    method_id: MethodId,
    name: String,
    param_types: &[(Symbol, TypeId)],
    return_type: TypeId,
    node_map: &NodeMap,
    interner: &mut Interner,
    type_arena: &TypeArena,
    entities: &EntityRegistry,
    name_table: &NameTable,
    type_table: &mut VirTypeTable,
    module_id: ModuleId,
    cross_module: &CrossModuleCtx,
    implements: &ImplementRegistry,
) -> Option<VirFunction> {
    let body_ast = method.body.as_ref()?;
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
        type_table,
        module_id,
        generic: false,
        func_return_type: return_type,
        captures: FxHashSet::default(),
        cross_module,
        implements,
    };
    let params = param_types
        .iter()
        .map(|(s, t)| {
            let vir_ty = ctx.translate(*t);
            (*s, vir_ty, vir_ty)
        })
        .collect();
    let vir_return_type = ctx.translate(return_type);
    let return_abi = ReturnAbi::classify(vir_return_type, ctx.type_table);
    let body = lower_func_body(body_ast, &mut ctx);
    Some(VirFunction {
        id: FunctionId::new(0), // dummy — methods use method_id for lookup
        name,
        params,
        return_type: vir_return_type,
        vir_return_type,
        return_abi,
        body,
        mangled_name_id: None,
        method_id: Some(method_id),
        type_params: Vec::new(),
    })
}

/// Lower a generic function declaration into a `VirFunction` template.
///
/// Like [`lower_function`], but uses `generic: true` mode so that missing
/// or type-parameter-dependent NodeMap entries produce placeholder values
/// instead of panicking.  The `param_types` and `return_type` should contain
/// abstract `TypeParam` types from the function's `GenericFuncInfo`.
///
/// The resulting `VirFunction` is a **template** — it must NOT reach codegen
/// directly.  A future VIR-to-VIR monomorphization pass substitutes type
/// parameters with concrete types before compilation.
#[expect(clippy::too_many_arguments)]
pub fn lower_generic_function(
    func: &FuncDecl,
    func_id: FunctionId,
    name: String,
    param_types: &[(Symbol, TypeId)],
    return_type: TypeId,
    node_map: &NodeMap,
    interner: &mut Interner,
    type_arena: &TypeArena,
    entities: &EntityRegistry,
    name_table: &NameTable,
    type_table: &mut VirTypeTable,
    type_param_names: &[NameId],
    module_id: ModuleId,
    cross_module: &CrossModuleCtx,
    implements: &ImplementRegistry,
) -> VirFunction {
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
        type_table,
        module_id,
        generic: true,
        func_return_type: return_type,
        captures: FxHashSet::default(),
        cross_module,
        implements,
    };
    let params = param_types
        .iter()
        .map(|(s, t)| {
            let vir_ty = ctx.translate(*t);
            (*s, vir_ty, vir_ty)
        })
        .collect();
    let vir_return_type = ctx.translate(return_type);
    // For generic templates, return type may contain type parameters;
    // classify with best-effort (defaults to Single for unknown layouts).
    // rederive_decisions will recompute after monomorphization.
    let return_abi = ReturnAbi::classify(vir_return_type, ctx.type_table);
    let body = lower_func_body(&func.body, &mut ctx);
    VirFunction {
        id: func_id,
        name,
        params,
        return_type: vir_return_type,
        vir_return_type,
        return_abi,
        body,
        mangled_name_id: None,
        method_id: None,
        type_params: type_param_names.to_vec(),
    }
}

/// Assert that all types in a monomorphized function signature are concrete —
/// no `TypeParam` or `TypeParamRef` remains. This is an invariant violation
/// (not a recoverable error), so we assert unconditionally.
fn assert_concrete_types(
    param_types: &[(Symbol, TypeId)],
    return_type: TypeId,
    arena: &TypeArena,
    func_name: &str,
) {
    for (i, (_sym, ty)) in param_types.iter().enumerate() {
        assert!(
            !arena.contains_type_param(*ty),
            "VIR monomorph `{func_name}`: param {i} still contains a type parameter \
             (TypeId={ty:?})"
        );
    }
    assert!(
        !arena.contains_type_param(return_type),
        "VIR monomorph `{func_name}`: return type still contains a type parameter \
         (TypeId={return_type:?})"
    );
}

/// Lower a test case body into a `VirBody`.
///
/// Test bodies use the same `FuncBody` type as functions, so this delegates
/// to `lower_func_body`.  Exposed as a public API so the lowering pipeline
/// in `analyzed.rs` can lower test bodies alongside function bodies.
#[allow(clippy::too_many_arguments)]
pub fn lower_test_body(
    body: &FuncBody,
    node_map: &NodeMap,
    interner: &mut Interner,
    type_arena: &TypeArena,
    entities: &EntityRegistry,
    name_table: &NameTable,
    type_table: &mut VirTypeTable,
    module_id: ModuleId,
    cross_module: &CrossModuleCtx,
    implements: &ImplementRegistry,
) -> VirBody {
    let mut ctx = LoweringCtx {
        node_map,
        interner,
        type_arena,
        entities,
        name_table,
        type_table,
        module_id,
        generic: false,
        func_return_type: TypeId::VOID,
        captures: FxHashSet::default(),
        cross_module,
        implements,
    };
    lower_func_body(body, &mut ctx)
}

/// Lower a `FuncBody` (block or expression) into a `VirBody`.
///
/// Block bodies have their statements walked individually; expression bodies
/// become a single trailing VIR expression.
pub fn lower_func_body(body: &FuncBody, ctx: &mut LoweringCtx<'_>) -> VirBody {
    match body {
        FuncBody::Block(block) => lower_stmts(&block.stmts, ctx),
        FuncBody::Expr(expr) => {
            let trailing = lower_expr(expr, ctx);
            VirBody {
                stmts: Vec::new(),
                trailing: Some(trailing),
            }
        }
    }
}

/// Lower a slice of AST statements into a `VirBody`.
///
/// Each statement is fully lowered to a typed `VirStmt` node via
/// `lower_stmt`.  Expression statements have their inner expression
/// lowered recursively through `lower_expr`.
pub fn lower_stmts(stmts: &[vole_frontend::ast::Stmt], ctx: &mut LoweringCtx<'_>) -> VirBody {
    let vir_stmts = stmts.iter().map(|s| lower_stmt(s, ctx)).collect();
    VirBody {
        stmts: vir_stmts,
        trailing: None,
    }
}

/// Check whether a sema `TypeId` is a wide type (i128 or f128) that
/// occupies 2 consecutive slots in class instance storage.
fn is_wide_sema_type(type_id: TypeId) -> bool {
    matches!(type_id, TypeId::I128 | TypeId::F128)
}

/// Error from where-clause type mapping resolution.
enum WhereMapError {
    /// Multiple exact arms matched the concrete substitution types.
    Ambiguous {
        /// Human-readable list of matching arms, e.g. `["i64 => \"array_len\""]`.
        matches: Vec<String>,
    },
    /// No exact arm matched and no default arm was present.
    Missing {
        /// Human-readable list of the concrete types that had no mapping.
        concrete_types: Vec<String>,
    },
}

/// Resolve an intrinsic key from type mappings and concrete monomorph types.
///
/// Matches the concrete type keys (from the sema-side `MonomorphKey`) against
/// the `TypeMappingEntry` list.  Resolution order:
/// 1. Exact type arm (`Type => "key"`) — requires exactly one match.
/// 2. Default arm (`default => "key"`) — fallback when no exact match.
///
/// Returns `Err(WhereMapError)` when no mapping matches or when there are
/// ambiguous matches, carrying enough info for a diagnostic.
fn resolve_intrinsic_key_from_type_mappings(
    type_mappings: &[crate::implement_registry::TypeMappingEntry],
    sema_type_keys: &[VirTypeId],
    type_arena: &TypeArena,
    name_table: &NameTable,
    entities: &EntityRegistry,
) -> Result<String, WhereMapError> {
    use crate::implement_registry::TypeMappingKind;

    // Collect the concrete TypeIds from the monomorph key's type_keys.
    // In sema, VirTypeIds encode raw TypeIds via VirTypeId::from_type_id().
    let concrete_types: std::collections::HashSet<TypeId> = sema_type_keys
        .iter()
        .map(|vir_ty| vir_ty.to_type_id_raw())
        .collect();

    let mut default_key = None;
    let mut exact_matches: Vec<(TypeId, String)> = Vec::new();

    for mapping in type_mappings {
        match &mapping.kind {
            TypeMappingKind::Exact(type_id) => {
                if concrete_types.contains(type_id) {
                    exact_matches.push((*type_id, mapping.intrinsic_key.clone()));
                }
            }
            TypeMappingKind::Default => {
                default_key = Some(mapping.intrinsic_key.clone());
            }
        }
    }

    // Exactly one exact match — use it.
    if exact_matches.len() == 1 {
        return Ok(exact_matches.into_iter().next().unwrap().1);
    }

    // Ambiguous (multiple exact matches).
    if exact_matches.len() > 1 {
        let mut display: Vec<String> = exact_matches
            .iter()
            .map(|(ty, key)| {
                let ty_name = crate::type_display::display_type_id_short(
                    *ty, type_arena, name_table, entities,
                );
                format!("{} => \"{}\"", ty_name, key)
            })
            .collect();
        display.sort();
        display.dedup();
        return Err(WhereMapError::Ambiguous { matches: display });
    }

    // No exact match — use the default if available.
    if let Some(key) = default_key {
        return Ok(key);
    }

    // No match at all.
    let mut type_names: Vec<String> = concrete_types
        .iter()
        .map(|ty| crate::type_display::display_type_id_short(*ty, type_arena, name_table, entities))
        .collect();
    type_names.sort();
    type_names.dedup();
    Err(WhereMapError::Missing {
        concrete_types: type_names,
    })
}
