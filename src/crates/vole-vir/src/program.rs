// program.rs
//
// VirProgram: the complete VIR output from sema/lowering, consumed by codegen.
// This is the clean boundary between VIR lowering and code generation.

use std::rc::Rc;

use rustc_hash::FxHashMap;
use vole_identity::{
    FieldId, FunctionId, Interner, MethodId, ModuleId, NameId, NameTable, NamerLookup, NodeId,
    Span, Symbol, TypeDefId, VirTypeId,
};

use vole_identity::{ClassMethodMonomorphKey, MonomorphKey, StaticMethodMonomorphKey};

use crate::entity_metadata::VirEntityMetadata;
use crate::func::{VirBody, VirFunction, VirTest};
use crate::implement_dispatch::{
    VirExternalFuncInfo, VirGenericExternalInfo, VirImplementDispatch, VirMethodImplInfo,
};
use crate::monomorph::instance::{
    VirClassMethodMonomorphInfo, VirMonomorphInfo, VirStaticMethodMonomorphInfo,
};
use crate::refs::VirRef;
use crate::type_table::VirTypeTable;
use crate::types::VirAnnotation;

/// The complete VIR output: all lowered functions, tests, global inits, and
/// type metadata bundled into a single struct.
///
/// Sema/lowering produces this, codegen consumes it. This struct owns all VIR
/// data so codegen never needs to reach back into sema for VIR information.
pub struct VirProgram {
    /// The shared type table for all VIR functions.
    pub type_table: VirTypeTable,

    /// Concrete VIR functions (top-level, monomorphized instances, and methods).
    pub functions: Vec<VirFunction>,

    /// Lookup map from monomorphized mangled `NameId` to index in `functions`.
    pub monomorph_map: FxHashMap<NameId, usize>,

    /// Lookup map from semantic `FunctionId` to index in `functions`.
    pub function_map: FxHashMap<FunctionId, usize>,

    /// Lookup map from semantic `MethodId` to index in `functions`.
    pub method_map: FxHashMap<MethodId, usize>,

    /// Generic VIR function templates (pre-monomorphization).
    ///
    /// Each entry is lowered with `generic: true` mode, where type parameter
    /// types are preserved as `VirType::Param`. These templates are consumed
    /// by a future VIR-to-VIR monomorphization pass.
    pub generic_functions: Vec<VirFunction>,

    /// Lookup map from generic function's original `NameId` to its index
    /// in `generic_functions`.
    pub generic_map: FxHashMap<NameId, usize>,

    /// VIR-lowered test cases with names and bodies.
    pub tests: Vec<VirTest>,

    /// VIR-lowered global variable initializer expressions for the main program.
    ///
    /// Keyed by the `let` binding's `Symbol`. Used by codegen to compile
    /// global lambda/functional-interface initializers through the VIR path.
    pub global_inits: FxHashMap<Symbol, VirRef>,

    /// VIR-lowered global variable initializer expressions for imported modules.
    ///
    /// Keyed by module path, then by the `let` binding's `Symbol`.
    pub module_global_inits: FxHashMap<String, FxHashMap<Symbol, VirRef>>,

    /// VIR-lowered default parameter expressions for functions.
    ///
    /// Keyed by semantic `FunctionId` and parameter slot index.
    pub function_default_inits: FxHashMap<(FunctionId, usize), VirRef>,

    /// VIR-lowered default parameter expressions for methods.
    ///
    /// Keyed by semantic `MethodId` and parameter slot index.
    pub method_default_inits: FxHashMap<(MethodId, usize), VirRef>,

    /// VIR-lowered default parameter expressions for lambda parameters.
    ///
    /// Keyed by lambda `NodeId` and parameter slot index.
    pub lambda_default_inits: FxHashMap<(NodeId, usize), VirRef>,

    /// VIR-lowered default field initializer expressions.
    ///
    /// Keyed by semantic `FieldId`. These are used when struct/class literals
    /// omit fields that have defaults.
    pub field_default_inits: FxHashMap<FieldId, VirRef>,

    /// VIR-lowered annotation data for field annotations.
    ///
    /// Keyed by semantic `FieldId`. Each entry is a list of `VirAnnotation`
    /// instances for that field, in declaration order. Used by codegen to
    /// build annotation instances without reaching back to AST `Expr` nodes.
    pub annotation_inits: FxHashMap<FieldId, Vec<VirAnnotation>>,

    /// Pre-resolved module export bindings for the main program's top-level
    /// destructuring imports (`let { foo } = import "mod"`).
    ///
    /// Keyed by local binding symbol. Value is `(module_id, export_name, export_vir_type)`.
    /// Populated during VIR lowering so codegen can register module bindings
    /// without reaching back into NodeMap.
    pub module_bindings: FxHashMap<Symbol, (ModuleId, Symbol, VirTypeId)>,

    /// Pre-resolved module export bindings for imported modules' top-level
    /// destructuring imports.
    ///
    /// Keyed by module path string, then by local binding symbol.
    /// Value is `(module_id, export_name, export_vir_type)`.
    pub module_module_bindings: FxHashMap<String, FxHashMap<Symbol, (ModuleId, Symbol, VirTypeId)>>,

    /// Base index of VIR-monomorphized functions within `functions`.
    ///
    /// Functions at indices `>= vir_monomorph_base` were produced by the VIR
    /// monomorphization pass and are referenced by `CallTarget::VirDirect`.
    /// Set by `run_vir_monomorphize`; defaults to `usize::MAX` (no VIR monomorphs).
    pub vir_monomorph_base: usize,

    /// Entity metadata: type definitions, field definitions, and method
    /// definitions.  Populated during VIR lowering from sema's
    /// `EntityRegistry`.  Replaces `EntityView` as the VIR-native source
    /// of entity-level data for codegen.
    pub entity_metadata: VirEntityMetadata,

    /// Implement-dispatch metadata: external function bindings, generic
    /// external dispatch, and implement-block method bindings.  Populated
    /// during VIR lowering from sema's `ImplementRegistry`.  Replaces
    /// codegen's `ImplementView` as the lookup source.
    pub implement_dispatch: VirImplementDispatch,

    /// VIR-native free-function monomorph instances.
    ///
    /// Keyed by mangled `NameId`. Populated during the VIR monomorph
    /// population pass (vol-3on3). Codegen reads these instead of sema's
    /// `MonomorphCache` once the VIR monomorph path is active.
    pub free_monomorphs: FxHashMap<NameId, VirMonomorphInfo>,

    /// Reverse index from `MonomorphKey` to mangled `NameId`.
    ///
    /// Allows codegen call sites to look up free-function monomorph info
    /// by the same `MonomorphKey` that sema's `MonomorphCache` uses.
    pub free_monomorphs_by_key: FxHashMap<MonomorphKey, NameId>,

    /// VIR-native class method monomorph instances.
    ///
    /// Keyed by `ClassMethodMonomorphKey`. Populated during the VIR
    /// monomorph population pass (vol-40jn). Codegen reads these instead
    /// of sema's `ClassMethodMonomorphCache`.
    pub class_method_monomorphs: FxHashMap<ClassMethodMonomorphKey, VirClassMethodMonomorphInfo>,

    /// VIR-native static method monomorph instances.
    ///
    /// Keyed by `StaticMethodMonomorphKey`. Populated during the VIR
    /// monomorph population pass (vol-bklt). Codegen reads these instead
    /// of sema's `StaticMethodMonomorphCache`.
    pub static_method_monomorphs: FxHashMap<StaticMethodMonomorphKey, VirStaticMethodMonomorphInfo>,

    /// Per-module string interners for resolving module-local Symbol IDs.
    ///
    /// Keyed by module path. Each module has its own interner because modules
    /// are parsed independently and their Symbol IDs are disjoint from the
    /// main program's interner. Used by codegen when compiling module function
    /// bodies via `compile_env!`.
    pub module_interners: FxHashMap<String, Rc<Interner>>,

    /// String interner for resolving Symbol IDs to strings.
    ///
    /// Rc-shared with AnalyzedProgram during the transition period.
    /// Codegen uses this to resolve field names, method names, and other
    /// symbol-based identifiers.
    pub interner: Rc<Interner>,

    /// Name table for resolving NameIds to qualified names and module paths.
    ///
    /// Rc-shared with AnalyzedProgram during the transition period.
    /// Codegen uses this for module path resolution, function/type name
    /// lookup, and NameId-based dispatch.
    pub name_table: Rc<NameTable>,
}

impl VirProgram {
    /// Look up a VIR function by its monomorphized mangled `NameId`.
    pub fn get_monomorph(&self, mangled_name_id: NameId) -> Option<&VirFunction> {
        self.monomorph_map
            .get(&mangled_name_id)
            .map(|&idx| &self.functions[idx])
    }

    /// Look up a VIR function by its semantic `FunctionId`.
    pub fn get_function(&self, func_id: FunctionId) -> Option<&VirFunction> {
        self.function_map
            .get(&func_id)
            .map(|&idx| &self.functions[idx])
    }

    /// Look up a VIR function by its semantic `MethodId`.
    pub fn get_method(&self, method_id: MethodId) -> Option<&VirFunction> {
        self.method_map
            .get(&method_id)
            .map(|&idx| &self.functions[idx])
    }

    /// Look up a generic VIR function template by its original `NameId`.
    pub fn get_generic_function(&self, original_name: NameId) -> Option<&VirFunction> {
        self.generic_map
            .get(&original_name)
            .map(|&idx| &self.generic_functions[idx])
    }

    /// Look up a VIR test body by the test case's span.
    pub fn get_test(&self, span: Span) -> Option<&VirBody> {
        self.tests.iter().find(|t| t.span == span).map(|t| &t.body)
    }

    /// Look up a VIR default initializer expression by semantic `FieldId`.
    pub fn get_field_default(&self, field_id: FieldId) -> Option<&VirRef> {
        self.field_default_inits.get(&field_id)
    }

    /// Look up a VIR default parameter expression by `FunctionId` and slot.
    pub fn get_function_default(&self, func_id: FunctionId, slot: usize) -> Option<&VirRef> {
        self.function_default_inits.get(&(func_id, slot))
    }

    /// Look up a VIR default parameter expression by `MethodId` and slot.
    pub fn get_method_default(&self, method_id: MethodId, slot: usize) -> Option<&VirRef> {
        self.method_default_inits.get(&(method_id, slot))
    }

    /// Look up a VIR default parameter expression by lambda `NodeId` and slot.
    pub fn get_lambda_default(&self, lambda_node_id: NodeId, slot: usize) -> Option<&VirRef> {
        self.lambda_default_inits.get(&(lambda_node_id, slot))
    }

    /// Look up VIR-lowered annotations for a field by semantic `FieldId`.
    pub fn get_field_annotations(&self, field_id: FieldId) -> Option<&[VirAnnotation]> {
        self.annotation_inits.get(&field_id).map(|v| v.as_slice())
    }

    /// Get a read-only reference to the entity metadata.
    pub fn entity_metadata(&self) -> &VirEntityMetadata {
        &self.entity_metadata
    }

    /// Get a mutable reference to the entity metadata (for population).
    pub fn entity_metadata_mut(&mut self) -> &mut VirEntityMetadata {
        &mut self.entity_metadata
    }

    /// Get a read-only reference to the implement-dispatch metadata.
    pub fn implement_dispatch(&self) -> &VirImplementDispatch {
        &self.implement_dispatch
    }

    /// Look up external function binding by short name.
    pub fn external_func_by_name(&self, name: &str) -> Option<VirExternalFuncInfo> {
        self.implement_dispatch.external_func_by_name(name)
    }

    /// Look up generic external function metadata by short name.
    pub fn generic_external_by_name(&self, name: &str) -> Option<&VirGenericExternalInfo> {
        self.implement_dispatch.generic_external_by_name(name)
    }

    /// Look up generic external method metadata by defining type and method name.
    pub fn generic_external_method(
        &self,
        type_def_id: TypeDefId,
        method_name: NameId,
    ) -> Option<&VirGenericExternalInfo> {
        self.implement_dispatch
            .generic_external_method(type_def_id, method_name)
    }

    /// Look up an implement-block method binding by type name key and method name.
    pub fn implement_method_by_name(
        &self,
        type_name_id: NameId,
        method_name_id: NameId,
    ) -> Option<&VirMethodImplInfo> {
        self.implement_dispatch
            .method_by_name(type_name_id, method_name_id)
    }

    // ---- Name resolution accessors ----

    /// Get read-only access to the string interner.
    pub fn interner(&self) -> &Interner {
        &self.interner
    }

    /// Clone the interner Rc for APIs that need shared ownership.
    pub fn interner_rc(&self) -> Rc<Interner> {
        Rc::clone(&self.interner)
    }

    /// Get a module's interner by module path.
    ///
    /// Returns the module-specific interner for symbol resolution during
    /// compilation of module function bodies.
    pub fn module_interner(&self, module_path: &str) -> Option<&Interner> {
        self.module_interners.get(module_path).map(|rc| rc.as_ref())
    }

    /// Clone a module's interner Rc for APIs that need shared ownership.
    pub fn module_interner_rc(&self, module_path: &str) -> Option<Rc<Interner>> {
        self.module_interners.get(module_path).cloned()
    }

    /// Get read-only access to the name table.
    pub fn name_table(&self) -> &NameTable {
        &self.name_table
    }

    /// Clone the name table Rc for APIs that need shared ownership.
    pub fn name_table_rc(&self) -> Rc<NameTable> {
        Rc::clone(&self.name_table)
    }

    /// Resolve a symbol to its string representation.
    pub fn resolve_symbol(&self, sym: Symbol) -> &str {
        self.interner.resolve(sym)
    }

    /// Resolve a NameId to display form (e.g. module::Type::method).
    pub fn display_name(&self, name_id: NameId) -> String {
        self.name_table.display(name_id)
    }

    /// Resolve a NameId to its last segment string.
    pub fn last_segment(&self, name_id: NameId) -> Option<String> {
        self.name_table.last_segment_str(name_id)
    }

    /// Resolve NameId by module and symbol segments using the interner.
    pub fn try_name_id(&self, module_id: ModuleId, segments: &[Symbol]) -> Option<NameId> {
        self.name_table.name_id(module_id, segments, &self.interner)
    }

    /// Resolve NameId by module and symbol segments, panicking when missing.
    pub fn name_id(&self, module_id: ModuleId, segments: &[Symbol]) -> NameId {
        self.try_name_id(module_id, segments).unwrap_or_else(|| {
            panic!(
                "name_id not found for segments {:?} in {:?}",
                segments, module_id
            )
        })
    }

    /// Resolve NameId by module and symbol segments with an explicit interner.
    pub fn try_name_id_with_interner(
        &self,
        module_id: ModuleId,
        segments: &[Symbol],
        interner: &Interner,
    ) -> Option<NameId> {
        self.name_table.name_id(module_id, segments, interner)
    }

    /// Resolve method NameId by Symbol.
    pub fn try_method_name_id(&self, name: Symbol) -> Option<NameId> {
        let namer = NamerLookup::new(&self.name_table, &self.interner);
        namer.method(name)
    }

    /// Resolve method NameId by short string.
    pub fn try_method_name_id_by_str(&self, name_str: &str) -> Option<NameId> {
        vole_identity::method_name_id_by_str(&self.name_table, &self.interner, name_str)
    }

    /// Resolve method NameId by short string, panicking when missing.
    pub fn method_name_id_by_str(&self, name_str: &str) -> NameId {
        self.try_method_name_id_by_str(name_str)
            .unwrap_or_else(|| panic!("method name_id not found for '{}'", name_str))
    }

    /// Resolve function NameId by module and Symbol.
    pub fn try_function_name_id(&self, module_id: ModuleId, name: Symbol) -> Option<NameId> {
        let namer = NamerLookup::new(&self.name_table, &self.interner);
        namer.function(module_id, name)
    }

    /// Resolve function NameId by module and Symbol, panicking when missing.
    pub fn function_name_id(&self, module_id: ModuleId, name: Symbol) -> NameId {
        self.try_function_name_id(module_id, name)
            .unwrap_or_else(|| {
                panic!(
                    "function name_id not found for '{}'",
                    self.resolve_symbol(name)
                )
            })
    }

    /// Return the main module ID from the name table.
    pub fn main_module(&self) -> ModuleId {
        self.name_table.main_module()
    }

    /// Return module ID for a path, falling back to main module.
    pub fn module_id_or_main(&self, path: &str) -> ModuleId {
        self.name_table
            .module_id_if_known(path)
            .unwrap_or_else(|| self.name_table.main_module())
    }

    /// Return module ID when known for a path.
    pub fn module_id_if_known(&self, path: &str) -> Option<ModuleId> {
        self.name_table.module_id_if_known(path)
    }

    /// Return the module path string for a module ID.
    pub fn module_path(&self, module_id: ModuleId) -> &str {
        self.name_table.module_path(module_id)
    }
}
