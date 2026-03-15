// program.rs
//
// VirProgram: the complete VIR output from sema/lowering, consumed by codegen.
// This is the clean boundary between VIR lowering and code generation.

use std::collections::HashSet;
use std::rc::Rc;

use rustc_hash::FxHashMap;
use vole_identity::{
    FieldId, FunctionId, Interner, MethodId, ModuleId, NameId, NameTable, NamerLookup, NodeId,
    Span, Symbol, TypeDefId, TypeId, VirTypeId,
};

use vole_identity::{
    ClassMethodMonomorphKey, ImplementMethodMonomorphKey, MonomorphKey, StaticMethodMonomorphKey,
};

use crate::entity_metadata::VirEntityMetadata;
use crate::func::{VirBody, VirFunction, VirTest};
use crate::implement_dispatch::{
    VirExternalFuncInfo, VirExternalImport, VirGenericExternalInfo, VirImplementDispatch,
    VirMethodImplInfo,
};
use crate::monomorph::instance::{
    VirClassMethodMonomorphInfo, VirImplementMethodMonomorphInfo, VirMonomorphInfo,
    VirStaticMethodMonomorphInfo,
};
use crate::refs::VirRef;
use crate::type_table::VirTypeTable;
use crate::types::VirAnnotation;

/// Substitution fallback function type.
///
/// Called when VirTypeTable cannot resolve a substituted compound type.
/// Allows the CLI crate to inject sema TypeArena substitution logic without
/// vole-codegen depending on vole-sema.
///
/// Arguments: (type_id, substitution_map) -> Option<TypeId>
pub type SubstituteFallbackFn = dyn Fn(TypeId, &FxHashMap<NameId, TypeId>) -> Option<TypeId>;

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

    /// Per-module compile-time constant values (e.g. `math.PI`).
    ///
    /// Populated during VIR lowering from `TypeArena::module_metadata`.
    /// Keyed by `(ModuleId, NameId)`.
    pub module_constants: FxHashMap<(ModuleId, NameId), vole_identity::ConstantValue>,

    /// Module type exports: `(ModuleId, exports)`.
    ///
    /// Populated during VIR lowering from `SemaType::Module` entries.
    /// Keyed by the sema `TypeId` of the module type so that codegen can
    /// resolve `obj.@field` on module values without arena access.
    pub module_exports: FxHashMap<TypeId, (ModuleId, Vec<(NameId, TypeId)>)>,

    /// Base index of VIR-monomorphized functions within `functions`.
    ///
    /// Functions at indices `>= vir_monomorph_base` were produced by the VIR
    /// monomorphization pass and are referenced by `CallTarget::VirDirect`.
    /// Set by `run_vir_monomorphize`; defaults to `usize::MAX` (no VIR monomorphs).
    pub vir_monomorph_base: usize,

    /// Instance index mapping `MonomorphInstance` to absolute function index.
    ///
    /// Built by the early VIR monomorph pass and merged with the final pass.
    /// Used by `resolve_all_calls` to resolve `Unresolved` calls with monomorph
    /// keys to `VirDirect` targets.
    pub vir_instance_index: crate::monomorph::InstanceIndex,

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

    /// Pre-resolved external function imports for codegen pre-declaration.
    ///
    /// Collected during VIR lowering from all `external("module:path") { ... }`
    /// blocks across the program and imported modules. Codegen iterates these
    /// at startup to declare native imports in the JIT module before any
    /// compilation begins, replacing lazy discovery during AST compilation.
    pub external_imports: Vec<VirExternalImport>,

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

    /// VIR-native implement-block default method monomorph instances.
    ///
    /// Keyed by `ImplementMethodMonomorphKey`. Populated during the VIR
    /// monomorph population pass (vol-cg1s). Codegen reads these instead
    /// of sema's `ImplementMethodMonomorphCache`.
    pub implement_method_monomorphs:
        FxHashMap<ImplementMethodMonomorphKey, VirImplementMethodMonomorphInfo>,

    /// Per-module string interners for resolving module-local Symbol IDs.
    ///
    /// Keyed by module path. Each module has its own interner because modules
    /// are parsed independently and their Symbol IDs are disjoint from the
    /// main program's interner. Used by codegen when compiling module function
    /// bodies via `compile_env!`.
    pub module_interners: FxHashMap<String, Rc<Interner>>,

    /// String interner for resolving Symbol IDs to strings.
    ///
    /// Codegen uses this to resolve field names, method names, and other
    /// symbol-based identifiers.
    pub interner: Rc<Interner>,

    /// Name table for resolving NameIds to qualified names and module paths.
    ///
    /// Codegen uses this for module path resolution, function/type name
    /// lookup, and NameId-based dispatch.
    pub name_table: Rc<NameTable>,

    /// Virtual module IDs for tests blocks. Maps tests block span to its virtual ModuleId.
    pub tests_virtual_modules: FxHashMap<Span, ModuleId>,

    /// The module ID for the main program (may differ from main_module when using shared cache).
    pub module_id: ModuleId,

    /// Module paths that had sema errors. Codegen should skip compiling
    /// function bodies for these modules to avoid INVALID type IDs.
    pub modules_with_errors: HashSet<String>,

    /// Substitution fallback for compound types not yet interned in VirTypeTable.
    ///
    /// Injected by the CLI crate (wraps sema TypeArena::lookup_substitute).
    /// Will be removed once VirTypeTable supports intern-on-substitute.
    pub substitute_fallback: Option<Box<SubstituteFallbackFn>>,
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

    /// Return whether a module with the given path is loaded.
    pub fn has_module(&self, module_path: &str) -> bool {
        self.module_interners.contains_key(module_path)
    }

    /// Return all loaded module paths.
    pub fn module_paths(&self) -> Vec<String> {
        self.module_interners.keys().cloned().collect()
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

    // ---- Methods migrated from AnalyzedProgram ----

    /// Try substituting via the injected fallback (TypeArena wrapper).
    ///
    /// Returns `None` when no fallback was provided or when the fallback itself
    /// cannot resolve the type.
    pub fn substitute_fallback(
        &self,
        ty: TypeId,
        subs: &FxHashMap<NameId, TypeId>,
    ) -> Option<TypeId> {
        self.substitute_fallback.as_ref()?.as_ref()(ty, subs)
    }

    /// Resolve the EntityRegistry NameId used for all array implement dispatch.
    pub fn array_type_name_id(&self) -> Option<NameId> {
        self.entity_metadata.array_name_id()
    }

    /// Resolve a type's canonical entity NameId from its TypeDefId.
    pub fn entity_type_name_id(&self, type_def_id: TypeDefId) -> NameId {
        self.entity_metadata
            .type_name_id(type_def_id)
            .unwrap_or_else(|| {
                panic!(
                    "entity_type_name_id: type def {:?} not in VirEntityMetadata",
                    type_def_id
                )
            })
    }

    /// Resolve a VIR type definition by ID.
    pub fn type_def(&self, type_def_id: TypeDefId) -> &crate::entity_metadata::VirTypeDef {
        self.entity_metadata
            .get_type_def(type_def_id)
            .unwrap_or_else(|| {
                panic!(
                    "type_def: type def {:?} not in VirEntityMetadata",
                    type_def_id
                )
            })
    }

    /// Query-compatible alias for resolving a VIR type definition by ID.
    pub fn get_type(&self, type_def_id: TypeDefId) -> &crate::entity_metadata::VirTypeDef {
        self.type_def(type_def_id)
    }

    /// Resolve a VIR field definition by ID.
    pub fn field_def(&self, field_id: FieldId) -> &crate::VirFieldDef {
        self.entity_metadata
            .get_field_def(field_id)
            .unwrap_or_else(|| panic!("field_def: no VirFieldDef for {field_id:?}"))
    }

    /// Query-compatible alias for resolving a VIR field definition by ID.
    pub fn get_field(&self, field_id: FieldId) -> &crate::VirFieldDef {
        self.field_def(field_id)
    }

    /// Resolve a VIR function definition by ID.
    pub fn function_def(&self, function_id: FunctionId) -> &crate::entity_metadata::VirFunctionDef {
        self.entity_metadata
            .get_function_def(function_id)
            .unwrap_or_else(|| panic!("function_def: no VirFunctionDef for {function_id:?}"))
    }

    /// Resolve a VIR method definition by ID.
    pub fn method_def(&self, method_id: MethodId) -> &crate::entity_metadata::VirMethodDef {
        self.entity_metadata
            .get_method_def(method_id)
            .unwrap_or_else(|| panic!("method_def: no VirMethodDef for {method_id:?}"))
    }

    /// Query-compatible alias for resolving a VIR method definition by ID.
    pub fn get_method_def(&self, method_id: MethodId) -> &crate::entity_metadata::VirMethodDef {
        self.method_def(method_id)
    }

    /// Return the sema signature TypeId for a method.
    pub fn method_signature_id(&self, method_id: MethodId) -> TypeId {
        self.method_def(method_id).signature_id
    }

    /// Return all field IDs declared on a type definition.
    pub fn fields_on_type(&self, type_def_id: TypeDefId) -> impl Iterator<Item = FieldId> + '_ {
        self.entity_metadata
            .fields_on_type(type_def_id)
            .unwrap_or(&[])
            .iter()
            .copied()
    }

    /// Return true when a global is present for the given NameId.
    pub fn has_global(&self, name_id: NameId) -> bool {
        self.entity_metadata.has_global(name_id)
    }

    /// Resolve type definition by NameId.
    pub fn try_type_def_id(&self, name_id: NameId) -> Option<TypeDefId> {
        self.entity_metadata.type_by_name(name_id)
    }

    /// Resolve semantic FunctionId by NameId.
    pub fn function_id_by_name_id(&self, name_id: NameId) -> Option<FunctionId> {
        self.entity_metadata.function_by_name(name_id)
    }

    /// Resolve a string type name in a module context.
    pub fn resolve_type_def_by_str(&self, module_id: ModuleId, name: &str) -> Option<TypeDefId> {
        self.entity_metadata.resolve_type_def_by_str(
            self.interner(),
            self.name_table(),
            module_id,
            name,
        )
    }

    /// Return sentinel base type for a sentinel TypeDef, when present.
    pub fn sentinel_base_type(&self, type_def_id: TypeDefId) -> Option<TypeId> {
        self.type_def(type_def_id).base_type_id
    }

    /// Return whether a type definition is a sentinel.
    pub fn is_sentinel_type(&self, type_def_id: TypeDefId) -> bool {
        self.entity_type_is_sentinel(type_def_id)
    }

    /// Return whether a type definition is an interface.
    pub fn is_interface_type(&self, type_def_id: TypeDefId) -> bool {
        self.entity_metadata
            .type_def_kind(type_def_id)
            .is_some_and(|k| k.is_interface())
    }

    /// Return interface method binding return type, when a binding exists.
    pub fn method_binding_return_type(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<TypeId> {
        self.entity_metadata
            .find_method_binding(type_def_id, method_name_id)
            .map(|binding| binding.sema_func_type.return_type_id)
    }

    /// Find a method on a type by method NameId.
    pub fn find_method(&self, type_def_id: TypeDefId, method_name_id: NameId) -> Option<MethodId> {
        self.entity_metadata
            .find_method_on_type(type_def_id, method_name_id)
    }

    /// Return direct method IDs declared on a type definition.
    pub fn type_methods(&self, type_def_id: TypeDefId) -> Vec<MethodId> {
        self.entity_metadata
            .methods_on_type(type_def_id)
            .map(|s| s.to_vec())
            .unwrap_or_default()
    }

    /// Build interface type-parameter substitutions for a concrete implementation.
    pub fn interface_impl_type_param_subs(
        &self,
        implementing_type_id: TypeDefId,
        interface_id: TypeDefId,
    ) -> FxHashMap<NameId, TypeId> {
        let type_params = self.entity_type_params(interface_id);
        let type_args = self
            .entity_metadata
            .implementation_sema_type_args(implementing_type_id, interface_id);
        type_params
            .into_iter()
            .zip(type_args.iter().copied())
            .collect()
    }

    /// Build VirTypeId-native interface type-parameter substitutions for a concrete
    /// implementation.
    pub fn interface_impl_type_param_vir_subs(
        &self,
        implementing_type_id: TypeDefId,
        interface_id: TypeDefId,
    ) -> FxHashMap<NameId, VirTypeId> {
        let sema_subs = self.interface_impl_type_param_subs(implementing_type_id, interface_id);
        sema_subs
            .into_iter()
            .map(|(name, tid)| {
                let vir_ty = self.type_table.lookup_type_id(tid).unwrap_or_else(|| {
                    debug_assert!(
                        false,
                        "interface impl sub TypeId({}) not in VirTypeTable",
                        tid.raw()
                    );
                    VirTypeId::UNKNOWN
                });
                (name, vir_ty)
            })
            .collect()
    }

    /// Get the full NameId for a semantic method.
    pub fn method_full_name(&self, method_id: MethodId) -> NameId {
        self.entity_metadata
            .method_full_name_id(method_id)
            .unwrap_or_else(|| {
                panic!(
                    "method_full_name: method {:?} not in VirEntityMetadata",
                    method_id
                )
            })
    }

    /// Return all interfaces implemented by a type definition.
    pub fn implemented_interfaces(&self, type_def_id: TypeDefId) -> Vec<TypeDefId> {
        self.entity_metadata.implemented_interfaces(type_def_id)
    }

    /// Return all implement block entries (main program + all modules) that
    /// target the given type.
    pub fn implement_blocks_for_type(
        &self,
        type_def_id: TypeDefId,
    ) -> impl Iterator<Item = &crate::VirImplementBlockEntry> {
        let em = &self.entity_metadata;
        em.implement_blocks()
            .iter()
            .chain(
                em.all_module_implement_blocks()
                    .flat_map(|(_, entries)| entries.iter()),
            )
            .filter(move |entry| entry.type_def_id == type_def_id)
    }

    /// Return external binding metadata for a method, when available.
    pub fn method_external_binding(
        &self,
        method_id: MethodId,
    ) -> Option<&crate::VirExternalMethodInfo> {
        self.method_def(method_id).external_binding.as_ref()
    }

    /// Return true when all methods on a type are external-only.
    pub fn is_external_only(&self, type_def_id: TypeDefId) -> bool {
        self.entity_metadata.is_external_only(type_def_id)
    }

    /// Return the single abstract method for functional interfaces.
    pub fn is_functional_interface(&self, type_def_id: TypeDefId) -> Option<MethodId> {
        self.entity_metadata.is_functional(type_def_id)
    }

    /// Return all test-scoped virtual module IDs.
    pub fn tests_virtual_module_ids(&self) -> Vec<ModuleId> {
        self.tests_virtual_modules.values().copied().collect()
    }

    /// Return function parameter TypeIds by FunctionId.
    pub fn function_param_type_ids(&self, func_id: FunctionId) -> Vec<TypeId> {
        self.function_def(func_id).sema_param_types.clone()
    }

    /// Return global declared VirTypeId by NameId.
    pub fn global_vir_type(&self, name_id: NameId) -> Option<VirTypeId> {
        let global_id = self.entity_metadata.global_by_name(name_id)?;
        Some(
            self.entity_metadata
                .get_global_def(global_id)
                .expect("global_vir_type: global ID not in VirEntityMetadata")
                .vir_ty,
        )
    }

    /// Return whether a function parameter has a default expression.
    pub fn has_function_default_expr(&self, func_id: FunctionId, param_idx: usize) -> bool {
        self.function_def(func_id)
            .has_defaults
            .get(param_idx)
            .copied()
            .unwrap_or(false)
    }

    /// Return whether a method parameter has a default expression.
    pub fn has_method_default_expr(&self, method_id: MethodId, param_idx: usize) -> bool {
        self.method_def(method_id)
            .has_param_defaults
            .get(param_idx)
            .copied()
            .unwrap_or(false)
    }

    /// Return imported-module interner for a module ID, when available.
    pub fn module_interner_for_id(&self, module_id: ModuleId) -> Option<&Interner> {
        let module_path = self.module_path(module_id);
        self.module_interner(module_path)
    }

    /// Return whether a type definition is marked as an annotation type.
    pub fn type_is_annotation(&self, type_def_id: TypeDefId) -> bool {
        self.entity_metadata.is_annotation(type_def_id)
    }

    /// Return interface method IDs in deterministic slot order.
    pub fn interface_method_ids_ordered(&self, interface_type_def_id: TypeDefId) -> Vec<MethodId> {
        self.entity_metadata
            .interface_methods_ordered(interface_type_def_id)
    }

    /// Return declared type parameter NameIds for a type definition.
    pub fn entity_type_params(&self, type_def_id: TypeDefId) -> Vec<NameId> {
        self.entity_metadata
            .type_params(type_def_id)
            .map(|s| s.to_vec())
            .unwrap_or_default()
    }

    /// Return whether a type definition is a sentinel type.
    pub fn entity_type_is_sentinel(&self, type_def_id: TypeDefId) -> bool {
        self.entity_metadata
            .type_def_kind(type_def_id)
            .is_some_and(|k| k.is_sentinel())
    }

    /// Find a type by its short (last-segment) name.
    pub fn type_by_short_name(&self, short_name: &str) -> Option<TypeDefId> {
        self.entity_metadata.type_by_short_name(short_name)
    }

    /// Return whether a VIR function belongs to the given module.
    pub fn vir_function_in_module(&self, func: &VirFunction, module_id: ModuleId) -> bool {
        if let Some(method_id) = func.method_id {
            let method_def = self.get_method_def(method_id);
            self.get_type(method_def.defining_type).module == module_id
        } else {
            self.function_def(func.id).module == module_id
        }
    }

    /// Resolve the implement-registry type key NameId from a `VirTypeId`.
    ///
    /// Inspects the `VirTypeTable` directly for Array / Class / Struct, and
    /// falls back through `vir_to_sema_type_id_lossy` for primitives that are
    /// in the pre-computed `impl_type_names` map.
    pub fn impl_type_name_id_from_vir_type_id(&self, vir_ty: VirTypeId) -> Option<NameId> {
        let entity_metadata = &self.entity_metadata;
        let table = &self.type_table;
        match table.get(vir_ty) {
            crate::types::VirType::Array { .. } => entity_metadata.array_name_id(),
            crate::types::VirType::Class { def, .. }
            | crate::types::VirType::Struct { def, .. } => entity_metadata.type_name_id(*def),
            _ => {
                // Primitives, Range, Handle: try the pre-computed map keyed by sema TypeId.
                let sema_id = self.type_table.vir_to_type_id(vir_ty);
                entity_metadata.impl_type_name(sema_id)
            }
        }
    }

    /// VirTypeId-accepting overload of implement method lookup.
    ///
    /// Converts VirTypeId to the implement-registry NameId via
    /// `impl_type_name_id_from_vir_type_id`, then delegates to
    /// `implement_method_by_name`.
    pub fn implement_method_for_type_v(
        &self,
        vir_ty: VirTypeId,
        method_name_id: NameId,
    ) -> Option<(NameId, &VirMethodImplInfo)> {
        let type_name_id = self.impl_type_name_id_from_vir_type_id(vir_ty)?;
        let method_impl = self.implement_method_by_name(type_name_id, method_name_id)?;
        Some((type_name_id, method_impl))
    }
}
