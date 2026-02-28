// program.rs
//
// VirProgram: the complete VIR output from sema/lowering, consumed by codegen.
// This is the clean boundary between VIR lowering and code generation.

use rustc_hash::FxHashMap;
use vole_identity::{FieldId, FunctionId, MethodId, NameId, NodeId, Span, Symbol, TypeDefId};

use crate::entity_metadata::VirEntityMetadata;
use crate::func::{VirBody, VirFunction, VirTest};
use crate::implement_dispatch::{
    VirExternalFuncInfo, VirGenericExternalInfo, VirImplementDispatch, VirMethodImplInfo,
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
}
