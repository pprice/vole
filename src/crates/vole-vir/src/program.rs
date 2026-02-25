// program.rs
//
// VirProgram: the complete VIR output from sema/lowering, consumed by codegen.
// This is the clean boundary between VIR lowering and code generation.

use rustc_hash::FxHashMap;
use vole_identity::{FunctionId, MethodId, NameId, Span, Symbol};

use crate::func::{VirBody, VirFunction, VirTest};
use crate::refs::VirRef;
use crate::type_table::VirTypeTable;

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

    /// Base index of VIR-monomorphized functions within `functions`.
    ///
    /// Functions at indices `>= vir_monomorph_base` were produced by the VIR
    /// monomorphization pass and are referenced by `CallTarget::VirDirect`.
    /// Set by `run_vir_monomorphize`; defaults to `usize::MAX` (no VIR monomorphs).
    pub vir_monomorph_base: usize,
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
}
