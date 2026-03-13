// implement_dispatch.rs
//
// VIR-native implement-dispatch metadata.
//
// Contains lookup maps for external function bindings, generic external
// dispatch, and implement-block method bindings.  Populated once during
// VIR lowering from sema's `ImplementRegistry`, then consumed by codegen
// without reaching back into sema.

use rustc_hash::FxHashMap;
use vole_identity::{NameId, Symbol, TypeDefId, TypeId};

// ---------------------------------------------------------------------------
// External function binding
// ---------------------------------------------------------------------------

/// External (native) function binding metadata.
///
/// `module_path` and `native_name` are single-segment `NameId`s for cheap Copy.
/// Use `name_table.last_segment_str(field)` to get the string value.
///
/// `module_path_sym` and `native_name_sym` are pre-interned `Symbol`s of the
/// same strings, so that post-monomorphization rederive can construct
/// `CallTarget::Native` without needing `&mut Interner`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VirExternalFuncInfo {
    pub module_path: NameId,
    pub native_name: NameId,
    /// Pre-interned Symbol for the module path string (e.g. "vole:std:runtime").
    pub module_path_sym: Symbol,
    /// Pre-interned Symbol for the native function name string (e.g. "empty").
    pub native_name_sym: Symbol,
}

// ---------------------------------------------------------------------------
// Generic external dispatch
// ---------------------------------------------------------------------------

/// Type-to-intrinsic mapping kind for generic external dispatch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VirTypeMappingKind {
    /// Match only a specific concrete type.
    Exact(TypeId),
    /// Fallback when no exact type arm matches.
    Default,
}

/// A where-mapping arm for generic external dispatch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VirTypeMappingEntry {
    /// Which kind of arm this is (exact or default).
    pub kind: VirTypeMappingKind,
    /// The intrinsic key to use when the function is called with this type.
    pub intrinsic_key: String,
}

/// Generic external function metadata with type-to-intrinsic mappings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VirGenericExternalInfo {
    /// The module path for this external function.
    pub module_path: NameId,
    /// Type-to-intrinsic mappings from the where block.
    pub type_mappings: Vec<VirTypeMappingEntry>,
}

// ---------------------------------------------------------------------------
// Implement-block method binding
// ---------------------------------------------------------------------------

/// Function signature metadata for an implement-block method.
///
/// A VIR-native equivalent of sema's `FunctionType`, using
/// `vole_identity::TypeId` (sema-compatible) so codegen can pass the
/// ids straight to the type arena without conversion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VirFuncSignature {
    /// Whether this function is a closure.
    pub is_closure: bool,
    /// Parameter types in declaration order.
    pub params: Vec<TypeId>,
    /// Return type.
    pub return_type: TypeId,
}

/// Implement-block method binding metadata.
#[derive(Debug, Clone)]
pub struct VirMethodImplInfo {
    /// Method signature.
    pub func_sig: VirFuncSignature,
    /// External binding metadata, if this is a native method.
    pub external_info: Option<VirExternalFuncInfo>,
}

// ---------------------------------------------------------------------------
// Top-level container
// ---------------------------------------------------------------------------

/// Complete implement-dispatch metadata for a VIR program.
///
/// Replaces codegen's `ImplementView` as the lookup source for external
/// function bindings and implement-block method dispatch.  Populated once
/// during VIR lowering from sema's `ImplementRegistry`.
#[derive(Debug, Clone, Default)]
pub struct VirImplementDispatch {
    /// External function info by short name (e.g. "print").
    external_funcs: FxHashMap<String, VirExternalFuncInfo>,
    /// Generic external function info by short name.
    generic_externals: FxHashMap<String, VirGenericExternalInfo>,
    /// Generic external method info by (defining type, method name).
    generic_external_methods: FxHashMap<(TypeDefId, NameId), VirGenericExternalInfo>,
    /// Implement-block method bindings by (type name key, method name).
    methods: FxHashMap<(NameId, NameId), VirMethodImplInfo>,
}

// ---------------------------------------------------------------------------
// Population (during lowering)
// ---------------------------------------------------------------------------

impl VirImplementDispatch {
    /// Create an empty dispatch container.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register an external function binding.
    pub fn insert_external_func(&mut self, name: String, info: VirExternalFuncInfo) {
        self.external_funcs.insert(name, info);
    }

    /// Register a generic external function.
    pub fn insert_generic_external(&mut self, name: String, info: VirGenericExternalInfo) {
        self.generic_externals.insert(name, info);
    }

    /// Register a generic external method.
    pub fn insert_generic_external_method(
        &mut self,
        type_def_id: TypeDefId,
        method_name: NameId,
        info: VirGenericExternalInfo,
    ) {
        self.generic_external_methods
            .insert((type_def_id, method_name), info);
    }

    /// Register an implement-block method binding.
    pub fn insert_method(
        &mut self,
        type_name_id: NameId,
        method_name: NameId,
        info: VirMethodImplInfo,
    ) {
        self.methods.insert((type_name_id, method_name), info);
    }
}

// ---------------------------------------------------------------------------
// Queries (used by codegen)
// ---------------------------------------------------------------------------

impl VirImplementDispatch {
    /// Look up external function binding by short name.
    pub fn external_func_by_name(&self, name: &str) -> Option<VirExternalFuncInfo> {
        self.external_funcs.get(name).copied()
    }

    /// Look up generic external function metadata by short name.
    pub fn generic_external_by_name(&self, name: &str) -> Option<&VirGenericExternalInfo> {
        self.generic_externals.get(name)
    }

    /// Look up generic external method metadata by defining type and method name.
    pub fn generic_external_method(
        &self,
        type_def_id: TypeDefId,
        method_name: NameId,
    ) -> Option<&VirGenericExternalInfo> {
        self.generic_external_methods
            .get(&(type_def_id, method_name))
    }

    /// Look up an implement-block method binding by type name key and method name.
    pub fn method_by_name(
        &self,
        type_name_id: NameId,
        method_name_id: NameId,
    ) -> Option<&VirMethodImplInfo> {
        self.methods.get(&(type_name_id, method_name_id))
    }
}

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn make_name_id(n: u32) -> NameId {
        NameId::new_for_test(n)
    }

    fn make_type_def_id(n: u32) -> TypeDefId {
        TypeDefId::new(n)
    }

    #[test]
    fn empty_dispatch() {
        let dispatch = VirImplementDispatch::new();
        assert!(dispatch.external_func_by_name("print").is_none());
        assert!(dispatch.generic_external_by_name("length").is_none());
        assert!(
            dispatch
                .generic_external_method(make_type_def_id(1), make_name_id(10))
                .is_none()
        );
        assert!(
            dispatch
                .method_by_name(make_name_id(1), make_name_id(2))
                .is_none()
        );
    }

    #[test]
    fn insert_and_query_external_func() {
        let mut dispatch = VirImplementDispatch::new();
        let info = VirExternalFuncInfo {
            module_path: make_name_id(100),
            native_name: make_name_id(101),
            module_path_sym: Symbol::new_for_test(100),
            native_name_sym: Symbol::new_for_test(101),
        };
        dispatch.insert_external_func("print".into(), info);

        let result = dispatch.external_func_by_name("print");
        assert_eq!(result, Some(info));
        assert!(dispatch.external_func_by_name("println").is_none());
    }

    #[test]
    fn insert_and_query_generic_external() {
        let mut dispatch = VirImplementDispatch::new();
        let info = VirGenericExternalInfo {
            module_path: make_name_id(200),
            type_mappings: vec![VirTypeMappingEntry {
                kind: VirTypeMappingKind::Default,
                intrinsic_key: "array_length_default".into(),
            }],
        };
        dispatch.insert_generic_external("length".into(), info.clone());

        let result = dispatch.generic_external_by_name("length").unwrap();
        assert_eq!(result.module_path, make_name_id(200));
        assert_eq!(result.type_mappings.len(), 1);
    }

    #[test]
    fn insert_and_query_generic_external_method() {
        let mut dispatch = VirImplementDispatch::new();
        let tdef = make_type_def_id(5);
        let method_name = make_name_id(50);
        let info = VirGenericExternalInfo {
            module_path: make_name_id(300),
            type_mappings: vec![],
        };
        dispatch.insert_generic_external_method(tdef, method_name, info);

        let result = dispatch.generic_external_method(tdef, method_name).unwrap();
        assert_eq!(result.module_path, make_name_id(300));

        // Different key returns None.
        assert!(
            dispatch
                .generic_external_method(make_type_def_id(999), method_name)
                .is_none()
        );
    }

    #[test]
    fn insert_and_query_method() {
        let mut dispatch = VirImplementDispatch::new();
        let type_name = make_name_id(10);
        let method_name = make_name_id(20);
        let info = VirMethodImplInfo {
            func_sig: VirFuncSignature {
                is_closure: false,
                params: vec![TypeId::I64],
                return_type: TypeId::BOOL,
            },
            external_info: None,
        };
        dispatch.insert_method(type_name, method_name, info);

        let result = dispatch.method_by_name(type_name, method_name).unwrap();
        assert!(!result.func_sig.is_closure);
        assert_eq!(result.func_sig.params, vec![TypeId::I64]);
        assert_eq!(result.func_sig.return_type, TypeId::BOOL);
        assert!(result.external_info.is_none());
    }
}
