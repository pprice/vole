// instance.rs
//
// VIR-native monomorph instance info types.
//
// These carry the data codegen needs to declare and compile monomorphized
// functions, class methods, and static methods — using VirTypeId where
// possible so codegen can work from VIR types instead of sema TypeIds.
//
// These are *data definitions only*; population logic lives in separate
// tickets (vol-3on3, vol-40jn, vol-bklt).

use rustc_hash::FxHashMap;
use vole_identity::{
    FunctionType, MethodId, MonomorphInstanceTrait, NameId, TypeDefId, TypeId, VirTypeId,
};

use crate::expr::VirExternalMethodInfo;

// ============================================================================
// VirMonomorphInfo — free-function monomorphs
// ============================================================================

/// VIR-native info for a monomorphized free function.
///
/// Mirrors `MonomorphInstance` from vole-identity but adds VirTypeId-level
/// function type information so codegen can eventually avoid reaching back
/// to sema's TypeId-based FunctionType.
#[derive(Debug, Clone)]
pub struct VirMonomorphInfo {
    /// Original generic function name.
    pub original_name: NameId,
    /// Mangled name for this concrete instance.
    pub mangled_name: NameId,
    /// Unique ID used to generate the mangled name.
    pub instance_id: u32,
    /// Concrete function type after substitution (sema TypeIds).
    ///
    /// Retained for the transition period while codegen still builds
    /// Cranelift signatures from `TypeId`-based param/return types.
    pub func_type: FunctionType,
    /// VIR-level function type (params + return as VirTypeIds).
    ///
    /// Used by VIR-path codegen to build signatures without sema TypeIds.
    pub vir_func_type: VirTypeId,
    /// Type parameter substitutions (sema TypeIds).
    ///
    /// Keyed by type param NameId. Retained for the transition period
    /// while fallback codegen still needs sema substitutions.
    pub substitutions: FxHashMap<NameId, TypeId>,
    /// VIR-level type parameter substitutions.
    ///
    /// Keyed by type param NameId. Used by VIR-path codegen.
    pub vir_substitutions: FxHashMap<NameId, VirTypeId>,
}

impl MonomorphInstanceTrait for VirMonomorphInfo {
    fn mangled_name(&self) -> NameId {
        self.mangled_name
    }
    fn instance_id(&self) -> u32 {
        self.instance_id
    }
    fn func_type(&self) -> &FunctionType {
        &self.func_type
    }
    fn substitutions(&self) -> &FxHashMap<NameId, TypeId> {
        &self.substitutions
    }
}

// ============================================================================
// VirClassMethodMonomorphInfo — class instance method monomorphs
// ============================================================================

/// VIR-native info for a monomorphized class instance method.
///
/// Mirrors `ClassMethodMonomorphInstance` from vole-identity but adds
/// VirTypeId-level type information.
#[derive(Debug, Clone)]
pub struct VirClassMethodMonomorphInfo {
    /// The class's NameId.
    pub class_name: NameId,
    /// Original method name.
    pub method_name: NameId,
    /// Mangled name for this concrete instance (e.g. "Container_i64__compute_hash").
    pub mangled_name: NameId,
    /// Unique ID used to generate the mangled name.
    pub instance_id: u32,
    /// Concrete method type after substitution (sema TypeIds).
    ///
    /// Retained for the transition period while codegen still builds
    /// Cranelift signatures from `TypeId`-based param/return types.
    pub func_type: FunctionType,
    /// VIR-level function type (params + return as VirTypeIds).
    pub vir_func_type: VirTypeId,
    /// Type parameter substitutions (sema TypeIds).
    pub substitutions: FxHashMap<NameId, TypeId>,
    /// VIR-level type parameter substitutions.
    pub vir_substitutions: FxHashMap<NameId, VirTypeId>,
    /// External method info (if this is an external/native method).
    ///
    /// When present, the method is a runtime function and doesn't need
    /// JIT compilation — codegen calls the runtime function directly.
    pub external_info: Option<VirExternalMethodInfo>,
    /// Pre-computed self type (e.g. Foo<String> for a method on Foo<String>).
    ///
    /// Sema TypeId — retained because codegen uses it to build the self
    /// parameter binding.
    pub self_type: TypeId,
    /// VIR-level self type.
    pub vir_self_type: VirTypeId,
}

impl MonomorphInstanceTrait for VirClassMethodMonomorphInfo {
    fn mangled_name(&self) -> NameId {
        self.mangled_name
    }
    fn instance_id(&self) -> u32 {
        self.instance_id
    }
    fn func_type(&self) -> &FunctionType {
        &self.func_type
    }
    fn substitutions(&self) -> &FxHashMap<NameId, TypeId> {
        &self.substitutions
    }
}

// ============================================================================
// VirStaticMethodMonomorphInfo — class static method monomorphs
// ============================================================================

/// VIR-native info for a monomorphized class static method.
///
/// Mirrors `StaticMethodMonomorphInstance` from vole-identity but adds
/// VirTypeId-level type information.
#[derive(Debug, Clone)]
pub struct VirStaticMethodMonomorphInfo {
    /// The class's NameId.
    pub class_name: NameId,
    /// Original method name.
    pub method_name: NameId,
    /// Mangled name for this concrete instance (e.g. "Box__static_create__mono_0").
    pub mangled_name: NameId,
    /// Unique ID used to generate the mangled name.
    pub instance_id: u32,
    /// Concrete method type after substitution (sema TypeIds).
    ///
    /// Retained for the transition period while codegen still builds
    /// Cranelift signatures from `TypeId`-based param/return types.
    pub func_type: FunctionType,
    /// VIR-level function type (params + return as VirTypeIds).
    pub vir_func_type: VirTypeId,
    /// Type parameter substitutions (sema TypeIds).
    pub substitutions: FxHashMap<NameId, TypeId>,
    /// VIR-level type parameter substitutions.
    pub vir_substitutions: FxHashMap<NameId, VirTypeId>,
}

impl MonomorphInstanceTrait for VirStaticMethodMonomorphInfo {
    fn mangled_name(&self) -> NameId {
        self.mangled_name
    }
    fn instance_id(&self) -> u32 {
        self.instance_id
    }
    fn func_type(&self) -> &FunctionType {
        &self.func_type
    }
    fn substitutions(&self) -> &FxHashMap<NameId, TypeId> {
        &self.substitutions
    }
}

// ============================================================================
// VirImplementMethodMonomorphInfo — implement-block default method monomorphs
// ============================================================================

/// VIR-native info for a monomorphized implement-block default method.
///
/// Mirrors `ImplementMethodMonomorphInstance` from vole-identity but adds
/// VirTypeId-level type information. These represent concrete instantiations
/// of interface default methods for specific implementing types and type args
/// (e.g., `[i64].map(...)`, `[i64].filter(...)` from `extend [T] with Iterable<T>`).
#[derive(Debug, Clone)]
pub struct VirImplementMethodMonomorphInfo {
    /// The interface's TypeDefId (e.g., Iterable).
    pub interface_type_def_id: TypeDefId,
    /// The implementing type's TypeDefId (e.g., array).
    pub implementing_type_def_id: TypeDefId,
    /// The method's MethodId on the implementing type.
    pub method_id: MethodId,
    /// The method's NameId.
    pub method_name: NameId,
    /// Mangled name for this instance (e.g., "__array_iterable_4_count").
    pub mangled_name: NameId,
    /// Unique ID for this instance.
    pub instance_id: u32,
    /// Concrete method type after substitution (sema TypeIds).
    ///
    /// Retained for the transition period while codegen still builds
    /// Cranelift signatures from `TypeId`-based param/return types.
    pub func_type: FunctionType,
    /// VIR-level function type (params + return as VirTypeIds).
    pub vir_func_type: VirTypeId,
    /// Type parameter substitutions (sema TypeIds).
    pub substitutions: FxHashMap<NameId, TypeId>,
    /// VIR-level type parameter substitutions.
    pub vir_substitutions: FxHashMap<NameId, VirTypeId>,
}

impl MonomorphInstanceTrait for VirImplementMethodMonomorphInfo {
    fn mangled_name(&self) -> NameId {
        self.mangled_name
    }
    fn instance_id(&self) -> u32 {
        self.instance_id
    }
    fn func_type(&self) -> &FunctionType {
        &self.func_type
    }
    fn substitutions(&self) -> &FxHashMap<NameId, TypeId> {
        &self.substitutions
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use vole_identity::TypeIdVec;

    fn name(n: u32) -> NameId {
        NameId::new_for_test(n)
    }

    #[test]
    fn vir_monomorph_info_fields() {
        let info = VirMonomorphInfo {
            original_name: name(1),
            mangled_name: name(2),
            instance_id: 0,
            func_type: FunctionType {
                is_closure: false,
                params_id: TypeIdVec::new(),
                return_type_id: TypeId::from_raw(0),
            },
            vir_func_type: VirTypeId::VOID,
            substitutions: FxHashMap::default(),
            vir_substitutions: FxHashMap::default(),
        };
        assert_eq!(info.original_name, name(1));
        assert_eq!(info.mangled_name, name(2));
        assert_eq!(info.instance_id, 0);
    }

    #[test]
    fn vir_class_method_monomorph_info_fields() {
        let info = VirClassMethodMonomorphInfo {
            class_name: name(10),
            method_name: name(11),
            mangled_name: name(12),
            instance_id: 1,
            func_type: FunctionType {
                is_closure: false,
                params_id: TypeIdVec::new(),
                return_type_id: TypeId::from_raw(0),
            },
            vir_func_type: VirTypeId::VOID,
            substitutions: FxHashMap::default(),
            vir_substitutions: FxHashMap::default(),
            external_info: None,
            self_type: TypeId::from_raw(0),
            vir_self_type: VirTypeId::VOID,
        };
        assert_eq!(info.class_name, name(10));
        assert_eq!(info.method_name, name(11));
        assert_eq!(info.mangled_name, name(12));
        assert!(info.external_info.is_none());
    }

    #[test]
    fn vir_class_method_with_external_info() {
        let info = VirClassMethodMonomorphInfo {
            class_name: name(10),
            method_name: name(11),
            mangled_name: name(12),
            instance_id: 2,
            func_type: FunctionType {
                is_closure: false,
                params_id: TypeIdVec::new(),
                return_type_id: TypeId::from_raw(0),
            },
            vir_func_type: VirTypeId::VOID,
            substitutions: FxHashMap::default(),
            vir_substitutions: FxHashMap::default(),
            external_info: Some(VirExternalMethodInfo {
                module_path: name(100),
                native_name: name(101),
            }),
            self_type: TypeId::from_raw(0),
            vir_self_type: VirTypeId::VOID,
        };
        assert!(info.external_info.is_some());
        let ext = info.external_info.unwrap();
        assert_eq!(ext.module_path, name(100));
        assert_eq!(ext.native_name, name(101));
    }

    #[test]
    fn vir_static_method_monomorph_info_fields() {
        let info = VirStaticMethodMonomorphInfo {
            class_name: name(20),
            method_name: name(21),
            mangled_name: name(22),
            instance_id: 3,
            func_type: FunctionType {
                is_closure: false,
                params_id: TypeIdVec::new(),
                return_type_id: TypeId::from_raw(0),
            },
            vir_func_type: VirTypeId::VOID,
            substitutions: FxHashMap::default(),
            vir_substitutions: FxHashMap::default(),
        };
        assert_eq!(info.class_name, name(20));
        assert_eq!(info.method_name, name(21));
        assert_eq!(info.mangled_name, name(22));
        assert_eq!(info.instance_id, 3);
    }

    #[test]
    fn vir_implement_method_monomorph_info_fields() {
        let info = VirImplementMethodMonomorphInfo {
            interface_type_def_id: TypeDefId::new(1),
            implementing_type_def_id: TypeDefId::new(2),
            method_id: MethodId::new(5),
            method_name: name(30),
            mangled_name: name(31),
            instance_id: 4,
            func_type: FunctionType {
                is_closure: false,
                params_id: TypeIdVec::new(),
                return_type_id: TypeId::from_raw(0),
            },
            vir_func_type: VirTypeId::VOID,
            substitutions: FxHashMap::default(),
            vir_substitutions: FxHashMap::default(),
        };
        assert_eq!(info.interface_type_def_id, TypeDefId::new(1));
        assert_eq!(info.implementing_type_def_id, TypeDefId::new(2));
        assert_eq!(info.method_id, MethodId::new(5));
        assert_eq!(info.method_name, name(30));
        assert_eq!(info.mangled_name, name(31));
        assert_eq!(info.instance_id, 4);
    }
}
