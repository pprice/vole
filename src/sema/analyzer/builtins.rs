//! Built-in interface and method registration for EntityRegistry.

use super::Analyzer;
use crate::frontend::Interner;
use crate::identity::Namer;
use crate::sema::implement_registry::{
    ExternalMethodInfo, ImplTypeId, MethodImpl, PrimitiveTypeId,
};
use crate::sema::{FunctionType, LegacyType, PrimitiveType};

impl Analyzer {
    /// Register built-in interfaces and their implementations
    /// NOTE: This is temporary - will eventually come from stdlib/traits.void
    pub(super) fn register_builtins(&mut self) {
        // For now, just set up the registries - actual builtin methods
        // will be registered when we have the interner available in a later task
    }

    pub(super) fn register_builtin_methods(&mut self, interner: &Interner) {
        macro_rules! register_builtin {
            ($type_id:expr, $method_id:expr, $func_type:expr) => {
                self.implement_registry.register_method(
                    $type_id,
                    $method_id,
                    MethodImpl {
                        trait_name: None,
                        func_type: $func_type,
                        is_builtin: true,
                        external_info: None,
                    },
                );
            };
            ($type_id:expr, $method_id:expr, $func_type:expr, $external_info:expr) => {
                self.implement_registry.register_method(
                    $type_id,
                    $method_id,
                    MethodImpl {
                        trait_name: None,
                        func_type: $func_type,
                        is_builtin: true,
                        external_info: $external_info,
                    },
                );
            };
        }

        let builtin_module = self.name_table.builtin_module();
        let mut namer = Namer::new(&mut self.name_table, interner);
        let mut method_id = |name: &str| namer.intern_raw(builtin_module, &[name]);
        let method_len = method_id("length");
        let method_iter = method_id("iter");
        let array_id = self
            .entity_registry
            .type_table
            .array_name_id()
            .map(ImplTypeId::from_name_id);
        let string_id = self
            .entity_registry
            .type_table
            .primitive_name_id(PrimitiveTypeId::String)
            .map(ImplTypeId::from_name_id);

        if let Some(type_id) = array_id {
            register_builtin!(
                type_id,
                method_len,
                FunctionType {
                    params: vec![].into(),
                    return_type: Box::new(LegacyType::Primitive(PrimitiveType::I64)),
                    is_closure: false,
                }
            );
            register_builtin!(
                type_id,
                method_iter,
                FunctionType {
                    params: vec![].into(),
                    return_type: Box::new(LegacyType::unknown()),
                    is_closure: false,
                },
                Some(ExternalMethodInfo {
                    module_path: "std:intrinsics".to_string(),
                    native_name: "array_iter".to_string(),
                    return_type: None, // Refined by check_builtin_method
                })
            );
        }

        if let Some(type_id) = string_id {
            register_builtin!(
                type_id,
                method_len,
                FunctionType {
                    params: vec![].into(),
                    return_type: Box::new(LegacyType::Primitive(PrimitiveType::I64)),
                    is_closure: false,
                }
            );
            register_builtin!(
                type_id,
                method_iter,
                FunctionType {
                    params: vec![].into(),
                    return_type: Box::new(LegacyType::unknown()), // Will be refined by check_builtin_method
                    is_closure: false,
                },
                Some(ExternalMethodInfo {
                    module_path: "std:intrinsics".to_string(),
                    native_name: "string_chars_iter".to_string(),
                    return_type: None, // Refined by check_builtin_method
                })
            );
        }

        // Range.iter() -> Iterator<i64>
        let range_id = self
            .entity_registry
            .type_table
            .primitive_name_id(PrimitiveTypeId::Range)
            .map(ImplTypeId::from_name_id);
        if let Some(type_id) = range_id {
            register_builtin!(
                type_id,
                method_iter,
                FunctionType {
                    params: vec![].into(),
                    return_type: Box::new(LegacyType::unknown()), // Will be refined by check_builtin_method
                    is_closure: false,
                },
                Some(ExternalMethodInfo {
                    module_path: "std:intrinsics".to_string(),
                    native_name: "range_iter".to_string(),
                    return_type: None, // Refined by check_builtin_method
                })
            );
        }

        // Iterator methods are resolved via interface declarations in the prelude.
    }

    pub(super) fn register_primitive_name_ids(&mut self, interner: &Interner) {
        let builtin_module = self.name_table.builtin_module();
        let mut namer = Namer::new(&mut self.name_table, interner);
        for prim in [
            PrimitiveTypeId::I8,
            PrimitiveTypeId::I16,
            PrimitiveTypeId::I32,
            PrimitiveTypeId::I64,
            PrimitiveTypeId::I128,
            PrimitiveTypeId::U8,
            PrimitiveTypeId::U16,
            PrimitiveTypeId::U32,
            PrimitiveTypeId::U64,
            PrimitiveTypeId::F32,
            PrimitiveTypeId::F64,
            PrimitiveTypeId::Bool,
            PrimitiveTypeId::String,
            PrimitiveTypeId::Range,
        ] {
            let name_id = if let Some(sym) = interner.lookup(prim.name()) {
                namer.intern_symbol(builtin_module, sym)
            } else {
                namer.intern_raw(builtin_module, &[prim.name()])
            };
            self.entity_registry
                .type_table
                .register_primitive_name(prim, name_id);
        }
        let array_name = namer.intern_raw(builtin_module, &["array"]);
        self.entity_registry
            .type_table
            .register_array_name(array_name);
    }
}
