//! Built-in interface and method registration for EntityRegistry.

use super::Analyzer;
use crate::FunctionType;
use crate::implement_registry::{ExternalMethodInfo, ImplTypeId, MethodImpl, PrimitiveTypeId};
use crate::types::PlaceholderKind;
use vole_frontend::Interner;
use vole_identity::Namer;

impl Analyzer {
    /// Register built-in interfaces and their implementations
    /// NOTE: This is temporary - will eventually come from stdlib/traits.void
    pub(super) fn register_builtins(&mut self) {
        // For now, just set up the registries - actual builtin methods
        // will be registered when we have the interner available in a later task
    }

    pub(super) fn register_builtin_methods(&mut self, interner: &Interner) {
        // Step 1: Collect all name IDs while holding name_table borrow
        let (
            method_len,
            method_iter,
            method_push,
            std_intrinsics,
            array_iter_name,
            string_chars_iter_name,
            range_iter_name,
        ) = {
            let builtin_module = self.name_table_mut().builtin_module();
            let mut name_table = self.name_table_mut();
            let mut namer = Namer::new(&mut name_table, interner);
            (
                namer.intern_raw(builtin_module, &["length"]),
                namer.intern_raw(builtin_module, &["iter"]),
                namer.intern_raw(builtin_module, &["push"]),
                namer.intern_raw(builtin_module, &["vole:std:runtime"]),
                namer.intern_raw(builtin_module, &["array_iter"]),
                namer.intern_raw(builtin_module, &["string_chars_iter"]),
                namer.intern_raw(builtin_module, &["range_iter"]),
            )
        };

        // Step 2: Get type IDs from entity registry
        let array_id = self
            .entity_registry()
            .array_name_id()
            .map(ImplTypeId::from_name_id);
        let string_id = self
            .entity_registry()
            .primitive_name_id(PrimitiveTypeId::String)
            .map(ImplTypeId::from_name_id);
        let range_id = self
            .entity_registry()
            .primitive_name_id(PrimitiveTypeId::Range)
            .map(ImplTypeId::from_name_id);

        // Step 3: Get type arena types
        let (i64_type, void_type, unknown_type) = {
            let mut arena = self.type_arena_mut();
            (
                arena.i64(),
                arena.void(),
                arena.placeholder(PlaceholderKind::Inference),
            )
        };

        // Step 4: Register methods via implement_registry
        if let Some(type_id) = array_id {
            self.implement_registry_mut().register_method(
                type_id,
                method_len,
                MethodImpl::builtin(FunctionType::from_ids(&[], i64_type, false)),
            );
            self.implement_registry_mut().register_method(
                type_id,
                method_iter,
                MethodImpl::external_builtin(
                    FunctionType::from_ids(&[], unknown_type, false),
                    ExternalMethodInfo {
                        module_path: std_intrinsics,
                        native_name: array_iter_name,
                    },
                ),
            );
            // push(value) -> void - adds element to end of array
            self.implement_registry_mut().register_method(
                type_id,
                method_push,
                MethodImpl::builtin(FunctionType::from_ids(&[unknown_type], void_type, false)),
            );
        }

        if let Some(type_id) = string_id {
            self.implement_registry_mut().register_method(
                type_id,
                method_len,
                MethodImpl::builtin(FunctionType::from_ids(&[], i64_type, false)),
            );
            self.implement_registry_mut().register_method(
                type_id,
                method_iter,
                MethodImpl::external_builtin(
                    FunctionType::from_ids(&[], unknown_type, false),
                    ExternalMethodInfo {
                        module_path: std_intrinsics,
                        native_name: string_chars_iter_name,
                    },
                ),
            );
        }

        if let Some(type_id) = range_id {
            self.implement_registry_mut().register_method(
                type_id,
                method_iter,
                MethodImpl::external_builtin(
                    FunctionType::from_ids(&[], unknown_type, false),
                    ExternalMethodInfo {
                        module_path: std_intrinsics,
                        native_name: range_iter_name,
                    },
                ),
            );
        }

        // Iterator methods are resolved via interface declarations in the prelude.
    }

    pub(super) fn register_primitive_name_ids(&mut self, interner: &Interner) {
        // Collect all name_ids while holding name_table borrow
        let (primitive_names, array_name) = {
            let builtin_module = self.name_table_mut().builtin_module();
            let mut name_table = self.name_table_mut();
            let mut namer = Namer::new(&mut name_table, interner);

            let primitives: Vec<_> = [
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
                PrimitiveTypeId::Handle,
            ]
            .iter()
            .map(|prim| {
                let name_id = if let Some(sym) = interner.lookup(prim.name()) {
                    namer.intern_symbol(builtin_module, sym)
                } else {
                    namer.intern_raw(builtin_module, &[prim.name()])
                };
                (*prim, name_id)
            })
            .collect();

            let array_name = namer.intern_raw(builtin_module, &["array"]);
            (primitives, array_name)
        };

        // Now register with entity_registry after dropping name_table borrow
        for (prim, name_id) in primitive_names {
            self.entity_registry_mut()
                .register_primitive_name(prim, name_id);
        }
        self.entity_registry_mut().register_array_name(array_name);
    }
}
