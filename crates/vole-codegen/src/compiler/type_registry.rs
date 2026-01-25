use rustc_hash::FxHashMap;

use super::{Compiler, SelfParam};
use crate::types::{MethodInfo, TypeMetadata, method_name_id_with_interner};
use vole_frontend::{
    ClassDecl, Decl, InterfaceDecl, Interner, Program, RecordDecl, StaticsBlock, Symbol,
};
use vole_runtime::type_registry::{FieldTypeTag, register_instance_type};
use vole_sema::type_arena::TypeId;

/// Convert a TypeId to a FieldTypeTag for runtime cleanup
fn type_id_to_field_tag(ty: TypeId, arena: &vole_sema::type_arena::TypeArena) -> FieldTypeTag {
    if arena.is_string(ty) {
        FieldTypeTag::String
    } else if arena.is_array(ty) {
        FieldTypeTag::Array
    } else if arena.is_class(ty) || arena.is_record(ty) {
        FieldTypeTag::Instance
    } else if let Some(variants) = arena.unwrap_union(ty) {
        // If any variant is a reference type, mark as needing cleanup
        for &variant in variants.iter() {
            let tag = type_id_to_field_tag(variant, arena);
            if tag.needs_cleanup() {
                return tag;
            }
        }
        FieldTypeTag::Value
    } else {
        FieldTypeTag::Value
    }
}

impl Compiler<'_> {
    /// Find an interface declaration by name in the program
    pub(super) fn find_interface_decl<'b>(
        &self,
        program: &'b Program,
        interface_name: Symbol,
    ) -> Option<&'b InterfaceDecl> {
        for decl in &program.declarations {
            if let Decl::Interface(iface) = decl
                && iface.name == interface_name
            {
                return Some(iface);
            }
        }
        None
    }

    /// Pre-register a class type (just the name and type_id)
    /// This is called first so that field type resolution can find other classes/records
    pub(super) fn pre_register_class(&mut self, class: &ClassDecl) {
        let type_id = self.next_type_id;
        self.next_type_id += 1;

        let query = self.query();
        let module_id = query.main_module();
        let name_id = query.name_id(module_id, &[class.name]);

        // Look up the TypeDefId from EntityRegistry
        let type_def_id = self
            .query()
            .try_type_def_id(name_id)
            .expect("class should be registered in entity registry");

        // Use pre-computed base_type_id from sema (no mutable arena access needed)
        let vole_type_id = self
            .query()
            .get_type(type_def_id)
            .base_type_id
            .expect("sema should pre-compute base_type_id for classes");

        self.state.type_metadata.insert(
            type_def_id,
            TypeMetadata {
                type_id,
                field_slots: FxHashMap::default(),
                vole_type: vole_type_id,
                type_def_id,
                method_infos: FxHashMap::default(),
            },
        );
    }

    /// Finalize a class type: fill in field types and declare methods
    pub(super) fn finalize_class(&mut self, class: &ClassDecl, program: &Program) {
        let query = self.query();
        let module_id = query.main_module();

        // Look up TypeDefId first (needed as key for type_metadata)
        let type_def_id = self
            .query()
            .try_name_id(module_id, &[class.name])
            .and_then(|name_id| self.query().try_type_def_id(name_id))
            .expect("class should be registered in entity registry");

        // Get the pre-registered type_id
        let type_id = self
            .state
            .type_metadata
            .get(&type_def_id)
            .expect("class should be pre-registered")
            .type_id;

        // Build field slots map using sema's pre-resolved field types
        let mut field_slots = FxHashMap::default();
        let mut field_type_tags = Vec::new();
        // Collect field IDs first to avoid borrow conflicts
        let field_ids: Vec<_> = self
            .analyzed
            .entity_registry()
            .fields_on_type(type_def_id)
            .collect();
        for field_id in field_ids {
            let (field_name, field_slot, field_type_id) = {
                let field_def = self.analyzed.entity_registry().get_field(field_id);
                let name = self
                    .query()
                    .last_segment(field_def.name_id)
                    .expect("field should have a name");
                (name, field_def.slot, field_def.ty)
            };
            field_slots.insert(field_name, field_slot);
            field_type_tags.push(type_id_to_field_tag(
                field_type_id,
                self.analyzed.type_arena(),
            ));
        }

        // Register field types in runtime type registry for cleanup
        register_instance_type(type_id, field_type_tags);

        // Collect method return types (TypeId-native)
        // type_def_id already looked up above
        let mut method_infos = FxHashMap::default();
        for method in &class.methods {
            let method_name_id = self.method_name_id(method.name);

            // Get MethodId and build signature from pre-resolved types
            let method_id = self
                .analyzed
                .entity_registry()
                .find_method_on_type(type_def_id, method_name_id)
                .expect("method should be registered in entity registry");
            let sig = self.build_signature_for_method(method_id, SelfParam::Pointer);
            let full_name_id = self
                .analyzed
                .entity_registry()
                .get_method(method_id)
                .full_name_id;
            let func_key = self.func_registry.intern_name_id(full_name_id);
            let display_name = self.func_registry.display(func_key);
            let jit_func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, jit_func_id);
            method_infos.insert(method_name_id, MethodInfo { func_key });
            // Also populate unified method_func_keys map
            self.state
                .method_func_keys
                .insert((type_def_id, method_name_id), func_key);
        }

        // Collect method names that the class directly defines
        let direct_methods: std::collections::HashSet<_> =
            class.methods.iter().map(|m| m.name).collect();

        // Also add return types for default methods from implemented interfaces
        // Look up class type_def_id via immutable name_id lookup
        // Collect interface info first to avoid borrow conflicts
        let interfaces_to_process: Vec<_> = {
            let query = self.query();
            query
                .try_name_id(module_id, &[class.name])
                .and_then(|class_name_id| query.try_type_def_id(class_name_id))
                .map(|type_def_id| {
                    query
                        .implemented_interfaces(type_def_id)
                        .into_iter()
                        .filter_map(|interface_id| {
                            let interface_def = query.get_type(interface_id);
                            let interface_name_str = query.last_segment(interface_def.name_id)?;
                            let interface_name = query.try_symbol(&interface_name_str)?;
                            Some(interface_name)
                        })
                        .collect()
                })
                .unwrap_or_default()
        };

        for interface_name in interfaces_to_process {
            if let Some(interface_decl) = self.find_interface_decl(program, interface_name) {
                for method in &interface_decl.methods {
                    if method.body.is_some() && !direct_methods.contains(&method.name) {
                        let method_name_id = self.query().method_name_id(method.name);
                        // Get MethodId and build signature from pre-resolved types
                        let semantic_method_id = self
                            .analyzed
                            .entity_registry()
                            .find_method_on_type(type_def_id, method_name_id)
                            .unwrap_or_else(|| {
                                let class_name_str = self.resolve_symbol(class.name);
                                let method_name_str = self.resolve_symbol(method.name);
                                panic!(
                                    "interface default method not registered on implementing class: {}::{} (type_def_id={:?}, method_name_id={:?})",
                                    class_name_str, method_name_str, type_def_id, method_name_id
                                )
                            });
                        let sig =
                            self.build_signature_for_method(semantic_method_id, SelfParam::Pointer);
                        let method_def = self
                            .analyzed
                            .entity_registry()
                            .get_method(semantic_method_id);
                        let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
                        let display_name = self.func_registry.display(func_key);
                        let jit_func_id = self.jit.declare_function(&display_name, &sig);
                        self.func_registry.set_func_id(func_key, jit_func_id);
                        method_infos.insert(method_name_id, MethodInfo { func_key });
                        // Also populate unified method_func_keys map
                        self.state
                            .method_func_keys
                            .insert((type_def_id, method_name_id), func_key);
                    }
                }
            }
        }

        // Register static methods from statics block
        if let Some(ref statics) = class.statics {
            self.register_static_methods(statics, class.name);
        }

        // Reuse the vole_type_id from pre_register (type_def_id already available)
        let vole_type_id = self
            .state
            .type_metadata
            .get(&type_def_id)
            .expect("class should be pre-registered")
            .vole_type;
        self.state.type_metadata.insert(
            type_def_id,
            TypeMetadata {
                type_id,
                field_slots,
                vole_type: vole_type_id,
                type_def_id,
                method_infos,
            },
        );
    }

    /// Pre-register a record type (just the name and type_id)
    /// This is called first so that field type resolution can find other records
    pub(super) fn pre_register_record(&mut self, record: &RecordDecl) {
        let type_id = self.next_type_id;
        self.next_type_id += 1;

        let query = self.query();
        let module_id = query.main_module();
        let name_id = query.name_id(module_id, &[record.name]);

        // Look up the TypeDefId from EntityRegistry
        let type_def_id = self
            .query()
            .try_type_def_id(name_id)
            .expect("record should be registered in entity registry");

        // Use pre-computed base_type_id from sema (no mutable arena access needed)
        let vole_type_id = self
            .query()
            .get_type(type_def_id)
            .base_type_id
            .expect("sema should pre-compute base_type_id for records");

        self.state.type_metadata.insert(
            type_def_id,
            TypeMetadata {
                type_id,
                field_slots: FxHashMap::default(),
                vole_type: vole_type_id,
                type_def_id,
                method_infos: FxHashMap::default(),
            },
        );
    }

    /// Finalize a record type: fill in field types and declare methods
    pub(super) fn finalize_record(&mut self, record: &RecordDecl, program: &Program) {
        let query = self.query();
        let module_id = query.main_module();

        // Look up TypeDefId first (needed as key for type_metadata)
        let type_def_id = self
            .query()
            .try_name_id(module_id, &[record.name])
            .and_then(|name_id| self.query().try_type_def_id(name_id))
            .expect("record should be registered in entity registry");

        // Get the pre-registered type_id
        let type_id = self
            .state
            .type_metadata
            .get(&type_def_id)
            .expect("record should be pre-registered")
            .type_id;

        // Build field slots map using sema's pre-resolved field types
        let mut field_slots = FxHashMap::default();
        let mut field_type_tags = Vec::new();
        // Collect field IDs first to avoid borrow conflicts
        let field_ids: Vec<_> = self
            .analyzed
            .entity_registry()
            .fields_on_type(type_def_id)
            .collect();
        for field_id in field_ids {
            let (field_name, field_slot, field_type_id) = {
                let field_def = self.analyzed.entity_registry().get_field(field_id);
                let name = self
                    .query()
                    .last_segment(field_def.name_id)
                    .expect("field should have a name");
                (name, field_def.slot, field_def.ty)
            };
            field_slots.insert(field_name, field_slot);
            field_type_tags.push(type_id_to_field_tag(
                field_type_id,
                self.analyzed.type_arena(),
            ));
        }

        // Register field types in runtime type registry for cleanup
        register_instance_type(type_id, field_type_tags);

        // Collect method return types (TypeId-native)
        let mut method_infos = FxHashMap::default();
        for method in &record.methods {
            let method_name_id = self.method_name_id(method.name);
            // Get MethodId and build signature from pre-resolved types
            let semantic_method_id = self
                .analyzed
                .entity_registry()
                .find_method_on_type(type_def_id, method_name_id)
                .unwrap_or_else(|| {
                    let record_name_str = self.resolve_symbol(record.name);
                    let method_name_str = self.resolve_symbol(method.name);
                    panic!(
                        "record method not registered in entity_registry: {}::{} (type_def_id={:?}, method_name_id={:?})",
                        record_name_str, method_name_str, type_def_id, method_name_id
                    )
                });
            let sig = self.build_signature_for_method(semantic_method_id, SelfParam::Pointer);
            let full_name_id = self
                .analyzed
                .entity_registry()
                .get_method(semantic_method_id)
                .full_name_id;
            let func_key = self.func_registry.intern_name_id(full_name_id);
            let display_name = self.func_registry.display(func_key);
            let jit_func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, jit_func_id);
            method_infos.insert(method_name_id, MethodInfo { func_key });
            // Also populate unified method_func_keys map
            self.state
                .method_func_keys
                .insert((type_def_id, method_name_id), func_key);
        }

        // Collect method names that the record directly defines
        let direct_methods: std::collections::HashSet<_> =
            record.methods.iter().map(|m| m.name).collect();

        // Also add return types for default methods from implemented interfaces
        // Look up record type_def_id via immutable name_id lookup
        // Collect interface info first to avoid borrow conflicts
        let interfaces_to_process: Vec<_> = {
            let query = self.query();
            query
                .try_name_id(module_id, &[record.name])
                .and_then(|record_name_id| query.try_type_def_id(record_name_id))
                .map(|type_def_id| {
                    query
                        .implemented_interfaces(type_def_id)
                        .into_iter()
                        .filter_map(|interface_id| {
                            let interface_def = query.get_type(interface_id);
                            let interface_name_str = query.last_segment(interface_def.name_id)?;
                            let interface_name = query.try_symbol(&interface_name_str)?;
                            Some(interface_name)
                        })
                        .collect()
                })
                .unwrap_or_default()
        };

        for interface_name in interfaces_to_process {
            if let Some(interface_decl) = self.find_interface_decl(program, interface_name) {
                for method in &interface_decl.methods {
                    if method.body.is_some() && !direct_methods.contains(&method.name) {
                        let method_name_id = self.query().method_name_id(method.name);
                        // Get MethodId and build signature from pre-resolved types
                        let semantic_method_id = self
                            .analyzed
                            .entity_registry()
                            .find_method_on_type(type_def_id, method_name_id)
                            .unwrap_or_else(|| {
                                let record_name_str = self.resolve_symbol(record.name);
                                let method_name_str = self.resolve_symbol(method.name);
                                panic!(
                                    "interface default method not registered on implementing record: {}::{} (type_def_id={:?}, method_name_id={:?})",
                                    record_name_str, method_name_str, type_def_id, method_name_id
                                )
                            });
                        let sig =
                            self.build_signature_for_method(semantic_method_id, SelfParam::Pointer);
                        let method_def = self
                            .analyzed
                            .entity_registry()
                            .get_method(semantic_method_id);
                        let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
                        let display_name = self.func_registry.display(func_key);
                        let jit_func_id = self.jit.declare_function(&display_name, &sig);
                        self.func_registry.set_func_id(func_key, jit_func_id);
                        method_infos.insert(method_name_id, MethodInfo { func_key });
                        // Also populate unified method_func_keys map
                        self.state
                            .method_func_keys
                            .insert((type_def_id, method_name_id), func_key);
                    }
                }
            }
        }

        // Register static methods from statics block
        if let Some(ref statics) = record.statics {
            self.register_static_methods(statics, record.name);
        }

        // Reuse the vole_type_id from pre_register (type_def_id already available)
        let vole_type_id = self
            .state
            .type_metadata
            .get(&type_def_id)
            .expect("record should be pre-registered")
            .vole_type;
        self.state.type_metadata.insert(
            type_def_id,
            TypeMetadata {
                type_id,
                field_slots,
                vole_type: vole_type_id,
                type_def_id,
                method_infos,
            },
        );
    }

    /// Register static methods from a statics block for a type
    fn register_static_methods(&mut self, statics: &StaticsBlock, type_name: Symbol) {
        // Get the TypeDefId for this type from entity_registry
        let query = self.query();
        let module_id = query.main_module();
        let type_name_id = query.name_id(module_id, &[type_name]);
        let type_def_id = query
            .try_type_def_id(type_name_id)
            .expect("type should be registered in entity registry");

        for method in &statics.methods {
            // Only register methods with bodies (not abstract ones)
            if method.body.is_none() {
                continue;
            }

            let method_name_id = self.method_name_id(method.name);

            // Get MethodId and build signature from pre-resolved types
            let method_id = self
                .analyzed
                .entity_registry()
                .find_static_method_on_type(type_def_id, method_name_id)
                .expect("static method should be registered in entity registry");
            let sig = self.build_signature_for_method(method_id, SelfParam::None);

            // Function key from entity registry
            let method_def = self.analyzed.entity_registry().get_method(method_id);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let display_name = self.func_registry.display(func_key);
            let jit_func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, jit_func_id);

            // Register in method_func_keys for codegen lookup
            self.state
                .method_func_keys
                .insert((type_def_id, method_name_id), func_key);
        }
    }

    /// Register and finalize a module class (uses module interner)
    /// This handles:
    /// 1. Pre-registration (type_id allocation)
    /// 2. Type metadata registration (fields, methods)
    /// 3. Static method registration
    pub(super) fn finalize_module_class(&mut self, class: &ClassDecl, module_interner: &Interner) {
        let type_name_str = module_interner.resolve(class.name);
        tracing::debug!(type_name = %type_name_str, "finalize_module_class called");

        // Look up the TypeDefId using the class name via full resolution chain
        tracing::debug!(type_name = %type_name_str, "Looking up TypeDefId for module class");
        let query = self.query();
        let module_id = query.main_module();
        let Some(type_def_id) = query.resolve_type_def_by_str(module_id, type_name_str) else {
            tracing::warn!(type_name = %type_name_str, "Could not find TypeDefId for module class");
            return;
        };
        tracing::debug!(type_name = %type_name_str, ?type_def_id, "Found TypeDefId for module class");

        // Skip if already registered (TypeDefId key ensures no cross-interner collisions)
        if self.state.type_metadata.contains_key(&type_def_id) {
            tracing::debug!(type_name = %type_name_str, "Skipping - already registered in type_metadata");
            return;
        }
        tracing::debug!(type_name = %type_name_str, "Proceeding with registration");

        // Allocate type_id
        let type_id = self.next_type_id;
        self.next_type_id += 1;

        // Build field slots map using sema's pre-resolved field types
        let mut field_slots = FxHashMap::default();
        let mut field_type_tags = Vec::new();
        // Collect field IDs first to avoid borrow conflicts
        let field_ids: Vec<_> = self
            .analyzed
            .entity_registry()
            .fields_on_type(type_def_id)
            .collect();
        for field_id in field_ids {
            let (field_name, field_slot, field_type_id) = {
                let field_def = self.analyzed.entity_registry().get_field(field_id);
                let name = self
                    .query()
                    .last_segment(field_def.name_id)
                    .expect("field should have a name");
                (name, field_def.slot, field_def.ty)
            };
            field_slots.insert(field_name, field_slot);
            field_type_tags.push(type_id_to_field_tag(
                field_type_id,
                self.analyzed.type_arena(),
            ));
        }

        // Register field types in runtime type registry
        register_instance_type(type_id, field_type_tags);

        // Collect method info and declare methods (TypeId-native)
        let mut method_infos = FxHashMap::default();

        tracing::debug!(type_name = %type_name_str, method_count = class.methods.len(), "Registering instance methods");
        for method in &class.methods {
            let method_name_str = module_interner.resolve(method.name);
            tracing::debug!(type_name = %type_name_str, method_name = %method_name_str, "Processing instance method");

            let method_name_id =
                method_name_id_with_interner(self.analyzed, module_interner, method.name)
                    .unwrap_or_else(|| {
                        panic!(
                            "module class method name not found in name_table: {}::{}",
                            type_name_str, method_name_str
                        )
                    });

            // Get MethodId and build signature from pre-resolved types
            let semantic_method_id = self
                .analyzed
                .entity_registry()
                .find_method_on_type(type_def_id, method_name_id)
                .unwrap_or_else(|| {
                    panic!(
                        "module class method not registered in entity_registry: {}::{} (type_def_id={:?}, method_name_id={:?})",
                        type_name_str, method_name_str, type_def_id, method_name_id
                    )
                });

            let sig = self.build_signature_for_method(semantic_method_id, SelfParam::Pointer);
            let method_def = self
                .analyzed
                .entity_registry()
                .get_method(semantic_method_id);
            let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
            let display_name = self.func_registry.display(func_key);
            let jit_func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, jit_func_id);

            tracing::debug!(type_name = %type_name_str, method_name = %method_name_str, method_name_id = ?method_name_id, "Registered instance method");
            method_infos.insert(method_name_id, MethodInfo { func_key });
            // Also populate unified method_func_keys map
            self.state
                .method_func_keys
                .insert((type_def_id, method_name_id), func_key);
        }
        tracing::debug!(type_name = %type_name_str, registered_count = method_infos.len(), "Finished registering instance methods");

        // Register type metadata (keyed by TypeDefId - no cross-interner Symbol collision issues)
        tracing::debug!(type_name = %type_name_str, ?type_def_id, "Inserting type_metadata");
        // Use pre-computed base_type_id from sema (no mutable arena access needed)
        let vole_type_id = self
            .query()
            .get_type(type_def_id)
            .base_type_id
            .expect("sema should pre-compute base_type_id for module classes");
        self.state.type_metadata.insert(
            type_def_id,
            TypeMetadata {
                type_id,
                field_slots,
                vole_type: vole_type_id,
                type_def_id,
                method_infos,
            },
        );

        // Register static methods
        if let Some(ref statics) = class.statics {
            for method in &statics.methods {
                if method.body.is_none() {
                    continue;
                }

                let method_name_str = module_interner.resolve(method.name);
                let method_name_id =
                    method_name_id_with_interner(self.analyzed, module_interner, method.name)
                        .unwrap_or_else(|| {
                            panic!(
                                "module class static method name not found in name_table: {}::{}",
                                type_name_str, method_name_str
                            )
                        });

                // Get MethodId and build signature from pre-resolved types
                let semantic_method_id = self
                    .analyzed
                    .entity_registry()
                    .find_static_method_on_type(type_def_id, method_name_id)
                    .unwrap_or_else(|| {
                        panic!(
                            "module class static method not registered in entity_registry: {}::{} (type_def_id={:?}, method_name_id={:?})",
                            type_name_str, method_name_str, type_def_id, method_name_id
                        )
                    });

                let sig = self.build_signature_for_method(semantic_method_id, SelfParam::None);
                let method_def = self
                    .analyzed
                    .entity_registry()
                    .get_method(semantic_method_id);
                let func_key = self.func_registry.intern_name_id(method_def.full_name_id);
                let display_name = self.func_registry.display(func_key);
                let jit_func_id = self.jit.declare_function(&display_name, &sig);
                self.func_registry.set_func_id(func_key, jit_func_id);

                tracing::debug!(
                    type_name = %type_name_str,
                    method_name = %method_name_str,
                    "Registering static method"
                );
                self.state
                    .method_func_keys
                    .insert((type_def_id, method_name_id), func_key);
            }
        }
    }
}
