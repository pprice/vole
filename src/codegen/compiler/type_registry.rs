use std::collections::HashMap;

use super::Compiler;
use crate::codegen::types::{
    MethodInfo, TypeMetadata, method_name_id_with_interner, resolve_type_expr_query,
    resolve_type_expr_with_metadata,
};
use crate::frontend::{
    ClassDecl, Decl, InterfaceDecl, Interner, Program, RecordDecl, StaticsBlock, Symbol, TypeExpr,
};
use crate::runtime::type_registry::{FieldTypeTag, register_instance_type};
use crate::sema::{ClassType, RecordType, Type};

/// Convert a Vole Type to a FieldTypeTag for runtime cleanup
fn type_to_field_tag(ty: &Type) -> FieldTypeTag {
    match ty {
        Type::String => FieldTypeTag::String,
        Type::Array(_) => FieldTypeTag::Array,
        Type::Class(_) | Type::Record(_) => FieldTypeTag::Instance,
        // Optional types containing reference types also need cleanup
        Type::Union(variants) => {
            // If any variant is a reference type, mark as needing cleanup
            for variant in variants {
                let tag = type_to_field_tag(variant);
                if tag.needs_cleanup() {
                    return tag;
                }
            }
            FieldTypeTag::Value
        }
        _ => FieldTypeTag::Value,
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

    /// Resolve a type expression using type_metadata (for record/class field types)
    /// This allows resolving types like `Person?` where Person is another record/class
    pub(super) fn resolve_type_with_metadata(&self, ty: &TypeExpr) -> Type {
        let query = self.query();
        resolve_type_expr_query(ty, &query, &self.type_metadata, query.main_module())
    }

    /// Resolve a type expression using a specific interner (for module types)
    /// This is needed because module classes have symbols from their own interner
    pub(super) fn resolve_type_with_interner(&self, ty: &TypeExpr, interner: &Interner) -> Type {
        resolve_type_expr_with_metadata(
            ty,
            &self.analyzed.entity_registry,
            &self.type_metadata,
            interner,
            &self.analyzed.name_table,
            self.func_registry.main_module(),
        )
    }

    /// Pre-register a class type (just the name and type_id)
    /// This is called first so that field type resolution can find other classes/records
    pub(super) fn pre_register_class(&mut self, class: &ClassDecl) {
        let type_id = self.next_type_id;
        self.next_type_id += 1;

        let query = self.query();
        let module_id = query.main_module();
        let name_id = query.name_id(module_id, &[class.name]);
        let type_key = query.type_key_by_name(name_id);

        // Look up the TypeDefId from EntityRegistry
        let type_def_id = self
            .analyzed
            .entity_registry
            .type_by_name(name_id)
            .expect("class should be registered in entity registry");

        // Create a placeholder vole_type (will be replaced in finalize_class)
        let placeholder_type = Type::Class(ClassType {
            type_def_id,
            type_args: vec![],
        });

        self.type_metadata.insert(
            class.name,
            TypeMetadata {
                type_id,
                type_key,
                field_slots: HashMap::new(),
                is_class: true,
                vole_type: placeholder_type,
                method_infos: HashMap::new(),
            },
        );
    }

    /// Finalize a class type: fill in field types and declare methods
    pub(super) fn finalize_class(&mut self, class: &ClassDecl, program: &Program) {
        // Get the pre-registered type_id
        let type_id = self
            .type_metadata
            .get(&class.name)
            .expect("class should be pre-registered")
            .type_id;

        let query = self.query();
        let module_id = query.main_module();

        // Build field slots map
        let mut field_slots = HashMap::new();
        let mut field_type_tags = Vec::new();
        for (i, field) in class.fields.iter().enumerate() {
            let field_name = query.resolve_symbol(field.name).to_string();
            field_slots.insert(field_name, i);
            let field_type = self.resolve_type_with_metadata(&field.ty);
            field_type_tags.push(type_to_field_tag(&field_type));
        }

        // Register field types in runtime type registry for cleanup
        register_instance_type(type_id, field_type_tags);

        // Look up the TypeDefId from EntityRegistry
        let name_id = query.name_id(module_id, &[class.name]);
        let type_def_id = self
            .analyzed
            .entity_registry
            .type_by_name(name_id)
            .expect("class should be registered in entity registry");

        // Create the Vole type
        let vole_type = Type::Class(ClassType {
            type_def_id,
            type_args: vec![],
        });

        // Collect method return types
        let func_module_id = self.func_registry.main_module();
        let mut method_infos = HashMap::new();
        for method in &class.methods {
            let return_type = method
                .return_type
                .as_ref()
                .map(|t| self.resolve_type_with_metadata(t))
                .unwrap_or(Type::Void);
            let sig = self.create_method_signature(method);
            let func_key = self.intern_func(func_module_id, &[class.name, method.name]);
            let display_name = self.func_registry.display(func_key);
            let func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, func_id);
            let method_id = self.query().method_name_id(method.name);
            method_infos.insert(
                method_id,
                MethodInfo {
                    func_key,
                    return_type,
                },
            );
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
                        let return_type = method
                            .return_type
                            .as_ref()
                            .map(|t| self.resolve_type_with_metadata(t))
                            .unwrap_or(Type::Void);
                        let sig = self.create_interface_method_signature(method);
                        let func_key = self.intern_func(func_module_id, &[class.name, method.name]);
                        let display_name = self.func_registry.display(func_key);
                        let func_id = self.jit.declare_function(&display_name, &sig);
                        self.func_registry.set_func_id(func_key, func_id);
                        let method_id = self.query().method_name_id(method.name);
                        method_infos.insert(
                            method_id,
                            MethodInfo {
                                func_key,
                                return_type,
                            },
                        );
                    }
                }
            }
        }

        // Register static methods from statics block
        if let Some(ref statics) = class.statics {
            self.register_static_methods(statics, class.name);
        }

        let query = self.query();
        let name_id = query.name_id(module_id, &[class.name]);
        self.type_metadata.insert(
            class.name,
            TypeMetadata {
                type_id,
                type_key: query.type_key_by_name(name_id),
                field_slots,
                is_class: true,
                vole_type,
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
        let type_key = query.type_key_by_name(name_id);

        // Look up the TypeDefId from EntityRegistry
        let type_def_id = self
            .analyzed
            .entity_registry
            .type_by_name(name_id)
            .expect("record should be registered in entity registry");

        // Create a placeholder vole_type (will be replaced in finalize_record)
        let placeholder_type = Type::Record(RecordType {
            type_def_id,
            type_args: vec![],
        });

        self.type_metadata.insert(
            record.name,
            TypeMetadata {
                type_id,
                type_key,
                field_slots: HashMap::new(),
                is_class: false,
                vole_type: placeholder_type,
                method_infos: HashMap::new(),
            },
        );
    }

    /// Finalize a record type: fill in field types and declare methods
    pub(super) fn finalize_record(&mut self, record: &RecordDecl, program: &Program) {
        // Get the pre-registered type_id
        let type_id = self
            .type_metadata
            .get(&record.name)
            .expect("record should be pre-registered")
            .type_id;

        let query = self.query();
        let module_id = query.main_module();

        // Build field slots map
        let mut field_slots = HashMap::new();
        let mut field_type_tags = Vec::new();
        for (i, field) in record.fields.iter().enumerate() {
            let field_name = query.resolve_symbol(field.name).to_string();
            field_slots.insert(field_name, i);
            let field_type = self.resolve_type_with_metadata(&field.ty);
            field_type_tags.push(type_to_field_tag(&field_type));
        }

        // Register field types in runtime type registry for cleanup
        register_instance_type(type_id, field_type_tags);

        // Look up the TypeDefId from EntityRegistry
        let name_id = query.name_id(module_id, &[record.name]);
        let type_def_id = self
            .analyzed
            .entity_registry
            .type_by_name(name_id)
            .expect("record should be registered in entity registry");

        // Create the Vole type
        let vole_type = Type::Record(RecordType {
            type_def_id,
            type_args: vec![],
        });

        // Collect method return types
        let func_module_id = self.func_registry.main_module();
        let mut method_infos = HashMap::new();
        for method in &record.methods {
            let return_type = method
                .return_type
                .as_ref()
                .map(|t| self.resolve_type_with_metadata(t))
                .unwrap_or(Type::Void);
            let sig = self.create_method_signature(method);
            let func_key = self.intern_func(func_module_id, &[record.name, method.name]);
            let display_name = self.func_registry.display(func_key);
            let func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, func_id);
            let method_id = self.query().method_name_id(method.name);
            method_infos.insert(
                method_id,
                MethodInfo {
                    func_key,
                    return_type,
                },
            );
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
                        let return_type = method
                            .return_type
                            .as_ref()
                            .map(|t| self.resolve_type_with_metadata(t))
                            .unwrap_or(Type::Void);
                        let sig = self.create_interface_method_signature(method);
                        let func_key =
                            self.intern_func(func_module_id, &[record.name, method.name]);
                        let display_name = self.func_registry.display(func_key);
                        let func_id = self.jit.declare_function(&display_name, &sig);
                        self.func_registry.set_func_id(func_key, func_id);
                        let method_id = self.query().method_name_id(method.name);
                        method_infos.insert(
                            method_id,
                            MethodInfo {
                                func_key,
                                return_type,
                            },
                        );
                    }
                }
            }
        }

        // Register static methods from statics block
        if let Some(ref statics) = record.statics {
            self.register_static_methods(statics, record.name);
        }

        let query = self.query();
        let name_id = query.name_id(module_id, &[record.name]);
        self.type_metadata.insert(
            record.name,
            TypeMetadata {
                type_id,
                type_key: query.type_key_by_name(name_id),
                field_slots,
                is_class: false,
                vole_type,
                method_infos,
            },
        );
    }

    /// Register static methods from a statics block for a type
    fn register_static_methods(&mut self, statics: &StaticsBlock, type_name: Symbol) {
        let func_module_id = self.func_registry.main_module();

        // Get the TypeDefId for this type from entity_registry
        let query = self.query();
        let module_id = query.main_module();
        let type_name_id = query.name_id(module_id, &[type_name]);
        let type_def_id = query.try_type_def_id(type_name_id);

        for method in &statics.methods {
            // Only register methods with bodies (not abstract ones)
            if method.body.is_none() {
                continue;
            }

            let return_type = method
                .return_type
                .as_ref()
                .map(|t| self.resolve_type_with_metadata(t))
                .unwrap_or(Type::Void);

            // Create signature without self parameter
            let sig = self.create_static_method_signature(method);

            // Function key: TypeName::methodName
            let func_key = self.intern_func(func_module_id, &[type_name, method.name]);
            let display_name = self.func_registry.display(func_key);
            let func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, func_id);

            // Register in static_method_infos for codegen lookup
            if let Some(type_def_id) = type_def_id {
                let method_name_id = self.method_name_id(method.name);
                self.static_method_infos.insert(
                    (type_def_id, method_name_id),
                    MethodInfo {
                        func_key,
                        return_type,
                    },
                );
            }
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

        // Look up the TypeDefId using the class name
        tracing::debug!(type_name = %type_name_str, "Looking up TypeDefId for module class");
        let Some(type_def_id) = self
            .analyzed
            .entity_registry
            .class_by_short_name(type_name_str, &self.analyzed.name_table)
        else {
            tracing::warn!(type_name = %type_name_str, "Could not find TypeDefId for module class");
            return;
        };
        tracing::debug!(type_name = %type_name_str, ?type_def_id, "Found TypeDefId for module class");

        // Skip if already registered - check by type name string to avoid Symbol collisions across interners
        let already_registered = self.type_metadata.values().any(|meta| {
            if let Type::Class(class_type) = &meta.vole_type {
                self.analyzed
                    .name_table
                    .last_segment_str(self.analyzed.entity_registry.class_name_id(class_type))
                    .is_some_and(|name| name == type_name_str)
            } else {
                false
            }
        });
        if already_registered {
            tracing::debug!(type_name = %type_name_str, "Skipping - already registered in type_metadata");
            return;
        }
        tracing::debug!(type_name = %type_name_str, "Proceeding with registration");

        // Allocate type_id
        let type_id = self.next_type_id;
        self.next_type_id += 1;

        // Build field slots map
        let mut field_slots = HashMap::new();
        let mut field_type_tags = Vec::new();
        for (i, field) in class.fields.iter().enumerate() {
            let field_name = module_interner.resolve(field.name).to_string();
            field_slots.insert(field_name, i);
            let field_type = self.resolve_type_with_interner(&field.ty, module_interner);
            field_type_tags.push(type_to_field_tag(&field_type));
        }

        // Register field types in runtime type registry
        register_instance_type(type_id, field_type_tags);

        // Create the Vole type
        let vole_type = Type::Class(ClassType {
            type_def_id,
            type_args: vec![],
        });

        // Collect method info and declare methods
        let func_module_id = self.func_registry.main_module();
        let mut method_infos = HashMap::new();

        tracing::debug!(type_name = %type_name_str, method_count = class.methods.len(), "Registering instance methods");
        for method in &class.methods {
            let method_name_str = module_interner.resolve(method.name);
            tracing::debug!(type_name = %type_name_str, method_name = %method_name_str, "Processing instance method");

            let return_type = method
                .return_type
                .as_ref()
                .map(|t| self.resolve_type_with_interner(t, module_interner))
                .unwrap_or(Type::Void);

            let sig = self.create_method_signature_with_interner(method, module_interner);
            let func_key = self
                .func_registry
                .intern_raw_qualified(func_module_id, &[type_name_str, method_name_str]);
            let display_name = self.func_registry.display(func_key);
            let func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, func_id);

            if let Some(method_name_id) =
                method_name_id_with_interner(self.analyzed, module_interner, method.name)
            {
                tracing::debug!(type_name = %type_name_str, method_name = %method_name_str, ?method_name_id, "Registered instance method");
                method_infos.insert(
                    method_name_id,
                    MethodInfo {
                        func_key,
                        return_type,
                    },
                );
            } else {
                tracing::warn!(type_name = %type_name_str, method_name = %method_name_str, "Could not get method_name_id for instance method");
            }
        }
        tracing::debug!(type_name = %type_name_str, registered_count = method_infos.len(), "Finished registering instance methods");

        // Get type_key from entity registry
        let type_def = self.analyzed.entity_registry.get_type(type_def_id);
        let type_key = self
            .analyzed
            .entity_registry
            .type_table
            .by_name(type_def.name_id);

        // Register type metadata
        // IMPORTANT: Use the main interner's Symbol for the class name, not the module's Symbol.
        // Module classes have Symbols from their own interners which may collide (e.g., both
        // Set and Map might have their class name as Symbol(0) in their respective interners).
        let main_class_symbol = self
            .analyzed
            .interner
            .lookup(type_name_str)
            .unwrap_or(class.name);
        tracing::debug!(type_name = %type_name_str, ?class.name, ?main_class_symbol, "Inserting type_metadata");
        self.type_metadata.insert(
            main_class_symbol,
            TypeMetadata {
                type_id,
                type_key,
                field_slots,
                is_class: true,
                vole_type,
                method_infos,
            },
        );

        // Register static methods
        if let Some(ref statics) = class.statics {
            for method in &statics.methods {
                if method.body.is_none() {
                    continue;
                }

                let return_type = method
                    .return_type
                    .as_ref()
                    .map(|t| self.resolve_type_with_interner(t, module_interner))
                    .unwrap_or(Type::Void);

                let sig =
                    self.create_static_method_signature_with_interner(method, module_interner);
                let method_name_str = module_interner.resolve(method.name);
                let func_key = self
                    .func_registry
                    .intern_raw_qualified(func_module_id, &[type_name_str, method_name_str]);
                let display_name = self.func_registry.display(func_key);
                let func_id = self.jit.declare_function(&display_name, &sig);
                self.func_registry.set_func_id(func_key, func_id);

                if let Some(method_name_id) =
                    method_name_id_with_interner(self.analyzed, module_interner, method.name)
                {
                    tracing::debug!(
                        type_name = %type_name_str,
                        method_name = %method_name_str,
                        "Registering static method"
                    );
                    self.static_method_infos.insert(
                        (type_def_id, method_name_id),
                        MethodInfo {
                            func_key,
                            return_type,
                        },
                    );
                }
            }
        }
    }
}
