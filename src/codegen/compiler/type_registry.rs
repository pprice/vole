use std::collections::HashMap;

use super::Compiler;
use crate::codegen::types::{MethodInfo, TypeMetadata, resolve_type_expr_query};
use crate::frontend::{
    ClassDecl, Decl, InterfaceDecl, Program, RecordDecl, StaticsBlock, Symbol, TypeExpr,
};
use crate::runtime::type_registry::{FieldTypeTag, register_instance_type};
use crate::sema::{ClassType, RecordType, StructField, Type};

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

    /// Pre-register a class type (just the name and type_id)
    /// This is called first so that field type resolution can find other classes/records
    pub(super) fn pre_register_class(&mut self, class: &ClassDecl) {
        let type_id = self.next_type_id;
        self.next_type_id += 1;

        let query = self.query();
        let module_id = query.main_module();
        let name_id = query.name_id(module_id, &[class.name]);
        let type_key = query.type_key_by_name(name_id);

        // Create a placeholder vole_type (will be replaced in finalize_class)
        let placeholder_type = Type::Class(ClassType {
            name_id,
            fields: vec![],
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

        // Build field slots map and StructField list
        let mut field_slots = HashMap::new();
        let mut struct_fields = Vec::new();
        let mut field_type_tags = Vec::new();
        for (i, field) in class.fields.iter().enumerate() {
            let field_name = query.resolve_symbol(field.name).to_string();
            field_slots.insert(field_name.clone(), i);
            let field_type = self.resolve_type_with_metadata(&field.ty);
            field_type_tags.push(type_to_field_tag(&field_type));
            struct_fields.push(StructField {
                name: field_name,
                ty: field_type,
                slot: i,
            });
        }

        // Register field types in runtime type registry for cleanup
        register_instance_type(type_id, field_type_tags);

        // Create the Vole type
        let vole_type = Type::Class(ClassType {
            name_id: query.name_id(module_id, &[class.name]),
            fields: struct_fields,
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
                        let method_id =
                            self.query().method_name_id(method.name);
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

        // Create a placeholder vole_type (will be replaced in finalize_record)
        let placeholder_type = Type::Record(RecordType {
            name_id,
            fields: vec![],
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

        // Build field slots map and StructField list
        let mut field_slots = HashMap::new();
        let mut struct_fields = Vec::new();
        let mut field_type_tags = Vec::new();
        for (i, field) in record.fields.iter().enumerate() {
            let field_name = query.resolve_symbol(field.name).to_string();
            field_slots.insert(field_name.clone(), i);
            let field_type = self.resolve_type_with_metadata(&field.ty);
            field_type_tags.push(type_to_field_tag(&field_type));
            struct_fields.push(StructField {
                name: field_name,
                ty: field_type,
                slot: i,
            });
        }

        // Register field types in runtime type registry for cleanup
        register_instance_type(type_id, field_type_tags);

        // Create the Vole type
        let vole_type = Type::Record(RecordType {
            name_id: query.name_id(module_id, &[record.name]),
            fields: struct_fields,
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
                        let func_key = self.intern_func(func_module_id, &[record.name, method.name]);
                        let display_name = self.func_registry.display(func_key);
                        let func_id = self.jit.declare_function(&display_name, &sig);
                        self.func_registry.set_func_id(func_key, func_id);
                        let method_id =
                            self.query().method_name_id(method.name);
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
}
