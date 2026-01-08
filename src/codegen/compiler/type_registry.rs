use std::collections::HashMap;

use super::Compiler;
use crate::codegen::types::{MethodInfo, TypeMetadata, method_name_id};
use crate::frontend::{ClassDecl, Decl, InterfaceDecl, Program, RecordDecl, Symbol, TypeExpr};
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
        let empty_error_types = HashMap::new();
        crate::codegen::types::resolve_type_expr_with_metadata(
            ty,
            &self.analyzed.type_aliases,
            &self.analyzed.interface_registry,
            &empty_error_types,
            &self.type_metadata,
            &self.analyzed.interner,
            &self.analyzed.name_table,
            self.analyzed.name_table.main_module(),
        )
    }

    /// Pre-register a class type (just the name and type_id)
    /// This is called first so that field type resolution can find other classes/records
    pub(super) fn pre_register_class(&mut self, class: &ClassDecl) {
        let type_id = self.next_type_id;
        self.next_type_id += 1;

        let type_key = self
            .analyzed
            .name_table
            .name_id(self.analyzed.name_table.main_module(), &[class.name])
            .and_then(|name_id| self.analyzed.type_table.by_name(name_id));
        let name_id = self
            .analyzed
            .name_table
            .name_id(self.analyzed.name_table.main_module(), &[class.name])
            .expect("class name_id should be registered");

        // Create a placeholder vole_type (will be replaced in finalize_class)
        let placeholder_type = Type::Class(ClassType {
            name: class.name,
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

        // Build field slots map and StructField list
        let mut field_slots = HashMap::new();
        let mut struct_fields = Vec::new();
        let mut field_type_tags = Vec::new();
        for (i, field) in class.fields.iter().enumerate() {
            field_slots.insert(field.name, i);
            let field_type = self.resolve_type_with_metadata(&field.ty);
            field_type_tags.push(type_to_field_tag(&field_type));
            struct_fields.push(StructField {
                name: field.name,
                ty: field_type,
                slot: i,
            });
        }

        // Register field types in runtime type registry for cleanup
        register_instance_type(type_id, field_type_tags);

        // Create the Vole type
        let vole_type = Type::Class(ClassType {
            name: class.name,
            name_id: self
                .analyzed
                .name_table
                .name_id(self.analyzed.name_table.main_module(), &[class.name])
                .expect("class name_id should be registered"),
            fields: struct_fields,
        });

        // Collect method return types
        let module_id = self.func_registry.main_module();
        let mut method_infos = HashMap::new();
        for method in &class.methods {
            let return_type = method
                .return_type
                .as_ref()
                .map(|t| self.resolve_type_with_metadata(t))
                .unwrap_or(Type::Void);
            let sig = self.create_method_signature(method);
            let func_key = self
                .func_registry
                .intern_qualified(module_id, &[class.name, method.name]);
            let display_name = self
                .func_registry
                .display(func_key, &self.analyzed.interner);
            let func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, func_id);
            let method_id = method_name_id(self.analyzed, &self.analyzed.interner, method.name)
                .unwrap_or_else(|| {
                    let type_name_str = self.analyzed.interner.resolve(class.name);
                    let method_name_str = self.analyzed.interner.resolve(method.name);
                    panic!(
                        "codegen error: method name not interned for class '{}': '{}'",
                        type_name_str, method_name_str
                    );
                });
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
        if let Some(interfaces) = self.analyzed.type_implements.get(&class.name).cloned() {
            for interface_name in &interfaces {
                if let Some(interface_decl) = self.find_interface_decl(program, *interface_name) {
                    for method in &interface_decl.methods {
                        if method.body.is_some() && !direct_methods.contains(&method.name) {
                            let return_type = method
                                .return_type
                                .as_ref()
                                .map(|t| self.resolve_type_with_metadata(t))
                                .unwrap_or(Type::Void);
                            let sig = self.create_interface_method_signature(method);
                            let func_key = self
                                .func_registry
                                .intern_qualified(module_id, &[class.name, method.name]);
                            let display_name = self
                                .func_registry
                                .display(func_key, &self.analyzed.interner);
                            let func_id = self.jit.declare_function(&display_name, &sig);
                            self.func_registry.set_func_id(func_key, func_id);
                            let method_id =
                                method_name_id(self.analyzed, &self.analyzed.interner, method.name)
                                    .unwrap_or_else(|| {
                                        let type_name_str =
                                            self.analyzed.interner.resolve(class.name);
                                        let method_name_str =
                                            self.analyzed.interner.resolve(method.name);
                                        panic!(
                                            "codegen error: default method name not interned for class '{}': '{}'",
                                            type_name_str, method_name_str
                                        );
                                    });
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
        }

        self.type_metadata.insert(
            class.name,
            TypeMetadata {
                type_id,
                type_key: self
                    .analyzed
                    .name_table
                    .name_id(self.analyzed.name_table.main_module(), &[class.name])
                    .and_then(|name_id| self.analyzed.type_table.by_name(name_id)),
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

        let type_key = self
            .analyzed
            .name_table
            .name_id(self.analyzed.name_table.main_module(), &[record.name])
            .and_then(|name_id| self.analyzed.type_table.by_name(name_id));
        let name_id = self
            .analyzed
            .name_table
            .name_id(self.analyzed.name_table.main_module(), &[record.name])
            .expect("record name_id should be registered");

        // Create a placeholder vole_type (will be replaced in finalize_record)
        let placeholder_type = Type::Record(RecordType {
            name: record.name,
            name_id,
            fields: vec![],
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

        // Build field slots map and StructField list
        let mut field_slots = HashMap::new();
        let mut struct_fields = Vec::new();
        let mut field_type_tags = Vec::new();
        for (i, field) in record.fields.iter().enumerate() {
            field_slots.insert(field.name, i);
            let field_type = self.resolve_type_with_metadata(&field.ty);
            field_type_tags.push(type_to_field_tag(&field_type));
            struct_fields.push(StructField {
                name: field.name,
                ty: field_type,
                slot: i,
            });
        }

        // Register field types in runtime type registry for cleanup
        register_instance_type(type_id, field_type_tags);

        // Create the Vole type
        let vole_type = Type::Record(RecordType {
            name: record.name,
            name_id: self
                .analyzed
                .name_table
                .name_id(self.analyzed.name_table.main_module(), &[record.name])
                .expect("record name_id should be registered"),
            fields: struct_fields,
        });

        // Collect method return types
        let module_id = self.func_registry.main_module();
        let mut method_infos = HashMap::new();
        for method in &record.methods {
            let return_type = method
                .return_type
                .as_ref()
                .map(|t| self.resolve_type_with_metadata(t))
                .unwrap_or(Type::Void);
            let sig = self.create_method_signature(method);
            let func_key = self
                .func_registry
                .intern_qualified(module_id, &[record.name, method.name]);
            let display_name = self
                .func_registry
                .display(func_key, &self.analyzed.interner);
            let func_id = self.jit.declare_function(&display_name, &sig);
            self.func_registry.set_func_id(func_key, func_id);
            let method_id = method_name_id(self.analyzed, &self.analyzed.interner, method.name)
                .unwrap_or_else(|| {
                    let type_name_str = self.analyzed.interner.resolve(record.name);
                    let method_name_str = self.analyzed.interner.resolve(method.name);
                    panic!(
                        "codegen error: method name not interned for record '{}': '{}'",
                        type_name_str, method_name_str
                    );
                });
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
        if let Some(interfaces) = self.analyzed.type_implements.get(&record.name).cloned() {
            for interface_name in &interfaces {
                if let Some(interface_decl) = self.find_interface_decl(program, *interface_name) {
                    for method in &interface_decl.methods {
                        if method.body.is_some() && !direct_methods.contains(&method.name) {
                            let return_type = method
                                .return_type
                                .as_ref()
                                .map(|t| self.resolve_type_with_metadata(t))
                                .unwrap_or(Type::Void);
                            let sig = self.create_interface_method_signature(method);
                            let func_key = self
                                .func_registry
                                .intern_qualified(module_id, &[record.name, method.name]);
                            let display_name = self
                                .func_registry
                                .display(func_key, &self.analyzed.interner);
                            let func_id = self.jit.declare_function(&display_name, &sig);
                            self.func_registry.set_func_id(func_key, func_id);
                            let method_id =
                                method_name_id(self.analyzed, &self.analyzed.interner, method.name)
                                    .unwrap_or_else(|| {
                                        let type_name_str =
                                            self.analyzed.interner.resolve(record.name);
                                        let method_name_str =
                                            self.analyzed.interner.resolve(method.name);
                                        panic!(
                                            "codegen error: default method name not interned for record '{}': '{}'",
                                            type_name_str, method_name_str
                                        );
                                    });
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
        }

        self.type_metadata.insert(
            record.name,
            TypeMetadata {
                type_id,
                type_key: self
                    .analyzed
                    .name_table
                    .name_id(self.analyzed.name_table.main_module(), &[record.name])
                    .and_then(|name_id| self.analyzed.type_table.by_name(name_id)),
                field_slots,
                is_class: false,
                vole_type,
                method_infos,
            },
        );
    }
}
