use std::collections::HashMap;

use super::Compiler;
use crate::codegen::types::TypeMetadata;
use crate::frontend::{ClassDecl, Decl, InterfaceDecl, Program, RecordDecl, Symbol, TypeExpr};
use crate::sema::{ClassType, RecordType, StructField, Type};

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
        )
    }

    /// Pre-register a class type (just the name and type_id)
    /// This is called first so that field type resolution can find other classes/records
    pub(super) fn pre_register_class(&mut self, class: &ClassDecl) {
        let type_id = self.next_type_id;
        self.next_type_id += 1;

        // Create a placeholder vole_type (will be replaced in finalize_class)
        let placeholder_type = Type::Class(ClassType {
            name: class.name,
            fields: vec![],
        });

        self.type_metadata.insert(
            class.name,
            TypeMetadata {
                type_id,
                field_slots: HashMap::new(),
                is_class: true,
                vole_type: placeholder_type,
                method_return_types: HashMap::new(),
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
        for (i, field) in class.fields.iter().enumerate() {
            field_slots.insert(field.name, i);
            struct_fields.push(StructField {
                name: field.name,
                ty: self.resolve_type_with_metadata(&field.ty),
                slot: i,
            });
        }

        // Create the Vole type
        let vole_type = Type::Class(ClassType {
            name: class.name,
            fields: struct_fields,
        });

        // Collect method return types
        let mut method_return_types = HashMap::new();
        for method in &class.methods {
            let return_type = method
                .return_type
                .as_ref()
                .map(|t| self.resolve_type_with_metadata(t))
                .unwrap_or(Type::Void);
            method_return_types.insert(method.name, return_type);
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
                            method_return_types.insert(method.name, return_type);
                        }
                    }
                }
            }
        }

        self.type_metadata.insert(
            class.name,
            TypeMetadata {
                type_id,
                field_slots,
                is_class: true,
                vole_type,
                method_return_types,
            },
        );

        // Declare methods as functions: ClassName_methodName
        let type_name = self.analyzed.interner.resolve(class.name);
        for method in &class.methods {
            let method_name_str = self.analyzed.interner.resolve(method.name);
            let full_name = format!("{}_{}", type_name, method_name_str);
            let sig = self.create_method_signature(method);
            self.jit.declare_function(&full_name, &sig);
        }

        // Declare default methods from implemented interfaces
        if let Some(interfaces) = self.analyzed.type_implements.get(&class.name).cloned() {
            for interface_name in &interfaces {
                if let Some(interface_decl) = self.find_interface_decl(program, *interface_name) {
                    for method in &interface_decl.methods {
                        if method.body.is_some() && !direct_methods.contains(&method.name) {
                            let method_name_str = self.analyzed.interner.resolve(method.name);
                            let full_name = format!("{}_{}", type_name, method_name_str);
                            let sig = self.create_interface_method_signature(method);
                            self.jit.declare_function(&full_name, &sig);
                        }
                    }
                }
            }
        }
    }

    /// Pre-register a record type (just the name and type_id)
    /// This is called first so that field type resolution can find other records
    pub(super) fn pre_register_record(&mut self, record: &RecordDecl) {
        let type_id = self.next_type_id;
        self.next_type_id += 1;

        // Create a placeholder vole_type (will be replaced in finalize_record)
        let placeholder_type = Type::Record(RecordType {
            name: record.name,
            fields: vec![],
        });

        self.type_metadata.insert(
            record.name,
            TypeMetadata {
                type_id,
                field_slots: HashMap::new(),
                is_class: false,
                vole_type: placeholder_type,
                method_return_types: HashMap::new(),
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
        for (i, field) in record.fields.iter().enumerate() {
            field_slots.insert(field.name, i);
            struct_fields.push(StructField {
                name: field.name,
                ty: self.resolve_type_with_metadata(&field.ty),
                slot: i,
            });
        }

        // Create the Vole type
        let vole_type = Type::Record(RecordType {
            name: record.name,
            fields: struct_fields,
        });

        // Collect method return types
        let mut method_return_types = HashMap::new();
        for method in &record.methods {
            let return_type = method
                .return_type
                .as_ref()
                .map(|t| self.resolve_type_with_metadata(t))
                .unwrap_or(Type::Void);
            method_return_types.insert(method.name, return_type);
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
                            method_return_types.insert(method.name, return_type);
                        }
                    }
                }
            }
        }

        self.type_metadata.insert(
            record.name,
            TypeMetadata {
                type_id,
                field_slots,
                is_class: false,
                vole_type,
                method_return_types,
            },
        );

        // Declare methods as functions: RecordName_methodName
        let type_name = self.analyzed.interner.resolve(record.name);
        for method in &record.methods {
            let method_name_str = self.analyzed.interner.resolve(method.name);
            let full_name = format!("{}_{}", type_name, method_name_str);
            let sig = self.create_method_signature(method);
            self.jit.declare_function(&full_name, &sig);
        }

        // Declare default methods from implemented interfaces
        if let Some(interfaces) = self.analyzed.type_implements.get(&record.name).cloned() {
            for interface_name in &interfaces {
                if let Some(interface_decl) = self.find_interface_decl(program, *interface_name) {
                    for method in &interface_decl.methods {
                        if method.body.is_some() && !direct_methods.contains(&method.name) {
                            let method_name_str = self.analyzed.interner.resolve(method.name);
                            let full_name = format!("{}_{}", type_name, method_name_str);
                            let sig = self.create_interface_method_signature(method);
                            self.jit.declare_function(&full_name, &sig);
                        }
                    }
                }
            }
        }
    }
}
