use cranelift::prelude::Signature;

use super::Compiler;
use crate::codegen::types::{resolve_type_expr_full, type_to_cranelift};
use crate::frontend::{FuncDecl, InterfaceMethod};
use crate::sema::Type;

impl Compiler<'_> {
    pub(super) fn create_function_signature(&self, func: &FuncDecl) -> Signature {
        let module_id = self.analyzed.name_table.main_module();
        let mut params = Vec::new();
        for param in &func.params {
            params.push(type_to_cranelift(
                &resolve_type_expr_full(
                    &param.ty,
                    &self.analyzed.entity_registry,
                    &self.type_metadata,
                    &self.analyzed.interner,
                    &self.analyzed.name_table,
                    module_id,
                ),
                self.pointer_type,
            ));
        }

        let ret = func.return_type.as_ref().map(|t| {
            type_to_cranelift(
                &resolve_type_expr_full(
                    t,
                    &self.analyzed.entity_registry,
                    &self.type_metadata,
                    &self.analyzed.interner,
                    &self.analyzed.name_table,
                    module_id,
                ),
                self.pointer_type,
            )
        });

        self.jit.create_signature(&params, ret)
    }

    /// Create a method signature (with self as first parameter)
    pub(super) fn create_method_signature(&self, method: &FuncDecl) -> Signature {
        let module_id = self.analyzed.name_table.main_module();
        // Methods have `self` as implicit first parameter (pointer to instance)
        let mut params = vec![self.pointer_type];
        for param in &method.params {
            params.push(type_to_cranelift(
                &resolve_type_expr_full(
                    &param.ty,
                    &self.analyzed.entity_registry,
                    &self.type_metadata,
                    &self.analyzed.interner,
                    &self.analyzed.name_table,
                    module_id,
                ),
                self.pointer_type,
            ));
        }

        let ret = method.return_type.as_ref().map(|t| {
            type_to_cranelift(
                &resolve_type_expr_full(
                    t,
                    &self.analyzed.entity_registry,
                    &self.type_metadata,
                    &self.analyzed.interner,
                    &self.analyzed.name_table,
                    module_id,
                ),
                self.pointer_type,
            )
        });

        self.jit.create_signature(&params, ret)
    }

    /// Create a method signature for implement blocks (self type can be primitive or pointer)
    pub(super) fn create_implement_method_signature(
        &self,
        method: &FuncDecl,
        self_type: &Type,
    ) -> Signature {
        let module_id = self.analyzed.name_table.main_module();
        // For implement blocks, `self` type depends on the target type
        // Primitives use their actual type, classes/records use pointer
        let self_cranelift_type = type_to_cranelift(self_type, self.pointer_type);
        let mut params = vec![self_cranelift_type];
        for param in &method.params {
            params.push(type_to_cranelift(
                &resolve_type_expr_full(
                    &param.ty,
                    &self.analyzed.entity_registry,
                    &self.type_metadata,
                    &self.analyzed.interner,
                    &self.analyzed.name_table,
                    module_id,
                ),
                self.pointer_type,
            ));
        }

        let ret = method.return_type.as_ref().map(|t| {
            type_to_cranelift(
                &resolve_type_expr_full(
                    t,
                    &self.analyzed.entity_registry,
                    &self.type_metadata,
                    &self.analyzed.interner,
                    &self.analyzed.name_table,
                    module_id,
                ),
                self.pointer_type,
            )
        });

        self.jit.create_signature(&params, ret)
    }

    /// Create a method signature for an interface method (self as pointer + params)
    pub(super) fn create_interface_method_signature(&self, method: &InterfaceMethod) -> Signature {
        let module_id = self.analyzed.name_table.main_module();
        // Methods have `self` as implicit first parameter (pointer to instance)
        let mut params = vec![self.pointer_type];
        for param in &method.params {
            params.push(type_to_cranelift(
                &resolve_type_expr_full(
                    &param.ty,
                    &self.analyzed.entity_registry,
                    &self.type_metadata,
                    &self.analyzed.interner,
                    &self.analyzed.name_table,
                    module_id,
                ),
                self.pointer_type,
            ));
        }

        let ret = method.return_type.as_ref().map(|t| {
            type_to_cranelift(
                &resolve_type_expr_full(
                    t,
                    &self.analyzed.entity_registry,
                    &self.type_metadata,
                    &self.analyzed.interner,
                    &self.analyzed.name_table,
                    module_id,
                ),
                self.pointer_type,
            )
        });

        self.jit.create_signature(&params, ret)
    }

    /// Create a signature for a static method (no self parameter)
    pub(super) fn create_static_method_signature(&self, method: &InterfaceMethod) -> Signature {
        let module_id = self.analyzed.name_table.main_module();
        // Static methods have NO self parameter
        let mut params = Vec::new();
        for param in &method.params {
            params.push(type_to_cranelift(
                &resolve_type_expr_full(
                    &param.ty,
                    &self.analyzed.entity_registry,
                    &self.type_metadata,
                    &self.analyzed.interner,
                    &self.analyzed.name_table,
                    module_id,
                ),
                self.pointer_type,
            ));
        }

        let ret = method.return_type.as_ref().map(|t| {
            type_to_cranelift(
                &resolve_type_expr_full(
                    t,
                    &self.analyzed.entity_registry,
                    &self.type_metadata,
                    &self.analyzed.interner,
                    &self.analyzed.name_table,
                    module_id,
                ),
                self.pointer_type,
            )
        });

        self.jit.create_signature(&params, ret)
    }
}
