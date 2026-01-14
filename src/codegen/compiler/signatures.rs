use cranelift::prelude::{Signature, Type as CraneliftType};
use smallvec::{SmallVec, smallvec};

use super::Compiler;
use crate::codegen::types::{
    resolve_type_expr_query, resolve_type_expr_with_metadata, type_to_cranelift,
};
use crate::frontend::{FuncDecl, InterfaceMethod, Interner, Param, TypeExpr};
use crate::sema::Type;

/// SmallVec for function parameters - most functions have <= 8 params
type ParamVec = SmallVec<[CraneliftType; 8]>;

/// Describes how to handle the `self` parameter in method signatures
pub(super) enum SelfParam<'a> {
    /// No self parameter (functions, static methods)
    None,
    /// Self is a pointer (regular methods)
    Pointer,
    /// Self has a specific type (implement blocks on primitives)
    Typed(&'a Type),
}

/// Describes how to resolve type expressions
pub(super) enum TypeResolver<'a> {
    /// Use query-based resolution (most common)
    Query,
    /// Use a specific interner (for module classes)
    Interner(&'a Interner),
}

impl Compiler<'_> {
    /// Build a signature with configurable self parameter and type resolution strategy.
    ///
    /// This is the core signature building function that all other create_*_signature
    /// methods delegate to.
    pub(super) fn build_signature(
        &self,
        params: &[Param],
        return_type: Option<&TypeExpr>,
        self_param: SelfParam,
        resolver: TypeResolver,
    ) -> Signature {
        // Start with self parameter if needed
        let mut cranelift_params: ParamVec = match self_param {
            SelfParam::None => SmallVec::new(),
            SelfParam::Pointer => smallvec![self.pointer_type],
            SelfParam::Typed(ty) => smallvec![type_to_cranelift(ty, self.pointer_type)],
        };

        // Resolve and add function parameters
        match &resolver {
            TypeResolver::Query => {
                let query = self.query();
                let module_id = query.main_module();
                for param in params {
                    cranelift_params.push(type_to_cranelift(
                        &resolve_type_expr_query(&param.ty, &query, &self.type_metadata, module_id),
                        self.pointer_type,
                    ));
                }
            }
            TypeResolver::Interner(interner) => {
                let module_id = self.func_registry.main_module();
                for param in params {
                    cranelift_params.push(type_to_cranelift(
                        &resolve_type_expr_with_metadata(
                            &param.ty,
                            &self.analyzed.entity_registry,
                            &self.type_metadata,
                            interner,
                            &self.analyzed.name_table,
                            module_id,
                        ),
                        self.pointer_type,
                    ));
                }
            }
        }

        // Resolve return type
        let ret = return_type.map(|t| match &resolver {
            TypeResolver::Query => {
                let query = self.query();
                let module_id = query.main_module();
                type_to_cranelift(
                    &resolve_type_expr_query(t, &query, &self.type_metadata, module_id),
                    self.pointer_type,
                )
            }
            TypeResolver::Interner(interner) => {
                let module_id = self.func_registry.main_module();
                type_to_cranelift(
                    &resolve_type_expr_with_metadata(
                        t,
                        &self.analyzed.entity_registry,
                        &self.type_metadata,
                        interner,
                        &self.analyzed.name_table,
                        module_id,
                    ),
                    self.pointer_type,
                )
            }
        });

        self.jit.create_signature(&cranelift_params, ret)
    }

    pub(super) fn create_function_signature(&self, func: &FuncDecl) -> Signature {
        self.build_signature(
            &func.params,
            func.return_type.as_ref(),
            SelfParam::None,
            TypeResolver::Query,
        )
    }

    /// Create a method signature (with self as first parameter)
    pub(super) fn create_method_signature(&self, method: &FuncDecl) -> Signature {
        self.build_signature(
            &method.params,
            method.return_type.as_ref(),
            SelfParam::Pointer,
            TypeResolver::Query,
        )
    }

    /// Create a method signature with a specific interner (for module classes)
    pub(super) fn create_method_signature_with_interner(
        &self,
        method: &FuncDecl,
        interner: &Interner,
    ) -> Signature {
        self.build_signature(
            &method.params,
            method.return_type.as_ref(),
            SelfParam::Pointer,
            TypeResolver::Interner(interner),
        )
    }

    /// Create a static method signature with a specific interner (for module classes)
    pub(super) fn create_static_method_signature_with_interner(
        &self,
        method: &InterfaceMethod,
        interner: &Interner,
    ) -> Signature {
        self.build_signature(
            &method.params,
            method.return_type.as_ref(),
            SelfParam::None,
            TypeResolver::Interner(interner),
        )
    }

    /// Create a method signature for implement blocks (self type can be primitive or pointer)
    pub(super) fn create_implement_method_signature(
        &self,
        method: &FuncDecl,
        self_type: &Type,
    ) -> Signature {
        self.build_signature(
            &method.params,
            method.return_type.as_ref(),
            SelfParam::Typed(self_type),
            TypeResolver::Query,
        )
    }

    /// Create a method signature for an interface method (self as pointer + params)
    pub(super) fn create_interface_method_signature(&self, method: &InterfaceMethod) -> Signature {
        self.build_signature(
            &method.params,
            method.return_type.as_ref(),
            SelfParam::Pointer,
            TypeResolver::Query,
        )
    }

    /// Create a signature for a static method (no self parameter)
    pub(super) fn create_static_method_signature(&self, method: &InterfaceMethod) -> Signature {
        self.build_signature(
            &method.params,
            method.return_type.as_ref(),
            SelfParam::None,
            TypeResolver::Query,
        )
    }
}
