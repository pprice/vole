use cranelift::prelude::{Signature, Type as CraneliftType};
use smallvec::{SmallVec, smallvec};

use super::Compiler;
use crate::codegen::types::{resolve_type_expr_with_metadata, type_to_cranelift};
use crate::frontend::{Interner, Param, TypeExpr};
use crate::sema::LegacyType;

/// SmallVec for function parameters - most functions have <= 8 params
type ParamVec = SmallVec<[CraneliftType; 8]>;

/// Describes how to handle the `self` parameter in method signatures
pub enum SelfParam<'a> {
    /// No self parameter (functions, static methods)
    None,
    /// Self is a pointer (regular methods)
    Pointer,
    /// Self has a specific type (implement blocks on primitives)
    Typed(&'a LegacyType),
}

/// Describes how to resolve type expressions
pub enum TypeResolver<'a> {
    /// Use query-based resolution (most common)
    Query,
    /// Use a specific interner (for module classes)
    Interner(&'a Interner),
}

impl Compiler<'_> {
    /// Build a signature with configurable self parameter and type resolution strategy.
    pub fn build_signature(
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
                        &resolve_type_expr_with_metadata(
                            &param.ty,
                            query.registry(),
                            &self.type_metadata,
                            query.interner(),
                            query.name_table(),
                            module_id,
                            &self.analyzed.type_arena.borrow(),
                        ),
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
                            &self.analyzed.type_arena.borrow(),
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
                    &resolve_type_expr_with_metadata(
                        t,
                        query.registry(),
                        &self.type_metadata,
                        query.interner(),
                        query.name_table(),
                        module_id,
                        &self.analyzed.type_arena.borrow(),
                    ),
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
                        &self.analyzed.type_arena.borrow(),
                    ),
                    self.pointer_type,
                )
            }
        });

        self.jit.create_signature(&cranelift_params, ret)
    }
}
