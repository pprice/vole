use cranelift::prelude::{Signature, Type as CraneliftType};
use smallvec::{SmallVec, smallvec};

use super::Compiler;
use crate::types::{resolve_type_expr_to_id, type_id_to_cranelift};
use vole_frontend::{Interner, Param, TypeExpr};
use vole_sema::type_arena::TypeId;

/// SmallVec for function parameters - most functions have <= 8 params
type ParamVec = SmallVec<[CraneliftType; 8]>;

/// Describes how to handle the `self` parameter in method signatures
pub enum SelfParam {
    /// No self parameter (functions, static methods)
    None,
    /// Self is a pointer (regular methods)
    Pointer,
    /// Self has a specific type using TypeId (implement blocks on primitives)
    TypedId(TypeId),
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
    /// Uses TypeId-native resolution for all types.
    pub fn build_signature(
        &self,
        params: &[Param],
        return_type: Option<&TypeExpr>,
        self_param: SelfParam,
        resolver: TypeResolver,
    ) -> Signature {
        // Collect TypeIds first (this borrows arena internally)
        let self_type_id = match self_param {
            SelfParam::None => None,
            SelfParam::Pointer => None, // Use pointer_type directly
            SelfParam::TypedId(type_id) => Some(type_id),
        };

        // Resolve param TypeIds
        let param_type_ids: SmallVec<[TypeId; 8]> = match &resolver {
            TypeResolver::Query => {
                let query = self.query();
                let module_id = query.main_module();
                params
                    .iter()
                    .map(|param| {
                        resolve_type_expr_to_id(
                            &param.ty,
                            query.registry(),
                            &self.type_metadata,
                            query.interner(),
                            query.name_table(),
                            module_id,
                            &self.analyzed.type_arena,
                        )
                    })
                    .collect()
            }
            TypeResolver::Interner(interner) => {
                let module_id = self.func_registry.main_module();
                params
                    .iter()
                    .map(|param| {
                        resolve_type_expr_to_id(
                            &param.ty,
                            &self.analyzed.entity_registry,
                            &self.type_metadata,
                            interner,
                            &self.analyzed.name_table,
                            module_id,
                            &self.analyzed.type_arena,
                        )
                    })
                    .collect()
            }
        };

        // Resolve return TypeId
        let return_type_id = return_type.map(|t| match &resolver {
            TypeResolver::Query => {
                let query = self.query();
                let module_id = query.main_module();
                resolve_type_expr_to_id(
                    t,
                    query.registry(),
                    &self.type_metadata,
                    query.interner(),
                    query.name_table(),
                    module_id,
                    &self.analyzed.type_arena,
                )
            }
            TypeResolver::Interner(interner) => {
                let module_id = self.func_registry.main_module();
                resolve_type_expr_to_id(
                    t,
                    &self.analyzed.entity_registry,
                    &self.type_metadata,
                    interner,
                    &self.analyzed.name_table,
                    module_id,
                    &self.analyzed.type_arena,
                )
            }
        });

        // Now convert TypeIds to Cranelift types (single arena borrow)
        let arena_ref = self.analyzed.type_arena.borrow();

        // Build cranelift params starting with self if needed
        let mut cranelift_params: ParamVec = match (self_param, self_type_id) {
            (SelfParam::None, _) => SmallVec::new(),
            (SelfParam::Pointer, _) => smallvec![self.pointer_type],
            (SelfParam::TypedId(_), Some(type_id)) => {
                smallvec![type_id_to_cranelift(type_id, &arena_ref, self.pointer_type)]
            }
            (SelfParam::TypedId(_), None) => unreachable!(),
        };

        // Add param types
        for type_id in param_type_ids {
            cranelift_params.push(type_id_to_cranelift(type_id, &arena_ref, self.pointer_type));
        }

        // Convert return type
        let ret = return_type_id.map(|id| type_id_to_cranelift(id, &arena_ref, self.pointer_type));

        drop(arena_ref);
        self.jit.create_signature(&cranelift_params, ret)
    }

    /// Build a signature with a pre-resolved return TypeId.
    /// This variant is used when the return type has been inferred and is already a TypeId.
    pub fn build_signature_with_return_type_id(
        &self,
        params: &[Param],
        return_type_id: Option<TypeId>,
        self_param: SelfParam,
        resolver: TypeResolver,
    ) -> Signature {
        // Collect TypeIds first (this borrows arena internally)
        let self_type_id = match self_param {
            SelfParam::None => None,
            SelfParam::Pointer => None, // Use pointer_type directly
            SelfParam::TypedId(type_id) => Some(type_id),
        };

        // Resolve param TypeIds
        let param_type_ids: SmallVec<[TypeId; 8]> = match &resolver {
            TypeResolver::Query => {
                let query = self.query();
                let module_id = query.main_module();
                params
                    .iter()
                    .map(|param| {
                        resolve_type_expr_to_id(
                            &param.ty,
                            query.registry(),
                            &self.type_metadata,
                            query.interner(),
                            query.name_table(),
                            module_id,
                            &self.analyzed.type_arena,
                        )
                    })
                    .collect()
            }
            TypeResolver::Interner(interner) => {
                let module_id = self.func_registry.main_module();
                params
                    .iter()
                    .map(|param| {
                        resolve_type_expr_to_id(
                            &param.ty,
                            &self.analyzed.entity_registry,
                            &self.type_metadata,
                            interner,
                            &self.analyzed.name_table,
                            module_id,
                            &self.analyzed.type_arena,
                        )
                    })
                    .collect()
            }
        };

        // Now convert TypeIds to Cranelift types (single arena borrow)
        let arena_ref = self.analyzed.type_arena.borrow();

        // Build cranelift params starting with self if needed
        let mut cranelift_params: ParamVec = match (self_param, self_type_id) {
            (SelfParam::None, _) => SmallVec::new(),
            (SelfParam::Pointer, _) => smallvec![self.pointer_type],
            (SelfParam::TypedId(_), Some(type_id)) => {
                smallvec![type_id_to_cranelift(type_id, &arena_ref, self.pointer_type)]
            }
            (SelfParam::TypedId(_), None) => unreachable!(),
        };

        // Add param types
        for type_id in param_type_ids {
            cranelift_params.push(type_id_to_cranelift(type_id, &arena_ref, self.pointer_type));
        }

        // Convert return type
        let ret = return_type_id
            .filter(|id| !id.is_void())
            .map(|id| type_id_to_cranelift(id, &arena_ref, self.pointer_type));

        drop(arena_ref);
        self.jit.create_signature(&cranelift_params, ret)
    }
}
