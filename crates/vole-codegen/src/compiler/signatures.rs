use cranelift::prelude::{Signature, Type as CraneliftType};
use smallvec::{SmallVec, smallvec};

use super::Compiler;
use crate::types::{resolve_type_expr_to_id, type_id_to_cranelift};
use vole_frontend::{Interner, Param, Symbol, TypeExpr};
use vole_identity::ModuleId;
use vole_sema::type_arena::TypeId;

/// SmallVec for function parameters - most functions have <= 8 params
type ParamVec = SmallVec<[CraneliftType; 8]>;

/// SmallVec for TypeIds - most functions have <= 8 params
#[allow(dead_code)]
type TypeIdVec = SmallVec<[TypeId; 8]>;

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
        let param_type_ids: SmallVec<[TypeId; 8]> = {
            let name_table = self.analyzed.name_table();
            match &resolver {
                TypeResolver::Query => {
                    let query = self.query();
                    let module_id = query.main_module();
                    params
                        .iter()
                        .map(|param| {
                            resolve_type_expr_to_id(
                                &param.ty,
                                query.registry(),
                                &self.state.type_metadata,
                                query.interner(),
                                &name_table,
                                module_id,
                                self.analyzed.type_arena_ref(),
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
                                self.analyzed.entity_registry(),
                                &self.state.type_metadata,
                                interner,
                                &name_table,
                                module_id,
                                self.analyzed.type_arena_ref(),
                            )
                        })
                        .collect()
                }
            }
        };

        // Resolve return TypeId
        let return_type_id = {
            let name_table = self.analyzed.name_table();
            return_type.map(|t| match &resolver {
                TypeResolver::Query => {
                    let query = self.query();
                    let module_id = query.main_module();
                    resolve_type_expr_to_id(
                        t,
                        query.registry(),
                        &self.state.type_metadata,
                        query.interner(),
                        &name_table,
                        module_id,
                        self.analyzed.type_arena_ref(),
                    )
                }
                TypeResolver::Interner(interner) => {
                    let module_id = self.func_registry.main_module();
                    resolve_type_expr_to_id(
                        t,
                        self.analyzed.entity_registry(),
                        &self.state.type_metadata,
                        interner,
                        &name_table,
                        module_id,
                        self.analyzed.type_arena_ref(),
                    )
                }
            })
        };

        // Now convert TypeIds to Cranelift types (single arena borrow)
        let arena_ref = self.analyzed.type_arena();

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
        let param_type_ids: SmallVec<[TypeId; 8]> = {
            let name_table = self.analyzed.name_table();
            match &resolver {
                TypeResolver::Query => {
                    let query = self.query();
                    let module_id = query.main_module();
                    params
                        .iter()
                        .map(|param| {
                            resolve_type_expr_to_id(
                                &param.ty,
                                query.registry(),
                                &self.state.type_metadata,
                                query.interner(),
                                &name_table,
                                module_id,
                                self.analyzed.type_arena_ref(),
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
                                self.analyzed.entity_registry(),
                                &self.state.type_metadata,
                                interner,
                                &name_table,
                                module_id,
                                self.analyzed.type_arena_ref(),
                            )
                        })
                        .collect()
                }
            }
        };

        // Now convert TypeIds to Cranelift types (single arena borrow)
        let arena_ref = self.analyzed.type_arena();

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

    /// Resolve parameter TypeExprs to TypeIds using the specified resolver.
    ///
    /// This helper extracts the common pattern of resolving function parameters
    /// to their semantic TypeIds. Callers can then convert to Cranelift types
    /// or use for variable binding.
    pub fn resolve_param_type_ids(&self, params: &[Param], resolver: &TypeResolver) -> Vec<TypeId> {
        let name_table = self.analyzed.name_table();
        match resolver {
            TypeResolver::Query => {
                let query = self.query();
                let module_id = query.main_module();
                params
                    .iter()
                    .map(|param| {
                        resolve_type_expr_to_id(
                            &param.ty,
                            query.registry(),
                            &self.state.type_metadata,
                            query.interner(),
                            &name_table,
                            module_id,
                            self.analyzed.type_arena_ref(),
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
                            self.analyzed.entity_registry(),
                            &self.state.type_metadata,
                            interner,
                            &name_table,
                            module_id,
                            self.analyzed.type_arena_ref(),
                        )
                    })
                    .collect()
            }
        }
    }

    /// Resolve parameter TypeExprs to TypeIds using a specific interner and module.
    ///
    /// This variant is used when the interner and module are known at the call site
    /// (e.g., in module compilation where we have a custom interner).
    pub fn resolve_param_type_ids_with_interner(
        &self,
        params: &[Param],
        interner: &Interner,
        module_id: ModuleId,
    ) -> Vec<TypeId> {
        let name_table = self.analyzed.name_table();
        params
            .iter()
            .map(|param| {
                resolve_type_expr_to_id(
                    &param.ty,
                    self.analyzed.entity_registry(),
                    &self.state.type_metadata,
                    interner,
                    &name_table,
                    module_id,
                    self.analyzed.type_arena_ref(),
                )
            })
            .collect()
    }

    /// Convert TypeIds to Cranelift types.
    ///
    /// This helper handles the common pattern of converting resolved TypeIds
    /// to their Cranelift representations for function signatures.
    pub fn type_ids_to_cranelift(&self, type_ids: &[TypeId]) -> Vec<CraneliftType> {
        let arena = self.analyzed.type_arena();
        type_ids
            .iter()
            .map(|&id| type_id_to_cranelift(id, &arena, self.pointer_type))
            .collect()
    }

    /// Resolve parameter TypeExprs to TypeIds with SelfType substitution.
    ///
    /// This helper handles implement block methods where `Self` type needs to be
    /// resolved to the implementing type. If `self_type_id` is provided, any
    /// `TypeExpr::SelfType` will be substituted with it.
    ///
    /// Returns `Vec<(Symbol, TypeId)>` for param binding.
    pub fn resolve_param_type_ids_with_self_type(
        &self,
        params: &[Param],
        self_type_id: TypeId,
        module_id: ModuleId,
    ) -> Vec<(Symbol, TypeId)> {
        let name_table = self.analyzed.name_table();
        let query = self.query();
        params
            .iter()
            .map(|p| {
                let type_id = if matches!(&p.ty, TypeExpr::SelfType) {
                    self_type_id
                } else {
                    resolve_type_expr_to_id(
                        &p.ty,
                        query.registry(),
                        &self.state.type_metadata,
                        query.interner(),
                        &name_table,
                        module_id,
                        self.analyzed.type_arena_ref(),
                    )
                };
                (p.name, type_id)
            })
            .collect()
    }

    /// Resolve parameter TypeExprs to just TypeIds with SelfType substitution.
    ///
    /// Similar to `resolve_param_type_ids_with_self_type` but returns only TypeIds
    /// without the Symbol pairing.
    pub fn resolve_param_type_ids_with_self_type_only(
        &self,
        params: &[Param],
        self_type_id: TypeId,
        module_id: ModuleId,
    ) -> Vec<TypeId> {
        let name_table = self.analyzed.name_table();
        let query = self.query();
        params
            .iter()
            .map(|p| {
                if matches!(&p.ty, TypeExpr::SelfType) {
                    self_type_id
                } else {
                    resolve_type_expr_to_id(
                        &p.ty,
                        query.registry(),
                        &self.state.type_metadata,
                        query.interner(),
                        &name_table,
                        module_id,
                        self.analyzed.type_arena_ref(),
                    )
                }
            })
            .collect()
    }
}
