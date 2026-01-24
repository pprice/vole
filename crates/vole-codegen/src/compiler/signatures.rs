use cranelift::prelude::{Signature, Type as CraneliftType};
use smallvec::{SmallVec, smallvec};

use super::Compiler;
use crate::types::type_id_to_cranelift;
use vole_identity::{FunctionId, MethodId};
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

impl Compiler<'_> {
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

    /// Convert a single TypeId to a Cranelift type.
    pub fn type_id_to_cranelift(&self, type_id: TypeId) -> CraneliftType {
        type_id_to_cranelift(type_id, &self.analyzed.type_arena(), self.pointer_type)
    }

    /// Convert a TypeId to Option<CraneliftType>, returning None for void types.
    pub fn return_type_to_cranelift(&self, type_id: TypeId) -> Option<CraneliftType> {
        if type_id.is_void() {
            None
        } else {
            Some(self.type_id_to_cranelift(type_id))
        }
    }

    /// Build a Cranelift signature from pre-resolved TypeIds.
    ///
    /// This is the most direct method for building signatures when types are already
    /// resolved to TypeIds (e.g., from FunctionDef.signature or type analysis).
    pub fn build_signature_from_type_ids(
        &self,
        params_id: &[TypeId],
        return_type_id: Option<TypeId>,
        self_param: SelfParam,
    ) -> Signature {
        let arena_ref = self.analyzed.type_arena();

        // Build cranelift params starting with self if needed
        let mut cranelift_params: ParamVec = match &self_param {
            SelfParam::None => SmallVec::new(),
            SelfParam::Pointer => smallvec![self.pointer_type],
            SelfParam::TypedId(type_id) => {
                smallvec![type_id_to_cranelift(
                    *type_id,
                    &arena_ref,
                    self.pointer_type
                )]
            }
        };

        // Add param types
        for &type_id in params_id {
            cranelift_params.push(type_id_to_cranelift(type_id, &arena_ref, self.pointer_type));
        }

        // Convert return type (filter out void)
        let ret = return_type_id
            .filter(|id| !id.is_void())
            .map(|id| type_id_to_cranelift(id, &arena_ref, self.pointer_type));

        drop(arena_ref);
        self.jit.create_signature(&cranelift_params, ret)
    }

    /// Build a Cranelift signature directly from a FunctionId.
    ///
    /// This is a convenience method that retrieves the function definition
    /// and builds the signature from its pre-resolved TypeIds.
    pub fn build_signature_for_function(&self, func_id: FunctionId) -> Signature {
        let func_def = self.query().registry().get_function(func_id);
        self.build_signature_from_type_ids(
            &func_def.signature.params_id,
            Some(func_def.signature.return_type_id),
            SelfParam::None,
        )
    }

    /// Build a Cranelift signature directly from a MethodId.
    ///
    /// This is a convenience method that retrieves the method definition
    /// and builds the signature from its pre-resolved TypeIds.
    pub fn build_signature_for_method(
        &self,
        method_id: MethodId,
        self_param: SelfParam,
    ) -> Signature {
        let method_def = self.query().registry().get_method(method_id);
        let arena = self.analyzed.type_arena();
        let (params, ret, _) = arena
            .unwrap_function(method_def.signature_id)
            .expect("method should have function signature");
        self.build_signature_from_type_ids(params, Some(ret), self_param)
    }
}
