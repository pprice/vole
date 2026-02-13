use cranelift::prelude::{Signature, Type as CraneliftType, types};
use smallvec::{SmallVec, smallvec};

use super::Compiler;
use crate::types::{is_wide_fallible, type_id_to_cranelift};
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
        let arena = self.arena();
        type_ids
            .iter()
            .map(|&id| type_id_to_cranelift(id, arena, self.pointer_type))
            .collect()
    }

    /// Convert a single TypeId to a Cranelift type.
    pub fn type_id_to_cranelift(&self, type_id: TypeId) -> CraneliftType {
        type_id_to_cranelift(type_id, self.arena(), self.pointer_type)
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
    ///
    /// For fallible return types, this generates a multi-value return signature
    /// with (tag: i64, payload: payload_type) to avoid stack allocation.
    pub fn build_signature_from_type_ids(
        &self,
        params_id: &[TypeId],
        return_type_id: Option<TypeId>,
        self_param: SelfParam,
    ) -> Signature {
        let arena_ref = self.arena();

        // Build cranelift params starting with self if needed
        let mut cranelift_params: ParamVec = match &self_param {
            SelfParam::None => SmallVec::new(),
            SelfParam::Pointer => smallvec![self.pointer_type],
            SelfParam::TypedId(type_id) => {
                smallvec![type_id_to_cranelift(*type_id, arena_ref, self.pointer_type)]
            }
        };

        // Add param types
        for &type_id in params_id {
            cranelift_params.push(type_id_to_cranelift(type_id, arena_ref, self.pointer_type));
        }

        // Check if this is a fallible return type - use multi-value returns
        if let Some(ret_type_id) = return_type_id
            && arena_ref.unwrap_fallible(ret_type_id).is_some()
        {
            if is_wide_fallible(ret_type_id, arena_ref) {
                // Wide fallible (i128 success): (tag: i64, low: i64, high: i64)
                return self.jit.create_signature_multi_return(
                    &cranelift_params,
                    &[types::I64, types::I64, types::I64],
                );
            }
            // Fallible returns: (tag: i64, payload: i64)
            // We use i64 for both to have a uniform representation that works
            // for both success values and error pointers.
            return self
                .jit
                .create_signature_multi_return(&cranelift_params, &[types::I64, types::I64]);
        }

        // Check for struct return types - use multi-value or sret convention
        if let Some(ret_type_id) = return_type_id
            && let Some(field_count) = self.struct_field_count(ret_type_id)
        {
            if field_count <= crate::MAX_SMALL_STRUCT_FIELDS {
                // Small struct: return in two i64 registers
                let mut returns: SmallVec<[CraneliftType; 2]> = SmallVec::new();
                for _ in 0..field_count {
                    returns.push(types::I64);
                }
                // Pad to 2 registers for consistent calling convention
                while returns.len() < crate::MAX_SMALL_STRUCT_FIELDS {
                    returns.push(types::I64);
                }
                return self
                    .jit
                    .create_signature_multi_return(&cranelift_params, &returns);
            } else {
                // Large struct: sret convention - add hidden first param for return buffer
                let mut sret_params = SmallVec::<[CraneliftType; 8]>::new();
                sret_params.push(self.pointer_type); // sret pointer
                sret_params.extend_from_slice(&cranelift_params);
                // Return the sret pointer
                return self
                    .jit
                    .create_signature(&sret_params, Some(self.pointer_type));
            }
        }

        // Convert return type (filter out void)
        let ret = return_type_id
            .filter(|id| !id.is_void())
            .map(|id| type_id_to_cranelift(id, arena_ref, self.pointer_type));

        self.jit.create_signature(&cranelift_params, ret)
    }

    /// Get the flat slot count for a struct (recursively counts leaf fields).
    /// Used by signature building to decide small-return vs sret convention.
    /// Returns None if the type is not a struct.
    pub fn struct_field_count(&self, type_id: TypeId) -> Option<usize> {
        let arena = self.arena();
        let entities = self.registry();
        crate::structs::struct_flat_slot_count(type_id, arena, entities)
    }

    /// Build a Cranelift signature directly from a FunctionId.
    ///
    /// This is a convenience method that retrieves the function definition
    /// and builds the signature from its pre-resolved TypeIds.
    pub fn build_signature_for_function(&self, func_id: FunctionId) -> Signature {
        let func_def = self.registry().get_function(func_id);
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
        let method_def = self.registry().get_method(method_id);
        let arena = self.arena();
        let (params, ret, _) = arena
            .unwrap_function(method_def.signature_id)
            .expect("INTERNAL: method signature: missing function signature");
        self.build_signature_from_type_ids(params, Some(ret), self_param)
    }
}
