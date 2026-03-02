use cranelift::prelude::{Signature, Type as CraneliftType, types};
use smallvec::{SmallVec, smallvec};

use super::Compiler;
use crate::types::vir_conversions::{vir_is_wide, vir_type_to_cranelift};
use crate::types::{is_wide_fallible, type_id_to_cranelift};
use vole_identity::{FunctionId, MethodId, TypeId, VirTypeId};
use vole_vir::types::VirType;

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

/// VIR-based equivalent of [`SelfParam`].
///
/// Uses `VirTypeId` instead of sema `TypeId`, for code paths that build
/// signatures from VIR function data.
pub enum VirSelfParam {
    /// No self parameter (functions, static methods)
    None,
    /// Self is a pointer (regular methods)
    Pointer,
    /// Self has a specific type using VirTypeId (implement blocks on primitives)
    Typed(VirTypeId),
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
        self.vir_query_type_to_cranelift(type_id)
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
            && self.vir_query_unwrap_fallible(ret_type_id).is_some()
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
            return self.build_struct_return_sig(&cranelift_params, field_count);
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
        crate::structs::struct_flat_slot_count(type_id, arena, self.analyzed)
    }

    /// Build a Cranelift signature directly from a FunctionId.
    ///
    /// This is a convenience method that retrieves the function definition
    /// and builds the signature from its pre-resolved TypeIds.
    pub fn build_signature_for_function(&self, func_id: FunctionId) -> Signature {
        let func_def = self.analyzed.function_def(func_id);
        self.build_signature_from_type_ids(
            &func_def.sema_param_types,
            Some(func_def.sema_return_type),
            SelfParam::None,
        )
    }

    /// Build a Cranelift signature directly from a MethodId.
    ///
    /// Uses the VIR method definition's `param_types` and `return_type`
    /// (VirTypeId) instead of unwrapping the sema TypeId signature.
    pub fn build_signature_for_method(
        &self,
        method_id: MethodId,
        self_param: SelfParam,
    ) -> Signature {
        let method_def = self.analyzed.method_def(method_id);
        let vir_self_param = match self_param {
            SelfParam::None => VirSelfParam::None,
            SelfParam::Pointer => VirSelfParam::Pointer,
            SelfParam::TypedId(type_id) => VirSelfParam::Typed(self.vir_lookup(type_id)),
        };
        self.build_signature_from_vir_types(
            &method_def.param_types,
            method_def.return_type,
            vir_self_param,
        )
    }

    // ========================================================================
    // VIR-based signature building (VirTypeTable instead of TypeArena)
    // ========================================================================

    /// Build a Cranelift signature from VIR types.
    ///
    /// VIR equivalent of [`build_signature_from_type_ids`](Self::build_signature_from_type_ids).
    /// Reads the VirTypeTable for type conversion and fallible detection,
    /// falling back to sema TypeId only for struct flat-slot counting (which
    /// depends on EntityRegistry field types not yet in VIR).
    pub fn build_signature_from_vir_types(
        &self,
        param_vir_types: &[VirTypeId],
        return_vir_type: VirTypeId,
        self_param: VirSelfParam,
    ) -> Signature {
        let table = self.vir_type_table();
        let ptr = self.pointer_type;

        // Build cranelift params starting with self if needed
        let mut cranelift_params: ParamVec = match &self_param {
            VirSelfParam::None => SmallVec::new(),
            VirSelfParam::Pointer => smallvec![ptr],
            VirSelfParam::Typed(vir_ty) => {
                smallvec![vir_type_to_cranelift(*vir_ty, table, ptr)]
            }
        };

        // Add param types via VirTypeTable
        for &vir_ty in param_vir_types {
            cranelift_params.push(vir_type_to_cranelift(vir_ty, table, ptr));
        }

        // Check for fallible return type via VirType variant
        if let VirType::Fallible { success, .. } = table.get(return_vir_type) {
            if vir_is_wide(*success, table) {
                // Wide fallible (i128 success): (tag, low, high)
                return self.jit.create_signature_multi_return(
                    &cranelift_params,
                    &[types::I64, types::I64, types::I64],
                );
            }
            // Fallible: (tag, payload)
            return self
                .jit
                .create_signature_multi_return(&cranelift_params, &[types::I64, types::I64]);
        }

        // Struct return: still uses sema TypeId for flat-slot counting
        // (EntityRegistry lookups come from TypeDefId in VirTypeTable).
        if matches!(table.get(return_vir_type), VirType::Struct { .. })
            && let Some(field_count) = crate::types::vir_struct_helpers::vir_struct_flat_slot_count(
                return_vir_type,
                table,
                self.analyzed,
            )
        {
            return self.build_struct_return_sig(&cranelift_params, field_count);
        }

        // Normal return (filter out void)
        let ret = (return_vir_type != VirTypeId::VOID)
            .then(|| vir_type_to_cranelift(return_vir_type, table, ptr));

        self.jit.create_signature(&cranelift_params, ret)
    }

    /// Build a Cranelift signature from a [`VirFunction`](vole_vir::func::VirFunction).
    ///
    /// Convenience wrapper that extracts VIR param/return types from the
    /// function definition and delegates to
    /// [`build_signature_from_vir_types`](Self::build_signature_from_vir_types).
    pub fn build_vir_signature_for_function(&self, func_id: FunctionId) -> Signature {
        let vir_func = self
            .analyzed
            .get_vir_function(func_id)
            .unwrap_or_else(|| panic!("build_vir_signature_for_function: no VIR for {func_id:?}"));
        let param_vir_types: SmallVec<[VirTypeId; 8]> = vir_func
            .params
            .iter()
            .map(|(_, _, vir_ty)| *vir_ty)
            .collect();
        self.build_signature_from_vir_types(
            &param_vir_types,
            vir_func.vir_return_type,
            VirSelfParam::None,
        )
    }

    /// Build a Cranelift signature directly from a `VirFunction` reference.
    ///
    /// Unlike [`build_vir_signature_for_function`](Self::build_vir_signature_for_function)
    /// which looks up the function by `FunctionId`, this takes the function
    /// directly.  Used for VIR-monomorphized functions whose `FunctionId` is
    /// shared with the generic template.
    pub fn build_signature_for_vir_func(
        &self,
        vir_func: &vole_vir::func::VirFunction,
    ) -> Signature {
        let param_vir_types: SmallVec<[VirTypeId; 8]> = vir_func
            .params
            .iter()
            .map(|(_, _, vir_ty)| *vir_ty)
            .collect();
        self.build_signature_from_vir_types(
            &param_vir_types,
            vir_func.vir_return_type,
            VirSelfParam::None,
        )
    }

    // ========================================================================
    // Shared helpers
    // ========================================================================

    /// Build a struct return signature (small-struct multi-return or sret).
    ///
    /// Shared by both TypeId and VirTypeId code paths.
    fn build_struct_return_sig(
        &self,
        cranelift_params: &[CraneliftType],
        field_count: usize,
    ) -> Signature {
        if field_count <= crate::MAX_SMALL_STRUCT_FIELDS {
            // Small struct: return in registers, padded to MAX_SMALL_STRUCT_FIELDS
            let mut returns: SmallVec<[CraneliftType; 2]> = SmallVec::new();
            for _ in 0..field_count {
                returns.push(types::I64);
            }
            while returns.len() < crate::MAX_SMALL_STRUCT_FIELDS {
                returns.push(types::I64);
            }
            self.jit
                .create_signature_multi_return(cranelift_params, &returns)
        } else {
            // Large struct: sret convention - hidden first param for return buffer
            let mut sret_params = SmallVec::<[CraneliftType; 8]>::new();
            sret_params.push(self.pointer_type);
            sret_params.extend_from_slice(cranelift_params);
            self.jit
                .create_signature(&sret_params, Some(self.pointer_type))
        }
    }
}
