// method_resolution.rs
//
// Utility functions for method resolution during codegen.
// Method resolution uses VirResolvedMethod from VIR lowering.

use vole_identity::{TypeDefId, VirTypeId};
use vole_vir::VirProgram;
use vole_vir::type_table::VirTypeTable;
use vole_vir::types::{VirPrimitiveKind, VirType};

/// VIR-native variant: extract `TypeDefId` from a `VirTypeId`.
///
/// For Class, Struct, Interface, and Error types the `TypeDefId` is returned
/// from the type table's cached lookup (populated at interning time).
/// Primitives, Handle, and Array require NameTable/VirProgram resolution.
pub(crate) fn get_type_def_id_from_vir_type_id(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    analyzed: &VirProgram,
) -> Option<TypeDefId> {
    // Fast path: types whose TypeDefId was cached during interning
    // (Class, Struct, Interface, Error).
    if let Some(def) = table.type_def_id(vir_ty) {
        return Some(def);
    }

    let name_table = analyzed.name_table();

    // Primitives and Array require NameTable lookup.
    let primitive_name_id = match table.get(vir_ty) {
        VirType::Primitive(kind) => match kind {
            VirPrimitiveKind::I8 => Some(name_table.primitives.i8),
            VirPrimitiveKind::I16 => Some(name_table.primitives.i16),
            VirPrimitiveKind::I32 => Some(name_table.primitives.i32),
            VirPrimitiveKind::I64 => Some(name_table.primitives.i64),
            VirPrimitiveKind::I128 => Some(name_table.primitives.i128),
            VirPrimitiveKind::U8 => Some(name_table.primitives.u8),
            VirPrimitiveKind::U16 => Some(name_table.primitives.u16),
            VirPrimitiveKind::U32 => Some(name_table.primitives.u32),
            VirPrimitiveKind::U64 => Some(name_table.primitives.u64),
            VirPrimitiveKind::F32 => Some(name_table.primitives.f32),
            VirPrimitiveKind::F64 => Some(name_table.primitives.f64),
            VirPrimitiveKind::F128 => Some(name_table.primitives.f128),
            VirPrimitiveKind::Bool => Some(name_table.primitives.bool),
            VirPrimitiveKind::String => Some(name_table.primitives.string),
            VirPrimitiveKind::Handle => {
                return analyzed.try_type_def_id(name_table.primitives.handle);
            }
        },
        VirType::Array { .. } => {
            let name_id = analyzed.array_type_name_id()?;
            return analyzed.try_type_def_id(name_id);
        }
        _ => None,
    };

    if let Some(name_id) = primitive_name_id {
        return analyzed.try_type_def_id(name_id);
    }

    None
}
