// method_resolution.rs
//
// Utility functions for method resolution during codegen.
// Method resolution uses VirResolvedMethod from VIR lowering.

use crate::AnalyzedProgram;
use vole_identity::{TypeDefId, TypeId, VirTypeId};
use vole_vir::type_table::VirTypeTable;
use vole_vir::types::{VirPrimitiveKind, VirType};

/// Get TypeDefId for a type during codegen using TypeId.
///
/// This is needed for the fallback path in monomorphized contexts where
/// sema resolution is not available and we need to derive TypeDefId from
/// the concrete object type.
#[allow(dead_code)]
pub(crate) fn get_type_def_id_from_type_id(
    type_id: TypeId,
    arena: &vole_sema::type_arena::TypeArena,
    analyzed: &AnalyzedProgram,
) -> Option<TypeDefId> {
    use vole_sema::type_arena::SemaType;

    let name_table = analyzed.name_table();
    let primitive_name_id = match type_id {
        TypeId::I8 => Some(name_table.primitives.i8),
        TypeId::I16 => Some(name_table.primitives.i16),
        TypeId::I32 => Some(name_table.primitives.i32),
        TypeId::I64 => Some(name_table.primitives.i64),
        TypeId::I128 => Some(name_table.primitives.i128),
        TypeId::U8 => Some(name_table.primitives.u8),
        TypeId::U16 => Some(name_table.primitives.u16),
        TypeId::U32 => Some(name_table.primitives.u32),
        TypeId::U64 => Some(name_table.primitives.u64),
        TypeId::F32 => Some(name_table.primitives.f32),
        TypeId::F64 => Some(name_table.primitives.f64),
        TypeId::F128 => Some(name_table.primitives.f128),
        TypeId::BOOL => Some(name_table.primitives.bool),
        TypeId::STRING => Some(name_table.primitives.string),
        _ => None,
    };
    if let Some(name_id) = primitive_name_id {
        return analyzed.try_type_def_id(name_id);
    }

    // For Class, Struct, and Interface, extract TypeDefId directly
    match arena.get(type_id) {
        SemaType::Class { type_def_id, .. } => Some(*type_def_id),
        SemaType::Struct { type_def_id, .. } => Some(*type_def_id),
        SemaType::Interface { type_def_id, .. } => Some(*type_def_id),
        SemaType::Handle => {
            let name_id = analyzed.name_table().primitives.handle;
            analyzed.try_type_def_id(name_id)
        }
        SemaType::Array(_) => {
            let name_id = analyzed.array_type_name_id()?;
            analyzed.try_type_def_id(name_id)
        }
        _ => None,
    }
}

/// VIR-native variant: extract `TypeDefId` from a `VirTypeId`.
///
/// Handles primitives (via NameTable), class/struct/interface/error (direct
/// `TypeDefId`), Handle (via NameTable), and Array (via `array_type_name_id`).
pub(crate) fn get_type_def_id_from_vir_type_id(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
    analyzed: &AnalyzedProgram,
) -> Option<TypeDefId> {
    let name_table = analyzed.name_table();

    // F128 is stored as VirType::Unknown in the type table but has a reserved VirTypeId.
    if vir_ty == VirTypeId::F128 {
        return analyzed.try_type_def_id(name_table.primitives.f128);
    }

    // Check primitives and structured types
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
            VirPrimitiveKind::Bool => Some(name_table.primitives.bool),
            VirPrimitiveKind::String => Some(name_table.primitives.string),
            VirPrimitiveKind::Handle => {
                return analyzed.try_type_def_id(name_table.primitives.handle);
            }
        },
        VirType::Class { def, .. }
        | VirType::Struct { def, .. }
        | VirType::Interface { def, .. }
        | VirType::Error { def } => return Some(*def),
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
