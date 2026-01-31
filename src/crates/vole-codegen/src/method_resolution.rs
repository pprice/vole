// method_resolution.rs
//
// Utility functions for method resolution during codegen.
// The main logic now uses ResolvedMethod directly from sema + method_func_keys lookup.

use crate::AnalyzedProgram;
use vole_identity::TypeDefId;
use vole_sema::PrimitiveType;
use vole_sema::type_arena::TypeId;

/// Get TypeDefId for a type during codegen using TypeId.
///
/// This is needed for the fallback path in monomorphized contexts where
/// sema resolution is not available and we need to derive TypeDefId from
/// the concrete object type.
pub(crate) fn get_type_def_id_from_type_id(
    type_id: TypeId,
    arena: &vole_sema::type_arena::TypeArena,
    analyzed: &AnalyzedProgram,
) -> Option<TypeDefId> {
    use vole_sema::type_arena::SemaType;

    // For Class, Record, and Interface, extract TypeDefId directly
    match arena.get(type_id) {
        SemaType::Class { type_def_id, .. } => Some(*type_def_id),
        SemaType::Interface { type_def_id, .. } => Some(*type_def_id),
        SemaType::Primitive(prim) => {
            let name_table = analyzed.name_table();
            let name_id = match prim {
                PrimitiveType::I8 => name_table.primitives.i8,
                PrimitiveType::I16 => name_table.primitives.i16,
                PrimitiveType::I32 => name_table.primitives.i32,
                PrimitiveType::I64 => name_table.primitives.i64,
                PrimitiveType::I128 => name_table.primitives.i128,
                PrimitiveType::U8 => name_table.primitives.u8,
                PrimitiveType::U16 => name_table.primitives.u16,
                PrimitiveType::U32 => name_table.primitives.u32,
                PrimitiveType::U64 => name_table.primitives.u64,
                PrimitiveType::F32 => name_table.primitives.f32,
                PrimitiveType::F64 => name_table.primitives.f64,
                PrimitiveType::Bool => name_table.primitives.bool,
                PrimitiveType::String => name_table.primitives.string,
            };
            analyzed.entity_registry().type_by_name(name_id)
        }
        _ => None,
    }
}
