//! Shared types and traits for class/struct/implement method compilation.
//!
//! This module contains the shared abstractions used by both:
//! - `impl_dispatch` (class/struct method compilation)
//! - `impl_monomorph` (implement block registration and compilation)

use vole_frontend::ast::PrimitiveType as AstPrimitive;
use vole_frontend::{Interner, Symbol};
use vole_identity::{MethodId, ModuleId, TypeId};
use vole_vir::entity_metadata::VirTypeDef;

/// Map a primitive type name string to its TypeId constant.
/// Used for `extend range with Iterable<i64>` and similar Named-primitive target blocks.
pub(super) fn primitive_type_id_by_name(name: &str) -> TypeId {
    match name {
        "i8" => TypeId::I8,
        "i16" => TypeId::I16,
        "i32" => TypeId::I32,
        "i64" => TypeId::I64,
        "i128" => TypeId::I128,
        "u8" => TypeId::U8,
        "u16" => TypeId::U16,
        "u32" => TypeId::U32,
        "u64" => TypeId::U64,
        "f32" => TypeId::F32,
        "f64" => TypeId::F64,
        "f128" => TypeId::F128,
        "bool" => TypeId::BOOL,
        "string" => TypeId::STRING,
        "handle" => TypeId::HANDLE,
        "range" => TypeId::RANGE,
        _ => TypeId::INVALID,
    }
}

/// Get the canonical name for an AST primitive type
pub(super) fn primitive_type_name(p: AstPrimitive) -> &'static str {
    match p {
        AstPrimitive::I8 => "i8",
        AstPrimitive::I16 => "i16",
        AstPrimitive::I32 => "i32",
        AstPrimitive::I64 => "i64",
        AstPrimitive::I128 => "i128",
        AstPrimitive::U8 => "u8",
        AstPrimitive::U16 => "u16",
        AstPrimitive::U32 => "u32",
        AstPrimitive::U64 => "u64",
        AstPrimitive::F32 => "f32",
        AstPrimitive::F64 => "f64",
        AstPrimitive::F128 => "f128",
        AstPrimitive::Bool => "bool",
        AstPrimitive::String => "string",
    }
}

/// Data needed to compile methods for a type (class or struct).
///
/// Uses VIR entity metadata: methods are referenced by MethodId (resolved
/// from `VirTypeDef.methods`) instead of AST `FuncDecl` nodes.
pub(super) struct TypeMethodsData<'a> {
    /// Type name symbol
    pub name: Symbol,
    /// Instance method IDs to compile
    pub method_ids: &'a [MethodId],
    /// Static method IDs to compile
    pub static_method_ids: &'a [MethodId],
    /// Type kind for error messages ("class" or "struct")
    pub type_kind: &'static str,
}

impl<'a> TypeMethodsData<'a> {
    /// Create from a VIR type definition.
    pub fn from_vir(type_def: &'a VirTypeDef, name: Symbol) -> Self {
        Self {
            name,
            method_ids: &type_def.methods,
            static_method_ids: &type_def.static_methods,
            type_kind: type_def.type_kind(),
        }
    }
}

/// Module-specific compilation context passed to method compilation helpers.
pub(super) struct ModuleCompileInfo<'a> {
    pub interner: &'a Interner,
    pub module_id: ModuleId,
}
