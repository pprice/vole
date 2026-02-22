//! Shared types and traits for class/struct/implement method compilation.
//!
//! This module contains the shared abstractions used by both:
//! - `impl_dispatch` (class/struct method compilation)
//! - `impl_monomorph` (implement block registration and compilation)

use std::rc::Rc;

use rustc_hash::FxHashMap;

use vole_frontend::ast::{ClassDecl, PrimitiveType as AstPrimitive, StaticsBlock, StructDecl};
use vole_frontend::{Expr, FuncDecl, Interner, Symbol};
use vole_identity::ModuleId;
use vole_sema::type_arena::TypeId;

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

/// Data needed to compile methods for a type (class or struct)
pub(super) struct TypeMethodsData<'a> {
    /// Type name symbol
    pub name: Symbol,
    /// Methods to compile
    pub methods: &'a [FuncDecl],
    /// Optional static methods block
    pub statics: Option<&'a StaticsBlock>,
    /// Type kind for error messages ("class" or "struct")
    pub type_kind: &'static str,
}

impl<'a> TypeMethodsData<'a> {
    /// Create from any type implementing TypeDeclInfo
    pub fn from_decl<T: TypeDeclInfo>(decl: &'a T) -> Self {
        Self {
            name: decl.name(),
            methods: decl.methods(),
            statics: decl.statics(),
            type_kind: decl.type_kind(),
        }
    }
}

/// Module-specific compilation context passed to method compilation helpers.
pub(super) struct ModuleCompileInfo<'a> {
    pub interner: &'a Interner,
    pub module_id: ModuleId,
    pub global_inits: &'a FxHashMap<Symbol, Rc<Expr>>,
}

/// Trait to abstract over class and struct declarations for unified method compilation.
/// This allows consolidating the parallel compile_module_class_methods/compile_module_struct_methods.
pub(crate) trait TypeDeclInfo {
    /// Get the type name symbol
    fn name(&self) -> Symbol;
    /// Get the instance methods
    fn methods(&self) -> &[FuncDecl];
    /// Get the statics block (if present)
    fn statics(&self) -> Option<&StaticsBlock>;
    /// Get the type kind string for error messages ("class" or "struct")
    fn type_kind(&self) -> &'static str;
    /// Whether this is a class (vs struct). Classes need runtime type registration.
    fn is_class(&self) -> bool;
    /// Whether this type has generic type parameters (classes can be generic, structs too)
    fn has_type_params(&self) -> bool;
}

impl TypeDeclInfo for ClassDecl {
    fn name(&self) -> Symbol {
        self.name
    }
    fn methods(&self) -> &[FuncDecl] {
        &self.methods
    }
    fn statics(&self) -> Option<&StaticsBlock> {
        self.statics.as_ref()
    }
    fn type_kind(&self) -> &'static str {
        "class"
    }
    fn is_class(&self) -> bool {
        true
    }
    fn has_type_params(&self) -> bool {
        !self.type_params.is_empty()
    }
}

impl TypeDeclInfo for StructDecl {
    fn name(&self) -> Symbol {
        self.name
    }
    fn methods(&self) -> &[FuncDecl] {
        &self.methods
    }
    fn statics(&self) -> Option<&StaticsBlock> {
        self.statics.as_ref()
    }
    fn type_kind(&self) -> &'static str {
        "struct"
    }
    fn is_class(&self) -> bool {
        false
    }
    fn has_type_params(&self) -> bool {
        !self.type_params.is_empty()
    }
}
