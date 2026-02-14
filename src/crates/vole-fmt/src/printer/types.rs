//! Type expression and type parameter printing.

use pretty::{Arena, DocAllocator, DocBuilder};

use vole_frontend::Interner;
use vole_frontend::ast::*;

/// Print type parameters (e.g., `<T, U: Constraint>`).
pub(crate) fn print_type_params<'a>(
    arena: &'a Arena<'a>,
    type_params: &[TypeParam],
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    if type_params.is_empty() {
        return arena.nil();
    }

    let params: Vec<_> = type_params
        .iter()
        .map(|tp| {
            let name = arena.text(interner.resolve(tp.name).to_string());
            if let Some(constraint) = &tp.constraint {
                name.append(arena.text(": "))
                    .append(print_type_constraint(arena, constraint, interner))
            } else {
                name
            }
        })
        .collect();

    arena
        .text("<")
        .append(arena.intersperse(params, arena.text(", ")))
        .append(arena.text(">"))
}

/// Print a type constraint (e.g., `Hashable + Eq` or `i32 | string`).
fn print_type_constraint<'a>(
    arena: &'a Arena<'a>,
    constraint: &TypeConstraint,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    match constraint {
        TypeConstraint::Interface(interfaces) => {
            let parts: Vec<_> = interfaces
                .iter()
                .map(|ci| {
                    let iface_name = arena.text(interner.resolve(ci.name).to_string());
                    if ci.type_args.is_empty() {
                        iface_name
                    } else {
                        let args: Vec<_> = ci
                            .type_args
                            .iter()
                            .map(|arg| print_type_expr(arena, arg, interner))
                            .collect();
                        iface_name
                            .append(arena.text("<"))
                            .append(arena.intersperse(args, arena.text(", ")))
                            .append(arena.text(">"))
                    }
                })
                .collect();
            arena.intersperse(parts, arena.text(" + "))
        }
        TypeConstraint::Union(types) => {
            let parts: Vec<_> = types
                .iter()
                .map(|ty| print_type_expr(arena, ty, interner))
                .collect();
            arena.intersperse(parts, arena.text(" | "))
        }
        TypeConstraint::Structural { fields, methods } => {
            let mut parts: Vec<DocBuilder<'a, Arena<'a>>> = Vec::new();
            for field in fields {
                parts.push(
                    arena
                        .text(interner.resolve(field.name).to_string())
                        .append(arena.text(": "))
                        .append(print_type_expr(arena, &field.ty, interner)),
                );
            }
            for method in methods {
                // Structural method params are just types, not named params
                let param_types: Vec<_> = method
                    .params
                    .iter()
                    .map(|ty| print_type_expr(arena, ty, interner))
                    .collect();
                let params = arena
                    .text("(")
                    .append(arena.intersperse(param_types, arena.text(", ")))
                    .append(arena.text(")"));
                let return_type = arena.text(" -> ").append(print_type_expr(
                    arena,
                    &method.return_type,
                    interner,
                ));
                parts.push(
                    arena
                        .text("func ")
                        .append(arena.text(interner.resolve(method.name).to_string()))
                        .append(params)
                        .append(return_type),
                );
            }
            arena
                .text("{ ")
                .append(arena.intersperse(parts, arena.text(", ")))
                .append(arena.text(" }"))
        }
    }
}

/// Print a type expression.
pub(crate) fn print_type_expr<'a>(
    arena: &'a Arena<'a>,
    ty: &TypeExpr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    match ty {
        TypeExpr::Primitive(prim) => arena.text(primitive_type_str(*prim)),
        TypeExpr::Named(sym) => arena.text(interner.resolve(*sym).to_string()),
        TypeExpr::Array(inner) => arena
            .text("[")
            .append(print_type_expr(arena, inner, interner))
            .append(arena.text("]")),
        TypeExpr::Optional(inner) => {
            print_type_expr(arena, inner, interner).append(arena.text("?"))
        }
        TypeExpr::Union(types) => {
            let type_docs: Vec<_> = types
                .iter()
                .map(|t| print_type_expr(arena, t, interner))
                .collect();
            arena.intersperse(type_docs, arena.text(" | "))
        }
        TypeExpr::Handle => arena.text("handle"),
        TypeExpr::Never => arena.text("never"),
        TypeExpr::Unknown => arena.text("unknown"),
        TypeExpr::Function {
            params,
            return_type,
        } => {
            let param_docs: Vec<_> = params
                .iter()
                .map(|t| print_type_expr(arena, t, interner))
                .collect();
            arena
                .text("(")
                .append(arena.intersperse(param_docs, arena.text(", ")))
                .append(arena.text(") -> "))
                .append(print_type_expr(arena, return_type, interner))
        }
        TypeExpr::SelfType => arena.text("Self"),
        TypeExpr::Fallible {
            success_type,
            error_type,
        } => arena
            .text("fallible(")
            .append(print_type_expr(arena, success_type, interner))
            .append(arena.text(", "))
            .append(print_type_expr(arena, error_type, interner))
            .append(arena.text(")")),
        TypeExpr::Generic { name, args } => {
            let arg_docs: Vec<_> = args
                .iter()
                .map(|t| print_type_expr(arena, t, interner))
                .collect();
            arena
                .text(interner.resolve(*name).to_string())
                .append(arena.text("<"))
                .append(arena.intersperse(arg_docs, arena.text(", ")))
                .append(arena.text(">"))
        }
        TypeExpr::Tuple(elements) => {
            let elem_docs: Vec<_> = elements
                .iter()
                .map(|t| print_type_expr(arena, t, interner))
                .collect();
            arena
                .text("[")
                .append(arena.intersperse(elem_docs, arena.text(", ")))
                .append(arena.text("]"))
        }
        TypeExpr::FixedArray { element, size } => arena
            .text("[")
            .append(print_type_expr(arena, element, interner))
            .append(arena.text("; "))
            .append(arena.text(size.to_string()))
            .append(arena.text("]")),
        TypeExpr::Structural { fields, methods } => {
            let mut parts = Vec::new();
            for field in fields {
                parts.push(
                    arena
                        .text(interner.resolve(field.name).to_string())
                        .append(arena.text(": "))
                        .append(print_type_expr(arena, &field.ty, interner)),
                );
            }
            for method in methods {
                let params: Vec<_> = method
                    .params
                    .iter()
                    .map(|p| print_type_expr(arena, p, interner))
                    .collect();
                parts.push(
                    arena
                        .text("func ")
                        .append(arena.text(interner.resolve(method.name).to_string()))
                        .append(arena.text("("))
                        .append(arena.intersperse(params, arena.text(", ")))
                        .append(arena.text(") -> "))
                        .append(print_type_expr(arena, &method.return_type, interner)),
                );
            }
            arena
                .text("{ ")
                .append(arena.intersperse(parts, arena.text(", ")))
                .append(arena.text(" }"))
        }
        TypeExpr::Combination(parts) => {
            let type_docs: Vec<_> = parts
                .iter()
                .map(|t| print_type_expr(arena, t, interner))
                .collect();
            arena.intersperse(type_docs, arena.text(" + "))
        }
        TypeExpr::QualifiedPath { segments, args } => {
            let path_doc = arena.intersperse(
                segments
                    .iter()
                    .map(|s| arena.text(interner.resolve(*s).to_string())),
                arena.text("."),
            );
            if args.is_empty() {
                path_doc
            } else {
                let arg_docs: Vec<_> = args
                    .iter()
                    .map(|t| print_type_expr(arena, t, interner))
                    .collect();
                path_doc
                    .append(arena.text("<"))
                    .append(arena.intersperse(arg_docs, arena.text(", ")))
                    .append(arena.text(">"))
            }
        }
    }
}

/// Get the string representation of a primitive type.
fn primitive_type_str(prim: PrimitiveType) -> &'static str {
    match prim {
        PrimitiveType::I8 => "i8",
        PrimitiveType::I16 => "i16",
        PrimitiveType::I32 => "i32",
        PrimitiveType::I64 => "i64",
        PrimitiveType::I128 => "i128",
        PrimitiveType::U8 => "u8",
        PrimitiveType::U16 => "u16",
        PrimitiveType::U32 => "u32",
        PrimitiveType::U64 => "u64",
        PrimitiveType::F32 => "f32",
        PrimitiveType::F64 => "f64",
        PrimitiveType::Bool => "bool",
        PrimitiveType::String => "string",
    }
}
