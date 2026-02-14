//! Declaration printing for the Vole formatter.

use pretty::{Arena, DocAllocator, DocBuilder};

use vole_frontend::Interner;
use vole_frontend::ast::*;

use super::expr::print_string_literal;
use super::{INDENT, print_func_body, print_return_type, print_type_expr, print_type_params};

/// Groups arguments for printing a class-like body (class, struct).
struct ClassLikeBody<'a, 'b> {
    name: &'b str,
    type_params: DocBuilder<'a, Arena<'a>>,
    implements: DocBuilder<'a, Arena<'a>>,
    fields: &'b [FieldDef],
    external: Option<&'b ExternalBlock>,
    methods: &'b [FuncDecl],
    statics: Option<&'b StaticsBlock>,
    keyword: &'b str,
}

/// Print a function declaration.
pub(super) fn print_func_decl<'a>(
    arena: &'a Arena<'a>,
    func: &FuncDecl,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let name = interner.resolve(func.name).to_string();

    // Type parameters
    let type_params = print_type_params(arena, &func.type_params, interner);

    // Build parameter list
    let params = print_params(arena, &func.params, interner);

    // Return type
    let return_type = print_return_type(arena, &func.return_type, interner);

    arena
        .text("func ")
        .append(arena.text(name))
        .append(type_params)
        .append(params)
        .append(return_type)
        .append(print_func_body(arena, &func.body, interner))
}

/// Print function parameters with grouping for line breaking.
fn print_params<'a>(
    arena: &'a Arena<'a>,
    params: &[Param],
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    if params.is_empty() {
        return arena.text("()");
    }

    let param_docs: Vec<_> = params
        .iter()
        .map(|p| print_param(arena, p, interner))
        .collect();

    // Always use single-line format: params separated by ", "
    // Vole's parser doesn't support newlines after opening paren in function declarations
    let single_line = arena.intersperse(param_docs, arena.text(", "));

    arena.text("(").append(single_line).append(arena.text(")"))
}

/// Print a single parameter.
fn print_param<'a>(
    arena: &'a Arena<'a>,
    param: &Param,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    arena
        .text(interner.resolve(param.name).to_string())
        .append(arena.text(": "))
        .append(print_type_expr(arena, &param.ty, interner))
}

/// Print an external block.
fn print_external_block<'a>(
    arena: &'a Arena<'a>,
    external: &ExternalBlock,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let header = arena
        .text("external(")
        .append(print_string_literal(arena, &external.module_path))
        .append(arena.text(")"));

    if external.functions.is_empty() {
        return header.append(arena.text(" {}"));
    }

    let func_docs: Vec<_> = external
        .functions
        .iter()
        .map(|f| print_external_func(arena, f, interner))
        .collect();

    let body = arena.intersperse(func_docs, arena.hardline());

    header
        .append(arena.text(" {"))
        .append(arena.hardline().append(body).nest(INDENT))
        .append(arena.hardline())
        .append(arena.text("}"))
}

/// Print an external function declaration.
fn print_external_func<'a>(
    arena: &'a Arena<'a>,
    func: &ExternalFunc,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let name_part = if let Some(native_name) = &func.native_name {
        arena
            .text("func ")
            .append(print_string_literal(arena, native_name))
            .append(arena.text(" as "))
            .append(arena.text(interner.resolve(func.vole_name).to_string()))
    } else {
        arena
            .text("func ")
            .append(arena.text(interner.resolve(func.vole_name).to_string()))
    };

    let params = print_params(arena, &func.params, interner);

    let return_type = print_return_type(arena, &func.return_type, interner);

    name_part.append(params).append(return_type)
}

/// Print a class declaration.
pub(super) fn print_class_decl<'a>(
    arena: &'a Arena<'a>,
    class: &ClassDecl,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let name = interner.resolve(class.name).to_string();

    let type_params = print_type_params(arena, &class.type_params, interner);

    let implements = if class.implements.is_empty() {
        arena.nil()
    } else {
        let impl_types: Vec<_> = class
            .implements
            .iter()
            .map(|ty| print_type_expr(arena, ty, interner))
            .collect();
        arena
            .text(" implements ")
            .append(arena.intersperse(impl_types, arena.text(", ")))
    };

    print_class_like_body(
        arena,
        ClassLikeBody {
            name: &name,
            type_params,
            implements,
            fields: &class.fields,
            external: class.external.as_ref(),
            methods: &class.methods,
            statics: class.statics.as_ref(),
            keyword: "class",
        },
        interner,
    )
}

/// Print a struct declaration.
pub(super) fn print_struct_decl<'a>(
    arena: &'a Arena<'a>,
    struct_decl: &StructDecl,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let name = interner.resolve(struct_decl.name).to_string();

    let type_params = print_type_params(arena, &struct_decl.type_params, interner);

    print_class_like_body(
        arena,
        ClassLikeBody {
            name: &name,
            type_params,
            implements: arena.nil(),
            fields: &struct_decl.fields,
            external: None,
            methods: &struct_decl.methods,
            statics: struct_decl.statics.as_ref(),
            keyword: "struct",
        },
        interner,
    )
}

/// Print an error declaration.
pub(super) fn print_error_decl<'a>(
    arena: &'a Arena<'a>,
    error_decl: &ErrorDecl,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let name = interner.resolve(error_decl.name).to_string();

    if error_decl.fields.is_empty() {
        // error Name {}
        arena.text("error ").append(name).append(" {}")
    } else {
        // error Name { field1: Type, field2: Type }
        let fields: Vec<_> = error_decl
            .fields
            .iter()
            .map(|f| print_field_def(arena, f, interner))
            .collect();

        let body = arena
            .hardline()
            .append(arena.intersperse(fields, arena.hardline()))
            .nest(INDENT)
            .append(arena.hardline());

        arena
            .text("error ")
            .append(name)
            .append(" {")
            .append(body)
            .append("}")
    }
}

/// Print a sentinel declaration.
pub(super) fn print_sentinel_decl<'a>(
    arena: &'a Arena<'a>,
    sentinel_decl: &SentinelDecl,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let name = interner.resolve(sentinel_decl.name).to_string();
    arena.text("sentinel ").append(arena.text(name))
}

/// Print the body of a class-like declaration.
fn print_class_like_body<'a, 'b>(
    arena: &'a Arena<'a>,
    body: ClassLikeBody<'a, 'b>,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let ClassLikeBody {
        name,
        type_params,
        implements,
        fields,
        external,
        methods,
        statics,
        keyword,
    } = body;

    if fields.is_empty() && external.is_none() && methods.is_empty() && statics.is_none() {
        return arena
            .text(keyword.to_string())
            .append(arena.text(" "))
            .append(arena.text(name.to_string()))
            .append(type_params)
            .append(implements)
            .append(arena.text(" {}"));
    }

    // Build body sections
    let mut sections: Vec<DocBuilder<'a, Arena<'a>>> = Vec::new();

    // Fields section
    if !fields.is_empty() {
        let field_docs: Vec<_> = fields
            .iter()
            .map(|f| print_field_def(arena, f, interner))
            .collect();
        sections.push(arena.intersperse(field_docs, arena.hardline()));
    }

    // External section
    if let Some(ext) = external {
        sections.push(print_external_block(arena, ext, interner));
    }

    // Methods section
    if !methods.is_empty() {
        let method_docs: Vec<_> = methods
            .iter()
            .map(|m| print_func_decl(arena, m, interner))
            .collect();
        sections.push(arena.intersperse(method_docs, arena.hardline().append(arena.hardline())));
    }

    // Statics section
    if let Some(statics_block) = statics {
        sections.push(print_statics_block(arena, statics_block, interner));
    }

    // Join sections with blank lines
    let body = arena.intersperse(sections, arena.hardline().append(arena.hardline()));

    arena
        .text(keyword.to_string())
        .append(arena.text(" "))
        .append(arena.text(name.to_string()))
        .append(type_params)
        .append(implements)
        .append(arena.text(" {"))
        .append(arena.hardline().append(body).nest(INDENT))
        .append(arena.hardline())
        .append(arena.text("}"))
}

/// Print a field definition.
fn print_field_def<'a>(
    arena: &'a Arena<'a>,
    field: &FieldDef,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    arena
        .text(interner.resolve(field.name).to_string())
        .append(arena.text(": "))
        .append(print_type_expr(arena, &field.ty, interner))
        .append(arena.text(","))
}

/// Print an interface declaration.
pub(super) fn print_interface_decl<'a>(
    arena: &'a Arena<'a>,
    iface: &InterfaceDecl,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let name = interner.resolve(iface.name).to_string();

    let type_params = print_type_params(arena, &iface.type_params, interner);

    let extends = if iface.extends.is_empty() {
        arena.nil()
    } else {
        let extend_names: Vec<_> = iface
            .extends
            .iter()
            .map(|s| arena.text(interner.resolve(*s).to_string()))
            .collect();
        arena
            .text(" extends ")
            .append(arena.intersperse(extend_names, arena.text(", ")))
    };

    if iface.fields.is_empty()
        && iface.external_blocks.is_empty()
        && iface.methods.is_empty()
        && iface.statics.is_none()
    {
        return arena
            .text("interface ")
            .append(arena.text(name))
            .append(type_params)
            .append(extends)
            .append(arena.text(" {}"));
    }

    // Build body sections
    let mut sections: Vec<DocBuilder<'a, Arena<'a>>> = Vec::new();

    // Fields section
    if !iface.fields.is_empty() {
        let field_docs: Vec<_> = iface
            .fields
            .iter()
            .map(|f| print_field_def(arena, f, interner))
            .collect();
        sections.push(arena.intersperse(field_docs, arena.hardline()));
    }

    // External sections
    for ext in &iface.external_blocks {
        sections.push(print_external_block(arena, ext, interner));
    }

    // Methods section
    if !iface.methods.is_empty() {
        let method_docs: Vec<_> = iface
            .methods
            .iter()
            .map(|m| print_interface_method(arena, m, interner))
            .collect();
        sections.push(arena.intersperse(method_docs, arena.hardline()));
    }

    // Statics section
    if let Some(ref statics_block) = iface.statics {
        sections.push(print_statics_block(arena, statics_block, interner));
    }

    // Join sections with blank lines
    let body = arena.intersperse(sections, arena.hardline().append(arena.hardline()));

    arena
        .text("interface ")
        .append(arena.text(name))
        .append(type_params)
        .append(extends)
        .append(arena.text(" {"))
        .append(arena.hardline().append(body).nest(INDENT))
        .append(arena.hardline())
        .append(arena.text("}"))
}

/// Print an interface method.
fn print_interface_method<'a>(
    arena: &'a Arena<'a>,
    method: &InterfaceMethod,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let name = interner.resolve(method.name).to_string();
    let params = print_params(arena, &method.params, interner);

    let return_type = print_return_type(arena, &method.return_type, interner);

    let signature = arena
        .text("func ")
        .append(arena.text(name))
        .append(params)
        .append(return_type);

    if let Some(body) = &method.body {
        signature.append(print_func_body(arena, body, interner))
    } else {
        signature
    }
}

/// Print an implement block.
pub(super) fn print_implement_block<'a>(
    arena: &'a Arena<'a>,
    impl_block: &ImplementBlock,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let header = if let Some(ref trait_type) = impl_block.trait_type {
        arena
            .text("implement ")
            .append(print_type_expr(arena, trait_type, interner))
            .append(arena.text(" for "))
            .append(print_type_expr(arena, &impl_block.target_type, interner))
    } else {
        arena
            .text("implement ")
            .append(print_type_expr(arena, &impl_block.target_type, interner))
    };

    if impl_block.external.is_none()
        && impl_block.methods.is_empty()
        && impl_block.statics.is_none()
    {
        return header.append(arena.text(" {}"));
    }

    // Build body sections
    let mut sections: Vec<DocBuilder<'a, Arena<'a>>> = Vec::new();

    // External section
    if let Some(ext) = &impl_block.external {
        sections.push(print_external_block(arena, ext, interner));
    }

    // Methods section
    if !impl_block.methods.is_empty() {
        let method_docs: Vec<_> = impl_block
            .methods
            .iter()
            .map(|m| print_func_decl(arena, m, interner))
            .collect();
        sections.push(arena.intersperse(method_docs, arena.hardline().append(arena.hardline())));
    }

    // Statics section
    if let Some(ref statics) = impl_block.statics {
        sections.push(print_statics_block(arena, statics, interner));
    }

    // Join sections with blank lines
    let body = arena.intersperse(sections, arena.hardline().append(arena.hardline()));

    header
        .append(arena.text(" {"))
        .append(arena.hardline().append(body).nest(INDENT))
        .append(arena.hardline())
        .append(arena.text("}"))
}

/// Print a statics block containing static methods and optional external blocks.
///
/// ```vole
/// statics {
///     func create() -> Self { ... }
///     external("native:mod") { func new() -> Self }
/// }
/// ```
fn print_statics_block<'a>(
    arena: &'a Arena<'a>,
    statics: &StaticsBlock,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    if statics.methods.is_empty() && statics.external_blocks.is_empty() {
        return arena.text("statics {}");
    }

    let mut sections: Vec<DocBuilder<'a, Arena<'a>>> = Vec::new();

    // External blocks within statics
    for ext in &statics.external_blocks {
        sections.push(print_external_block(arena, ext, interner));
    }

    // Static methods
    if !statics.methods.is_empty() {
        let method_docs: Vec<_> = statics
            .methods
            .iter()
            .map(|m| print_interface_method(arena, m, interner))
            .collect();
        sections.push(arena.intersperse(method_docs, arena.hardline().append(arena.hardline())));
    }

    let body = arena.intersperse(sections, arena.hardline().append(arena.hardline()));

    arena
        .text("statics {")
        .append(arena.hardline().append(body).nest(INDENT))
        .append(arena.hardline())
        .append(arena.text("}"))
}
