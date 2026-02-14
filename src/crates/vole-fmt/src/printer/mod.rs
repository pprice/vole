//! AST to pretty::Doc conversion for the Vole formatter.

mod expr;

use pretty::{Arena, DocAllocator, DocBuilder};

use vole_frontend::Interner;
use vole_frontend::ast::*;

use expr::{print_expr, print_pattern, print_string_literal};

/// Indent width for formatting (4 spaces)
const INDENT: isize = 4;

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

/// Pretty-print a program to a Doc.
pub fn print_program<'a>(
    arena: &'a Arena<'a>,
    program: &Program,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    if program.declarations.is_empty() {
        return arena.nil();
    }

    // Join declarations with blank lines
    let docs: Vec<_> = program
        .declarations
        .iter()
        .map(|decl| print_decl(arena, decl, interner))
        .collect();

    arena.intersperse(docs, arena.hardline().append(arena.hardline()))
}

/// Print a top-level declaration.
fn print_decl<'a>(
    arena: &'a Arena<'a>,
    decl: &Decl,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    match decl {
        Decl::Function(func) => print_func_decl(arena, func, interner),
        Decl::Let(let_stmt) => print_let_stmt(arena, let_stmt, interner),
        Decl::LetTuple(_) => todo!("let tuple decl printing"),
        Decl::Tests(tests) => print_tests_decl(arena, tests, interner),
        Decl::Class(class) => print_class_decl(arena, class, interner),
        Decl::Struct(struct_decl) => print_struct_decl(arena, struct_decl, interner),
        Decl::Interface(iface) => print_interface_decl(arena, iface, interner),
        Decl::Implement(impl_block) => print_implement_block(arena, impl_block, interner),
        Decl::Error(error_decl) => print_error_decl(arena, error_decl, interner),
        Decl::Sentinel(sentinel_decl) => print_sentinel_decl(arena, sentinel_decl, interner),
        Decl::External(_) => todo!("external decl printing"),
    }
}

/// Print a let statement.
fn print_let_stmt<'a>(
    arena: &'a Arena<'a>,
    stmt: &LetStmt,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let keyword = if stmt.mutable {
        arena.text("let mut ")
    } else {
        arena.text("let ")
    };

    let name = arena.text(interner.resolve(stmt.name).to_string());

    let type_annotation = if let Some(ty) = &stmt.ty {
        arena
            .text(": ")
            .append(print_type_expr(arena, ty, interner))
    } else {
        arena.nil()
    };

    let init_doc = match &stmt.init {
        LetInit::Expr(e) => print_expr(arena, e, interner),
        LetInit::TypeAlias(ty) => print_type_expr(arena, ty, interner),
    };

    keyword
        .append(name)
        .append(type_annotation)
        .append(arena.text(" = "))
        .append(init_doc)
}

/// Print a let tuple destructuring statement.
fn print_let_tuple_stmt<'a>(
    arena: &'a Arena<'a>,
    stmt: &LetTupleStmt,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let keyword = if stmt.mutable {
        arena.text("let mut ")
    } else {
        arena.text("let ")
    };

    keyword
        .append(print_pattern(arena, &stmt.pattern, interner))
        .append(arena.text(" = "))
        .append(print_expr(arena, &stmt.init, interner))
}

/// Print type parameters (e.g., `<T, U: Constraint>`).
fn print_type_params<'a>(
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

/// Print a function declaration.
fn print_func_decl<'a>(
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
    let return_type = if let Some(ty) = &func.return_type {
        arena
            .text(" -> ")
            .append(print_type_expr(arena, ty, interner))
    } else {
        arena.nil()
    };

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

/// Print a function body (block or expression).
pub(super) fn print_func_body<'a>(
    arena: &'a Arena<'a>,
    body: &FuncBody,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    match body {
        FuncBody::Block(block) => arena.text(" ").append(print_block(arena, block, interner)),
        FuncBody::Expr(expr) => arena.text(" => ").append(print_expr(arena, expr, interner)),
    }
}

/// Print a block of statements.
pub(super) fn print_block<'a>(
    arena: &'a Arena<'a>,
    block: &Block,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    if block.stmts.is_empty() {
        return arena.text("{}");
    }

    let stmts = arena.intersperse(
        block
            .stmts
            .iter()
            .map(|stmt| print_stmt(arena, stmt, interner)),
        arena.hardline(),
    );

    arena
        .text("{")
        .append(arena.hardline().append(stmts).nest(INDENT))
        .append(arena.hardline())
        .append(arena.text("}"))
}

/// Print a statement.
pub(super) fn print_stmt<'a>(
    arena: &'a Arena<'a>,
    stmt: &Stmt,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    match stmt {
        Stmt::Let(let_stmt) => print_let_stmt(arena, let_stmt, interner),
        Stmt::LetTuple(let_tuple) => print_let_tuple_stmt(arena, let_tuple, interner),
        Stmt::Expr(expr_stmt) => print_expr(arena, &expr_stmt.expr, interner),
        Stmt::While(while_stmt) => print_while_stmt(arena, while_stmt, interner),
        Stmt::For(for_stmt) => print_for_stmt(arena, for_stmt, interner),
        Stmt::If(if_stmt) => print_if_stmt(arena, if_stmt, interner),
        Stmt::Break(_) => arena.text("break"),
        Stmt::Continue(_) => arena.text("continue"),
        Stmt::Return(return_stmt) => print_return_stmt(arena, return_stmt, interner),
        Stmt::Raise(raise_stmt) => print_raise_stmt(arena, raise_stmt, interner),
    }
}

/// Print a while statement.
fn print_while_stmt<'a>(
    arena: &'a Arena<'a>,
    stmt: &WhileStmt,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    arena
        .text("while ")
        .append(print_expr(arena, &stmt.condition, interner))
        .append(arena.text(" "))
        .append(print_block(arena, &stmt.body, interner))
}

/// Print a for statement.
fn print_for_stmt<'a>(
    arena: &'a Arena<'a>,
    stmt: &ForStmt,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    arena
        .text("for ")
        .append(arena.text(interner.resolve(stmt.var_name).to_string()))
        .append(arena.text(" in "))
        .append(print_expr(arena, &stmt.iterable, interner))
        .append(arena.text(" "))
        .append(print_block(arena, &stmt.body, interner))
}

/// Print an if statement.
fn print_if_stmt<'a>(
    arena: &'a Arena<'a>,
    stmt: &IfStmt,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let if_part = arena
        .text("if ")
        .append(print_expr(arena, &stmt.condition, interner))
        .append(arena.text(" "))
        .append(print_block(arena, &stmt.then_branch, interner));

    if let Some(else_branch) = &stmt.else_branch {
        // K&R style: } else { on same line
        if_part
            .append(arena.text(" else "))
            .append(print_block(arena, else_branch, interner))
    } else {
        if_part
    }
}

/// Print a return statement.
fn print_return_stmt<'a>(
    arena: &'a Arena<'a>,
    stmt: &ReturnStmt,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    if let Some(value) = &stmt.value {
        arena
            .text("return ")
            .append(print_expr(arena, value, interner))
    } else {
        arena.text("return")
    }
}

/// Print a raise statement.
fn print_raise_stmt<'a>(
    arena: &'a Arena<'a>,
    stmt: &RaiseStmt,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let name = interner.resolve(stmt.error_name).to_string();

    if stmt.fields.is_empty() {
        return arena.text("raise ").append(name).append(" {}");
    }

    let field_docs: Vec<_> = stmt
        .fields
        .iter()
        .map(|f| {
            arena
                .text(interner.resolve(f.name).to_string())
                .append(": ")
                .append(print_expr(arena, &f.value, interner))
        })
        .collect();

    arena
        .text("raise ")
        .append(name)
        .append(" { ")
        .append(arena.intersperse(field_docs, arena.text(", ")))
        .append(" }")
}

/// Print a type expression.
pub(super) fn print_type_expr<'a>(
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

    let return_type = if let Some(ty) = &func.return_type {
        arena
            .text(" -> ")
            .append(print_type_expr(arena, ty, interner))
    } else {
        arena.nil()
    };

    name_part.append(params).append(return_type)
}

/// Print a tests declaration.
fn print_tests_decl<'a>(
    arena: &'a Arena<'a>,
    tests: &TestsDecl,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let label = if let Some(label) = &tests.label {
        arena
            .text("tests ")
            .append(print_string_literal(arena, label))
    } else {
        arena.text("tests")
    };

    if tests.decls.is_empty() && tests.tests.is_empty() {
        return label.append(arena.text(" {}"));
    }

    // Print scoped declarations
    let decl_docs: Vec<_> = tests
        .decls
        .iter()
        .map(|decl| print_decl(arena, decl, interner))
        .collect();

    // Print test cases
    let test_docs: Vec<_> = tests
        .tests
        .iter()
        .map(|test| print_test_case(arena, test, interner))
        .collect();

    // Combine: decls first, then blank line, then tests (if both present)
    let body = if decl_docs.is_empty() {
        arena.intersperse(test_docs, arena.hardline().append(arena.hardline()))
    } else if test_docs.is_empty() {
        arena.intersperse(decl_docs, arena.hardline().append(arena.hardline()))
    } else {
        let decls_body = arena.intersperse(decl_docs, arena.hardline().append(arena.hardline()));
        let tests_body = arena.intersperse(test_docs, arena.hardline().append(arena.hardline()));
        decls_body
            .append(arena.hardline())
            .append(arena.hardline())
            .append(tests_body)
    };

    label
        .append(arena.text(" {"))
        .append(arena.hardline().append(body).nest(INDENT))
        .append(arena.hardline())
        .append(arena.text("}"))
}

/// Print a test case.
fn print_test_case<'a>(
    arena: &'a Arena<'a>,
    test: &TestCase,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    arena
        .text("test ")
        .append(print_string_literal(arena, &test.name))
        .append(print_func_body(arena, &test.body, interner))
}

/// Print a class declaration.
fn print_class_decl<'a>(
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

fn print_struct_decl<'a>(
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
fn print_error_decl<'a>(
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
fn print_sentinel_decl<'a>(
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
fn print_interface_decl<'a>(
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

    let return_type = if let Some(ty) = &method.return_type {
        arena
            .text(" -> ")
            .append(print_type_expr(arena, ty, interner))
    } else {
        arena.nil()
    };

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
fn print_implement_block<'a>(
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
