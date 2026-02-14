//! AST to pretty::Doc conversion for the Vole formatter.

mod decl;
mod expr;
mod types;

use pretty::{Arena, DocAllocator, DocBuilder};

use vole_frontend::Interner;
use vole_frontend::ast::*;

use decl::{
    print_class_decl, print_error_decl, print_func_decl, print_implement_block,
    print_interface_decl, print_sentinel_decl, print_struct_decl,
};
use expr::{print_expr, print_pattern, print_string_literal};
pub(super) use types::{print_return_type, print_type_expr, print_type_params};

/// Indent width for formatting (4 spaces)
pub(super) const INDENT: isize = 4;

/// Pretty-print a program to a Doc.
pub(crate) fn print_program<'a>(
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
