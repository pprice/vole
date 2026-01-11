//! AST to pretty::Doc conversion for the Vole formatter.

use pretty::{Arena, DocAllocator, DocBuilder};

use crate::frontend::Interner;
use crate::frontend::ast::*;

/// Indent width for formatting (4 spaces)
const INDENT: isize = 4;

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
        Decl::Tests(tests) => print_tests_decl(arena, tests, interner),
        Decl::Class(class) => print_class_decl(arena, class, interner),
        Decl::Record(record) => print_record_decl(arena, record, interner),
        Decl::Interface(iface) => print_interface_decl(arena, iface, interner),
        Decl::Implement(impl_block) => print_implement_block(arena, impl_block, interner),
        Decl::Error(error_decl) => print_error_decl(arena, error_decl, interner),
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

/// Print a function declaration.
fn print_func_decl<'a>(
    arena: &'a Arena<'a>,
    func: &FuncDecl,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let name = interner.resolve(func.name).to_string();

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
        .append(params)
        .append(return_type)
        .append(arena.text(" "))
        .append(print_block(arena, &func.body, interner))
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

    // Multi-line format: each param on its own line with trailing comma
    let multi_line = arena
        .hardline()
        .append(arena.intersperse(
            param_docs.iter().cloned(),
            arena.text(",").append(arena.hardline()),
        ))
        .append(arena.text(","))
        .nest(INDENT)
        .append(arena.hardline());

    // Single line format: params separated by ", "
    let single_line = arena.intersperse(param_docs, arena.text(", "));

    arena
        .text("(")
        .append(multi_line.flat_alt(single_line).group())
        .append(arena.text(")"))
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

/// Print a block of statements.
fn print_block<'a>(
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
fn print_stmt<'a>(
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

/// Print an expression.
fn print_expr<'a>(
    arena: &'a Arena<'a>,
    expr: &Expr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    match &expr.kind {
        ExprKind::IntLiteral(n) => arena.text(n.to_string()),
        ExprKind::FloatLiteral(f) => print_float_literal(arena, *f),
        ExprKind::BoolLiteral(b) => arena.text(if *b { "true" } else { "false" }),
        ExprKind::StringLiteral(s) => print_string_literal(arena, s),
        ExprKind::InterpolatedString(parts) => print_interpolated_string(arena, parts, interner),
        ExprKind::Identifier(sym) => arena.text(interner.resolve(*sym).to_string()),
        ExprKind::Binary(bin) => print_binary_expr(arena, bin, interner),
        ExprKind::Unary(unary) => print_unary_expr(arena, unary, interner),
        ExprKind::Call(call) => print_call_expr(arena, call, interner),
        ExprKind::Assign(assign) => print_assign_expr(arena, assign, interner),
        ExprKind::CompoundAssign(compound) => print_compound_assign_expr(arena, compound, interner),
        ExprKind::Range(range) => print_range_expr(arena, range, interner),
        ExprKind::Grouping(inner) => arena
            .text("(")
            .append(print_expr(arena, inner, interner))
            .append(arena.text(")")),
        ExprKind::ArrayLiteral(elements) => print_array_literal(arena, elements, interner),
        ExprKind::RepeatLiteral { element, count } => arena
            .text("[")
            .append(print_expr(arena, element, interner))
            .append(arena.text("; "))
            .append(arena.text(count.to_string()))
            .append(arena.text("]")),
        ExprKind::Index(index) => print_index_expr(arena, index, interner),
        ExprKind::Match(match_expr) => print_match_expr(arena, match_expr, interner),
        ExprKind::Nil => arena.text("nil"),
        ExprKind::Done => arena.text("Done {}"),
        ExprKind::NullCoalesce(nc) => print_null_coalesce_expr(arena, nc, interner),
        ExprKind::Is(is_expr) => print_is_expr(arena, is_expr, interner),
        ExprKind::Lambda(lambda) => print_lambda_expr(arena, lambda, interner),
        ExprKind::TypeLiteral(ty) => print_type_expr(arena, ty, interner),
        ExprKind::StructLiteral(struct_lit) => print_struct_literal(arena, struct_lit, interner),
        ExprKind::FieldAccess(field) => print_field_access(arena, field, interner),
        ExprKind::OptionalChain(chain) => print_optional_chain(arena, chain, interner),
        ExprKind::MethodCall(method) => print_method_call(arena, method, interner),
        ExprKind::Try(inner) => arena
            .text("try")
            .append(arena.space())
            .append(print_expr(arena, inner, interner)),
        ExprKind::Import(path) => arena
            .text("import")
            .append(arena.space())
            .append(arena.text(format!("\"{}\"", path))),
        ExprKind::Yield(yield_expr) => arena
            .text("yield")
            .append(arena.space())
            .append(print_expr(arena, &yield_expr.value, interner)),
        ExprKind::Block(block) => {
            let mut doc = arena.text("{");
            if !block.stmts.is_empty() || block.trailing_expr.is_some() {
                doc = doc.append(arena.hardline());
            }
            for stmt in &block.stmts {
                doc = doc.append(print_stmt(arena, stmt, interner).nest(INDENT));
                doc = doc.append(arena.hardline());
            }
            if let Some(trailing) = &block.trailing_expr {
                doc = doc.append(print_expr(arena, trailing, interner).nest(INDENT));
                doc = doc.append(arena.hardline());
            }
            doc.append(arena.text("}"))
        }
        ExprKind::If(if_expr) => {
            let mut doc = arena
                .text("if ")
                .append(print_expr(arena, &if_expr.condition, interner))
                .append(arena.text(" "))
                .append(print_expr(arena, &if_expr.then_branch, interner));
            if let Some(else_branch) = &if_expr.else_branch {
                doc = doc.append(arena.text(" else ")).append(print_expr(
                    arena,
                    else_branch,
                    interner,
                ));
            }
            doc
        }
    }
}

/// Print a float literal, ensuring it has a decimal point.
fn print_float_literal<'a>(arena: &'a Arena<'a>, f: f64) -> DocBuilder<'a, Arena<'a>> {
    let s = f.to_string();
    // Ensure we have a decimal point
    if s.contains('.') || s.contains('e') || s.contains('E') {
        arena.text(s)
    } else {
        arena.text(format!("{}.0", s))
    }
}

/// Print a string literal with proper escaping.
fn print_string_literal<'a>(arena: &'a Arena<'a>, s: &str) -> DocBuilder<'a, Arena<'a>> {
    // Check if it's a raw string (contains unescaped backslashes that would need escaping)
    // For now, just use regular string literals
    let mut result = String::with_capacity(s.len() + 2);
    result.push('"');
    for c in s.chars() {
        match c {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            c => result.push(c),
        }
    }
    result.push('"');
    arena.text(result)
}

/// Print an interpolated string.
fn print_interpolated_string<'a>(
    arena: &'a Arena<'a>,
    parts: &[StringPart],
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let mut result = arena.text("\"");
    for part in parts {
        result = match part {
            StringPart::Literal(s) => {
                // Escape the literal part (but don't double-escape { and })
                let mut escaped = String::new();
                for c in s.chars() {
                    match c {
                        '"' => escaped.push_str("\\\""),
                        '\\' => escaped.push_str("\\\\"),
                        '\n' => escaped.push_str("\\n"),
                        '\r' => escaped.push_str("\\r"),
                        '\t' => escaped.push_str("\\t"),
                        c => escaped.push(c),
                    }
                }
                result.append(arena.text(escaped))
            }
            StringPart::Expr(expr) => {
                // Render the expression inside {expr}
                result
                    .append(arena.text("{"))
                    .append(print_expr(arena, expr, interner))
                    .append(arena.text("}"))
            }
        };
    }
    result.append(arena.text("\""))
}

/// Print a binary expression.
fn print_binary_expr<'a>(
    arena: &'a Arena<'a>,
    bin: &BinaryExpr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let op_str = match bin.op {
        BinaryOp::Add => "+",
        BinaryOp::Sub => "-",
        BinaryOp::Mul => "*",
        BinaryOp::Div => "/",
        BinaryOp::Mod => "%",
        BinaryOp::Eq => "==",
        BinaryOp::Ne => "!=",
        BinaryOp::Lt => "<",
        BinaryOp::Gt => ">",
        BinaryOp::Le => "<=",
        BinaryOp::Ge => ">=",
        BinaryOp::And => "&&",
        BinaryOp::Or => "||",
        BinaryOp::BitAnd => "&",
        BinaryOp::BitOr => "|",
        BinaryOp::BitXor => "^",
        BinaryOp::Shl => "<<",
        BinaryOp::Shr => ">>",
    };

    // For long expressions, break before the operator
    let left = print_expr(arena, &bin.left, interner);
    let right = print_expr(arena, &bin.right, interner);

    // Single line: left op right
    // Multi-line: left\n    op right (break before operator)
    left.append(arena.text(" "))
        .append(arena.text(op_str))
        .append(arena.text(" "))
        .append(right)
        .group()
}

/// Print a unary expression.
fn print_unary_expr<'a>(
    arena: &'a Arena<'a>,
    unary: &UnaryExpr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let op_str = match unary.op {
        UnaryOp::Neg => "-",
        UnaryOp::Not => "!",
        UnaryOp::BitNot => "~",
    };

    arena
        .text(op_str)
        .append(print_expr(arena, &unary.operand, interner))
}

/// Print a call expression.
fn print_call_expr<'a>(
    arena: &'a Arena<'a>,
    call: &CallExpr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let callee = print_expr(arena, &call.callee, interner);
    let args = print_call_args(arena, &call.args, interner);

    callee.append(args)
}

/// Print call arguments with grouping for line breaking.
fn print_call_args<'a>(
    arena: &'a Arena<'a>,
    args: &[Expr],
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    if args.is_empty() {
        return arena.text("()");
    }

    let arg_docs: Vec<_> = args
        .iter()
        .map(|a| print_expr(arena, a, interner))
        .collect();

    // Multi-line format: each arg on its own line with trailing comma
    let multi_line = arena
        .hardline()
        .append(arena.intersperse(
            arg_docs.iter().cloned(),
            arena.text(",").append(arena.hardline()),
        ))
        .append(arena.text(","))
        .nest(INDENT)
        .append(arena.hardline());

    // Single line format: args separated by ", "
    let single_line = arena.intersperse(arg_docs, arena.text(", "));

    arena
        .text("(")
        .append(multi_line.flat_alt(single_line).group())
        .append(arena.text(")"))
}

/// Print an assignment expression.
fn print_assign_expr<'a>(
    arena: &'a Arena<'a>,
    assign: &AssignExpr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let target = print_assign_target(arena, &assign.target, interner);
    let value = print_expr(arena, &assign.value, interner);

    target.append(arena.text(" = ")).append(value)
}

/// Print an assignment target.
fn print_assign_target<'a>(
    arena: &'a Arena<'a>,
    target: &AssignTarget,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    match target {
        AssignTarget::Variable(sym) => arena.text(interner.resolve(*sym).to_string()),
        AssignTarget::Index { object, index } => print_expr(arena, object, interner)
            .append(arena.text("["))
            .append(print_expr(arena, index, interner))
            .append(arena.text("]")),
        AssignTarget::Field { object, field, .. } => print_expr(arena, object, interner)
            .append(arena.text("."))
            .append(arena.text(interner.resolve(*field).to_string())),
    }
}

/// Print a compound assignment expression.
fn print_compound_assign_expr<'a>(
    arena: &'a Arena<'a>,
    compound: &CompoundAssignExpr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let op_str = match compound.op {
        CompoundOp::Add => "+=",
        CompoundOp::Sub => "-=",
        CompoundOp::Mul => "*=",
        CompoundOp::Div => "/=",
        CompoundOp::Mod => "%=",
    };

    let target = print_assign_target(arena, &compound.target, interner);
    let value = print_expr(arena, &compound.value, interner);

    target
        .append(arena.text(" "))
        .append(arena.text(op_str))
        .append(arena.text(" "))
        .append(value)
}

/// Print a range expression.
fn print_range_expr<'a>(
    arena: &'a Arena<'a>,
    range: &RangeExpr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let op = if range.inclusive { "..=" } else { ".." };

    print_expr(arena, &range.start, interner)
        .append(arena.text(op))
        .append(print_expr(arena, &range.end, interner))
}

/// Print an array literal.
fn print_array_literal<'a>(
    arena: &'a Arena<'a>,
    elements: &[Expr],
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    if elements.is_empty() {
        return arena.text("[]");
    }

    let elem_docs: Vec<_> = elements
        .iter()
        .map(|e| print_expr(arena, e, interner))
        .collect();

    // Multi-line format with trailing comma
    let multi_line = arena
        .hardline()
        .append(arena.intersperse(
            elem_docs.iter().cloned(),
            arena.text(",").append(arena.hardline()),
        ))
        .append(arena.text(","))
        .nest(INDENT)
        .append(arena.hardline());

    // Single line format with spaces inside brackets: [ 1, 2, 3 ]
    let single_line = arena
        .text(" ")
        .append(arena.intersperse(elem_docs, arena.text(", ")))
        .append(arena.text(" "));

    arena
        .text("[")
        .append(multi_line.flat_alt(single_line).group())
        .append(arena.text("]"))
}

/// Print an index expression.
fn print_index_expr<'a>(
    arena: &'a Arena<'a>,
    index: &IndexExpr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    print_expr(arena, &index.object, interner)
        .append(arena.text("["))
        .append(print_expr(arena, &index.index, interner))
        .append(arena.text("]"))
}

/// Print a match expression.
fn print_match_expr<'a>(
    arena: &'a Arena<'a>,
    match_expr: &MatchExpr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let scrutinee = print_expr(arena, &match_expr.scrutinee, interner);

    let arms: Vec<_> = match_expr
        .arms
        .iter()
        .map(|arm| print_match_arm(arena, arm, interner))
        .collect();

    let arms_doc = arena.intersperse(arms, arena.hardline());

    arena
        .text("match ")
        .append(scrutinee)
        .append(arena.text(" {"))
        .append(arena.hardline().append(arms_doc).nest(INDENT))
        .append(arena.hardline())
        .append(arena.text("}"))
}

/// Print a match arm.
fn print_match_arm<'a>(
    arena: &'a Arena<'a>,
    arm: &MatchArm,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let pattern = print_pattern(arena, &arm.pattern, interner);

    let guard = if let Some(guard_expr) = &arm.guard {
        arena
            .text(" if ")
            .append(print_expr(arena, guard_expr, interner))
    } else {
        arena.nil()
    };

    let body = print_expr(arena, &arm.body, interner);

    pattern
        .append(guard)
        .append(arena.text(" => "))
        .append(body)
}

/// Print a pattern.
fn print_pattern<'a>(
    arena: &'a Arena<'a>,
    pattern: &Pattern,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    match pattern {
        Pattern::Wildcard(_) => arena.text("_"),
        Pattern::Literal(expr) => print_expr(arena, expr, interner),
        Pattern::Identifier { name, .. } => arena.text(interner.resolve(*name).to_string()),
        Pattern::Type { type_expr, .. } => print_type_expr(arena, type_expr, interner),
        Pattern::Val { name, .. } => arena
            .text("val ")
            .append(arena.text(interner.resolve(*name).to_string())),
        Pattern::Success { inner, .. } => {
            let base = arena.text("success");
            match inner {
                Some(inner_pattern) => base.append(arena.text(" ")).append(print_pattern(
                    arena,
                    inner_pattern,
                    interner,
                )),
                None => base,
            }
        }
        Pattern::Error { inner, .. } => {
            let base = arena.text("error");
            match inner {
                Some(inner_pattern) => base.append(arena.text(" ")).append(print_pattern(
                    arena,
                    inner_pattern,
                    interner,
                )),
                None => base,
            }
        }
        Pattern::Tuple { elements, .. } => {
            let inner = arena.intersperse(
                elements
                    .iter()
                    .map(|elem| print_pattern(arena, elem, interner)),
                arena.text(", "),
            );
            arena.text("[").append(inner).append(arena.text("]"))
        }
        Pattern::Record { fields, .. } => {
            let inner = arena.intersperse(
                fields.iter().map(|field| {
                    let field_name = interner.resolve(field.field_name);
                    let binding_name = interner.resolve(field.binding);
                    if field.field_name == field.binding {
                        arena.text(field_name.to_string())
                    } else {
                        arena.text(format!("{}: {}", field_name, binding_name))
                    }
                }),
                arena.text(", "),
            );
            arena.text("{ ").append(inner).append(arena.text(" }"))
        }
    }
}

/// Print a null coalescing expression.
fn print_null_coalesce_expr<'a>(
    arena: &'a Arena<'a>,
    nc: &NullCoalesceExpr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    print_expr(arena, &nc.value, interner)
        .append(arena.text(" ?? "))
        .append(print_expr(arena, &nc.default, interner))
}

/// Print an is expression.
fn print_is_expr<'a>(
    arena: &'a Arena<'a>,
    is_expr: &IsExpr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    print_expr(arena, &is_expr.value, interner)
        .append(arena.text(" is "))
        .append(print_type_expr(arena, &is_expr.type_expr, interner))
}

/// Print a lambda expression.
fn print_lambda_expr<'a>(
    arena: &'a Arena<'a>,
    lambda: &LambdaExpr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    // Print parameters
    let params = print_lambda_params(arena, &lambda.params, interner);

    // Print return type if present
    let return_type = if let Some(ty) = &lambda.return_type {
        arena
            .text(" -> ")
            .append(print_type_expr(arena, ty, interner))
    } else {
        arena.nil()
    };

    // Print body
    let body = match &lambda.body {
        LambdaBody::Expr(expr) => arena.text(" ").append(print_expr(arena, expr, interner)),
        LambdaBody::Block(block) => arena.text(" ").append(print_block(arena, block, interner)),
    };

    params
        .append(return_type)
        .append(arena.text(" =>"))
        .append(body)
}

/// Print lambda parameters.
fn print_lambda_params<'a>(
    arena: &'a Arena<'a>,
    params: &[LambdaParam],
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    if params.is_empty() {
        return arena.text("()");
    }

    let param_docs: Vec<_> = params
        .iter()
        .map(|p| print_lambda_param(arena, p, interner))
        .collect();

    arena
        .text("(")
        .append(arena.intersperse(param_docs, arena.text(", ")))
        .append(arena.text(")"))
}

/// Print a single lambda parameter.
fn print_lambda_param<'a>(
    arena: &'a Arena<'a>,
    param: &LambdaParam,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let name = arena.text(interner.resolve(param.name).to_string());
    if let Some(ty) = &param.ty {
        name.append(arena.text(": "))
            .append(print_type_expr(arena, ty, interner))
    } else {
        name
    }
}

/// Print a struct literal.
fn print_struct_literal<'a>(
    arena: &'a Arena<'a>,
    struct_lit: &StructLiteralExpr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let name = interner.resolve(struct_lit.name).to_string();

    if struct_lit.fields.is_empty() {
        return arena.text(name).append(arena.text(" {}"));
    }

    let field_docs: Vec<_> = struct_lit
        .fields
        .iter()
        .map(|f| {
            arena
                .text(interner.resolve(f.name).to_string())
                .append(arena.text(": "))
                .append(print_expr(arena, &f.value, interner))
        })
        .collect();

    // Multi-line format with trailing comma
    let multi_line = arena
        .hardline()
        .append(arena.intersperse(
            field_docs.iter().cloned(),
            arena.text(",").append(arena.hardline()),
        ))
        .append(arena.text(","))
        .nest(INDENT)
        .append(arena.hardline());

    // Single line format with spaces inside braces: { x: 1, y: 2 }
    let single_line = arena
        .text(" ")
        .append(arena.intersperse(field_docs, arena.text(", ")))
        .append(arena.text(" "));

    arena
        .text(name)
        .append(arena.text(" {"))
        .append(multi_line.flat_alt(single_line).group())
        .append(arena.text("}"))
}

/// Print a field access expression.
fn print_field_access<'a>(
    arena: &'a Arena<'a>,
    field: &FieldAccessExpr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    print_expr(arena, &field.object, interner)
        .append(arena.text("."))
        .append(arena.text(interner.resolve(field.field).to_string()))
}

/// Print an optional chain expression.
fn print_optional_chain<'a>(
    arena: &'a Arena<'a>,
    chain: &OptionalChainExpr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    print_expr(arena, &chain.object, interner)
        .append(arena.text("?."))
        .append(arena.text(interner.resolve(chain.field).to_string()))
}

/// Print a method call expression.
fn print_method_call<'a>(
    arena: &'a Arena<'a>,
    method: &MethodCallExpr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let object = print_expr(arena, &method.object, interner);
    let method_name = interner.resolve(method.method).to_string();
    let args = print_call_args(arena, &method.args, interner);

    object
        .append(arena.text("."))
        .append(arena.text(method_name))
        .append(args)
}

/// Print a type expression.
fn print_type_expr<'a>(
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
        TypeExpr::Nil => arena.text("nil"),
        TypeExpr::Done => arena.text("Done"),
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

    if tests.tests.is_empty() {
        return label.append(arena.text(" {}"));
    }

    let test_docs: Vec<_> = tests
        .tests
        .iter()
        .map(|test| print_test_case(arena, test, interner))
        .collect();

    // Separate test cases with blank lines
    let tests_body = arena.intersperse(test_docs, arena.hardline().append(arena.hardline()));

    label
        .append(arena.text(" {"))
        .append(arena.hardline().append(tests_body).nest(INDENT))
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
        .append(arena.text(" "))
        .append(print_block(arena, &test.body, interner))
}

/// Print a class declaration.
fn print_class_decl<'a>(
    arena: &'a Arena<'a>,
    class: &ClassDecl,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let name = interner.resolve(class.name).to_string();

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
        &name,
        implements,
        &class.fields,
        class.external.as_ref(),
        &class.methods,
        interner,
        "class",
    )
}

/// Print a record declaration.
fn print_record_decl<'a>(
    arena: &'a Arena<'a>,
    record: &RecordDecl,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let name = interner.resolve(record.name).to_string();

    let implements = if record.implements.is_empty() {
        arena.nil()
    } else {
        let impl_types: Vec<_> = record
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
        &name,
        implements,
        &record.fields,
        record.external.as_ref(),
        &record.methods,
        interner,
        "record",
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

/// Print the body of a class-like declaration (class or record).
#[allow(clippy::too_many_arguments)]
fn print_class_like_body<'a>(
    arena: &'a Arena<'a>,
    name: &str,
    implements: DocBuilder<'a, Arena<'a>>,
    fields: &[FieldDef],
    external: Option<&ExternalBlock>,
    methods: &[FuncDecl],
    interner: &Interner,
    keyword: &str,
) -> DocBuilder<'a, Arena<'a>> {
    if fields.is_empty() && external.is_none() && methods.is_empty() {
        return arena
            .text(keyword.to_string())
            .append(arena.text(" "))
            .append(arena.text(name.to_string()))
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

    // Join sections with blank lines
    let body = arena.intersperse(sections, arena.hardline().append(arena.hardline()));

    arena
        .text(keyword.to_string())
        .append(arena.text(" "))
        .append(arena.text(name.to_string()))
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

    if iface.fields.is_empty() && iface.external_blocks.is_empty() && iface.methods.is_empty() {
        return arena
            .text("interface ")
            .append(arena.text(name))
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

    // Join sections with blank lines
    let body = arena.intersperse(sections, arena.hardline().append(arena.hardline()));

    arena
        .text("interface ")
        .append(arena.text(name))
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
        signature
            .append(arena.text(" "))
            .append(print_block(arena, body, interner))
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

    if impl_block.external.is_none() && impl_block.methods.is_empty() {
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

    // Join sections with blank lines
    let body = arena.intersperse(sections, arena.hardline().append(arena.hardline()));

    header
        .append(arena.text(" {"))
        .append(arena.hardline().append(body).nest(INDENT))
        .append(arena.hardline())
        .append(arena.text("}"))
}
