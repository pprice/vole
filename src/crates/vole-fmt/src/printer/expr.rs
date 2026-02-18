//! Expression printing for the Vole formatter.

use pretty::{Arena, DocAllocator, DocBuilder};

use vole_frontend::Interner;
use vole_frontend::PatternKind;
use vole_frontend::ast::*;

use super::{INDENT, print_block, print_return_type, print_stmt, print_type_expr};

/// Print an expression.
pub(super) fn print_expr<'a>(
    arena: &'a Arena<'a>,
    expr: &Expr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    match &expr.kind {
        ExprKind::IntLiteral(n, suffix) => {
            let mut s = n.to_string();
            if let Some(sfx) = suffix {
                s.push('_');
                s.push_str(sfx.as_str());
            }
            arena.text(s)
        }
        ExprKind::FloatLiteral(f, suffix) => {
            if let Some(sfx) = suffix {
                let base = print_float_literal(arena, *f);
                let sfx_doc = arena.text(format!("_{}", sfx.as_str()));
                base.append(sfx_doc)
            } else {
                print_float_literal(arena, *f)
            }
        }
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
        ExprKind::When(when_expr) => {
            let mut doc = arena.text("when {").append(arena.hardline());
            for arm in &when_expr.arms {
                let arm_doc = if let Some(ref cond) = arm.condition {
                    print_expr(arena, cond, interner)
                } else {
                    arena.text("_")
                };
                doc = doc.append(
                    arm_doc
                        .append(arena.text(" => "))
                        .append(print_expr(arena, &arm.body, interner))
                        .nest(INDENT),
                );
                doc = doc.append(arena.hardline());
            }
            doc.append(arena.text("}"))
        }
        ExprKind::Unreachable => arena.text("unreachable"),
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

/// Escape special characters in a string for output.
fn escape_string_chars(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            '{' => result.push_str("\\{"),
            '}' => result.push_str("\\}"),
            c => result.push(c),
        }
    }
    result
}

/// Print a string literal with proper escaping.
pub(super) fn print_string_literal<'a>(arena: &'a Arena<'a>, s: &str) -> DocBuilder<'a, Arena<'a>> {
    let mut result = String::with_capacity(s.len() + 2);
    result.push('"');
    result.push_str(&escape_string_chars(s));
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
            StringPart::Literal(s) => result.append(arena.text(escape_string_chars(s))),
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
        AssignTarget::Discard => arena.text("_"),
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
pub(super) fn print_pattern<'a>(
    arena: &'a Arena<'a>,
    pattern: &Pattern,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    match &pattern.kind {
        PatternKind::Wildcard => arena.text("_"),
        PatternKind::Literal(expr) => print_expr(arena, expr, interner),
        PatternKind::Identifier { name } => arena.text(interner.resolve(*name).to_string()),
        PatternKind::Type { type_expr } => print_type_expr(arena, type_expr, interner),
        PatternKind::Val { name } => arena
            .text("val ")
            .append(arena.text(interner.resolve(*name).to_string())),
        PatternKind::Success { inner } => {
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
        PatternKind::Error { inner } => {
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
        PatternKind::Tuple { elements } => {
            let inner = arena.intersperse(
                elements
                    .iter()
                    .map(|elem| print_pattern(arena, elem, interner)),
                arena.text(", "),
            );
            arena.text("[").append(inner).append(arena.text("]"))
        }
        PatternKind::Record { type_name, fields } => {
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
            let record = arena.text("{ ").append(inner).append(arena.text(" }"));
            if let Some(type_expr) = type_name {
                print_type_expr(arena, type_expr, interner)
                    .append(arena.text(" "))
                    .append(record)
            } else {
                record
            }
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
    let return_type = print_return_type(arena, &lambda.return_type, interner);

    // Print body
    let body = match &lambda.body {
        FuncBody::Expr(expr) => arena.text(" ").append(print_expr(arena, expr, interner)),
        FuncBody::Block(block) => arena.text(" ").append(print_block(arena, block, interner)),
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
    let base = if let Some(ty) = &param.ty {
        name.append(arena.text(": "))
            .append(print_type_expr(arena, ty, interner))
    } else {
        name
    };
    if let Some(default) = &param.default_value {
        base.append(arena.text(" = "))
            .append(print_expr(arena, default, interner))
    } else {
        base
    }
}

/// Print a struct literal.
fn print_struct_literal<'a>(
    arena: &'a Arena<'a>,
    struct_lit: &StructLiteralExpr,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    let name = struct_lit
        .path
        .iter()
        .map(|s| interner.resolve(*s))
        .collect::<Vec<_>>()
        .join(".");

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
