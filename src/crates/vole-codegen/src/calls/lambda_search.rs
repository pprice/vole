// calls/lambda_search.rs
//
// Lambda search utilities: find lambda expressions by NodeId in the AST.

use vole_frontend::{Decl, Expr, ExprKind, LambdaExpr, NodeId, Program, Stmt};

/// Find a lambda expression by NodeId in an `AnalyzedProgram`.
///
/// Searches the main program's AST. Returns a reference with the same
/// lifetime as the `AnalyzedProgram`, so the caller may hold it while
/// taking a separate `&mut Cg` borrow.
pub(crate) fn find_lambda_in_analyzed(
    analyzed: &crate::AnalyzedProgram,
    node_id: NodeId,
) -> Option<&LambdaExpr> {
    find_lambda_in_program(&analyzed.program, node_id)
}

/// Find a lambda expression by NodeId in a program.
fn find_lambda_in_program(program: &Program, node_id: NodeId) -> Option<&LambdaExpr> {
    // Search expressions in declarations and statements
    for decl in &program.declarations {
        if let Some(lambda) = find_lambda_in_decl(decl, node_id) {
            return Some(lambda);
        }
    }
    None
}

/// Find a lambda in a declaration.
fn find_lambda_in_decl(decl: &Decl, node_id: NodeId) -> Option<&LambdaExpr> {
    match decl {
        Decl::Function(func) => {
            // Search function body for lambdas
            match &func.body {
                vole_frontend::FuncBody::Expr(expr) => find_lambda_in_expr(expr, node_id),
                vole_frontend::FuncBody::Block(block) => {
                    find_lambda_in_stmts(&block.stmts, node_id)
                }
            }
        }
        Decl::Let(let_stmt) => {
            if let vole_frontend::LetInit::Expr(expr) = &let_stmt.init {
                find_lambda_in_expr(expr, node_id)
            } else {
                None
            }
        }
        Decl::Tests(tests) => {
            // Search scoped declarations first
            for inner_decl in &tests.decls {
                if let Some(lambda) = find_lambda_in_decl(inner_decl, node_id) {
                    return Some(lambda);
                }
            }
            // Then search test cases
            for test in &tests.tests {
                if let Some(lambda) = find_lambda_in_func_body(&test.body, node_id) {
                    return Some(lambda);
                }
            }
            None
        }
        _ => None,
    }
}

/// Find a lambda in a function body.
fn find_lambda_in_func_body(
    body: &vole_frontend::FuncBody,
    node_id: NodeId,
) -> Option<&LambdaExpr> {
    match body {
        vole_frontend::FuncBody::Expr(expr) => find_lambda_in_expr(expr, node_id),
        vole_frontend::FuncBody::Block(block) => find_lambda_in_stmts(&block.stmts, node_id),
    }
}

/// Find a lambda in a list of statements.
fn find_lambda_in_stmts(stmts: &[Stmt], node_id: NodeId) -> Option<&LambdaExpr> {
    for stmt in stmts {
        if let Some(lambda) = find_lambda_in_stmt(stmt, node_id) {
            return Some(lambda);
        }
    }
    None
}

/// Find a lambda in a statement.
fn find_lambda_in_stmt(stmt: &Stmt, node_id: NodeId) -> Option<&LambdaExpr> {
    match stmt {
        Stmt::Let(let_stmt) => {
            if let vole_frontend::LetInit::Expr(expr) = &let_stmt.init {
                find_lambda_in_expr(expr, node_id)
            } else {
                None
            }
        }
        Stmt::LetTuple(let_tuple) => find_lambda_in_expr(&let_tuple.init, node_id),
        Stmt::Expr(expr_stmt) => find_lambda_in_expr(&expr_stmt.expr, node_id),
        Stmt::Return(ret_stmt) => ret_stmt
            .value
            .as_ref()
            .and_then(|e| find_lambda_in_expr(e, node_id)),
        Stmt::If(if_stmt) => {
            if let Some(lambda) = find_lambda_in_expr(&if_stmt.condition, node_id) {
                return Some(lambda);
            }
            if let Some(lambda) = find_lambda_in_stmts(&if_stmt.then_branch.stmts, node_id) {
                return Some(lambda);
            }
            if let Some(else_branch) = &if_stmt.else_branch
                && let Some(lambda) = find_lambda_in_stmts(&else_branch.stmts, node_id)
            {
                return Some(lambda);
            }
            None
        }
        Stmt::While(while_stmt) => {
            if let Some(lambda) = find_lambda_in_expr(&while_stmt.condition, node_id) {
                return Some(lambda);
            }
            find_lambda_in_stmts(&while_stmt.body.stmts, node_id)
        }
        Stmt::For(for_stmt) => {
            if let Some(lambda) = find_lambda_in_expr(&for_stmt.iterable, node_id) {
                return Some(lambda);
            }
            find_lambda_in_stmts(&for_stmt.body.stmts, node_id)
        }
        Stmt::Raise(raise_stmt) => {
            // Raise has fields that could contain lambdas
            for field in &raise_stmt.fields {
                if let Some(lambda) = find_lambda_in_expr(&field.value, node_id) {
                    return Some(lambda);
                }
            }
            None
        }
        Stmt::Break(_) | Stmt::Continue(_) => None,
    }
}

/// Find a lambda in an expression.
fn find_lambda_in_expr(expr: &Expr, node_id: NodeId) -> Option<&LambdaExpr> {
    if expr.id == node_id
        && let ExprKind::Lambda(lambda) = &expr.kind
    {
        return Some(lambda);
    }

    match &expr.kind {
        ExprKind::Lambda(lambda) => {
            // Check body for nested lambdas
            match &lambda.body {
                vole_frontend::FuncBody::Expr(body) => find_lambda_in_expr(body, node_id),
                vole_frontend::FuncBody::Block(block) => {
                    find_lambda_in_stmts(&block.stmts, node_id)
                }
            }
        }
        ExprKind::Call(call) => {
            if let Some(lambda) = find_lambda_in_expr(&call.callee, node_id) {
                return Some(lambda);
            }
            for arg in &call.args {
                if let Some(lambda) = find_lambda_in_expr(arg, node_id) {
                    return Some(lambda);
                }
            }
            None
        }
        ExprKind::Binary(binary) => find_lambda_in_expr(&binary.left, node_id)
            .or_else(|| find_lambda_in_expr(&binary.right, node_id)),
        ExprKind::Unary(unary) => find_lambda_in_expr(&unary.operand, node_id),
        ExprKind::Block(block) => find_lambda_in_stmts(&block.stmts, node_id),
        ExprKind::If(if_expr) => {
            if let Some(lambda) = find_lambda_in_expr(&if_expr.condition, node_id) {
                return Some(lambda);
            }
            if let Some(lambda) = find_lambda_in_expr(&if_expr.then_branch, node_id) {
                return Some(lambda);
            }
            if let Some(else_branch) = &if_expr.else_branch {
                find_lambda_in_expr(else_branch, node_id)
            } else {
                None
            }
        }
        ExprKind::ArrayLiteral(elems) => {
            for elem in elems {
                if let Some(lambda) = find_lambda_in_expr(elem, node_id) {
                    return Some(lambda);
                }
            }
            None
        }
        ExprKind::RepeatLiteral { element, .. } => find_lambda_in_expr(element, node_id),
        ExprKind::Index(idx) => find_lambda_in_expr(&idx.object, node_id)
            .or_else(|| find_lambda_in_expr(&idx.index, node_id)),
        ExprKind::FieldAccess(fa) => find_lambda_in_expr(&fa.object, node_id),
        ExprKind::MethodCall(mc) => {
            if let Some(lambda) = find_lambda_in_expr(&mc.object, node_id) {
                return Some(lambda);
            }
            for arg in &mc.args {
                if let Some(lambda) = find_lambda_in_expr(arg, node_id) {
                    return Some(lambda);
                }
            }
            None
        }
        ExprKind::Assign(assign) => find_lambda_in_expr(&assign.value, node_id),
        ExprKind::CompoundAssign(compound) => find_lambda_in_expr(&compound.value, node_id),
        ExprKind::Grouping(inner) => find_lambda_in_expr(inner, node_id),
        ExprKind::Range(range) => find_lambda_in_expr(&range.start, node_id)
            .or_else(|| find_lambda_in_expr(&range.end, node_id)),
        ExprKind::NullCoalesce(nc) => find_lambda_in_expr(&nc.value, node_id)
            .or_else(|| find_lambda_in_expr(&nc.default, node_id)),
        ExprKind::Is(is_expr) => find_lambda_in_expr(&is_expr.value, node_id),
        ExprKind::StructLiteral(lit) => {
            for field in &lit.fields {
                if let Some(lambda) = find_lambda_in_expr(&field.value, node_id) {
                    return Some(lambda);
                }
            }
            None
        }
        ExprKind::OptionalChain(oc) => find_lambda_in_expr(&oc.object, node_id),
        ExprKind::Try(inner) => find_lambda_in_expr(inner, node_id),
        ExprKind::Yield(y) => find_lambda_in_expr(&y.value, node_id),
        ExprKind::Match(m) => {
            if let Some(lambda) = find_lambda_in_expr(&m.scrutinee, node_id) {
                return Some(lambda);
            }
            for arm in &m.arms {
                if let Some(lambda) = find_lambda_in_expr(&arm.body, node_id) {
                    return Some(lambda);
                }
            }
            None
        }
        ExprKind::When(w) => {
            for arm in &w.arms {
                if let Some(ref cond) = arm.condition
                    && let Some(lambda) = find_lambda_in_expr(cond, node_id)
                {
                    return Some(lambda);
                }
                if let Some(lambda) = find_lambda_in_expr(&arm.body, node_id) {
                    return Some(lambda);
                }
            }
            None
        }
        // Leaf nodes with no sub-expressions
        ExprKind::IntLiteral(..)
        | ExprKind::FloatLiteral(..)
        | ExprKind::BoolLiteral(_)
        | ExprKind::StringLiteral(_)
        | ExprKind::InterpolatedString(_)
        | ExprKind::Identifier(_)
        | ExprKind::Unreachable
        | ExprKind::TypeLiteral(_)
        | ExprKind::Import(_) => None,
    }
}
