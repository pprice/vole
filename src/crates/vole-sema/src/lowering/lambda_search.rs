// calls/lambda_search.rs
//
// Lambda search utilities: find lambda expressions by NodeId in the AST.

use rustc_hash::FxHashMap;
use vole_frontend::{Decl, Expr, ExprKind, LambdaExpr, Program, Stmt};
use vole_identity::NodeId;

/// Collect all lambda expressions in a program, keyed by their NodeId.
///
/// Single O(n) walk — use this instead of repeated `find_lambda_in_program`
/// calls when multiple lambdas need to be resolved from the same program.
pub fn collect_lambdas_in_program(program: &Program) -> FxHashMap<NodeId, &LambdaExpr> {
    let mut map = FxHashMap::default();
    for decl in &program.declarations {
        collect_lambdas_in_decl(decl, &mut map);
    }
    map
}

/// Find a lambda expression by NodeId in a program (single-lookup fallback).
#[allow(dead_code)]
pub fn find_lambda_in_program(program: &Program, node_id: NodeId) -> Option<&LambdaExpr> {
    // Search expressions in declarations and statements
    for decl in &program.declarations {
        if let Some(lambda) = find_lambda_in_decl(decl, node_id) {
            return Some(lambda);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Collect (batch) variants — walk everything, insert all lambdas into map
// ---------------------------------------------------------------------------

fn collect_lambdas_in_decl<'a>(decl: &'a Decl, map: &mut FxHashMap<NodeId, &'a LambdaExpr>) {
    match decl {
        Decl::Function(func) => collect_lambdas_in_func_body(&func.body, map),
        Decl::Let(let_stmt) => {
            if let vole_frontend::LetInit::Expr(expr) = &let_stmt.init {
                collect_lambdas_in_expr(expr, map);
            }
        }
        Decl::Tests(tests) => {
            for inner_decl in &tests.decls {
                collect_lambdas_in_decl(inner_decl, map);
            }
            for test in &tests.tests {
                collect_lambdas_in_func_body(&test.body, map);
            }
        }
        Decl::Class(class) => {
            for method in &class.methods {
                collect_lambdas_in_func_body(&method.body, map);
            }
            if let Some(statics) = &class.statics {
                collect_lambdas_in_statics(statics, map);
            }
        }
        Decl::Struct(struct_decl) => {
            for method in &struct_decl.methods {
                collect_lambdas_in_func_body(&method.body, map);
            }
            if let Some(statics) = &struct_decl.statics {
                collect_lambdas_in_statics(statics, map);
            }
        }
        Decl::Interface(iface) => {
            for method in &iface.methods {
                if let Some(body) = &method.body {
                    collect_lambdas_in_func_body(body, map);
                }
            }
            if let Some(statics) = &iface.statics {
                collect_lambdas_in_statics(statics, map);
            }
        }
        Decl::Implement(impl_block) => {
            for method in &impl_block.methods {
                collect_lambdas_in_func_body(&method.body, map);
            }
            if let Some(statics) = &impl_block.statics {
                collect_lambdas_in_statics(statics, map);
            }
        }
        _ => {}
    }
}

fn collect_lambdas_in_statics<'a>(
    statics: &'a vole_frontend::ast::StaticsBlock,
    map: &mut FxHashMap<NodeId, &'a LambdaExpr>,
) {
    for method in &statics.methods {
        if let Some(body) = &method.body {
            collect_lambdas_in_func_body(body, map);
        }
    }
}

fn collect_lambdas_in_func_body<'a>(
    body: &'a vole_frontend::FuncBody,
    map: &mut FxHashMap<NodeId, &'a LambdaExpr>,
) {
    match body {
        vole_frontend::FuncBody::Expr(expr) => collect_lambdas_in_expr(expr, map),
        vole_frontend::FuncBody::Block(block) => collect_lambdas_in_stmts(&block.stmts, map),
    }
}

fn collect_lambdas_in_stmts<'a>(stmts: &'a [Stmt], map: &mut FxHashMap<NodeId, &'a LambdaExpr>) {
    for stmt in stmts {
        collect_lambdas_in_stmt(stmt, map);
    }
}

fn collect_lambdas_in_stmt<'a>(stmt: &'a Stmt, map: &mut FxHashMap<NodeId, &'a LambdaExpr>) {
    match stmt {
        Stmt::Let(let_stmt) => {
            if let vole_frontend::LetInit::Expr(expr) = &let_stmt.init {
                collect_lambdas_in_expr(expr, map);
            }
        }
        Stmt::LetTuple(let_tuple) => collect_lambdas_in_expr(&let_tuple.init, map),
        Stmt::Expr(expr_stmt) => collect_lambdas_in_expr(&expr_stmt.expr, map),
        Stmt::Return(ret_stmt) => {
            if let Some(e) = ret_stmt.value.as_ref() {
                collect_lambdas_in_expr(e, map);
            }
        }
        Stmt::If(if_stmt) => {
            collect_lambdas_in_expr(&if_stmt.condition, map);
            collect_lambdas_in_stmts(&if_stmt.then_branch.stmts, map);
            if let Some(else_branch) = &if_stmt.else_branch {
                collect_lambdas_in_stmts(&else_branch.stmts, map);
            }
        }
        Stmt::While(while_stmt) => {
            collect_lambdas_in_expr(&while_stmt.condition, map);
            collect_lambdas_in_stmts(&while_stmt.body.stmts, map);
        }
        Stmt::For(for_stmt) => {
            collect_lambdas_in_expr(&for_stmt.iterable, map);
            collect_lambdas_in_stmts(&for_stmt.body.stmts, map);
        }
        Stmt::Raise(raise_stmt) => {
            for field in &raise_stmt.fields {
                collect_lambdas_in_expr(&field.value, map);
            }
        }
        Stmt::Break(_) | Stmt::Continue(_) => {}
    }
}

fn collect_lambdas_in_expr<'a>(expr: &'a Expr, map: &mut FxHashMap<NodeId, &'a LambdaExpr>) {
    if let ExprKind::Lambda(lambda) = &expr.kind {
        map.insert(expr.id, lambda);
        // Also walk the lambda body for nested lambdas
        match &lambda.body {
            vole_frontend::FuncBody::Expr(body) => collect_lambdas_in_expr(body, map),
            vole_frontend::FuncBody::Block(block) => collect_lambdas_in_stmts(&block.stmts, map),
        }
        return;
    }

    match &expr.kind {
        ExprKind::Call(call) => {
            collect_lambdas_in_expr(&call.callee, map);
            for arg in &call.args {
                collect_lambdas_in_expr(arg.expr(), map);
            }
        }
        ExprKind::Binary(binary) => {
            collect_lambdas_in_expr(&binary.left, map);
            collect_lambdas_in_expr(&binary.right, map);
        }
        ExprKind::Unary(unary) => collect_lambdas_in_expr(&unary.operand, map),
        ExprKind::Block(block) => collect_lambdas_in_stmts(&block.stmts, map),
        ExprKind::If(if_expr) => {
            collect_lambdas_in_expr(&if_expr.condition, map);
            collect_lambdas_in_expr(&if_expr.then_branch, map);
            if let Some(else_branch) = &if_expr.else_branch {
                collect_lambdas_in_expr(else_branch, map);
            }
        }
        ExprKind::ArrayLiteral(elems) => {
            for elem in elems {
                collect_lambdas_in_expr(elem, map);
            }
        }
        ExprKind::RepeatLiteral { element, .. } => collect_lambdas_in_expr(element, map),
        ExprKind::Index(idx) => {
            collect_lambdas_in_expr(&idx.object, map);
            collect_lambdas_in_expr(&idx.index, map);
        }
        ExprKind::FieldAccess(fa) => collect_lambdas_in_expr(&fa.object, map),
        ExprKind::MethodCall(mc) => {
            collect_lambdas_in_expr(&mc.object, map);
            for arg in &mc.args {
                collect_lambdas_in_expr(arg.expr(), map);
            }
        }
        ExprKind::Assign(assign) => collect_lambdas_in_expr(&assign.value, map),
        ExprKind::CompoundAssign(compound) => collect_lambdas_in_expr(&compound.value, map),
        ExprKind::Grouping(inner) => collect_lambdas_in_expr(inner, map),
        ExprKind::Range(range) => {
            collect_lambdas_in_expr(&range.start, map);
            collect_lambdas_in_expr(&range.end, map);
        }
        ExprKind::NullCoalesce(nc) => {
            collect_lambdas_in_expr(&nc.value, map);
            collect_lambdas_in_expr(&nc.default, map);
        }
        ExprKind::Is(is_expr) => collect_lambdas_in_expr(&is_expr.value, map),
        ExprKind::AsCast(as_cast) => collect_lambdas_in_expr(&as_cast.value, map),
        ExprKind::StructLiteral(lit) => {
            for field in &lit.fields {
                collect_lambdas_in_expr(&field.value, map);
            }
        }
        ExprKind::OptionalChain(oc) => collect_lambdas_in_expr(&oc.object, map),
        ExprKind::MetaAccess(ma) => collect_lambdas_in_expr(&ma.object, map),
        ExprKind::OptionalMethodCall(omc) => {
            collect_lambdas_in_expr(&omc.object, map);
            for arg in &omc.args {
                collect_lambdas_in_expr(arg.expr(), map);
            }
        }
        ExprKind::Try(inner) => collect_lambdas_in_expr(inner, map),
        ExprKind::Yield(y) => collect_lambdas_in_expr(&y.value, map),
        ExprKind::Match(m) => {
            collect_lambdas_in_expr(&m.scrutinee, map);
            for arm in &m.arms {
                collect_lambdas_in_expr(&arm.body, map);
            }
        }
        ExprKind::When(w) => {
            for arm in &w.arms {
                if let Some(ref cond) = arm.condition {
                    collect_lambdas_in_expr(cond, map);
                }
                collect_lambdas_in_expr(&arm.body, map);
            }
        }
        // Leaf nodes with no sub-expressions
        ExprKind::Lambda(_) => unreachable!("handled above"),
        ExprKind::IntLiteral(..)
        | ExprKind::FloatLiteral(..)
        | ExprKind::BoolLiteral(_)
        | ExprKind::StringLiteral(_)
        | ExprKind::InterpolatedString(_)
        | ExprKind::Identifier(_)
        | ExprKind::Unreachable
        | ExprKind::TypeLiteral(_)
        | ExprKind::Import(_) => {}
    }
}

// ---------------------------------------------------------------------------
// Single-lookup variants (kept for any remaining single-search call sites)
// ---------------------------------------------------------------------------

/// Find a lambda in a declaration.
fn find_lambda_in_decl(decl: &Decl, node_id: NodeId) -> Option<&LambdaExpr> {
    match decl {
        Decl::Function(func) => find_lambda_in_func_body(&func.body, node_id),
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
        Decl::Class(class) => {
            for method in &class.methods {
                if let Some(lambda) = find_lambda_in_func_body(&method.body, node_id) {
                    return Some(lambda);
                }
            }
            if let Some(statics) = &class.statics
                && let Some(lambda) = find_lambda_in_statics(statics, node_id)
            {
                return Some(lambda);
            }
            None
        }
        Decl::Struct(struct_decl) => {
            for method in &struct_decl.methods {
                if let Some(lambda) = find_lambda_in_func_body(&method.body, node_id) {
                    return Some(lambda);
                }
            }
            if let Some(statics) = &struct_decl.statics
                && let Some(lambda) = find_lambda_in_statics(statics, node_id)
            {
                return Some(lambda);
            }
            None
        }
        Decl::Interface(iface) => {
            for method in &iface.methods {
                if let Some(body) = &method.body
                    && let Some(lambda) = find_lambda_in_func_body(body, node_id)
                {
                    return Some(lambda);
                }
            }
            if let Some(statics) = &iface.statics
                && let Some(lambda) = find_lambda_in_statics(statics, node_id)
            {
                return Some(lambda);
            }
            None
        }
        Decl::Implement(impl_block) => {
            for method in &impl_block.methods {
                if let Some(lambda) = find_lambda_in_func_body(&method.body, node_id) {
                    return Some(lambda);
                }
            }
            if let Some(statics) = &impl_block.statics
                && let Some(lambda) = find_lambda_in_statics(statics, node_id)
            {
                return Some(lambda);
            }
            None
        }
        // LetTuple, Error, Sentinel, External have no lambda bodies
        _ => None,
    }
}

/// Find a lambda in a StaticsBlock (static methods with optional bodies).
fn find_lambda_in_statics(
    statics: &vole_frontend::ast::StaticsBlock,
    node_id: NodeId,
) -> Option<&LambdaExpr> {
    for method in &statics.methods {
        if let Some(body) = &method.body
            && let Some(lambda) = find_lambda_in_func_body(body, node_id)
        {
            return Some(lambda);
        }
    }
    None
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
                if let Some(lambda) = find_lambda_in_expr(arg.expr(), node_id) {
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
                if let Some(lambda) = find_lambda_in_expr(arg.expr(), node_id) {
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
        ExprKind::AsCast(as_cast) => find_lambda_in_expr(&as_cast.value, node_id),
        ExprKind::StructLiteral(lit) => {
            for field in &lit.fields {
                if let Some(lambda) = find_lambda_in_expr(&field.value, node_id) {
                    return Some(lambda);
                }
            }
            None
        }
        ExprKind::OptionalChain(oc) => find_lambda_in_expr(&oc.object, node_id),
        ExprKind::MetaAccess(ma) => find_lambda_in_expr(&ma.object, node_id),
        ExprKind::OptionalMethodCall(omc) => {
            if let Some(lambda) = find_lambda_in_expr(&omc.object, node_id) {
                return Some(lambda);
            }
            for arg in &omc.args {
                if let Some(lambda) = find_lambda_in_expr(arg.expr(), node_id) {
                    return Some(lambda);
                }
            }
            None
        }
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
