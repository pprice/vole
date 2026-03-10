// calls/lambda_search.rs
//
// Lambda search utilities: find lambda expressions by NodeId in the AST.

use rustc_hash::FxHashMap;
use vole_frontend::{Decl, Expr, ExprKind, LambdaExpr, Program, Stmt};
use vole_identity::NodeId;

/// Collect all lambda expressions in a program, keyed by their NodeId.
///
/// Single O(n) walk — collects all lambdas so they can be looked up by NodeId.
pub fn collect_lambdas_in_program(program: &Program) -> FxHashMap<NodeId, &LambdaExpr> {
    let mut map = FxHashMap::default();
    for decl in &program.declarations {
        collect_lambdas_in_decl(decl, &mut map);
    }
    map
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
