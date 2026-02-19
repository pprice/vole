// vole-sema/src/transforms/generator.rs
//! Generator detection utilities.
//!
//! Provides `contains_yield` for checking whether a function body contains
//! yield expressions (used by codegen to detect generator functions).
//!
//! The AST-level generator-to-state-machine transform has been removed.
//! Generators are now compiled directly to coroutine-backed iterators
//! in vole-codegen.

use super::expr_walker::{any_child_expr, any_child_expr_in_block};
use vole_frontend::ast::*;

/// Check if a function body contains any yield expressions.
pub fn contains_yield(body: &FuncBody) -> bool {
    match body {
        FuncBody::Block(block) => any_child_expr_in_block(block, &mut expr_contains_yield),
        FuncBody::Expr(expr) => expr_contains_yield(expr),
    }
}

fn expr_contains_yield(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Yield(_) => true,
        _ => any_child_expr(expr, &mut expr_contains_yield),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use vole_frontend::Parser;

    #[test]
    fn test_contains_yield() {
        let source = r#"
            func gen() -> Iterator<i64> {
                yield 1
                yield 2
            }
        "#;
        let mut parser = Parser::new(source, ModuleId::new(0));
        let program = parser.parse_program().expect("parse failed");

        if let Decl::Function(func) = &program.declarations[0] {
            assert!(contains_yield(&func.body));
        }
    }

    #[test]
    fn test_no_yield() {
        let source = r#"
            func regular() -> i64 {
                return 42
            }
        "#;
        let mut parser = Parser::new(source, ModuleId::new(0));
        let program = parser.parse_program().expect("parse failed");

        if let Decl::Function(func) = &program.declarations[0] {
            assert!(!contains_yield(&func.body));
        }
    }
}
