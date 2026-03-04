//! Lightweight import discovery from a parsed AST.
//!
//! Extracts import paths from top-level declarations without requiring sema.
//! Used by the parallel parse pipeline to determine module dependencies
//! before full analysis.

use crate::ast::{Decl, ExprKind, LetInit, Program};

/// Extract all import paths from a parsed program's top-level declarations.
///
/// Walks `program.declarations` looking for:
/// - `let x = import "path"` (`Decl::Let` with `ExprKind::Import`)
/// - `let { a, b } = import "path"` (`Decl::LetTuple` with `ExprKind::Import`)
///
/// Returns the collected path strings in declaration order.
pub fn extract_imports(program: &Program) -> Vec<String> {
    let mut paths = Vec::new();
    for decl in &program.declarations {
        match decl {
            Decl::Let(let_stmt) => {
                if let LetInit::Expr(init_expr) = &let_stmt.init
                    && let ExprKind::Import(path) = &init_expr.kind
                {
                    paths.push(path.clone());
                }
            }
            Decl::LetTuple(let_tuple) => {
                if let ExprKind::Import(path) = &let_tuple.init.kind {
                    paths.push(path.clone());
                }
            }
            _ => {}
        }
    }
    paths
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Parser;

    fn parse_source(source: &str) -> Program {
        let mut parser = Parser::new(source, Default::default());
        parser.parse_program().expect("parse should succeed")
    }

    #[test]
    fn extracts_two_imports() {
        let source = r#"
let math = import "std:math"
let { readFile } = import "./utils"
"#;
        let program = parse_source(source);
        let imports = extract_imports(&program);
        assert_eq!(imports, vec!["std:math", "./utils"]);
    }

    #[test]
    fn no_imports_returns_empty() {
        let source = r#"
let x = 42
func greet() -> string => "hello"
"#;
        let program = parse_source(source);
        let imports = extract_imports(&program);
        assert!(imports.is_empty());
    }

    #[test]
    fn preserves_declaration_order() {
        let source = r#"
let a = import "alpha"
let b = import "beta"
let c = import "gamma"
"#;
        let program = parse_source(source);
        let imports = extract_imports(&program);
        assert_eq!(imports, vec!["alpha", "beta", "gamma"]);
    }

    #[test]
    fn ignores_non_import_lets() {
        let source = r#"
let x = 10
let io = import "std:io"
let y = 20
"#;
        let program = parse_source(source);
        let imports = extract_imports(&program);
        assert_eq!(imports, vec!["std:io"]);
    }
}
