//! AST to pretty::Doc conversion for the Vole formatter.

use pretty::{Arena, DocAllocator, DocBuilder};

use crate::frontend::ast::*;
use crate::frontend::Interner;

/// Pretty-print a program to a Doc.
pub fn print_program<'a>(
    arena: &'a Arena<'a>,
    program: &Program,
    interner: &Interner,
) -> DocBuilder<'a, Arena<'a>> {
    // TODO: implement
    let _ = (program, interner);
    arena.nil()
}
