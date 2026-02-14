// vole-sema/src/transforms/rewrite_refs.rs
//! Rewriting captured variable references in generator state machines.
//!
//! Transforms bare identifier references to captured parameters and hoisted
//! locals into `self.<name>` field accesses so they resolve correctly inside
//! the generated `next()` method.

use super::expr_walker::map_expr_children;
use super::generator::GeneratorTransformer;
use vole_frontend::Span;
use vole_frontend::ast::*;

impl GeneratorTransformer<'_> {
    /// Rewrite identifier references to captured names (parameters and hoisted
    /// locals) into `self.<name>` field accesses so they resolve correctly
    /// inside the generated `next()` method.
    pub(super) fn rewrite_captured_refs(
        &mut self,
        expr: &Expr,
        captured: &[Symbol],
        self_sym: Symbol,
    ) -> Expr {
        let kind = match &expr.kind {
            // Captured identifier -> self.field_name
            ExprKind::Identifier(sym) if captured.contains(sym) => {
                return self.rewrite_to_self_field(*sym, self_sym, expr.span);
            }
            // Assignment targets can reference captured variables directly
            ExprKind::Assign(assign) => {
                let target = self.rewrite_captured_target(&assign.target, captured, self_sym);
                let value = self.rewrite_captured_refs(&assign.value, captured, self_sym);
                ExprKind::Assign(Box::new(AssignExpr { target, value }))
            }
            ExprKind::CompoundAssign(ca) => {
                let target = self.rewrite_captured_target(&ca.target, captured, self_sym);
                let value = self.rewrite_captured_refs(&ca.value, captured, self_sym);
                ExprKind::CompoundAssign(Box::new(CompoundAssignExpr {
                    target,
                    op: ca.op,
                    value,
                }))
            }
            // All other variants: generic child mapping
            other => map_expr_children(other, &mut |e| {
                self.rewrite_captured_refs(e, captured, self_sym)
            }),
        };
        Expr {
            id: self.next_id(),
            kind,
            span: expr.span,
        }
    }

    /// Rewrite `name` -> `self.name`
    fn rewrite_to_self_field(&mut self, sym: Symbol, self_sym: Symbol, span: Span) -> Expr {
        let self_expr = Expr {
            id: self.next_id(),
            kind: ExprKind::Identifier(self_sym),
            span,
        };
        Expr {
            id: self.next_id(),
            kind: ExprKind::FieldAccess(Box::new(FieldAccessExpr {
                object: self_expr,
                field: sym,
                field_span: span,
            })),
            span,
        }
    }

    /// Rewrite captured variable references in an assignment target.
    fn rewrite_captured_target(
        &mut self,
        target: &AssignTarget,
        captured: &[Symbol],
        self_sym: Symbol,
    ) -> AssignTarget {
        match target {
            AssignTarget::Variable(sym) if captured.contains(sym) => AssignTarget::Field {
                object: Box::new(Expr {
                    id: self.next_id(),
                    kind: ExprKind::Identifier(self_sym),
                    span: Span::default(),
                }),
                field: *sym,
                field_span: Span::default(),
            },
            AssignTarget::Variable(_) | AssignTarget::Discard => target.clone(),
            AssignTarget::Index { object, index } => AssignTarget::Index {
                object: Box::new(self.rewrite_captured_refs(object, captured, self_sym)),
                index: Box::new(self.rewrite_captured_refs(index, captured, self_sym)),
            },
            AssignTarget::Field {
                object,
                field,
                field_span,
            } => AssignTarget::Field {
                object: Box::new(self.rewrite_captured_refs(object, captured, self_sym)),
                field: *field,
                field_span: *field_span,
            },
        }
    }
}
