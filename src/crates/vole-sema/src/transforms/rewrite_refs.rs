// vole-sema/src/transforms/rewrite_refs.rs
//! Rewriting captured variable references in generator state machines.
//!
//! Transforms bare identifier references to captured parameters and hoisted
//! locals into `self.<name>` field accesses so they resolve correctly inside
//! the generated `next()` method.

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
        match &expr.kind {
            ExprKind::Identifier(sym) if captured.contains(sym) => {
                self.rewrite_to_self_field(*sym, self_sym, expr.span)
            }
            ExprKind::Binary(bin) => Expr {
                id: self.next_id(),
                kind: ExprKind::Binary(Box::new(BinaryExpr {
                    left: self.rewrite_captured_refs(&bin.left, captured, self_sym),
                    op: bin.op,
                    right: self.rewrite_captured_refs(&bin.right, captured, self_sym),
                })),
                span: expr.span,
            },
            ExprKind::Unary(un) => Expr {
                id: self.next_id(),
                kind: ExprKind::Unary(Box::new(UnaryExpr {
                    op: un.op,
                    operand: self.rewrite_captured_refs(&un.operand, captured, self_sym),
                })),
                span: expr.span,
            },
            ExprKind::Call(call) => self.rewrite_call(call, captured, self_sym, expr.span),
            ExprKind::Grouping(inner) => {
                let rewritten = self.rewrite_captured_refs(inner, captured, self_sym);
                Expr {
                    id: self.next_id(),
                    kind: ExprKind::Grouping(Box::new(rewritten)),
                    span: expr.span,
                }
            }
            ExprKind::FieldAccess(fa) => {
                self.rewrite_field_access(fa, captured, self_sym, expr.span)
            }
            ExprKind::MethodCall(mc) => self.rewrite_method_call(mc, captured, self_sym, expr.span),
            ExprKind::Index(idx) => self.rewrite_index(idx, captured, self_sym, expr.span),
            ExprKind::ArrayLiteral(elems) => {
                let elems = elems
                    .iter()
                    .map(|e| self.rewrite_captured_refs(e, captured, self_sym))
                    .collect();
                Expr {
                    id: self.next_id(),
                    kind: ExprKind::ArrayLiteral(elems),
                    span: expr.span,
                }
            }
            ExprKind::StructLiteral(sl) => {
                self.rewrite_struct_literal(sl, captured, self_sym, expr.span)
            }
            ExprKind::NullCoalesce(nc) => {
                let value = self.rewrite_captured_refs(&nc.value, captured, self_sym);
                let default = self.rewrite_captured_refs(&nc.default, captured, self_sym);
                Expr {
                    id: self.next_id(),
                    kind: ExprKind::NullCoalesce(Box::new(NullCoalesceExpr { value, default })),
                    span: expr.span,
                }
            }
            ExprKind::InterpolatedString(parts) => {
                self.rewrite_interpolated_string(parts, captured, self_sym, expr.span)
            }
            ExprKind::If(if_expr) => self.rewrite_if_expr(if_expr, captured, self_sym, expr.span),
            ExprKind::Is(is_expr) => {
                let value = self.rewrite_captured_refs(&is_expr.value, captured, self_sym);
                Expr {
                    id: self.next_id(),
                    kind: ExprKind::Is(Box::new(IsExpr {
                        value,
                        type_expr: is_expr.type_expr.clone(),
                        type_span: is_expr.type_span,
                    })),
                    span: expr.span,
                }
            }
            ExprKind::Try(inner) => {
                let rewritten = self.rewrite_captured_refs(inner, captured, self_sym);
                Expr {
                    id: self.next_id(),
                    kind: ExprKind::Try(Box::new(rewritten)),
                    span: expr.span,
                }
            }
            ExprKind::Range(range) => {
                let start = self.rewrite_captured_refs(&range.start, captured, self_sym);
                let end = self.rewrite_captured_refs(&range.end, captured, self_sym);
                Expr {
                    id: self.next_id(),
                    kind: ExprKind::Range(Box::new(RangeExpr {
                        start,
                        end,
                        inclusive: range.inclusive,
                    })),
                    span: expr.span,
                }
            }
            ExprKind::Yield(yield_expr) => {
                let value = self.rewrite_captured_refs(&yield_expr.value, captured, self_sym);
                Expr {
                    id: self.next_id(),
                    kind: ExprKind::Yield(Box::new(YieldExpr {
                        value,
                        span: yield_expr.span,
                    })),
                    span: expr.span,
                }
            }
            ExprKind::Block(block) => self.rewrite_block_expr(block, captured, self_sym, expr.span),
            ExprKind::When(when_expr) => {
                self.rewrite_when_expr(when_expr, captured, self_sym, expr.span)
            }
            ExprKind::Lambda(lambda) => {
                self.rewrite_lambda_expr(lambda, captured, self_sym, expr.span)
            }
            ExprKind::Match(m) => self.rewrite_match_expr(m, captured, self_sym, expr.span),
            ExprKind::RepeatLiteral { element, count } => {
                let element = self.rewrite_captured_refs(element, captured, self_sym);
                Expr {
                    id: self.next_id(),
                    kind: ExprKind::RepeatLiteral {
                        element: Box::new(element),
                        count: *count,
                    },
                    span: expr.span,
                }
            }
            ExprKind::Assign(assign) => self.rewrite_assign(assign, captured, self_sym, expr.span),
            ExprKind::CompoundAssign(ca) => {
                self.rewrite_compound_assign(ca, captured, self_sym, expr.span)
            }
            ExprKind::OptionalChain(oc) => {
                let object = self.rewrite_captured_refs(&oc.object, captured, self_sym);
                Expr {
                    id: self.next_id(),
                    kind: ExprKind::OptionalChain(Box::new(OptionalChainExpr {
                        object,
                        field: oc.field,
                        field_span: oc.field_span,
                    })),
                    span: expr.span,
                }
            }
            // Leaf expressions: no sub-expressions to rewrite
            ExprKind::IntLiteral(..)
            | ExprKind::FloatLiteral(..)
            | ExprKind::BoolLiteral(_)
            | ExprKind::StringLiteral(_)
            | ExprKind::Identifier(_)
            | ExprKind::Unreachable
            | ExprKind::TypeLiteral(_)
            | ExprKind::Import(_) => expr.clone(),
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

    fn rewrite_call(
        &mut self,
        call: &CallExpr,
        captured: &[Symbol],
        self_sym: Symbol,
        span: Span,
    ) -> Expr {
        let callee = self.rewrite_captured_refs(&call.callee, captured, self_sym);
        let args = call
            .args
            .iter()
            .map(|a| self.rewrite_captured_refs(a, captured, self_sym))
            .collect();
        Expr {
            id: self.next_id(),
            kind: ExprKind::Call(Box::new(CallExpr { callee, args })),
            span,
        }
    }

    fn rewrite_field_access(
        &mut self,
        fa: &FieldAccessExpr,
        captured: &[Symbol],
        self_sym: Symbol,
        span: Span,
    ) -> Expr {
        let object = self.rewrite_captured_refs(&fa.object, captured, self_sym);
        Expr {
            id: self.next_id(),
            kind: ExprKind::FieldAccess(Box::new(FieldAccessExpr {
                object,
                field: fa.field,
                field_span: fa.field_span,
            })),
            span,
        }
    }

    fn rewrite_method_call(
        &mut self,
        mc: &MethodCallExpr,
        captured: &[Symbol],
        self_sym: Symbol,
        span: Span,
    ) -> Expr {
        let object = self.rewrite_captured_refs(&mc.object, captured, self_sym);
        let args = mc
            .args
            .iter()
            .map(|a| self.rewrite_captured_refs(a, captured, self_sym))
            .collect();
        Expr {
            id: self.next_id(),
            kind: ExprKind::MethodCall(Box::new(MethodCallExpr {
                object,
                method: mc.method,
                args,
                method_span: mc.method_span,
                type_args: mc.type_args.clone(),
            })),
            span,
        }
    }

    fn rewrite_index(
        &mut self,
        idx: &IndexExpr,
        captured: &[Symbol],
        self_sym: Symbol,
        span: Span,
    ) -> Expr {
        let object = self.rewrite_captured_refs(&idx.object, captured, self_sym);
        let index = self.rewrite_captured_refs(&idx.index, captured, self_sym);
        Expr {
            id: self.next_id(),
            kind: ExprKind::Index(Box::new(IndexExpr { object, index })),
            span,
        }
    }

    fn rewrite_struct_literal(
        &mut self,
        sl: &StructLiteralExpr,
        captured: &[Symbol],
        self_sym: Symbol,
        span: Span,
    ) -> Expr {
        let fields = sl
            .fields
            .iter()
            .map(|f| StructFieldInit {
                name: f.name,
                value: self.rewrite_captured_refs(&f.value, captured, self_sym),
                span: f.span,
                shorthand: f.shorthand,
            })
            .collect();
        Expr {
            id: self.next_id(),
            kind: ExprKind::StructLiteral(Box::new(StructLiteralExpr {
                path: sl.path.clone(),
                type_args: sl.type_args.clone(),
                fields,
            })),
            span,
        }
    }

    fn rewrite_interpolated_string(
        &mut self,
        parts: &[StringPart],
        captured: &[Symbol],
        self_sym: Symbol,
        span: Span,
    ) -> Expr {
        let parts = parts
            .iter()
            .map(|p| match p {
                StringPart::Literal(s) => StringPart::Literal(s.clone()),
                StringPart::Expr(e) => {
                    StringPart::Expr(Box::new(self.rewrite_captured_refs(e, captured, self_sym)))
                }
            })
            .collect();
        Expr {
            id: self.next_id(),
            kind: ExprKind::InterpolatedString(parts),
            span,
        }
    }

    fn rewrite_if_expr(
        &mut self,
        if_expr: &IfExpr,
        captured: &[Symbol],
        self_sym: Symbol,
        span: Span,
    ) -> Expr {
        let condition = self.rewrite_captured_refs(&if_expr.condition, captured, self_sym);
        let then_branch = self.rewrite_captured_refs(&if_expr.then_branch, captured, self_sym);
        let else_branch = if_expr
            .else_branch
            .as_ref()
            .map(|e| self.rewrite_captured_refs(e, captured, self_sym));
        Expr {
            id: self.next_id(),
            kind: ExprKind::If(Box::new(IfExpr {
                condition,
                then_branch,
                else_branch,
                span: if_expr.span,
            })),
            span,
        }
    }

    fn rewrite_block_expr(
        &mut self,
        block: &BlockExpr,
        captured: &[Symbol],
        self_sym: Symbol,
        span: Span,
    ) -> Expr {
        let stmts = block
            .stmts
            .iter()
            .map(|s| self.rewrite_captured_refs_in_stmt(s, captured, self_sym))
            .collect();
        let trailing_expr = block
            .trailing_expr
            .as_ref()
            .map(|e| self.rewrite_captured_refs(e, captured, self_sym));
        Expr {
            id: self.next_id(),
            kind: ExprKind::Block(Box::new(BlockExpr {
                stmts,
                trailing_expr,
                span: block.span,
            })),
            span,
        }
    }

    fn rewrite_when_expr(
        &mut self,
        when_expr: &WhenExpr,
        captured: &[Symbol],
        self_sym: Symbol,
        span: Span,
    ) -> Expr {
        let arms = when_expr
            .arms
            .iter()
            .map(|arm| WhenArm {
                condition: arm
                    .condition
                    .as_ref()
                    .map(|c| self.rewrite_captured_refs(c, captured, self_sym)),
                body: self.rewrite_captured_refs(&arm.body, captured, self_sym),
                span: arm.span,
            })
            .collect();
        Expr {
            id: self.next_id(),
            kind: ExprKind::When(Box::new(WhenExpr {
                arms,
                span: when_expr.span,
            })),
            span,
        }
    }

    fn rewrite_lambda_expr(
        &mut self,
        lambda: &LambdaExpr,
        captured: &[Symbol],
        self_sym: Symbol,
        span: Span,
    ) -> Expr {
        let body = match &lambda.body {
            FuncBody::Expr(e) => {
                FuncBody::Expr(Box::new(self.rewrite_captured_refs(e, captured, self_sym)))
            }
            FuncBody::Block(b) => {
                FuncBody::Block(self.rewrite_captured_refs_in_block(b, captured, self_sym))
            }
        };
        Expr {
            id: self.next_id(),
            kind: ExprKind::Lambda(Box::new(LambdaExpr {
                type_params: lambda.type_params.clone(),
                params: lambda.params.clone(),
                return_type: lambda.return_type.clone(),
                body,
                span: lambda.span,
                captures: lambda.captures.clone(),
                has_side_effects: lambda.has_side_effects.clone(),
            })),
            span,
        }
    }

    fn rewrite_match_expr(
        &mut self,
        m: &MatchExpr,
        captured: &[Symbol],
        self_sym: Symbol,
        span: Span,
    ) -> Expr {
        let scrutinee = self.rewrite_captured_refs(&m.scrutinee, captured, self_sym);
        let arms = m
            .arms
            .iter()
            .map(|arm| MatchArm {
                id: arm.id,
                pattern: arm.pattern.clone(),
                guard: arm
                    .guard
                    .as_ref()
                    .map(|g| self.rewrite_captured_refs(g, captured, self_sym)),
                body: self.rewrite_captured_refs(&arm.body, captured, self_sym),
                span: arm.span,
            })
            .collect();
        Expr {
            id: self.next_id(),
            kind: ExprKind::Match(Box::new(MatchExpr {
                scrutinee,
                arms,
                span: m.span,
            })),
            span,
        }
    }

    fn rewrite_assign(
        &mut self,
        assign: &AssignExpr,
        captured: &[Symbol],
        self_sym: Symbol,
        span: Span,
    ) -> Expr {
        let target = self.rewrite_captured_refs_in_target(&assign.target, captured, self_sym);
        let value = self.rewrite_captured_refs(&assign.value, captured, self_sym);
        Expr {
            id: self.next_id(),
            kind: ExprKind::Assign(Box::new(AssignExpr { target, value })),
            span,
        }
    }

    fn rewrite_compound_assign(
        &mut self,
        ca: &CompoundAssignExpr,
        captured: &[Symbol],
        self_sym: Symbol,
        span: Span,
    ) -> Expr {
        let target = self.rewrite_captured_refs_in_target(&ca.target, captured, self_sym);
        let value = self.rewrite_captured_refs(&ca.value, captured, self_sym);
        Expr {
            id: self.next_id(),
            kind: ExprKind::CompoundAssign(Box::new(CompoundAssignExpr {
                target,
                op: ca.op,
                value,
            })),
            span,
        }
    }

    /// Rewrite captured variable references in an assignment target.
    fn rewrite_captured_refs_in_target(
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

    /// Rewrite captured variable references in a block.
    fn rewrite_captured_refs_in_block(
        &mut self,
        block: &Block,
        captured: &[Symbol],
        self_sym: Symbol,
    ) -> Block {
        let stmts = block
            .stmts
            .iter()
            .map(|s| self.rewrite_captured_refs_in_stmt(s, captured, self_sym))
            .collect();
        Block {
            stmts,
            span: block.span,
        }
    }

    /// Rewrite captured variable references in a statement.
    fn rewrite_captured_refs_in_stmt(
        &mut self,
        stmt: &Stmt,
        captured: &[Symbol],
        self_sym: Symbol,
    ) -> Stmt {
        match stmt {
            Stmt::Expr(expr_stmt) => Stmt::Expr(ExprStmt {
                expr: self.rewrite_captured_refs(&expr_stmt.expr, captured, self_sym),
                span: expr_stmt.span,
            }),
            Stmt::Let(let_stmt) => {
                let init = match &let_stmt.init {
                    LetInit::Expr(e) => {
                        LetInit::Expr(self.rewrite_captured_refs(e, captured, self_sym))
                    }
                    LetInit::TypeAlias(ty) => LetInit::TypeAlias(ty.clone()),
                };
                Stmt::Let(LetStmt {
                    name: let_stmt.name,
                    ty: let_stmt.ty.clone(),
                    mutable: let_stmt.mutable,
                    init,
                    span: let_stmt.span,
                })
            }
            Stmt::LetTuple(lt) => Stmt::LetTuple(LetTupleStmt {
                pattern: lt.pattern.clone(),
                mutable: lt.mutable,
                init: self.rewrite_captured_refs(&lt.init, captured, self_sym),
                span: lt.span,
            }),
            Stmt::While(while_stmt) => Stmt::While(WhileStmt {
                condition: self.rewrite_captured_refs(&while_stmt.condition, captured, self_sym),
                body: self.rewrite_captured_refs_in_block(&while_stmt.body, captured, self_sym),
                span: while_stmt.span,
            }),
            Stmt::For(for_stmt) => Stmt::For(ForStmt {
                var_name: for_stmt.var_name,
                iterable: self.rewrite_captured_refs(&for_stmt.iterable, captured, self_sym),
                body: self.rewrite_captured_refs_in_block(&for_stmt.body, captured, self_sym),
                span: for_stmt.span,
            }),
            Stmt::If(if_stmt) => Stmt::If(IfStmt {
                condition: self.rewrite_captured_refs(&if_stmt.condition, captured, self_sym),
                then_branch: self.rewrite_captured_refs_in_block(
                    &if_stmt.then_branch,
                    captured,
                    self_sym,
                ),
                else_branch: if_stmt
                    .else_branch
                    .as_ref()
                    .map(|b| self.rewrite_captured_refs_in_block(b, captured, self_sym)),
                span: if_stmt.span,
            }),
            Stmt::Return(ret_stmt) => Stmt::Return(ReturnStmt {
                value: ret_stmt
                    .value
                    .as_ref()
                    .map(|e| self.rewrite_captured_refs(e, captured, self_sym)),
                span: ret_stmt.span,
            }),
            Stmt::Raise(raise_stmt) => {
                let fields = raise_stmt
                    .fields
                    .iter()
                    .map(|f| StructFieldInit {
                        name: f.name,
                        value: self.rewrite_captured_refs(&f.value, captured, self_sym),
                        span: f.span,
                        shorthand: f.shorthand,
                    })
                    .collect();
                Stmt::Raise(RaiseStmt {
                    error_name: raise_stmt.error_name,
                    fields,
                    span: raise_stmt.span,
                })
            }
            Stmt::Break(span) => Stmt::Break(*span),
            Stmt::Continue(span) => Stmt::Continue(*span),
        }
    }
}
