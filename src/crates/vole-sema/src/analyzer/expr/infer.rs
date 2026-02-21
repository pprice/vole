use super::super::*;
use super::ExprContext;
use crate::type_arena::TypeId as ArenaTypeId;

impl Analyzer {
    /// Check expression and return TypeId.
    /// This is THE entry point for expression type checking.
    pub(crate) fn check_expr(
        &mut self,
        expr: &Expr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        self.check_expr_with_ctx(expr, interner, ExprContext::Standard)
    }

    /// Check expression in an arm body context (trailing block expressions allowed).
    pub(crate) fn check_expr_in_arm(
        &mut self,
        expr: &Expr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        self.check_expr_with_ctx(expr, interner, ExprContext::ArmBody)
    }

    /// Check expression with an explicit context.
    pub(crate) fn check_expr_with_ctx(
        &mut self,
        expr: &Expr,
        interner: &Interner,
        ctx: ExprContext,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let type_id = self.check_expr_inner(expr, interner, ctx)?;
        tracing::trace!(
            line = expr.span.line,
            inferred_type = %self.type_display_id(type_id),
            "type inferred"
        );
        Ok(self.record_expr_type_id(expr, type_id))
    }

    /// Dispatch expression checking to focused helper methods.
    fn check_expr_inner(
        &mut self,
        expr: &Expr,
        interner: &Interner,
        ctx: ExprContext,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        match &expr.kind {
            // Literals - simple type returns
            ExprKind::IntLiteral(_, suffix) => Ok(self.check_int_literal(*suffix)),
            ExprKind::FloatLiteral(_, suffix) => Ok(self.check_float_literal(*suffix)),
            ExprKind::BoolLiteral(_) => Ok(ArenaTypeId::BOOL),
            ExprKind::StringLiteral(_) => Ok(ArenaTypeId::STRING),
            ExprKind::InterpolatedString(parts) => {
                // Type-check each embedded expression and annotate string conversions
                for part in parts {
                    if let StringPart::Expr(inner_expr) = part {
                        let part_type = self.check_expr(inner_expr, interner)?;
                        let conversion = self.classify_string_conversion(part_type);
                        self.results
                            .node_map
                            .set_string_conversion(inner_expr.id, conversion);
                    }
                }
                Ok(ArenaTypeId::STRING)
            }
            ExprKind::TypeLiteral(_) => Ok(ArenaTypeId::METATYPE),
            // Identifier and variable access
            ExprKind::Identifier(sym) => self.check_identifier_expr(expr, *sym, interner),

            // Operators
            ExprKind::Binary(bin) => self.check_binary_expr(expr, bin, interner),
            ExprKind::Unary(un) => self.check_unary_expr(expr, un, interner),

            // Calls and assignments (existing helpers)
            ExprKind::Call(call) => self.check_call_expr(expr, call, interner),
            ExprKind::Assign(assign) => self.check_assign_expr(expr, assign, interner),
            ExprKind::CompoundAssign(compound) => {
                self.check_compound_assign_expr(expr, compound, interner)
            }

            // Grouping - just recurse
            ExprKind::Grouping(inner) => self.check_expr_with_ctx(inner, interner, ctx),

            // Array and range expressions
            ExprKind::ArrayLiteral(elements) => self.check_array_literal_expr(elements, interner),
            ExprKind::RepeatLiteral { element, count } => {
                self.check_repeat_literal_expr(element, *count, interner)
            }
            ExprKind::Index(idx) => self.check_index_expr(idx, interner),
            ExprKind::Range(range) => self.check_range_expr(range, expr.span, interner),

            // Pattern matching (existing helper)
            ExprKind::Match(match_expr) => self.check_match_expr(match_expr, None, interner),

            // Null coalesce and is expression
            ExprKind::NullCoalesce(nc) => self.check_null_coalesce_expr(nc, interner),
            ExprKind::Is(is_expr) => self.check_is_expr(expr, is_expr, interner),

            // Lambda - delegate to existing analyze_lambda
            ExprKind::Lambda(lambda) => Ok(self.analyze_lambda(lambda, expr.id, None, interner)),

            // Struct and field access (existing helpers)
            ExprKind::StructLiteral(struct_lit) => {
                self.check_struct_literal_expr(expr, struct_lit, interner)
            }
            ExprKind::FieldAccess(field_access) => {
                self.check_field_access_expr(field_access, interner)
            }
            ExprKind::OptionalChain(opt_chain) => {
                self.check_optional_chain_expr(opt_chain, expr.id, interner)
            }
            ExprKind::OptionalMethodCall(omc) => {
                self.check_optional_method_call_expr(omc, expr.id, interner)
            }
            ExprKind::MethodCall(method_call) => {
                self.check_method_call_expr(expr, method_call, interner)
            }

            // Try expression - delegate to existing analyze_try
            ExprKind::Try(inner) => self.analyze_try(inner, interner),

            // Import - delegate to existing analyze_module
            ExprKind::Import(path) => self
                .analyze_module(path, expr.span, interner)
                .map_err(|_| self.diagnostics.errors.clone()),

            // Yield expression
            ExprKind::Yield(yield_expr) => self.check_yield_expr(yield_expr, interner),

            // Control flow
            ExprKind::Block(block) => self.check_block_expr(block, interner, ctx),
            ExprKind::If(if_expr) => self.check_if_expr(if_expr, interner),
            ExprKind::When(when_expr) => self.check_when_expr(when_expr, interner),

            // Unreachable returns never type
            ExprKind::Unreachable => Ok(ArenaTypeId::NEVER),
        }
    }

    /// Check integer literal type based on suffix.
    fn check_int_literal(&self, suffix: Option<NumericSuffix>) -> ArenaTypeId {
        if let Some(s) = suffix {
            self.suffix_to_type_id(s)
        } else {
            ArenaTypeId::I64 // Default to i64
        }
    }

    /// Check float literal type based on suffix.
    fn check_float_literal(&self, suffix: Option<NumericSuffix>) -> ArenaTypeId {
        if let Some(s) = suffix {
            self.suffix_to_type_id(s)
        } else {
            ArenaTypeId::F64 // Default to f64
        }
    }

    /// Infer a literal's type from a type hint for bidirectional type inference.
    /// Takes a TypeId hint and returns the hint if the literal can be that type,
    /// otherwise returns the default type for the literal.
    pub(crate) fn infer_literal_type_id(
        &mut self,
        expr: &Expr,
        hint: ArenaTypeId,
        _interner: &Interner,
    ) -> ArenaTypeId {
        match &expr.kind {
            ExprKind::IntLiteral(value, suffix) => {
                // If suffix is present, it overrides the hint
                if let Some(s) = suffix {
                    return self.suffix_to_type_id(*s);
                }
                // Use TypeArena's literal_fits_id which handles primitives and unions
                if self.type_arena().literal_fits_id(*value, hint) {
                    hint
                } else {
                    self.ty_i64_id() // Default
                }
            }
            ExprKind::FloatLiteral(_, suffix) => {
                // If suffix is present, it overrides the hint
                if let Some(s) = suffix {
                    return self.suffix_to_type_id(*s);
                }
                if hint == ArenaTypeId::F32 || hint == ArenaTypeId::F64 || hint == ArenaTypeId::F128
                {
                    hint
                } else {
                    self.ty_f64_id() // Default
                }
            }
            // Bool and String have only one possible type
            ExprKind::BoolLiteral(_) => self.ty_bool_id(),
            ExprKind::StringLiteral(_) => self.ty_string_id(),
            // Not a literal - this shouldn't happen if is_literal() was checked
            _ => self.ty_invalid_traced_id("fallback"),
        }
    }
}
