use super::super::*;
use super::ExprContext;
use crate::type_arena::TypeId as ArenaTypeId;
use crate::types::PlaceholderKind;

impl Analyzer {
    /// Check expression against expected type and return TypeId directly.
    /// Uses TypeId throughout for bidirectional type checking.
    pub(crate) fn check_expr_expecting_id(
        &mut self,
        expr: &Expr,
        expected: Option<ArenaTypeId>,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        self.check_expr_expecting_id_with_ctx(expr, expected, interner, ExprContext::Standard)
    }

    /// Check expression against expected type in an arm body context.
    pub(crate) fn check_expr_expecting_id_in_arm(
        &mut self,
        expr: &Expr,
        expected: Option<ArenaTypeId>,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        self.check_expr_expecting_id_with_ctx(expr, expected, interner, ExprContext::ArmBody)
    }

    fn check_expr_expecting_id_with_ctx(
        &mut self,
        expr: &Expr,
        expected: Option<ArenaTypeId>,
        interner: &Interner,
        ctx: ExprContext,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        let ty_id = self.check_expr_expecting_inner_id(expr, expected, interner, ctx)?;
        Ok(self.record_expr_type_id(expr, ty_id))
    }

    fn check_expr_expecting_inner_id(
        &mut self,
        expr: &Expr,
        expected: Option<ArenaTypeId>,
        interner: &Interner,
        ctx: ExprContext,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        match &expr.kind {
            ExprKind::IntLiteral(value, suffix) => {
                // If the literal has a suffix, resolve its type from the suffix
                if let Some(s) = suffix {
                    let suffix_type_id = self.suffix_to_type_id(*s);

                    // Validate: integer suffix on integer literal only
                    if s.is_float() {
                        self.add_error(
                            SemanticError::InvalidLiteralSuffix {
                                suffix: s.as_str().to_string(),
                                suffix_kind: "float".to_string(),
                                literal_kind: "integer".to_string(),
                                hint: "use `_f32` or `_f64` only on decimal or float literals"
                                    .to_string(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        return Ok(suffix_type_id);
                    }

                    // Validate: value fits in the suffix type
                    if !suffix_type_id.fits_literal(*value) {
                        self.add_error(
                            SemanticError::LiteralOutOfRange {
                                suffix: s.as_str().to_string(),
                                value: value.to_string(),
                                range: Self::type_range_str(*s),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        return Ok(suffix_type_id);
                    }

                    // Validate: suffix type matches expected type (if any)
                    // Skip check if expected is INVALID (prior error)
                    if let Some(exp_id) = expected
                        && !exp_id.is_invalid()
                        && exp_id != suffix_type_id
                        && !self
                            .type_arena()
                            .unwrap_union(exp_id)
                            .is_some_and(|variants| variants.contains(&suffix_type_id))
                    {
                        self.add_type_mismatch_expected_id(exp_id, s.as_str(), expr.span);
                    }
                    return Ok(suffix_type_id);
                }

                // No suffix - original logic
                // Check if expected is a union type
                let union_variants =
                    expected.and_then(|id| self.type_arena().unwrap_union(id).map(|v| v.to_vec()));

                if let Some(variants) = union_variants {
                    // Find the smallest integer variant that fits this literal.
                    // When multiple integer types can hold a value, prefer the smallest
                    // (e.g., prefer i32 over i64 for the literal 42).
                    let mut best_variant: Option<ArenaTypeId> = None;
                    for variant_id in variants {
                        if variant_id.is_integer() && variant_id.fits_literal(*value) {
                            best_variant = Some(match best_variant {
                                None => variant_id,
                                Some(current) => {
                                    // Prefer smaller integer types
                                    if variant_id.integer_bit_width() < current.integer_bit_width()
                                    {
                                        variant_id
                                    } else {
                                        current
                                    }
                                }
                            });
                        }
                    }
                    let Some(best) = best_variant else {
                        // No matching integer variant - emit error unless expected is INVALID
                        let exp_id =
                            expected.expect("expected type set for integer literal mismatch");
                        self.add_type_mismatch_expected_id(exp_id, "integer literal", expr.span);
                        return Ok(ArenaTypeId::I64);
                    };
                    return Ok(best);
                }

                if let Some(exp_id) = expected {
                    // For unknown type, accept the literal but keep its actual type
                    if exp_id.is_unknown() {
                        return Ok(ArenaTypeId::I64);
                    }
                    // For invalid type (from prior error), accept the literal
                    if exp_id.is_invalid() {
                        return Ok(ArenaTypeId::I64);
                    }
                    if self.type_arena().literal_fits_id(*value, exp_id) {
                        return Ok(exp_id);
                    }
                    self.add_type_mismatch_expected_id(exp_id, "integer literal", expr.span);
                    return Ok(exp_id);
                }
                Ok(ArenaTypeId::I64)
            }
            ExprKind::TypeLiteral(_) => {
                if let Some(exp_id) = expected
                    && !exp_id.is_invalid()
                    && exp_id != ArenaTypeId::METATYPE
                {
                    self.add_type_mismatch_expected_id(exp_id, "type", expr.span);
                }
                Ok(ArenaTypeId::METATYPE)
            }
            ExprKind::FloatLiteral(_, suffix) => {
                // If the literal has a suffix, resolve its type from the suffix
                if let Some(s) = suffix {
                    let suffix_type_id = self.suffix_to_type_id(*s);

                    // Validate: float suffix on float literal only
                    if s.is_integer() {
                        self.add_error(
                            SemanticError::InvalidLiteralSuffix {
                                suffix: s.as_str().to_string(),
                                suffix_kind: "integer".to_string(),
                                literal_kind: "float".to_string(),
                                hint: "use `_f32` or `_f64` for float literals".to_string(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        return Ok(suffix_type_id);
                    }

                    // Validate: suffix type matches expected type (if any)
                    // Skip check if expected is INVALID (prior error)
                    if let Some(exp_id) = expected
                        && !exp_id.is_invalid()
                        && exp_id != suffix_type_id
                        && !self
                            .type_arena()
                            .unwrap_union(exp_id)
                            .is_some_and(|variants| variants.contains(&suffix_type_id))
                    {
                        self.add_type_mismatch_expected_id(exp_id, s.as_str(), expr.span);
                    }
                    return Ok(suffix_type_id);
                }

                // No suffix - original logic
                if let Some(exp_id) = expected {
                    if exp_id == ArenaTypeId::F64 {
                        return Ok(ArenaTypeId::F64);
                    }
                    if exp_id.is_numeric() {
                        return Ok(exp_id);
                    }
                    // Unknown type accepts any value
                    if exp_id.is_unknown() {
                        return Ok(ArenaTypeId::F64);
                    }
                    // Invalid type (from prior error) - accept the literal
                    if exp_id.is_invalid() {
                        return Ok(ArenaTypeId::F64);
                    }
                    // Check if union contains f64
                    if let Some(variants) = self.type_arena().unwrap_union(exp_id)
                        && variants.contains(&ArenaTypeId::F64)
                    {
                        return Ok(ArenaTypeId::F64);
                    }
                    self.add_type_mismatch_expected_id(exp_id, "f64", expr.span);
                }
                Ok(ArenaTypeId::F64)
            }
            ExprKind::Binary(bin) => {
                self.check_binary_expr_expecting_id(expr, bin, expected, interner)
            }
            ExprKind::Unary(un) => self.check_unary_expr_expecting_id(expr, un, expected, interner),
            ExprKind::Grouping(inner) => {
                self.check_expr_expecting_id_with_ctx(inner, expected, interner, ctx)
            }
            ExprKind::ArrayLiteral(elements) => {
                self.check_array_literal_expecting_id(expr, elements, expected, interner)
            }
            ExprKind::Index(_) => {
                // Index expressions just delegate to check_expr
                self.check_expr_with_ctx(expr, interner, ctx)
            }
            ExprKind::Lambda(lambda) => {
                // Extract expected function type if available
                let expected_fn = expected.and_then(|exp_id| {
                    let arena = self.type_arena();
                    if let Some((params, ret, _)) = arena.unwrap_function(exp_id) {
                        // Build FunctionType from TypeIds
                        Some(FunctionType::from_ids(params, ret, false))
                    } else if let Some((iface_id, _)) = arena.unwrap_interface(exp_id) {
                        drop(arena);
                        self.get_functional_interface_type_by_type_def_id(iface_id)
                    } else {
                        None
                    }
                });
                let lambda_ty_id = self.analyze_lambda(lambda, expr.id, expected_fn.as_ref(), interner);
                if let Some(expected_id) = expected
                    && self.types_compatible_id(lambda_ty_id, expected_id, interner)
                {
                    // Preserve the caller's expected function type identity (e.g. closure
                    // array literals passed directly to [() -> T] params), instead of
                    // propagating a closure-flavored inferred type that only prints the same.
                    return Ok(expected_id);
                }
                Ok(lambda_ty_id)
            }
            // Match expressions: propagate expected type for bidirectional inference
            ExprKind::Match(match_expr) => self.check_match_expr(match_expr, expected, interner),
            // All other cases: infer type, then check compatibility
            _ => {
                let inferred_id = self.check_expr_with_ctx(expr, interner, ctx)?;
                if let Some(expected_id) = expected
                    && !self.types_compatible_id(inferred_id, expected_id, interner)
                {
                    // Use helper that suppresses errors if either type is INVALID
                    self.add_type_mismatch_id(expected_id, inferred_id, expr.span);
                }
                Ok(inferred_id)
            }
        }
    }

    fn check_binary_expr_expecting_id(
        &mut self,
        expr: &Expr,
        bin: &BinaryExpr,
        expected: Option<ArenaTypeId>,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        match bin.op {
            // Add handles both numeric addition and string concatenation
            BinaryOp::Add => {
                let left_id = self.check_expr_expecting_id(&bin.left, expected, interner)?;
                let right_id = self.check_expr_expecting_id(&bin.right, expected, interner)?;

                // Handle string concatenation
                if left_id == ArenaTypeId::STRING {
                    // String is Stringable but check it explicitly since primitives
                    // don't structurally implement interfaces
                    #[expect(clippy::if_same_then_else)]
                    if right_id == ArenaTypeId::STRING {
                        return Ok(ArenaTypeId::STRING);
                    } else if self.satisfies_stringable_id(right_id, interner) {
                        return Ok(ArenaTypeId::STRING);
                    } else {
                        self.type_error_id("Stringable", right_id, bin.right.span);
                        return Ok(ArenaTypeId::INVALID);
                    }
                }

                // Numeric addition
                if left_id.is_numeric() && right_id.is_numeric() {
                    if let Some(exp) = expected
                        && self.types_compatible_id(left_id, exp, interner)
                        && self.types_compatible_id(right_id, exp, interner)
                    {
                        return Ok(exp);
                    }
                    return Ok(self.numeric_result_type(left_id, right_id));
                }

                self.type_error_pair_id("numeric or string", left_id, right_id, expr.span);
                Ok(ArenaTypeId::INVALID)
            }
            // Arithmetic ops
            BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
                let left_id = self.check_expr_expecting_id(&bin.left, expected, interner)?;
                let right_id = self.check_expr_expecting_id(&bin.right, expected, interner)?;

                if left_id.is_numeric() && right_id.is_numeric() {
                    if let Some(exp) = expected
                        && self.types_compatible_id(left_id, exp, interner)
                        && self.types_compatible_id(right_id, exp, interner)
                    {
                        return Ok(exp);
                    }
                    return Ok(self.numeric_result_type(left_id, right_id));
                }

                self.type_error_pair_id("numeric", left_id, right_id, expr.span);
                Ok(ArenaTypeId::INVALID)
            }
            // Equality ops (handle allowed)
            BinaryOp::Eq | BinaryOp::Ne => {
                let left_id = self.check_expr_expecting_id(&bin.left, None, interner)?;
                let right_id = self.check_expr_expecting_id(&bin.right, Some(left_id), interner)?;
                self.check_nil_comparison(left_id, right_id, bin.op, expr.span);
                Ok(ArenaTypeId::BOOL)
            }
            // Ordering ops (handle rejected)
            BinaryOp::Lt | BinaryOp::Gt | BinaryOp::Le | BinaryOp::Ge => {
                let left_id = self.check_expr_expecting_id(&bin.left, None, interner)?;
                let right_id = self.check_expr_expecting_id(&bin.right, Some(left_id), interner)?;
                if left_id == ArenaTypeId::HANDLE || right_id == ArenaTypeId::HANDLE {
                    self.type_error_pair_id("orderable", left_id, right_id, expr.span);
                    Ok(ArenaTypeId::INVALID)
                } else {
                    Ok(ArenaTypeId::BOOL)
                }
            }
            // Logical ops
            BinaryOp::And | BinaryOp::Or => {
                let left_id =
                    self.check_expr_expecting_id(&bin.left, Some(ArenaTypeId::BOOL), interner)?;
                let right_id =
                    self.check_expr_expecting_id(&bin.right, Some(ArenaTypeId::BOOL), interner)?;

                if left_id == ArenaTypeId::BOOL && right_id == ArenaTypeId::BOOL {
                    Ok(ArenaTypeId::BOOL)
                } else {
                    self.type_error_pair_id("bool", left_id, right_id, expr.span);
                    Ok(ArenaTypeId::INVALID)
                }
            }
            // Bitwise ops
            BinaryOp::BitAnd
            | BinaryOp::BitOr
            | BinaryOp::BitXor
            | BinaryOp::Shl
            | BinaryOp::Shr => {
                let left_id = self.check_expr_expecting_id(&bin.left, expected, interner)?;
                let right_id = self.check_expr_expecting_id(&bin.right, expected, interner)?;

                if left_id.is_integer() && right_id.is_integer() {
                    if let Some(exp) = expected
                        && self.types_compatible_id(left_id, exp, interner)
                        && self.types_compatible_id(right_id, exp, interner)
                    {
                        return Ok(exp);
                    }
                    return Ok(self.integer_result_type(left_id, right_id));
                }

                self.type_error_pair_id("integer", left_id, right_id, expr.span);
                Ok(ArenaTypeId::INVALID)
            }
        }
    }

    fn check_unary_expr_expecting_id(
        &mut self,
        expr: &Expr,
        un: &UnaryExpr,
        expected: Option<ArenaTypeId>,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        match un.op {
            UnaryOp::Neg => {
                // Special case: -INT_LITERAL
                if let ExprKind::IntLiteral(value, suffix) = &un.operand.kind {
                    // If there's a suffix, use its type
                    if let Some(s) = suffix {
                        let suffix_type_id = self.suffix_to_type_id(*s);
                        self.record_expr_type_id(&un.operand, suffix_type_id);
                        return Ok(suffix_type_id);
                    }
                    let negated = value.wrapping_neg();
                    if let Some(target) = expected
                        && self.type_arena().literal_fits_id(negated, target)
                    {
                        self.record_expr_type_id(&un.operand, target);
                        return Ok(target);
                    }
                    self.record_expr_type_id(&un.operand, ArenaTypeId::I64);
                    return Ok(ArenaTypeId::I64);
                }

                let operand_id = self.check_expr_expecting_id(&un.operand, expected, interner)?;
                if operand_id.is_numeric() {
                    Ok(operand_id)
                } else {
                    self.type_error_id("numeric", operand_id, expr.span);
                    Ok(ArenaTypeId::INVALID)
                }
            }
            UnaryOp::Not => {
                let operand_id =
                    self.check_expr_expecting_id(&un.operand, Some(ArenaTypeId::BOOL), interner)?;
                if operand_id == ArenaTypeId::BOOL {
                    Ok(ArenaTypeId::BOOL)
                } else {
                    self.type_error_id("bool", operand_id, expr.span);
                    Ok(ArenaTypeId::INVALID)
                }
            }
            UnaryOp::BitNot => {
                let operand_id = self.check_expr_expecting_id(&un.operand, expected, interner)?;
                if operand_id.is_integer() {
                    Ok(operand_id)
                } else {
                    self.type_error_id("integer", operand_id, expr.span);
                    Ok(ArenaTypeId::INVALID)
                }
            }
        }
    }

    fn check_array_literal_expecting_id(
        &mut self,
        expr: &Expr,
        elements: &[Expr],
        expected: Option<ArenaTypeId>,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // Check if expecting a tuple type
        // Skip if expected type is INVALID (prior error)
        if let Some(exp_id) = expected
            && !exp_id.is_invalid()
        {
            // Extract tuple elements upfront to avoid borrow conflict
            let tuple_elems = self.type_arena().unwrap_tuple(exp_id).map(|e| e.to_vec());
            if let Some(expected_elems) = tuple_elems {
                if elements.len() != expected_elems.len() {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: format!("tuple with {} elements", expected_elems.len()),
                            found: format!("{} elements", elements.len()),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    return Ok(ArenaTypeId::INVALID);
                }
                let mut elem_ids = Vec::with_capacity(elements.len());
                for (elem, &exp_elem) in elements.iter().zip(expected_elems.iter()) {
                    elem_ids.push(self.check_expr_expecting_id(elem, Some(exp_elem), interner)?);
                }
                return Ok(self.ty_tuple_id(elem_ids));
            }

            // Extract array element type upfront to avoid borrow conflict
            let array_elem = self.type_arena().unwrap_array(exp_id);
            if let Some(elem_expected) = array_elem {
                if elements.is_empty() {
                    return Ok(exp_id);
                }
                for e in elements {
                    self.check_expr_expecting_id(e, Some(elem_expected), interner)?;
                }
                return Ok(exp_id);
            }
        }

        if elements.is_empty() {
            // Empty array with unknown element type - use arena.placeholder directly
            let unknown_id = self
                .type_arena_mut()
                .placeholder(PlaceholderKind::Inference);
            return Ok(self.ty_array_id(unknown_id));
        }

        // Infer types for all elements
        let elem_ids: Vec<ArenaTypeId> = elements
            .iter()
            .map(|e| self.check_expr_expecting_id(e, None, interner))
            .collect::<Result<Vec<_>, _>>()?;

        // Check if all elements have compatible types
        let first_id = elem_ids[0];
        let is_homogeneous = elem_ids
            .iter()
            .skip(1)
            .all(|&id| self.types_compatible_id(id, first_id, interner));

        if is_homogeneous {
            Ok(self.ty_array_id(first_id))
        } else {
            Ok(self.ty_tuple_id(elem_ids))
        }
    }

    /// Get the result type for numeric operations (wider type wins)
    /// Float > int, wider > narrower
    pub(crate) fn numeric_result_type(&self, left: ArenaTypeId, right: ArenaTypeId) -> ArenaTypeId {
        // Float types take precedence, wider float wins
        if left == ArenaTypeId::F128 || right == ArenaTypeId::F128 {
            ArenaTypeId::F128
        } else if left == ArenaTypeId::F64 || right == ArenaTypeId::F64 {
            ArenaTypeId::F64
        } else if left == ArenaTypeId::F32 || right == ArenaTypeId::F32 {
            ArenaTypeId::F32
        } else {
            // Both are integers - use integer promotion rules
            self.integer_result_type(left, right)
        }
    }

    /// Get the result type for integer operations (wider type wins)
    /// Follows C-like promotion: smaller types widen to larger types
    pub(crate) fn integer_result_type(&self, left: ArenaTypeId, right: ArenaTypeId) -> ArenaTypeId {
        // i128 is widest
        if left == ArenaTypeId::I128 || right == ArenaTypeId::I128 {
            ArenaTypeId::I128
        }
        // 64-bit types
        else if left == ArenaTypeId::I64
            || right == ArenaTypeId::I64
            || left == ArenaTypeId::U64
            || right == ArenaTypeId::U64
        {
            // If mixing signed/unsigned 64-bit, result is i64
            ArenaTypeId::I64
        }
        // 32-bit types
        else if left == ArenaTypeId::I32
            || right == ArenaTypeId::I32
            || left == ArenaTypeId::U32
            || right == ArenaTypeId::U32
        {
            ArenaTypeId::I32
        }
        // 16-bit types
        else if left == ArenaTypeId::I16
            || right == ArenaTypeId::I16
            || left == ArenaTypeId::U16
            || right == ArenaTypeId::U16
        {
            // Promote to i32 (standard integer promotion)
            ArenaTypeId::I32
        }
        // 8-bit types - promote to i32
        else {
            ArenaTypeId::I32
        }
    }
}
