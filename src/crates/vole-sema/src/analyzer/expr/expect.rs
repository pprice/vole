use super::super::*;
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
        let ty_id = self.check_expr_expecting_inner_id(expr, expected, interner)?;
        Ok(self.record_expr_type_id(expr, ty_id))
    }

    fn check_expr_expecting_inner_id(
        &mut self,
        expr: &Expr,
        expected: Option<ArenaTypeId>,
        interner: &Interner,
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
                    if let Some(exp_id) = expected
                        && exp_id != suffix_type_id
                        && !self
                            .type_arena()
                            .unwrap_union(exp_id)
                            .is_some_and(|variants| variants.contains(&suffix_type_id))
                    {
                        let expected_str = self.type_display_id(exp_id);
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: expected_str,
                                found: s.as_str().to_string(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
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
                    if let Some(best) = best_variant {
                        return Ok(best);
                    }
                    // No matching integer variant
                    let expected_str = self.type_display_id(expected.unwrap());
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: expected_str,
                            found: "integer literal".to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    return Ok(ArenaTypeId::I64);
                }

                if let Some(exp_id) = expected {
                    if self.type_arena().literal_fits_id(*value, exp_id) {
                        return Ok(exp_id);
                    }
                    let expected_str = self.type_display_id(exp_id);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: expected_str,
                            found: "integer literal".to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    return Ok(exp_id);
                }
                Ok(ArenaTypeId::I64)
            }
            ExprKind::TypeLiteral(_) => {
                if let Some(exp_id) = expected
                    && exp_id != ArenaTypeId::METATYPE
                {
                    let expected_str = self.type_display_id(exp_id);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: expected_str,
                            found: "type".to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
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
                    if let Some(exp_id) = expected
                        && exp_id != suffix_type_id
                        && !self
                            .type_arena()
                            .unwrap_union(exp_id)
                            .is_some_and(|variants| variants.contains(&suffix_type_id))
                    {
                        let expected_str = self.type_display_id(exp_id);
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: expected_str,
                                found: s.as_str().to_string(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
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
                    // Check if union contains f64
                    if let Some(variants) = self.type_arena().unwrap_union(exp_id)
                        && variants.contains(&ArenaTypeId::F64)
                    {
                        return Ok(ArenaTypeId::F64);
                    }
                    let expected_str = self.type_display_id(exp_id);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: expected_str,
                            found: "f64".to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                }
                Ok(ArenaTypeId::F64)
            }
            ExprKind::Binary(bin) => {
                self.check_binary_expr_expecting_id(expr, bin, expected, interner)
            }
            ExprKind::Unary(un) => self.check_unary_expr_expecting_id(expr, un, expected, interner),
            ExprKind::Grouping(inner) => self.check_expr_expecting_id(inner, expected, interner),
            ExprKind::ArrayLiteral(elements) => {
                self.check_array_literal_expecting_id(expr, elements, expected, interner)
            }
            ExprKind::Index(_) => {
                // Index expressions just delegate to check_expr
                self.check_expr(expr, interner)
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
                Ok(self.analyze_lambda(lambda, expected_fn.as_ref(), interner))
            }
            // All other cases: infer type, then check compatibility
            _ => {
                let inferred_id = self.check_expr(expr, interner)?;
                if let Some(expected_id) = expected
                    && !self.types_compatible_id(inferred_id, expected_id, interner)
                {
                    let expected_str = self.type_display_id(expected_id);
                    let found = self.type_display_id(inferred_id);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: expected_str,
                            found,
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
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
                    #[allow(clippy::if_same_then_else)]
                    if right_id == ArenaTypeId::STRING {
                        return Ok(ArenaTypeId::STRING);
                    } else if self.satisfies_stringable_id(right_id, interner) {
                        return Ok(ArenaTypeId::STRING);
                    } else {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "Stringable".to_string(),
                                found: self.type_display_id(right_id),
                                span: bin.right.span.into(),
                            },
                            bin.right.span,
                        );
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

                self.add_error(
                    SemanticError::TypeMismatch {
                        expected: "numeric or string".to_string(),
                        found: self.type_display_pair_id(left_id, right_id),
                        span: expr.span.into(),
                    },
                    expr.span,
                );
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

                self.add_error(
                    SemanticError::TypeMismatch {
                        expected: "numeric".to_string(),
                        found: self.type_display_pair_id(left_id, right_id),
                        span: expr.span.into(),
                    },
                    expr.span,
                );
                Ok(ArenaTypeId::INVALID)
            }
            // Comparison ops
            BinaryOp::Eq
            | BinaryOp::Ne
            | BinaryOp::Lt
            | BinaryOp::Gt
            | BinaryOp::Le
            | BinaryOp::Ge => {
                let left_id = self.check_expr_expecting_id(&bin.left, None, interner)?;
                self.check_expr_expecting_id(&bin.right, Some(left_id), interner)?;
                Ok(ArenaTypeId::BOOL)
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
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "bool".to_string(),
                            found: self.type_display_pair_id(left_id, right_id),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
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

                self.add_error(
                    SemanticError::TypeMismatch {
                        expected: "integer".to_string(),
                        found: self.type_display_pair_id(left_id, right_id),
                        span: expr.span.into(),
                    },
                    expr.span,
                );
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
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "numeric".to_string(),
                            found: self.type_display_id(operand_id),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    Ok(ArenaTypeId::INVALID)
                }
            }
            UnaryOp::Not => {
                let operand_id =
                    self.check_expr_expecting_id(&un.operand, Some(ArenaTypeId::BOOL), interner)?;
                if operand_id == ArenaTypeId::BOOL {
                    Ok(ArenaTypeId::BOOL)
                } else {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "bool".to_string(),
                            found: self.type_display_id(operand_id),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    Ok(ArenaTypeId::INVALID)
                }
            }
            UnaryOp::BitNot => {
                let operand_id = self.check_expr_expecting_id(&un.operand, expected, interner)?;
                if operand_id.is_integer() {
                    Ok(operand_id)
                } else {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "integer".to_string(),
                            found: self.type_display_id(operand_id),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
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
        if let Some(exp_id) = expected {
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
                let mut elem_ids = Vec::with_capacity(elements.len());
                for e in elements {
                    elem_ids.push(self.check_expr_expecting_id(
                        e,
                        Some(elem_expected),
                        interner,
                    )?);
                }
                return Ok(self.ty_array_id(elem_ids[0]));
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
    fn numeric_result_type(&self, left: ArenaTypeId, right: ArenaTypeId) -> ArenaTypeId {
        if left == ArenaTypeId::F64 || right == ArenaTypeId::F64 {
            ArenaTypeId::F64
        } else if left == ArenaTypeId::I64 || right == ArenaTypeId::I64 {
            ArenaTypeId::I64
        } else {
            ArenaTypeId::I32
        }
    }

    /// Get the result type for integer operations (wider type wins)
    fn integer_result_type(&self, left: ArenaTypeId, right: ArenaTypeId) -> ArenaTypeId {
        if left == ArenaTypeId::I64 || right == ArenaTypeId::I64 {
            ArenaTypeId::I64
        } else {
            ArenaTypeId::I32
        }
    }
}
