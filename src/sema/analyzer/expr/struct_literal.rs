use super::super::*;

impl Analyzer {
    pub(super) fn check_struct_literal_expr(
        &mut self,
        expr: &Expr,
        struct_lit: &StructLiteralExpr,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        // Look up the type (class or record)
        let (type_name, fields, is_class) =
            if let Some(class_type) = self.classes.get(&struct_lit.name).cloned() {
                (
                    interner.resolve(struct_lit.name).to_string(),
                    class_type.fields,
                    true,
                )
            } else if let Some(record_type) = self.records.get(&struct_lit.name).cloned() {
                (
                    interner.resolve(struct_lit.name).to_string(),
                    record_type.fields,
                    false,
                )
            } else {
                self.add_error(
                    SemanticError::UnknownType {
                        name: interner.resolve(struct_lit.name).to_string(),
                        span: expr.span.into(),
                    },
                    expr.span,
                );
                return Ok(Type::Error);
            };

        // Check that all required fields are present
        let provided_fields: HashSet<Symbol> = struct_lit.fields.iter().map(|f| f.name).collect();

        for field in &fields {
            if !provided_fields.contains(&field.name) {
                self.add_error(
                    SemanticError::MissingField {
                        ty: type_name.clone(),
                        field: interner.resolve(field.name).to_string(),
                        span: expr.span.into(),
                    },
                    expr.span,
                );
            }
        }

        // Check each provided field
        for field_init in &struct_lit.fields {
            if let Some(expected_field) = fields.iter().find(|f| f.name == field_init.name) {
                // check_expr_expecting will report errors if types don't match
                self.check_expr_expecting(&field_init.value, Some(&expected_field.ty), interner)?;
            } else {
                self.add_error(
                    SemanticError::UnknownField {
                        ty: type_name.clone(),
                        field: interner.resolve(field_init.name).to_string(),
                        span: field_init.span.into(),
                    },
                    field_init.span,
                );
                // Still check the value for more errors
                self.check_expr(&field_init.value, interner)?;
            }
        }

        // Return the appropriate type
        if is_class {
            Ok(Type::Class(
                self.classes.get(&struct_lit.name).unwrap().clone(),
            ))
        } else {
            Ok(Type::Record(
                self.records.get(&struct_lit.name).unwrap().clone(),
            ))
        }
    }
}
