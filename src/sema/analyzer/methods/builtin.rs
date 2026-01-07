use super::super::*;

impl Analyzer {
    /// Check if a method call is a built-in method on a primitive type
    /// Returns Some(return_type) if handled, None if not a built-in
    pub(crate) fn check_builtin_method(
        &mut self,
        object_type: &Type,
        method_name: &str,
        args: &[Expr],
        interner: &Interner,
    ) -> Option<Type> {
        match (object_type, method_name) {
            // Array.length() -> i64
            (Type::Array(_), "length") => {
                if !args.is_empty() {
                    self.add_error(
                        SemanticError::WrongArgumentCount {
                            expected: 0,
                            found: args.len(),
                            span: args[0].span.into(),
                        },
                        args[0].span,
                    );
                }
                Some(Type::I64)
            }
            // Array.iter() -> Iterator<T>
            (Type::Array(elem_ty), "iter") => {
                if !args.is_empty() {
                    self.add_error(
                        SemanticError::WrongArgumentCount {
                            expected: 0,
                            found: args.len(),
                            span: args[0].span.into(),
                        },
                        args[0].span,
                    );
                }
                Some(Type::Iterator(elem_ty.clone()))
            }
            // Iterator.next() -> T | Done
            (Type::Iterator(elem_ty), "next")
            | (Type::MapIterator(elem_ty), "next")
            | (Type::FilterIterator(elem_ty), "next")
            | (Type::TakeIterator(elem_ty), "next")
            | (Type::SkipIterator(elem_ty), "next") => {
                if !args.is_empty() {
                    self.add_error(
                        SemanticError::WrongArgumentCount {
                            expected: 0,
                            found: args.len(),
                            span: args[0].span.into(),
                        },
                        args[0].span,
                    );
                }
                Some(Type::Union(vec![*elem_ty.clone(), Type::Done]))
            }
            // Iterator.collect() -> [T]
            (Type::Iterator(elem_ty), "collect")
            | (Type::MapIterator(elem_ty), "collect")
            | (Type::FilterIterator(elem_ty), "collect")
            | (Type::TakeIterator(elem_ty), "collect")
            | (Type::SkipIterator(elem_ty), "collect") => {
                if !args.is_empty() {
                    self.add_error(
                        SemanticError::WrongArgumentCount {
                            expected: 0,
                            found: args.len(),
                            span: args[0].span.into(),
                        },
                        args[0].span,
                    );
                }
                Some(Type::Array(elem_ty.clone()))
            }
            // Iterator.count() -> i64
            (Type::Iterator(_), "count")
            | (Type::MapIterator(_), "count")
            | (Type::FilterIterator(_), "count")
            | (Type::TakeIterator(_), "count")
            | (Type::SkipIterator(_), "count") => {
                if !args.is_empty() {
                    self.add_error(
                        SemanticError::WrongArgumentCount {
                            expected: 0,
                            found: args.len(),
                            span: args[0].span.into(),
                        },
                        args[0].span,
                    );
                }
                Some(Type::I64)
            }
            // Iterator.sum() -> i64 (only for numeric iterators)
            (Type::Iterator(elem_ty), "sum")
            | (Type::MapIterator(elem_ty), "sum")
            | (Type::FilterIterator(elem_ty), "sum")
            | (Type::TakeIterator(elem_ty), "sum")
            | (Type::SkipIterator(elem_ty), "sum") => {
                if !args.is_empty() {
                    self.add_error(
                        SemanticError::WrongArgumentCount {
                            expected: 0,
                            found: args.len(),
                            span: args[0].span.into(),
                        },
                        args[0].span,
                    );
                }
                // sum() only works on numeric types (i64, i32)
                match elem_ty.as_ref() {
                    Type::I64 | Type::I32 => Some(Type::I64),
                    _ => {
                        let iterator_type = Type::Iterator(elem_ty.clone());
                        let found = self.type_display(&iterator_type, interner);
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "numeric iterator (i64 or i32)".to_string(),
                                found,
                                span: args.first().map(|a| a.span).unwrap_or_default().into(),
                            },
                            args.first().map(|a| a.span).unwrap_or_default(),
                        );
                        Some(Type::I64)
                    }
                }
            }
            // Iterator.for_each(fn) -> () where fn: (T) -> ()
            (Type::Iterator(elem_ty), "for_each")
            | (Type::MapIterator(elem_ty), "for_each")
            | (Type::FilterIterator(elem_ty), "for_each")
            | (Type::TakeIterator(elem_ty), "for_each")
            | (Type::SkipIterator(elem_ty), "for_each") => {
                if args.len() != 1 {
                    self.add_error(
                        SemanticError::WrongArgumentCount {
                            expected: 1,
                            found: args.len(),
                            span: args.first().map(|a| a.span).unwrap_or_default().into(),
                        },
                        args.first().map(|a| a.span).unwrap_or_default(),
                    );
                    return Some(Type::Void);
                }

                // The argument should be a function (T) -> ()
                let expected_fn_type = FunctionType {
                    params: vec![*elem_ty.clone()],
                    return_type: Box::new(Type::Void),
                    is_closure: true,
                };

                let arg = &args[0];
                let arg_ty = if let ExprKind::Lambda(lambda) = &arg.kind {
                    self.analyze_lambda(lambda, Some(&expected_fn_type), interner)
                } else {
                    self.check_expr(arg, interner).unwrap_or(Type::Error)
                };

                // Verify it's a function
                if !matches!(&arg_ty, Type::Function(_)) {
                    let found = self.type_display(&arg_ty, interner);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "function".to_string(),
                            found,
                            span: arg.span.into(),
                        },
                        arg.span,
                    );
                }

                Some(Type::Void)
            }
            // Iterator.filter(fn) -> FilterIterator<T> where fn: (T) -> bool
            // MapIterator.filter(fn) -> FilterIterator<T> (chained filter)
            // FilterIterator.filter(fn) -> FilterIterator<T> (chained filter)
            // TakeIterator.filter(fn) -> FilterIterator<T> (chained filter)
            // SkipIterator.filter(fn) -> FilterIterator<T> (chained filter)
            (Type::Iterator(elem_ty), "filter")
            | (Type::MapIterator(elem_ty), "filter")
            | (Type::FilterIterator(elem_ty), "filter")
            | (Type::TakeIterator(elem_ty), "filter")
            | (Type::SkipIterator(elem_ty), "filter") => {
                if args.len() != 1 {
                    self.add_error(
                        SemanticError::WrongArgumentCount {
                            expected: 1,
                            found: args.len(),
                            span: args.first().map(|a| a.span).unwrap_or_default().into(),
                        },
                        args.first().map(|a| a.span).unwrap_or_default(),
                    );
                    return Some(Type::FilterIterator(elem_ty.clone()));
                }

                // The argument should be a function (T) -> bool
                let expected_fn_type = FunctionType {
                    params: vec![*elem_ty.clone()],
                    return_type: Box::new(Type::Bool),
                    is_closure: true,
                };

                let arg = &args[0];
                let arg_ty = if let ExprKind::Lambda(lambda) = &arg.kind {
                    self.analyze_lambda(lambda, Some(&expected_fn_type), interner)
                } else {
                    self.check_expr(arg, interner).unwrap_or(Type::Error)
                };

                // Verify it's a function returning bool
                match &arg_ty {
                    Type::Function(ft) => {
                        if *ft.return_type != Type::Bool {
                            let found = self.type_display(&ft.return_type, interner);
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "bool".to_string(),
                                    found,
                                    span: arg.span.into(),
                                },
                                arg.span,
                            );
                        }
                    }
                    _ => {
                        let found = self.type_display(&arg_ty, interner);
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "function".to_string(),
                                found,
                                span: arg.span.into(),
                            },
                            arg.span,
                        );
                    }
                }

                // Filter preserves element type
                Some(Type::FilterIterator(elem_ty.clone()))
            }
            // Iterator.map(fn) -> MapIterator<U> where fn: (T) -> U
            // MapIterator.map(fn) -> MapIterator<V> where fn: (U) -> V (chained map)
            // FilterIterator.map(fn) -> MapIterator<V> (map after filter)
            // TakeIterator.map(fn) -> MapIterator<V> (map after take)
            // SkipIterator.map(fn) -> MapIterator<V> (map after skip)
            (Type::Iterator(elem_ty), "map")
            | (Type::MapIterator(elem_ty), "map")
            | (Type::FilterIterator(elem_ty), "map")
            | (Type::TakeIterator(elem_ty), "map")
            | (Type::SkipIterator(elem_ty), "map") => {
                if args.len() != 1 {
                    self.add_error(
                        SemanticError::WrongArgumentCount {
                            expected: 1,
                            found: args.len(),
                            span: args.first().map(|a| a.span).unwrap_or_default().into(),
                        },
                        args.first().map(|a| a.span).unwrap_or_default(),
                    );
                    return Some(Type::MapIterator(elem_ty.clone()));
                }

                // The argument should be a function (T) -> U
                // We need to analyze the lambda with expected type context
                let expected_fn_type = FunctionType {
                    params: vec![*elem_ty.clone()],
                    return_type: Box::new(Type::I64), // Default, will be inferred
                    is_closure: true,
                };

                let arg = &args[0];
                let arg_ty = if let ExprKind::Lambda(lambda) = &arg.kind {
                    self.analyze_lambda(lambda, Some(&expected_fn_type), interner)
                } else {
                    self.check_expr(arg, interner).unwrap_or(Type::Error)
                };

                // Extract return type from the function
                let output_type = match &arg_ty {
                    Type::Function(ft) => (*ft.return_type).clone(),
                    _ => {
                        let found = self.type_display(&arg_ty, interner);
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "function".to_string(),
                                found,
                                span: arg.span.into(),
                            },
                            arg.span,
                        );
                        *elem_ty.clone()
                    }
                };

                Some(Type::MapIterator(Box::new(output_type)))
            }
            // Iterator.take(n) -> TakeIterator<T> where n: i64
            // Works on any iterator type
            (Type::Iterator(elem_ty), "take")
            | (Type::MapIterator(elem_ty), "take")
            | (Type::FilterIterator(elem_ty), "take")
            | (Type::TakeIterator(elem_ty), "take")
            | (Type::SkipIterator(elem_ty), "take") => {
                if args.len() != 1 {
                    self.add_error(
                        SemanticError::WrongArgumentCount {
                            expected: 1,
                            found: args.len(),
                            span: args.first().map(|a| a.span).unwrap_or_default().into(),
                        },
                        args.first().map(|a| a.span).unwrap_or_default(),
                    );
                    return Some(Type::TakeIterator(elem_ty.clone()));
                }

                // The argument should be an integer (i64)
                let arg = &args[0];
                let arg_ty = self.check_expr(arg, interner).unwrap_or(Type::Error);

                // Verify it's an integer type
                if !arg_ty.is_integer() {
                    let found = self.type_display(&arg_ty, interner);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "i64".to_string(),
                            found,
                            span: arg.span.into(),
                        },
                        arg.span,
                    );
                }

                // Take preserves element type
                Some(Type::TakeIterator(elem_ty.clone()))
            }
            // Iterator.skip(n) -> SkipIterator<T> where n: i64
            // Works on any iterator type
            (Type::Iterator(elem_ty), "skip")
            | (Type::MapIterator(elem_ty), "skip")
            | (Type::FilterIterator(elem_ty), "skip")
            | (Type::TakeIterator(elem_ty), "skip")
            | (Type::SkipIterator(elem_ty), "skip") => {
                if args.len() != 1 {
                    self.add_error(
                        SemanticError::WrongArgumentCount {
                            expected: 1,
                            found: args.len(),
                            span: args.first().map(|a| a.span).unwrap_or_default().into(),
                        },
                        args.first().map(|a| a.span).unwrap_or_default(),
                    );
                    return Some(Type::SkipIterator(elem_ty.clone()));
                }

                // The argument should be an integer (i64)
                let arg = &args[0];
                let arg_ty = self.check_expr(arg, interner).unwrap_or(Type::Error);

                // Verify it's an integer type
                if !arg_ty.is_integer() {
                    let found = self.type_display(&arg_ty, interner);
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "i64".to_string(),
                            found,
                            span: arg.span.into(),
                        },
                        arg.span,
                    );
                }

                // Skip preserves element type
                Some(Type::SkipIterator(elem_ty.clone()))
            }
            // Iterator.reduce(init, fn) -> U where fn: (U, T) -> U
            // Takes an initial value and an accumulator function, returns the final accumulated value
            (Type::Iterator(elem_ty), "reduce")
            | (Type::MapIterator(elem_ty), "reduce")
            | (Type::FilterIterator(elem_ty), "reduce")
            | (Type::TakeIterator(elem_ty), "reduce")
            | (Type::SkipIterator(elem_ty), "reduce") => {
                if args.len() != 2 {
                    self.add_error(
                        SemanticError::WrongArgumentCount {
                            expected: 2,
                            found: args.len(),
                            span: args.first().map(|a| a.span).unwrap_or_default().into(),
                        },
                        args.first().map(|a| a.span).unwrap_or_default(),
                    );
                    // Return I64 as default - the actual type depends on the init value
                    return Some(Type::I64);
                }

                // First argument is the initial value (any type U)
                let init_arg = &args[0];
                let init_ty = self.check_expr(init_arg, interner).unwrap_or(Type::Error);

                // Second argument should be a function (U, T) -> U
                let expected_fn_type = FunctionType {
                    params: vec![init_ty.clone(), *elem_ty.clone()],
                    return_type: Box::new(init_ty.clone()),
                    is_closure: true,
                };

                let reducer_arg = &args[1];
                let reducer_ty = if let ExprKind::Lambda(lambda) = &reducer_arg.kind {
                    self.analyze_lambda(lambda, Some(&expected_fn_type), interner)
                } else {
                    self.check_expr(reducer_arg, interner)
                        .unwrap_or(Type::Error)
                };

                // Verify it's a function with correct signature
                match &reducer_ty {
                    Type::Function(ft) => {
                        // Check it has 2 parameters
                        if ft.params.len() != 2 {
                            self.add_error(
                                SemanticError::WrongArgumentCount {
                                    expected: 2,
                                    found: ft.params.len(),
                                    span: reducer_arg.span.into(),
                                },
                                reducer_arg.span,
                            );
                        }
                        // Return type should match the accumulator type (init type)
                        if *ft.return_type != init_ty {
                            let expected = self.type_display(&init_ty, interner);
                            let found = self.type_display(&ft.return_type, interner);
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected,
                                    found,
                                    span: reducer_arg.span.into(),
                                },
                                reducer_arg.span,
                            );
                        }
                    }
                    _ => {
                        let found = self.type_display(&reducer_ty, interner);
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "function".to_string(),
                                found,
                                span: reducer_arg.span.into(),
                            },
                            reducer_arg.span,
                        );
                    }
                }

                // reduce returns the same type as the initial value
                Some(init_ty)
            }
            // String.length() -> i64
            (Type::String, "length") => {
                if !args.is_empty() {
                    self.add_error(
                        SemanticError::WrongArgumentCount {
                            expected: 0,
                            found: args.len(),
                            span: args[0].span.into(),
                        },
                        args[0].span,
                    );
                }
                Some(Type::I64)
            }
            _ => None,
        }
    }
}
