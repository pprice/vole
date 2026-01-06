// src/sema/analyzer/methods.rs

use super::*;

#[allow(dead_code)]
impl Analyzer {
    pub(crate) fn types_compatible(&self, from: &Type, to: &Type, interner: &Interner) -> bool {
        // Use the core compatibility check for most cases
        if types_compatible_core(from, to) {
            return true;
        }

        // Function type is compatible with functional interface if signatures match
        if let Type::Function(fn_type) = from
            && let Type::Interface(iface) = to
            && let Some(iface_fn) = self.get_functional_interface_type(iface.name, interner)
            && function_compatible_with_interface(fn_type, &iface_fn)
        {
            return true;
        }

        false
    }

    /// Check call arguments against expected parameter types.
    ///
    /// This helper unifies the argument checking logic used for:
    /// - Named function calls
    /// - Function-typed variable calls
    /// - Expression calls (e.g., immediately invoked lambdas)
    ///
    /// If `with_inference` is true, uses `check_expr_expecting` for argument type checking,
    /// enabling integer literal inference and lambda parameter inference. Otherwise uses
    /// plain `check_expr` (for cases where type inference context isn't available).
    pub(crate) fn check_call_args(
        &mut self,
        args: &[Expr],
        param_types: &[Type],
        call_span: Span,
        with_inference: bool,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Check argument count
        if args.len() != param_types.len() {
            self.add_error(
                SemanticError::WrongArgumentCount {
                    expected: param_types.len(),
                    found: args.len(),
                    span: call_span.into(),
                },
                call_span,
            );
        }

        // Check each argument against its expected parameter type
        for (arg, param_ty) in args.iter().zip(param_types.iter()) {
            let arg_ty = if with_inference {
                // For lambda arguments, pass expected function type for inference
                if let ExprKind::Lambda(lambda) = &arg.kind {
                    let expected_fn = if let Type::Function(ft) = param_ty {
                        Some(ft)
                    } else {
                        None
                    };
                    self.analyze_lambda(lambda, expected_fn, interner)
                } else {
                    // Pass expected type to allow integer literal inference
                    self.check_expr_expecting(arg, Some(param_ty), interner)?
                }
            } else {
                self.check_expr(arg, interner)?
            };

            if !self.types_compatible(&arg_ty, param_ty, interner) {
                self.add_error(
                    SemanticError::TypeMismatch {
                        expected: param_ty.name().to_string(),
                        found: arg_ty.name().to_string(),
                        span: arg.span.into(),
                    },
                    arg.span,
                );
            }
        }

        Ok(())
    }

    /// Check if a method call is a built-in method on a primitive type
    /// Returns Some(return_type) if handled, None if not a built-in
    pub(crate) fn check_builtin_method(
        &mut self,
        object_type: &Type,
        method_name: &str,
        args: &[Expr],
        _interner: &Interner,
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
            (Type::Iterator(elem_ty), "next") => {
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

    /// Resolve a method call and record the resolution for codegen
    #[allow(dead_code)] // Will be used in future tasks
    pub(crate) fn resolve_method_call(
        &mut self,
        object_type: &Type,
        method_name: Symbol,
        call_node_id: NodeId,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        let method_str = interner.resolve(method_name);

        // 1. Check built-in methods (array/string.length)
        if let Some(return_type) = self.check_builtin_method_for_resolution(object_type, method_str)
        {
            let resolved = ResolvedMethod::Implemented {
                trait_name: None, // Will be Sized eventually
                func_type: FunctionType {
                    params: vec![],
                    return_type: Box::new(return_type),
                    is_closure: false,
                },
                is_builtin: true,
                external_info: None,
            };
            self.method_resolutions
                .insert(call_node_id, resolved.clone());
            return Some(resolved);
        }

        // 2. Check direct methods on type (classes/records)
        let type_sym = match object_type {
            Type::Class(c) => Some(c.name),
            Type::Record(r) => Some(r.name),
            _ => None,
        };

        if let Some(ts) = type_sym
            && let Some(func_type) = self.methods.get(&(ts, method_name)).cloned()
        {
            let resolved = ResolvedMethod::Direct { func_type };
            self.method_resolutions
                .insert(call_node_id, resolved.clone());
            return Some(resolved);
        }

        // 3. Check implement registry
        if let Some(type_id) = TypeId::from_type(object_type)
            && let Some(impl_) = self.implement_registry.get_method(&type_id, method_name)
        {
            let resolved = ResolvedMethod::Implemented {
                trait_name: impl_.trait_name,
                func_type: impl_.func_type.clone(),
                is_builtin: impl_.is_builtin,
                external_info: impl_.external_info.clone(),
            };
            self.method_resolutions
                .insert(call_node_id, resolved.clone());
            return Some(resolved);
        }

        None
    }

    /// Simple check for builtin methods, returns return type if found
    pub(crate) fn check_builtin_method_for_resolution(
        &self,
        object_type: &Type,
        method_name: &str,
    ) -> Option<Type> {
        match (object_type, method_name) {
            (Type::Array(_), "length") => Some(Type::I64),
            (Type::Array(elem_ty), "iter") => Some(Type::Iterator(elem_ty.clone())),
            (Type::Iterator(elem_ty), "next") => {
                Some(Type::Union(vec![*elem_ty.clone(), Type::Done]))
            }
            (Type::String, "length") => Some(Type::I64),
            _ => None,
        }
    }

    /// Get the function type for a functional interface (single abstract method, no fields)
    pub(crate) fn get_functional_interface_type(
        &self,
        interface_name: Symbol,
        interner: &Interner,
    ) -> Option<FunctionType> {
        let method = self
            .interface_registry
            .is_functional(interface_name, interner)?;
        Some(FunctionType {
            params: method.params.clone(),
            return_type: Box::new(method.return_type.clone()),
            is_closure: true,
        })
    }

    /// Check if a type structurally satisfies an interface
    ///
    /// This implements duck typing: a type satisfies an interface if it has
    /// all required fields and methods, regardless of explicit `implements`.
    pub fn satisfies_interface(
        &self,
        ty: &Type,
        interface_name: Symbol,
        interner: &Interner,
    ) -> bool {
        let Some(interface) = self.interface_registry.get(interface_name, interner) else {
            return false;
        };

        // Check required fields
        for field in &interface.fields {
            if !self.type_has_field(ty, field.name, &field.ty, interner) {
                return false;
            }
        }

        // Check required methods (skip those with defaults)
        for method in &interface.methods {
            if method.has_default {
                continue;
            }

            if !self.type_has_method(ty, method) {
                return false;
            }
        }

        // Check parent interfaces (extends)
        for parent in &interface.extends {
            if !self.satisfies_interface(ty, *parent, interner) {
                return false;
            }
        }

        true
    }

    /// Check if a type has a field with the given name and compatible type
    pub(crate) fn type_has_field(
        &self,
        ty: &Type,
        field_name: Symbol,
        expected_type: &Type,
        interner: &Interner,
    ) -> bool {
        match ty {
            Type::Record(r) => r.fields.iter().any(|f| {
                f.name == field_name && self.types_compatible(&f.ty, expected_type, interner)
            }),
            Type::Class(c) => c.fields.iter().any(|f| {
                f.name == field_name && self.types_compatible(&f.ty, expected_type, interner)
            }),
            _ => false,
        }
    }

    /// Check if a type has a method that matches the interface method signature
    pub(crate) fn type_has_method(&self, ty: &Type, interface_method: &InterfaceMethodDef) -> bool {
        // Get type symbol for method lookup
        let type_sym = match ty {
            Type::Record(r) => r.name,
            Type::Class(c) => c.name,
            _ => {
                // For primitives/arrays, check implement registry
                if let Some(type_id) = TypeId::from_type(ty) {
                    return self
                        .implement_registry
                        .get_method(&type_id, interface_method.name)
                        .is_some();
                }
                return false;
            }
        };

        // Check direct methods on the type
        let method_key = (type_sym, interface_method.name);
        if self.methods.contains_key(&method_key) {
            return true;
        }

        // Check implement registry
        if let Some(type_id) = TypeId::from_type(ty)
            && self
                .implement_registry
                .get_method(&type_id, interface_method.name)
                .is_some()
        {
            return true;
        }

        false
    }

    /// Validate that a type satisfies an interface by having all required methods with correct signatures
    pub(crate) fn validate_interface_satisfaction(
        &mut self,
        type_name: Symbol,
        iface_name: Symbol,
        type_methods: &HashMap<Symbol, FunctionType>,
        span: Span,
        interner: &Interner,
    ) {
        if let Some(iface) = self.interface_registry.get(iface_name, interner).cloned() {
            // Check methods required by this interface
            for required in &iface.methods {
                if required.has_default {
                    continue;
                }
                match type_methods.get(&required.name) {
                    None => {
                        // Method is missing entirely
                        self.add_error(
                            SemanticError::InterfaceNotSatisfied {
                                type_name: interner.resolve(type_name).to_string(),
                                interface_name: interner.resolve(iface_name).to_string(),
                                method: interner.resolve(required.name).to_string(),
                                span: span.into(),
                            },
                            span,
                        );
                    }
                    Some(found_sig) => {
                        // Method exists, check signature
                        if !Self::signatures_match(required, found_sig) {
                            self.add_error(
                                SemanticError::InterfaceSignatureMismatch {
                                    interface_name: interner.resolve(iface_name).to_string(),
                                    method: interner.resolve(required.name).to_string(),
                                    expected: Self::format_method_signature(
                                        &required.params,
                                        &required.return_type,
                                    ),
                                    found: Self::format_method_signature(
                                        &found_sig.params,
                                        &found_sig.return_type,
                                    ),
                                    span: span.into(),
                                },
                                span,
                            );
                        }
                    }
                }
            }
            // Check parent interfaces (extends)
            for parent_iface in &iface.extends {
                self.validate_interface_satisfaction(
                    type_name,
                    *parent_iface,
                    type_methods,
                    span,
                    interner,
                );
            }
        }
    }

    /// Get all method signatures for a type (from direct methods + implement blocks)
    pub(crate) fn get_type_method_signatures(
        &self,
        type_name: Symbol,
    ) -> HashMap<Symbol, FunctionType> {
        let mut method_sigs = HashMap::new();

        // Methods defined directly on the type
        for ((ty, method_name), func_type) in &self.methods {
            if *ty == type_name {
                method_sigs.insert(*method_name, func_type.clone());
            }
        }

        // Methods from implement blocks
        if let Some(type_id) = self
            .records
            .get(&type_name)
            .map(|_| TypeId::Record(type_name))
            .or_else(|| {
                self.classes
                    .get(&type_name)
                    .map(|_| TypeId::Class(type_name))
            })
        {
            for (method_name, method_impl) in self.implement_registry.get_methods_for_type(&type_id)
            {
                method_sigs.insert(method_name, method_impl.func_type.clone());
            }
        }

        method_sigs
    }

    /// Check if a method signature matches an interface requirement
    pub(crate) fn signatures_match(required: &InterfaceMethodDef, found: &FunctionType) -> bool {
        // Check parameter count
        if required.params.len() != found.params.len() {
            return false;
        }
        // Check parameter types
        for (req_param, found_param) in required.params.iter().zip(found.params.iter()) {
            if req_param != found_param {
                return false;
            }
        }
        // Check return type
        required.return_type == *found.return_type
    }

    /// Format a method signature for error messages
    pub(crate) fn format_method_signature(params: &[Type], return_type: &Type) -> String {
        let params_str: Vec<String> = params.iter().map(|t| t.to_string()).collect();
        format!("({}) -> {}", params_str.join(", "), return_type)
    }
}
