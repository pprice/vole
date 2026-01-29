// src/sema/analyzer/test_checking.rs
//
// Test block checking and related analysis passes:
// - check_tests / check_scoped_decl / is_assert_call
// - process_global_lets / collect_type_aliases / register_type_alias_id
// - check_type_body / validate_interfaces_for_type / TypeBodyDecl trait

use super::*;

/// Trait for type declarations (Class or Record) that share common checking logic.
/// This allows unified handling of field defaults, methods, statics, and interface validation.
pub(crate) trait TypeBodyDecl {
    fn name(&self) -> Symbol;
    fn type_params(&self) -> &[TypeParam];
    fn fields(&self) -> &[FieldDef];
    fn methods(&self) -> &[FuncDecl];
    fn statics(&self) -> Option<&StaticsBlock>;
    fn span(&self) -> Span;
}

impl TypeBodyDecl for ClassDecl {
    fn name(&self) -> Symbol {
        self.name
    }
    fn type_params(&self) -> &[TypeParam] {
        &self.type_params
    }
    fn fields(&self) -> &[FieldDef] {
        &self.fields
    }
    fn methods(&self) -> &[FuncDecl] {
        &self.methods
    }
    fn statics(&self) -> Option<&StaticsBlock> {
        self.statics.as_ref()
    }
    fn span(&self) -> Span {
        self.span
    }
}

impl TypeBodyDecl for RecordDecl {
    fn name(&self) -> Symbol {
        self.name
    }
    fn type_params(&self) -> &[TypeParam] {
        &self.type_params
    }
    fn fields(&self) -> &[FieldDef] {
        &self.fields
    }
    fn methods(&self) -> &[FuncDecl] {
        &self.methods
    }
    fn statics(&self) -> Option<&StaticsBlock> {
        self.statics.as_ref()
    }
    fn span(&self) -> Span {
        self.span
    }
}

impl Analyzer {
    pub(crate) fn collect_type_aliases(&mut self, program: &Program, interner: &Interner) {
        for decl in &program.declarations {
            if let Decl::Let(let_stmt) = decl {
                match &let_stmt.init {
                    LetInit::TypeAlias(type_expr) => {
                        let aliased_type_id = self.resolve_type_id(type_expr, interner);
                        self.register_type_alias_id(let_stmt.name, aliased_type_id, interner);
                    }
                    LetInit::Expr(init_expr) => {
                        // Legacy: handle let X: type = SomeType
                        if let ExprKind::TypeLiteral(type_expr) = &init_expr.kind {
                            let aliased_type_id = self.resolve_type_id(type_expr, interner);
                            self.register_type_alias_id(let_stmt.name, aliased_type_id, interner);
                        }
                    }
                }
            }
        }
    }

    /// Register a type alias in EntityRegistry
    pub(crate) fn register_type_alias_id(
        &mut self,
        name: Symbol,
        aliased_type_id: ArenaTypeId,
        interner: &Interner,
    ) {
        // Lookup shell registered in register_all_type_shells
        let name_id = self
            .name_table_mut()
            .intern(self.current_module, &[name], interner);
        let type_id = self
            .entity_registry_mut()
            .type_by_name(name_id)
            .expect("alias shell registered in register_all_type_shells");
        // Set the aliased type (uses TypeId directly as alias index key)
        self.entity_registry_mut()
            .set_aliased_type(type_id, aliased_type_id);
    }

    /// Process global let declarations (type check and add to scope)
    pub(crate) fn process_global_lets(
        &mut self,
        program: &Program,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        for decl in &program.declarations {
            if let Decl::Let(let_stmt) = decl {
                match &let_stmt.init {
                    LetInit::TypeAlias(_) => {
                        // Type aliases are already handled in collect_type_aliases
                    }
                    LetInit::Expr(init_expr) => {
                        // Skip imports - already handled in process_module_imports
                        if matches!(&init_expr.kind, ExprKind::Import(_)) {
                            continue;
                        }

                        // Check for ambiguous type alias: let Alias = TypeName
                        if let ExprKind::Identifier(ident_sym) = &init_expr.kind {
                            let ident_name = interner.resolve(*ident_sym);
                            if self
                                .resolver(interner)
                                .resolve_type(*ident_sym, &self.entity_registry())
                                .is_some()
                            {
                                let let_name = interner.resolve(let_stmt.name);
                                self.add_error(
                                    SemanticError::AmbiguousTypeAlias {
                                        name: let_name.to_string(),
                                        type_name: ident_name.to_string(),
                                        span: init_expr.span.into(),
                                    },
                                    init_expr.span,
                                );
                            }
                        }

                        let declared_type_id = let_stmt
                            .ty
                            .as_ref()
                            .map(|t| self.resolve_type_id(t, interner));

                        // Check that never is not used in variable declarations
                        if let Some(decl_type_id) = declared_type_id {
                            self.check_never_not_allowed(decl_type_id, let_stmt.span);
                        }
                        if let Some(ty) = &let_stmt.ty {
                            self.check_union_simplification(ty, let_stmt.span);
                        }

                        let init_type_id =
                            self.check_expr_expecting_id(init_expr, declared_type_id, interner)?;

                        // Check if trying to use void return value
                        if init_type_id == ArenaTypeId::VOID {
                            self.add_error(
                                SemanticError::VoidReturnUsed {
                                    span: init_expr.span.into(),
                                },
                                init_expr.span,
                            );
                        }

                        let var_type_id = declared_type_id.unwrap_or(init_type_id);

                        // If this is a type alias (RHS is a type expression), store it
                        if var_type_id == ArenaTypeId::METATYPE
                            && let ExprKind::TypeLiteral(type_expr) = &init_expr.kind
                        {
                            let aliased_type_id = self.resolve_type_id(type_expr, interner);
                            self.register_type_alias_id(let_stmt.name, aliased_type_id, interner);
                        }
                        self.globals.insert(let_stmt.name, var_type_id);
                        self.scope.define(
                            let_stmt.name,
                            Variable {
                                ty: var_type_id,
                                mutable: let_stmt.mutable,
                            },
                        );

                        // Track if this immutable global has a constant initializer
                        // This enables using it in other constant expressions (e.g., default params)
                        if !let_stmt.mutable && self.is_constant_expr(init_expr) {
                            self.constant_globals.insert(let_stmt.name);
                        }

                        // Register in entity registry for proper global variable tracking
                        let global_name_id = self.name_table_mut().intern(
                            self.current_module,
                            &[let_stmt.name],
                            interner,
                        );
                        self.entity_registry_mut().register_global(
                            global_name_id,
                            var_type_id,
                            self.current_module,
                            let_stmt.mutable,
                            init_expr.id,
                        );
                    }
                }
            }

            // Handle destructuring let declarations: let { x, y } = expr
            if let Decl::LetTuple(let_tuple) = decl {
                // Skip imports - already handled in process_module_imports
                if matches!(&let_tuple.init.kind, ExprKind::Import(_)) {
                    continue;
                }

                // Check the initializer expression
                let init_type_id = self.check_expr(&let_tuple.init, interner)?;
                self.check_destructure_pattern_id(
                    &let_tuple.pattern,
                    init_type_id,
                    let_tuple.mutable,
                    let_tuple.init.span,
                    interner,
                );
            }
        }
        Ok(())
    }

    /// Check field defaults, methods, and static methods for a type declaration.
    /// This is the common logic shared between Class and Record checking.
    pub(crate) fn check_type_body<T: TypeBodyDecl>(
        &mut self,
        decl: &T,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        let type_name = decl.name();

        // Set up type param scope for generic type methods
        let generic_type_params = if !decl.type_params().is_empty() {
            let name_id = self
                .name_table()
                .name_id(self.current_module, &[type_name], interner);
            name_id.and_then(|name_id| {
                let registry = self.entity_registry();
                registry
                    .type_by_name(name_id)
                    .and_then(|type_def_id| registry.get_generic_info(type_def_id))
                    .map(|gi| gi.type_params.clone())
            })
        } else {
            None
        };

        if let Some(ref type_params) = generic_type_params {
            let mut scope = TypeParamScope::new();
            for tp in type_params {
                scope.add(tp.clone());
            }
            self.type_param_stack.push_scope(scope);
        }

        // Type-check field default expressions
        {
            let name_id = self
                .name_table()
                .name_id(self.current_module, &[type_name], interner);
            let field_types = name_id.and_then(|name_id| {
                let registry = self.entity_registry();
                registry
                    .type_by_name(name_id)
                    .and_then(|type_def_id| registry.get_generic_info(type_def_id))
                    .map(|gi| gi.field_types.clone())
            });
            if let Some(field_types) = field_types {
                self.check_field_defaults(decl.fields(), &field_types, interner)?;
            }
        }

        // Check instance methods
        for method in decl.methods() {
            self.check_method(method, type_name, interner)?;
        }

        // Check static methods if present
        if let Some(statics) = decl.statics() {
            for method in &statics.methods {
                self.check_static_method(method, type_name, interner)?;
            }
        }

        // Pop type param scope after checking methods
        if generic_type_params.is_some() {
            self.type_param_stack.pop();
        }

        // Validate interface satisfaction
        self.validate_interfaces_for_type(type_name, decl.span(), interner);

        Ok(())
    }

    /// Validate that a type satisfies all its implemented interfaces.
    pub(crate) fn validate_interfaces_for_type(
        &mut self,
        type_name: Symbol,
        span: Span,
        interner: &Interner,
    ) {
        let maybe_type_def_id = {
            let name_id = self
                .name_table()
                .name_id(self.current_module, &[type_name], interner);
            name_id.and_then(|name_id| self.entity_registry().type_by_name(name_id))
        };

        if let Some(type_def_id) = maybe_type_def_id {
            let type_methods = self.get_type_method_signatures(type_name, interner);
            let interface_ids = self
                .entity_registry()
                .get_implemented_interfaces(type_def_id);

            for interface_id in interface_ids {
                let interface_name_id = self.entity_registry().name_id(interface_id);
                let iface_name_str = self.name_table().last_segment_str(interface_name_id);
                if let Some(iface_name_str) = iface_name_str
                    && let Some(iface_name) = interner.lookup(&iface_name_str)
                {
                    self.validate_interface_satisfaction(
                        type_name,
                        iface_name,
                        &type_methods,
                        span,
                        interner,
                    );
                }
            }
        }
    }

    pub(crate) fn check_tests(
        &mut self,
        tests_decl: &TestsDecl,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Create a scope for the tests block (scoped declarations live here)
        let module_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(module_scope);

        // Process scoped declarations
        for decl in &tests_decl.decls {
            self.check_scoped_decl(decl, interner)?;
        }

        // Check each test case (each gets its own child scope)
        for test_case in &tests_decl.tests {
            // Each test gets its own scope (child of tests block scope)
            let tests_block_scope = std::mem::take(&mut self.scope);
            self.scope = Scope::with_parent(tests_block_scope);

            // Tests implicitly return void
            let void_id = self.type_arena().void();
            let saved_ctx = self.enter_function_context(void_id);

            // Type check the test body
            let _body_info = self.check_func_body(&test_case.body, interner)?;

            // Restore to tests block scope
            if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                self.scope = parent;
            }
            self.exit_function_context(saved_ctx);
        }

        // Restore to module scope
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }

        Ok(())
    }

    /// Check a scoped declaration in a tests block
    pub(crate) fn check_scoped_decl(
        &mut self,
        decl: &Decl,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        match decl {
            Decl::Function(func) => {
                self.check_scoped_function(func, interner)?;
            }
            Decl::Let(let_stmt) => {
                // Process let like a local let (check init, add to scope)
                // We create a temporary Stmt::Let wrapper to reuse the existing logic
                let _ = self.check_stmt(&Stmt::Let(let_stmt.clone()), interner)?;
            }
            _ => {
                // record, class, interface, implement, error, external
                // TODO(vole-2vgz): Support these declaration types in tests blocks
                // For now, they will be silently ignored (types won't be visible)
            }
        }
        Ok(())
    }

    pub(crate) fn is_assert_call(&self, callee: &Expr, interner: &Interner) -> bool {
        if let ExprKind::Identifier(sym) = &callee.kind {
            interner.resolve(*sym) == "assert"
        } else {
            false
        }
    }
}
