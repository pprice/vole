// src/sema/analyzer/declarations.rs
//! Declaration signature collection (Pass 1 of semantic analysis).

use super::*;
use crate::entity_defs::{GenericFuncInfo, GenericTypeInfo, TypeDefKind};
use crate::generic::TypeConstraint;
use crate::type_arena::{InternedStructural, TypeId as ArenaTypeId, TypeIdVec};
use vole_frontend::ast::{ExprKind, FieldDef as AstFieldDef, LetInit, TypeExpr, TypeMapping};

/// Extract the base interface name from a TypeExpr.
/// For `Iterator` returns `Iterator`, for `Iterator<i64>` returns `Iterator`.
/// For `mod.Interface` returns the last segment `Interface`.
fn interface_base_name(type_expr: &TypeExpr) -> Option<Symbol> {
    match type_expr {
        TypeExpr::Named(sym) => Some(*sym),
        TypeExpr::Generic { name, .. } => Some(*name),
        TypeExpr::QualifiedPath { segments, .. } => segments.last().copied(),
        _ => None,
    }
}

/// Check if a TypeExpr is a qualified path (mod.Interface).
fn is_qualified_path(type_expr: &TypeExpr) -> bool {
    matches!(type_expr, TypeExpr::QualifiedPath { .. })
}

/// Format a TypeExpr for error messages.
fn format_type_expr(type_expr: &TypeExpr, interner: &Interner) -> String {
    match type_expr {
        TypeExpr::Named(sym) => interner.resolve(*sym).to_string(),
        TypeExpr::Generic { name, args } => {
            let args_str: Vec<String> =
                args.iter().map(|a| format_type_expr(a, interner)).collect();
            format!("{}<{}>", interner.resolve(*name), args_str.join(", "))
        }
        TypeExpr::QualifiedPath { segments, args } => {
            let path_str: String = segments
                .iter()
                .map(|s| interner.resolve(*s))
                .collect::<Vec<_>>()
                .join(".");
            if args.is_empty() {
                path_str
            } else {
                let args_str: Vec<String> =
                    args.iter().map(|a| format_type_expr(a, interner)).collect();
                format!("{}<{}>", path_str, args_str.join(", "))
            }
        }
        _ => "unknown".to_string(),
    }
}

impl Analyzer {
    /// Build type parameters with resolved constraints.
    ///
    /// This performs the two-pass type parameter resolution pattern:
    /// 1. First pass: Create a name scope with all type params (constraint=None) for constraint resolution
    /// 2. Second pass: Resolve constraints using that scope, building the final TypeParamInfo list
    ///
    /// Returns a TypeParamScope containing the fully resolved type parameters.
    /// Use `scope.to_params()` to get a cloned Vec, or `scope.into_params()` to consume and get owned Vec.
    fn build_type_params_with_constraints(
        &mut self,
        ast_type_params: &[TypeParam],
        interner: &Interner,
    ) -> TypeParamScope {
        // First pass: create name_scope for constraint resolution
        // Type param constraints may reference other type params (e.g., T: Container<U>),
        // so we need all type param names available before resolving constraints.
        let name_scope = self.build_unconstrained_scope(ast_type_params, interner);

        // Second pass: resolve constraints with name_scope available, building final scope
        let type_params: Vec<TypeParamInfo> = ast_type_params
            .iter()
            .map(|tp| {
                let mut info = self.intern_type_param(tp, interner);
                info.constraint = tp.constraint.as_ref().and_then(|c| {
                    self.resolve_type_param_constraint(c, &name_scope, interner, tp.span)
                });
                info
            })
            .collect();

        TypeParamScope::from_params(type_params)
    }

    /// Create an unconstrained TypeParamInfo from an AST TypeParam.
    /// Interns the type param name as a NameId under the builtin module.
    fn intern_type_param(&mut self, tp: &TypeParam, interner: &Interner) -> TypeParamInfo {
        let builtin_mod = self.name_table_mut().builtin_module();
        let tp_name_str = interner.resolve(tp.name);
        let tp_name_id = self
            .name_table_mut()
            .intern_raw(builtin_mod, &[tp_name_str]);
        TypeParamInfo {
            name: tp.name,
            name_id: tp_name_id,
            constraint: None,
            type_param_id: None,
            variance: TypeParamVariance::default(),
        }
    }

    /// Build a TypeParamScope with unconstrained entries from AST type params.
    /// This is the first pass of type param resolution - names only, no constraints.
    /// Used when constraints aren't needed (e.g., building a name scope for structural type resolution).
    fn build_unconstrained_scope(
        &mut self,
        ast_type_params: &[TypeParam],
        interner: &Interner,
    ) -> TypeParamScope {
        let mut scope = TypeParamScope::new();
        for tp in ast_type_params {
            scope.add(self.intern_type_param(tp, interner));
        }
        scope
    }

    /// Extract type param NameIds from a scope and register them on an entity type.
    fn register_type_params_on_entity(
        &mut self,
        entity_type_id: TypeDefId,
        scope: &TypeParamScope,
    ) {
        let name_ids: Vec<NameId> = scope.params().iter().map(|tp| tp.name_id).collect();
        self.entity_registry_mut()
            .set_type_params(entity_type_id, name_ids);
    }

    /// Build type argument placeholder TypeIds from a type param scope.
    /// Each type param gets a `type_param(name_id)` entry in the arena.
    fn build_type_arg_placeholders(&mut self, scope: &TypeParamScope) -> Vec<ArenaTypeId> {
        scope
            .params()
            .iter()
            .map(|tp| self.type_arena_mut().type_param(tp.name_id))
            .collect()
    }

    /// Register a type shell (name and kind only, no fields/methods yet).
    /// This enables forward references - types can reference each other regardless of declaration order.
    ///
    /// If the type already exists in the registry (e.g., from a previous analysis of the same module
    /// in a shared cache scenario), returns the existing TypeDefId instead of creating a duplicate.
    fn register_type_shell(
        &mut self,
        name: Symbol,
        kind: TypeDefKind,
        interner: &Interner,
    ) -> TypeDefId {
        let name_id = self
            .name_table_mut()
            .intern(self.current_module, &[name], interner);

        // Check if type already exists (important for shared cache across test files)
        if let Some(existing_id) = self.entity_registry().type_by_name(name_id) {
            return existing_id;
        }

        self.entity_registry_mut()
            .register_type(name_id, kind, self.current_module)
    }

    /// Pass 0.5: Register all type shells so forward references work.
    /// Must be called before collect_signatures.
    pub(super) fn register_all_type_shells(&mut self, program: &Program, interner: &Interner) {
        for decl in &program.declarations {
            match decl {
                Decl::Class(c) => {
                    self.register_type_shell(c.name, TypeDefKind::Class, interner);
                }
                Decl::Struct(s) => {
                    self.register_type_shell(s.name, TypeDefKind::Struct, interner);
                }
                Decl::Interface(i) => {
                    self.register_type_shell(i.name, TypeDefKind::Interface, interner);
                }
                Decl::Sentinel(s) => {
                    self.register_type_shell(s.name, TypeDefKind::Sentinel, interner);
                }
                Decl::Let(l) => {
                    // Handle both new syntax (let T = SomeType) and legacy (let T: type = SomeType)
                    let is_type_alias = match &l.init {
                        LetInit::TypeAlias(_) => true,
                        LetInit::Expr(expr) => {
                            matches!(expr.kind, ExprKind::TypeLiteral(_))
                        }
                    };
                    if is_type_alias {
                        self.register_type_shell(l.name, TypeDefKind::Alias, interner);
                    }
                }
                _ => {}
            }
        }
    }

    /// Pass 1: Collect signatures for functions, classes, records, interfaces, and implement blocks
    pub(super) fn collect_signatures(&mut self, program: &Program, interner: &Interner) {
        self.collect_type_signatures(program, interner);
        self.collect_function_signatures(program, interner);
    }

    /// Collect signatures for type declarations: classes, records, interfaces, implement blocks, errors.
    pub(super) fn collect_type_signatures(&mut self, program: &Program, interner: &Interner) {
        for decl in &program.declarations {
            match decl {
                Decl::Class(class) => {
                    self.collect_class_signature(class, interner);
                }
                Decl::Struct(struct_decl) => {
                    self.collect_struct_signature(struct_decl, interner);
                }
                Decl::Interface(interface_decl) => {
                    self.collect_interface_def(interface_decl, interner);
                }
                Decl::Implement(impl_block) => {
                    self.collect_implement_block(impl_block, interner);
                }
                Decl::Error(decl) => {
                    self.analyze_error_decl(decl, interner);
                }
                Decl::Sentinel(sentinel_decl) => {
                    self.collect_sentinel_signature(sentinel_decl, interner);
                }
                _ => {}
            }
        }
    }

    /// Collect signatures for functions and external blocks.
    pub(super) fn collect_function_signatures(&mut self, program: &Program, interner: &Interner) {
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    self.collect_function_signature(func, interner);
                }
                Decl::External(ext_block) => {
                    self.collect_external_block(ext_block, interner);
                }
                _ => {}
            }
        }
    }

    /// Check if a TypeExpr resolves to a structural type, with type params in scope.
    /// This is needed when the structural type may reference explicit type parameters
    /// (e.g., `{ name: T }` where T is a type param).
    fn extract_structural_from_type_expr_with_scope(
        &self,
        ty: &TypeExpr,
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
    ) -> Option<InternedStructural> {
        match ty {
            TypeExpr::Structural {
                fields: _,
                methods: _,
            } => {
                // Direct structural type - resolve it to an InternedStructural
                let module_id = self.current_module;
                let mut ctx = if let Some(scope) = type_param_scope {
                    TypeResolutionContext::with_type_params(
                        &self.ctx.db,
                        interner,
                        module_id,
                        scope,
                    )
                } else {
                    TypeResolutionContext::new(&self.ctx.db, interner, module_id)
                };
                let type_id = resolve_type_to_id(ty, &mut ctx);
                self.type_arena().unwrap_structural(type_id).cloned()
            }
            TypeExpr::Named(sym) => {
                // Check if this named type is a type alias that resolves to a structural type
                let _name_str = interner.resolve(*sym);
                if let Some(type_def_id) = self
                    .resolver(interner)
                    .resolve_type(*sym, &self.entity_registry())
                {
                    let kind = self.entity_registry().type_kind(type_def_id);
                    let aliased_type = self.entity_registry().type_aliased(type_def_id);
                    if kind == TypeDefKind::Alias
                        && let Some(aliased_type_id) = aliased_type
                    {
                        return self
                            .type_arena()
                            .unwrap_structural(aliased_type_id)
                            .cloned();
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn collect_function_signature(&mut self, func: &FuncDecl, interner: &Interner) {
        let name_id = self
            .name_table_mut()
            .intern(self.current_module, &[func.name], interner);

        // Validate parameter default ordering: non-defaulted params must come before defaulted
        let required_params = self.validate_param_defaults(&func.params, interner);

        // Clone the default expressions for storage
        let param_defaults: Vec<Option<Box<Expr>>> = func
            .params
            .iter()
            .map(|p| p.default_value.clone())
            .collect();

        // Build initial type param scope from explicit type params (if any)
        // This is needed so that structural types like { name: T } can resolve T
        let explicit_type_param_scope: Option<TypeParamScope> = if !func.type_params.is_empty() {
            Some(self.build_unconstrained_scope(&func.type_params, interner))
        } else {
            None
        };

        // Check for parameters with structural types (duck typing)
        // These need implicit generification: func f(x: { name: string }) -> func f<__T0: { name: string }>(x: __T0)
        // Use the explicit type param scope so that structural types can reference type params like T
        let mut synthetic_type_params: Vec<(usize, InternedStructural)> = Vec::new();
        for (i, param) in func.params.iter().enumerate() {
            if let Some(structural) = self.extract_structural_from_type_expr_with_scope(
                &param.ty,
                interner,
                explicit_type_param_scope.as_ref(),
            ) {
                let func_name = interner.resolve(func.name);
                tracing::debug!(
                    ?func_name,
                    param_idx = i,
                    ?structural,
                    "implicit generification: found structural type param"
                );
                synthetic_type_params.push((i, structural));
            }
        }

        let has_explicit_type_params = !func.type_params.is_empty();
        let has_synthetic_type_params = !synthetic_type_params.is_empty();

        if !has_explicit_type_params && !has_synthetic_type_params {
            // Non-generic function: resolve types directly to TypeId
            let params_id: Vec<_> = func
                .params
                .iter()
                .map(|p| {
                    let type_id = self.resolve_type_id(&p.ty, interner);
                    self.check_never_not_allowed(type_id, p.span);
                    self.check_union_simplification(&p.ty, p.span);
                    self.check_combination_not_allowed(&p.ty, p.span);
                    type_id
                })
                .collect();
            let return_type_id = func
                .return_type
                .as_ref()
                .map(|t| self.resolve_type_id(t, interner))
                .unwrap_or_else(|| self.type_arena().void());
            if let Some(rt) = &func.return_type {
                self.check_union_simplification(rt, func.span);
                self.check_combination_not_allowed(rt, func.span);
            }

            let signature = FunctionType::from_ids(&params_id, return_type_id, false);

            self.functions.insert(func.name, signature.clone());

            // Register in EntityRegistry with default expressions
            self.entity_registry_mut().register_function_full(
                name_id,
                name_id, // For top-level functions, name_id == full_name_id
                self.current_module,
                signature,
                required_params,
                param_defaults,
            );
        } else {
            // Generic function (explicit or via implicit generification)
            // Build explicit type params with resolved constraints
            let mut type_param_scope =
                self.build_type_params_with_constraints(&func.type_params, interner);

            // Create synthetic type parameters for structural types in parameters
            // Map: param index -> synthetic type param name_id
            let builtin_mod = self.name_table_mut().builtin_module();
            let mut synthetic_param_map: FxHashMap<usize, NameId> = FxHashMap::default();
            for (i, (param_idx, structural)) in synthetic_type_params.into_iter().enumerate() {
                // Generate synthetic type param name like __T0, __T1, etc.
                let synthetic_name = format!("__T{}", i);
                let synthetic_name_id = self
                    .name_table_mut()
                    .intern_raw(builtin_mod, &[&synthetic_name]);

                // Create a synthetic Symbol for the type param
                // Use a high value that won't collide with user symbols.
                // This is safe because synthetic type params are never looked up by Symbol,
                // only by name_id during monomorphization/codegen.
                let synthetic_symbol = Symbol(0x8000_0000 + i as u32);

                tracing::debug!(
                    ?synthetic_name,
                    ?synthetic_name_id,
                    ?param_idx,
                    "created synthetic type param for structural constraint"
                );

                type_param_scope.add(TypeParamInfo {
                    name: synthetic_symbol,
                    name_id: synthetic_name_id,
                    constraint: Some(TypeConstraint::Structural(structural)),
                    type_param_id: None,
                    variance: TypeParamVariance::default(),
                });
                synthetic_param_map.insert(param_idx, synthetic_name_id);
            }

            // Resolve param types with type params in scope
            // For synthetic type params, use the type param instead of the structural type
            let module_id = self.current_module;
            let mut ctx = TypeResolutionContext::with_type_params(
                &self.ctx.db,
                interner,
                module_id,
                &type_param_scope,
            );

            let param_type_ids: Vec<ArenaTypeId> = func
                .params
                .iter()
                .enumerate()
                .map(|(i, p)| {
                    if let Some(&synthetic_name_id) = synthetic_param_map.get(&i) {
                        // Use the synthetic type parameter instead of the structural type
                        ctx.type_arena_mut().type_param(synthetic_name_id)
                    } else {
                        resolve_type_to_id(&p.ty, &mut ctx)
                    }
                })
                .collect();

            let return_type_id = func
                .return_type
                .as_ref()
                .map(|t| resolve_type_to_id(t, &mut ctx))
                .unwrap_or_else(|| self.type_arena().void());

            // Check that never is not used in function parameters (after ctx is no longer borrowed)
            for (param, &type_id) in func.params.iter().zip(&param_type_ids) {
                self.check_never_not_allowed(type_id, param.span);
                self.check_union_simplification(&param.ty, param.span);
                self.check_combination_not_allowed(&param.ty, param.span);
            }
            if let Some(rt) = &func.return_type {
                self.check_combination_not_allowed(rt, func.span);
            }

            // Create a FunctionType from TypeIds
            let signature = FunctionType::from_ids(&param_type_ids, return_type_id, false);

            // Register in EntityRegistry with default expressions
            let func_id = self.entity_registry_mut().register_function_full(
                name_id,
                name_id, // For top-level functions, name_id == full_name_id
                self.current_module,
                signature,
                required_params,
                param_defaults,
            );
            // Extract type params from scope (consumes scope, avoids clone)
            let type_params = type_param_scope.into_params();
            self.entity_registry_mut().set_function_generic_info(
                func_id,
                GenericFuncInfo {
                    type_params,
                    param_types: param_type_ids,
                    return_type: return_type_id,
                },
            );
        }
    }

    /// Validate parameter default ordering and count required params.
    /// Returns the number of required (non-defaulted) parameters.
    /// Emits errors if non-defaulted params come after defaulted params.
    fn validate_param_defaults(&mut self, params: &[Param], interner: &Interner) -> usize {
        let (required_count, _) = validate_defaults(params, interner, |name, span| {
            self.add_error(
                SemanticError::DefaultParamNotLast {
                    name,
                    span: span.into(),
                },
                span,
            );
        });
        required_count
    }

    /// Validate field default ordering and collect which fields have defaults.
    /// Returns a Vec<bool> indicating whether each field has a default.
    /// Emits errors if non-defaulted fields come after defaulted fields.
    fn validate_field_defaults(
        &mut self,
        fields: &[AstFieldDef],
        interner: &Interner,
    ) -> Vec<bool> {
        let (_, has_default_vec) = validate_defaults(fields, interner, |field, span| {
            self.add_error(
                SemanticError::RequiredFieldAfterDefaulted {
                    field,
                    span: span.into(),
                },
                span,
            );
        });
        has_default_vec
    }

    /// Build method name IDs for registration.
    /// Returns (method_name_id, full_method_name_id).
    fn build_method_names(
        &mut self,
        type_name: Symbol,
        method_name: Symbol,
        interner: &Interner,
    ) -> (NameId, NameId) {
        let builtin_mod = self.name_table_mut().builtin_module();
        let method_name_str = interner.resolve(method_name);
        let method_name_id = self
            .name_table_mut()
            .intern_raw(builtin_mod, &[method_name_str]);
        let type_name_str = interner.resolve(type_name);
        let full_method_name_id = self
            .name_table_mut()
            .intern_raw(self.current_module, &[type_name_str, method_name_str]);
        (method_name_id, full_method_name_id)
    }

    /// Build a method signature by resolving params and return type.
    /// Uses the provided type param scope and optional self_type for resolution.
    fn build_method_signature(
        &mut self,
        params: &[Param],
        return_type: &Option<TypeExpr>,
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
        self_type: Option<ArenaTypeId>,
    ) -> ArenaTypeId {
        let module_id = self.current_module;
        let params_id: Vec<ArenaTypeId> = params
            .iter()
            .map(|p| {
                if let Some(scope) = type_param_scope {
                    let mut ctx = TypeResolutionContext::with_type_params(
                        &self.ctx.db,
                        interner,
                        module_id,
                        scope,
                    );
                    ctx.self_type = self_type;
                    resolve_type_to_id(&p.ty, &mut ctx)
                } else if let Some(self_type_id) = self_type {
                    self.resolve_type_id_with_self(&p.ty, interner, Some(self_type_id))
                } else {
                    self.resolve_type_id(&p.ty, interner)
                }
            })
            .collect();

        // Check that never is not used in method parameters
        for (param, &type_id) in params.iter().zip(&params_id) {
            self.check_never_not_allowed(type_id, param.span);
            self.check_union_simplification(&param.ty, param.span);
            self.check_combination_not_allowed(&param.ty, param.span);
        }

        let return_type_id = return_type
            .as_ref()
            .map(|t| {
                if let Some(scope) = type_param_scope {
                    let mut ctx = TypeResolutionContext::with_type_params(
                        &self.ctx.db,
                        interner,
                        module_id,
                        scope,
                    );
                    ctx.self_type = self_type;
                    resolve_type_to_id(t, &mut ctx)
                } else if let Some(self_type_id) = self_type {
                    self.resolve_type_id_with_self(t, interner, Some(self_type_id))
                } else {
                    self.resolve_type_id(t, interner)
                }
            })
            .unwrap_or_else(|| self.type_arena().void());

        FunctionType::from_ids(&params_id, return_type_id, false).intern(&mut self.type_arena_mut())
    }

    /// Validate a type expression and emit an error if it resolves to an unknown type.
    /// This is called during method registration to provide proper error messages
    /// for unknown types in method signatures.
    fn validate_type_annotation(
        &mut self,
        type_expr: &TypeExpr,
        span: Span,
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
    ) {
        // For TypeExpr::Named, check if the type is resolvable
        match type_expr {
            TypeExpr::Named(sym) => {
                let name_str = interner.resolve(*sym);
                // Skip primitive types, "void", and well-known sentinel types
                if matches!(name_str, "void" | "nil" | "Done") {
                    return;
                }
                // Check if it's a type parameter in scope
                if let Some(scope) = type_param_scope
                    && scope.get(*sym).is_some()
                {
                    return;
                }
                // Check from type_param_stack too
                if self
                    .type_param_stack
                    .current()
                    .is_some_and(|s| s.get(*sym).is_some())
                {
                    return;
                }
                // Try to resolve the type
                let resolved = self
                    .resolver(interner)
                    .resolve_type(*sym, &self.entity_registry());
                if resolved.is_none() {
                    self.add_error(
                        SemanticError::UnknownType {
                            name: name_str.to_string(),
                            span: span.into(),
                        },
                        span,
                    );
                }
            }
            TypeExpr::Generic { name, args } => {
                // Validate the base type
                self.validate_type_annotation(
                    &TypeExpr::Named(*name),
                    span,
                    interner,
                    type_param_scope,
                );
                // Validate type arguments
                for arg in args {
                    self.validate_type_annotation(arg, span, interner, type_param_scope);
                    // Check if type argument is a struct type (not allowed as generic args)
                    if let TypeExpr::Named(sym) = arg {
                        let resolved = self
                            .resolver(interner)
                            .resolve_type(*sym, &self.entity_registry());
                        if let Some(type_def_id) = resolved {
                            let kind = self.entity_registry().type_kind(type_def_id);
                            if kind == TypeDefKind::Struct || kind == TypeDefKind::Sentinel {
                                self.add_error(
                                    SemanticError::StructAsTypeArg {
                                        name: interner.resolve(*sym).to_string(),
                                        span: span.into(),
                                    },
                                    span,
                                );
                            }
                        }
                    }
                }
            }
            TypeExpr::Array(elem) | TypeExpr::Optional(elem) => {
                self.validate_type_annotation(elem, span, interner, type_param_scope);
            }
            TypeExpr::FixedArray { element, .. } => {
                self.validate_type_annotation(element, span, interner, type_param_scope);
            }
            TypeExpr::Tuple(elements) => {
                for elem in elements {
                    self.validate_type_annotation(elem, span, interner, type_param_scope);
                }
            }
            TypeExpr::Union(variants) => {
                for variant in variants {
                    self.validate_type_annotation(variant, span, interner, type_param_scope);
                    // Structs are allowed in unions via auto-boxing (v-7d4b)
                }
            }
            TypeExpr::Function {
                params,
                return_type,
            } => {
                for param in params {
                    self.validate_type_annotation(param, span, interner, type_param_scope);
                }
                self.validate_type_annotation(return_type, span, interner, type_param_scope);
            }
            TypeExpr::Fallible {
                success_type,
                error_type,
            } => {
                self.validate_type_annotation(success_type, span, interner, type_param_scope);
                self.validate_type_annotation(error_type, span, interner, type_param_scope);
            }
            // Primitives, SelfType, etc. don't need validation
            _ => {}
        }
    }

    /// Validate method parameter and return type annotations, emitting errors for unknown types.
    fn validate_method_types(
        &mut self,
        params: &[Param],
        return_type: &Option<TypeExpr>,
        func_span: Span,
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
    ) {
        for param in params {
            self.validate_type_annotation(&param.ty, param.span, interner, type_param_scope);
        }
        if let Some(ret_ty) = return_type {
            // Use the function span for return type errors since TypeExpr doesn't have its own span
            self.validate_type_annotation(ret_ty, func_span, interner, type_param_scope);
        }
    }

    /// Register an instance method from a FuncDecl.
    /// Used for class instance methods.
    fn register_instance_method(
        &mut self,
        entity_type_id: TypeDefId,
        type_name: Symbol,
        method: &FuncDecl,
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
        self_type: Option<ArenaTypeId>,
    ) {
        // Validate type annotations to emit errors for unknown types
        self.validate_method_types(
            &method.params,
            &method.return_type,
            method.span,
            interner,
            type_param_scope,
        );

        let (method_name_id, full_method_name_id) =
            self.build_method_names(type_name, method.name, interner);
        let signature_id = self.build_method_signature(
            &method.params,
            &method.return_type,
            interner,
            type_param_scope,
            self_type,
        );

        let required_params = self.validate_param_defaults(&method.params, interner);
        let param_defaults: Vec<Option<Box<Expr>>> = method
            .params
            .iter()
            .map(|p| p.default_value.clone())
            .collect();

        self.entity_registry_mut().register_method_with_defaults(
            entity_type_id,
            method_name_id,
            full_method_name_id,
            signature_id,
            false, // instance methods don't have defaults (implementation defaults)
            None,  // no external binding
            required_params,
            param_defaults,
        );
    }

    /// Register a static method from an InterfaceMethod.
    /// Used for class static methods.
    fn register_static_method_helper(
        &mut self,
        entity_type_id: TypeDefId,
        type_name: Symbol,
        method: &InterfaceMethod,
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
        method_type_params: Vec<TypeParamInfo>,
    ) {
        let (method_name_id, full_method_name_id) =
            self.build_method_names(type_name, method.name, interner);

        // Build merged scope if method has its own type params
        let merged_scope: Option<TypeParamScope>;
        let scope_for_resolution = if !method.type_params.is_empty() {
            let mut scope = type_param_scope
                .cloned()
                .unwrap_or_else(TypeParamScope::new);
            let method_scope = self.build_unconstrained_scope(&method.type_params, interner);
            scope.extend(method_scope.params());
            merged_scope = Some(scope);
            merged_scope.as_ref()
        } else {
            type_param_scope
        };

        // Validate type annotations to emit errors for unknown types
        // Must be after building merged_scope so method's own type params are in scope
        self.validate_method_types(
            &method.params,
            &method.return_type,
            method.span,
            interner,
            scope_for_resolution,
        );

        let signature_id = self.build_method_signature(
            &method.params,
            &method.return_type,
            interner,
            scope_for_resolution,
            None, // static methods don't have self
        );

        let has_default = method.is_default || method.body.is_some();
        let required_params = self.validate_param_defaults(&method.params, interner);
        let param_defaults: Vec<Option<Box<Expr>>> = method
            .params
            .iter()
            .map(|p| p.default_value.clone())
            .collect();

        self.entity_registry_mut()
            .register_static_method_with_defaults(
                entity_type_id,
                method_name_id,
                full_method_name_id,
                signature_id,
                has_default,
                None, // no external binding
                method_type_params,
                required_params,
                param_defaults,
            );
    }

    /// Build method type params with resolved constraints for a static method.
    fn build_method_type_params(
        &mut self,
        method: &InterfaceMethod,
        type_param_scope: Option<&TypeParamScope>,
        interner: &Interner,
    ) -> Vec<TypeParamInfo> {
        if method.type_params.is_empty() {
            return Vec::new();
        }

        // Build merged scope for constraint resolution (parent + method type params)
        let mut merged_scope = type_param_scope
            .cloned()
            .unwrap_or_else(TypeParamScope::new);
        let method_scope = self.build_unconstrained_scope(&method.type_params, interner);
        merged_scope.extend(method_scope.params());

        // Resolve constraints using merged scope
        method
            .type_params
            .iter()
            .map(|tp| {
                let mut info = self.intern_type_param(tp, interner);
                info.constraint = tp.constraint.as_ref().and_then(|c| {
                    self.resolve_type_param_constraint(c, &merged_scope, interner, tp.span)
                });
                info
            })
            .collect()
    }

    /// Register an external method from an ExternalFunc.
    /// Used for class external methods.
    fn register_external_method(
        &mut self,
        entity_type_id: TypeDefId,
        type_name: Symbol,
        func: &ExternalFunc,
        module_path: &str,
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
    ) {
        let (method_name_id, full_method_name_id) =
            self.build_method_names(type_name, func.vole_name, interner);
        let signature_id = self.build_method_signature(
            &func.params,
            &func.return_type,
            interner,
            type_param_scope,
            None, // external methods don't have self
        );

        let method_name_str = interner.resolve(func.vole_name);
        let native_name_str = func
            .native_name
            .clone()
            .unwrap_or_else(|| method_name_str.to_string());
        let builtin_mod = self.name_table_mut().builtin_module();

        self.entity_registry_mut().register_method_with_binding(
            entity_type_id,
            method_name_id,
            full_method_name_id,
            signature_id,
            false, // external methods don't have defaults
            Some(ExternalMethodInfo {
                module_path: self
                    .name_table_mut()
                    .intern_raw(builtin_mod, &[module_path]),
                native_name: self
                    .name_table_mut()
                    .intern_raw(builtin_mod, &[&native_name_str]),
            }),
        );
    }

    fn collect_class_signature(&mut self, class: &ClassDecl, interner: &Interner) {
        let name_id = self
            .name_table_mut()
            .intern(self.current_module, &[class.name], interner);

        // Dispatch to appropriate handler based on whether class is generic
        if class.type_params.is_empty() {
            self.collect_class_signature_non_generic(class, name_id, interner);
        } else {
            self.collect_class_signature_generic(class, name_id, interner);
        }
    }

    /// Collect signature for a non-generic class.
    fn collect_class_signature_non_generic(
        &mut self,
        class: &ClassDecl,
        name_id: NameId,
        interner: &Interner,
    ) {
        // Lookup shell registered in pass 0.5
        let entity_type_id = self
            .entity_registry_mut()
            .type_by_name(name_id)
            .expect("class shell registered in register_all_type_shells");

        // Skip if already processed (shared cache scenario)
        if self
            .entity_registry()
            .get_type(entity_type_id)
            .generic_info
            .is_some()
        {
            return;
        }

        // Validate field defaults and collect field info
        let field_has_default = self.validate_field_defaults(&class.fields, interner);
        let (field_names, field_type_ids) = self.collect_field_info(&class.fields, interner, None);

        // Set generic_info (with empty type_params for non-generic classes)
        self.entity_registry_mut().set_generic_info(
            entity_type_id,
            GenericTypeInfo {
                type_params: vec![],
                field_names: field_names.clone(),
                field_types: field_type_ids.clone(),
                field_has_default,
            },
        );

        // Register fields in EntityRegistry
        self.register_type_fields(
            entity_type_id,
            class.name,
            &class.fields,
            &field_names,
            &field_type_ids,
            interner,
        );

        // Register and validate implements list
        self.validate_and_register_implements(
            entity_type_id,
            &class.implements,
            class.span,
            interner,
        );

        // Build self_type_id for method signatures
        let self_type_id = self
            .type_arena_mut()
            .class(entity_type_id, TypeIdVec::new());
        self.entity_registry_mut()
            .set_base_type_id(entity_type_id, self_type_id);

        // Register all methods
        self.register_class_methods(
            entity_type_id,
            class,
            interner,
            None, // no type param scope
            self_type_id,
        );
    }

    /// Collect signature for a generic class.
    fn collect_class_signature_generic(
        &mut self,
        class: &ClassDecl,
        name_id: NameId,
        interner: &Interner,
    ) {
        // Validate field defaults
        let field_has_default = self.validate_field_defaults(&class.fields, interner);

        // Build type params with resolved constraints
        let type_param_scope =
            self.build_type_params_with_constraints(&class.type_params, interner);

        // Collect field info with type params in scope
        let (field_names, field_type_ids) =
            self.collect_field_info(&class.fields, interner, Some(&type_param_scope));

        // Lookup shell registered in pass 0.5
        let entity_type_id = self
            .entity_registry_mut()
            .type_by_name(name_id)
            .expect("class shell registered in register_all_type_shells");

        // Skip if already processed (shared cache scenario)
        if self
            .entity_registry()
            .get_type(entity_type_id)
            .generic_info
            .is_some()
        {
            return;
        }

        // Set type params on the type definition (needed for method substitutions)
        self.register_type_params_on_entity(entity_type_id, &type_param_scope);

        // Set generic info for type inference during struct literal checking
        // Use to_params() since we still need type_param_scope below
        self.entity_registry_mut().set_generic_info(
            entity_type_id,
            GenericTypeInfo {
                type_params: type_param_scope.to_params(),
                field_names: field_names.clone(),
                field_types: field_type_ids.clone(),
                field_has_default,
            },
        );

        // Register fields with placeholder types
        self.register_type_fields(
            entity_type_id,
            class.name,
            &class.fields,
            &field_names,
            &field_type_ids,
            interner,
        );

        // Register and validate implements list
        self.validate_and_register_implements(
            entity_type_id,
            &class.implements,
            class.span,
            interner,
        );

        // Build self_type_id with type param placeholders
        let type_arg_ids = self.build_type_arg_placeholders(&type_param_scope);
        let self_type_id = self.type_arena_mut().class(entity_type_id, type_arg_ids);
        let base_type_id = self
            .type_arena_mut()
            .class(entity_type_id, TypeIdVec::new());
        self.entity_registry_mut()
            .set_base_type_id(entity_type_id, base_type_id);

        // Register all methods with type params in scope
        self.register_class_methods(
            entity_type_id,
            class,
            interner,
            Some(&type_param_scope),
            self_type_id,
        );
    }

    /// Collect field names and types for a class.
    /// If type_param_scope is provided, resolves types with type params in scope.
    fn collect_field_info(
        &mut self,
        fields: &[AstFieldDef],
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
    ) -> (Vec<NameId>, Vec<ArenaTypeId>) {
        let builtin_mod = self.name_table_mut().builtin_module();

        // Convert Symbol field names to NameId
        let field_names: Vec<NameId> = fields
            .iter()
            .map(|f| {
                let name_str = interner.resolve(f.name);
                self.name_table_mut().intern_raw(builtin_mod, &[name_str])
            })
            .collect();

        // Resolve field types (with or without type params)
        let field_type_ids: Vec<ArenaTypeId> = if let Some(scope) = type_param_scope {
            let module_id = self.current_module;
            let mut ctx =
                TypeResolutionContext::with_type_params(&self.ctx.db, interner, module_id, scope);
            fields
                .iter()
                .map(|f| resolve_type_to_id(&f.ty, &mut ctx))
                .collect()
        } else {
            fields
                .iter()
                .map(|f| self.resolve_type_id(&f.ty, interner))
                .collect()
        };

        // Check that never is not used in class fields
        for (field, &type_id) in fields.iter().zip(&field_type_ids) {
            self.check_never_not_allowed(type_id, field.span);
            self.check_union_simplification(&field.ty, field.span);
            self.check_combination_not_allowed(&field.ty, field.span);
        }

        (field_names, field_type_ids)
    }

    /// Register fields in the EntityRegistry for a class.
    fn register_type_fields(
        &mut self,
        entity_type_id: TypeDefId,
        type_name: Symbol,
        fields: &[AstFieldDef],
        field_names: &[NameId],
        field_type_ids: &[ArenaTypeId],
        interner: &Interner,
    ) {
        for (i, field) in fields.iter().enumerate() {
            let field_name_str = interner.resolve(field.name);
            let full_field_name_id = self.name_table_mut().intern_raw(
                self.current_module,
                &[interner.resolve(type_name), field_name_str],
            );
            self.entity_registry_mut().register_field(
                entity_type_id,
                field_names[i],
                full_field_name_id,
                field_type_ids[i],
                i,
            );
        }
    }

    /// Register all methods (instance, static, external) for a class.
    fn register_class_methods(
        &mut self,
        entity_type_id: TypeDefId,
        class: &ClassDecl,
        interner: &Interner,
        type_param_scope: Option<&TypeParamScope>,
        self_type_id: ArenaTypeId,
    ) {
        // Register instance methods
        for method in &class.methods {
            self.register_instance_method(
                entity_type_id,
                class.name,
                method,
                interner,
                type_param_scope,
                Some(self_type_id),
            );
        }

        // Register static methods
        if let Some(ref statics) = class.statics {
            for method in &statics.methods {
                let method_type_params =
                    self.build_method_type_params(method, type_param_scope, interner);
                self.register_static_method_helper(
                    entity_type_id,
                    class.name,
                    method,
                    interner,
                    type_param_scope,
                    method_type_params,
                );
            }
        }

        // Register external methods
        if let Some(ref external) = class.external {
            for func in &external.functions {
                self.register_external_method(
                    entity_type_id,
                    class.name,
                    func,
                    &external.module_path,
                    interner,
                    type_param_scope,
                );
            }
        }
    }

    /// Collect the signature for a struct declaration (non-generic, no methods).
    fn collect_struct_signature(&mut self, struct_decl: &StructDecl, interner: &Interner) {
        let name_id =
            self.name_table_mut()
                .intern(self.current_module, &[struct_decl.name], interner);

        let entity_type_id = self
            .entity_registry_mut()
            .type_by_name(name_id)
            .expect("struct shell registered in register_all_type_shells");

        // Skip if already processed (shared cache scenario)
        if self
            .entity_registry()
            .get_type(entity_type_id)
            .generic_info
            .is_some()
        {
            return;
        }

        // Validate field defaults and collect field info
        let field_has_default = self.validate_field_defaults(&struct_decl.fields, interner);
        let (field_names, field_type_ids) =
            self.collect_field_info(&struct_decl.fields, interner, None);

        // Set generic_info (with empty type_params for non-generic structs)
        self.entity_registry_mut().set_generic_info(
            entity_type_id,
            GenericTypeInfo {
                type_params: vec![],
                field_names: field_names.clone(),
                field_types: field_type_ids.clone(),
                field_has_default,
            },
        );

        // Register fields in EntityRegistry
        self.register_type_fields(
            entity_type_id,
            struct_decl.name,
            &struct_decl.fields,
            &field_names,
            &field_type_ids,
            interner,
        );

        // Register the struct's base TypeId
        let self_type_id = self
            .type_arena_mut()
            .struct_type(entity_type_id, TypeIdVec::new());
        self.entity_registry_mut()
            .set_base_type_id(entity_type_id, self_type_id);

        // Register instance methods
        for method in &struct_decl.methods {
            self.register_instance_method(
                entity_type_id,
                struct_decl.name,
                method,
                interner,
                None, // no type_param_scope for non-generic structs
                Some(self_type_id),
            );
        }

        // Register static methods
        if let Some(ref statics) = struct_decl.statics {
            for method in &statics.methods {
                let method_type_params = self.build_method_type_params(method, None, interner);
                self.register_static_method_helper(
                    entity_type_id,
                    struct_decl.name,
                    method,
                    interner,
                    None, // no type_param_scope for non-generic structs
                    method_type_params,
                );
            }
        }
    }

    /// Collect the signature for a sentinel declaration (zero-field struct).
    fn collect_sentinel_signature(&mut self, sentinel_decl: &SentinelDecl, interner: &Interner) {
        let name_id =
            self.name_table_mut()
                .intern(self.current_module, &[sentinel_decl.name], interner);

        let entity_type_id = self
            .entity_registry_mut()
            .type_by_name(name_id)
            .expect("sentinel shell registered in register_all_type_shells");

        // Skip if already processed (shared cache scenario)
        if self
            .entity_registry()
            .get_type(entity_type_id)
            .generic_info
            .is_some()
        {
            return;
        }

        // Set generic_info with empty everything (zero-field struct)
        self.entity_registry_mut().set_generic_info(
            entity_type_id,
            GenericTypeInfo {
                type_params: vec![],
                field_names: vec![],
                field_types: vec![],
                field_has_default: vec![],
            },
        );

        // Check if this is a well-known sentinel (Done or nil) that has a reserved TypeId.
        // If so, rebind the reserved slot to point to the sentinel's struct type instead
        // of creating a new TypeId. This ensures TypeId::DONE and TypeId::NIL remain the
        // canonical identifiers for these types.
        let sentinel_name = interner.resolve(sentinel_decl.name);
        let well_known_type_id = match sentinel_name {
            "Done" => Some(ArenaTypeId::DONE),
            "nil" => Some(ArenaTypeId::NIL),
            _ => None,
        };

        if let Some(reserved_id) = well_known_type_id {
            use crate::type_arena::SemaType;
            // Rebind the reserved TypeId slot to point to the sentinel's struct type
            self.type_arena_mut().rebind(
                reserved_id,
                SemaType::Struct {
                    type_def_id: entity_type_id,
                    type_args: TypeIdVec::new(),
                },
            );
            self.type_arena_mut().mark_sentinel(reserved_id);
            self.entity_registry_mut()
                .set_base_type_id(entity_type_id, reserved_id);
        } else {
            // Non-well-known sentinel: create a new TypeId as usual
            let self_type_id = self
                .type_arena_mut()
                .struct_type(entity_type_id, TypeIdVec::new());
            self.type_arena_mut().mark_sentinel(self_type_id);
            self.entity_registry_mut()
                .set_base_type_id(entity_type_id, self_type_id);
        }
    }

    /// Validate and register interface implementations for a type.
    /// Reports errors for unknown interfaces.
    fn validate_and_register_implements(
        &mut self,
        entity_type_id: TypeDefId,
        implements: &[TypeExpr],
        span: Span,
        interner: &Interner,
    ) {
        for iface_type in implements {
            let Some(iface_sym) = interface_base_name(iface_type) else {
                self.add_error(
                    SemanticError::UnknownInterface {
                        name: format_type_expr(iface_type, interner),
                        span: span.into(),
                    },
                    span,
                );
                continue;
            };

            let iface_str = interner.resolve(iface_sym);
            let Some(interface_type_id) = self
                .resolver(interner)
                .resolve_type_str_or_interface(iface_str, &self.entity_registry())
            else {
                self.add_error(
                    SemanticError::UnknownInterface {
                        name: format_type_expr(iface_type, interner),
                        span: span.into(),
                    },
                    span,
                );
                continue;
            };

            // Extract and resolve type arguments directly to TypeId
            let type_arg_ids: Vec<ArenaTypeId> = match iface_type {
                TypeExpr::Generic { args, .. } => args
                    .iter()
                    .map(|arg| self.resolve_type_id(arg, interner))
                    .collect(),
                _ => Vec::new(),
            };

            // Validate that type args match interface's type params
            let expected_count = self.entity_registry().type_params(interface_type_id).len();
            let found_count = type_arg_ids.len();
            if expected_count != found_count {
                self.add_error(
                    SemanticError::WrongTypeArgCount {
                        expected: expected_count,
                        found: found_count,
                        span: span.into(),
                    },
                    span,
                );
                continue;
            }
            self.entity_registry_mut().add_implementation(
                entity_type_id,
                interface_type_id,
                type_arg_ids.clone(),
            );

            // Register interface default methods on the implementing type
            // so that find_method_on_type works for inherited default methods.
            // Destructure db to allow simultaneous mutable access to entities and names.
            {
                let mut db = self.ctx.db.borrow_mut();
                let CompilationDb {
                    ref mut entities,
                    ref mut names,
                    ..
                } = *db;
                Rc::make_mut(entities).register_interface_default_methods_on_implementing_type(
                    entity_type_id,
                    interface_type_id,
                    names,
                );
            }

            // Pre-compute substituted method signatures for codegen's lookup_substitute
            self.precompute_interface_method_substitutions(interface_type_id, &type_arg_ids);
        }
    }

    fn collect_interface_def(&mut self, interface_decl: &InterfaceDecl, interner: &Interner) {
        // Build type params with resolved constraints
        let type_param_scope =
            self.build_type_params_with_constraints(&interface_decl.type_params, interner);

        // Use current_module for proper module-qualified NameIds
        let name_str = interner.resolve(interface_decl.name).to_string();
        let name_id = self
            .name_table_mut()
            .intern_raw(self.current_module, &[&name_str]);

        // Lookup shell registered in pass 0.5
        let entity_type_id = self
            .entity_registry_mut()
            .type_by_name(name_id)
            .expect("interface shell registered in register_all_type_shells");

        // Skip if already processed (e.g., from a previous analysis of the same module
        // in a shared cache scenario). Check if methods are already registered.
        if !self
            .entity_registry()
            .get_type(entity_type_id)
            .methods
            .is_empty()
        {
            return;
        }

        // Validate interface method type annotations
        for method in &interface_decl.methods {
            self.validate_method_types(
                &method.params,
                &method.return_type,
                method.span,
                interner,
                Some(&type_param_scope),
            );
        }

        let module_id = self.current_module;
        let mut type_ctx = TypeResolutionContext::with_type_params(
            &self.ctx.db,
            interner,
            module_id,
            &type_param_scope,
        );

        // Resolve field types directly to TypeId
        let resolved_fields: Vec<(Symbol, ArenaTypeId)> = interface_decl
            .fields
            .iter()
            .map(|f| (f.name, resolve_type_to_id(&f.ty, &mut type_ctx)))
            .collect();

        // Collect method names with default external bindings (from `default external` blocks)
        let default_external_methods: HashSet<Symbol> = interface_decl
            .external_blocks
            .iter()
            .filter(|ext| ext.is_default)
            .flat_map(|ext| ext.functions.iter().map(|f| f.vole_name))
            .collect();

        // Collect errors for methods with bodies that aren't marked as default
        let body_without_default_errors: Vec<_> = interface_decl
            .methods
            .iter()
            .filter(|m| {
                m.body.is_some() && !m.is_default && !default_external_methods.contains(&m.name)
            })
            .map(|m| (interner.resolve(m.name).to_string(), m.span))
            .collect();

        // Build interface_methods for Type and collect method data for EntityRegistry registration
        // We resolve types once to TypeId and reuse the data
        // Get void type before the loop to avoid borrowing db while type_ctx is borrowed
        let void_type = self.type_arena().void();
        let method_data: Vec<(Symbol, String, Vec<ArenaTypeId>, ArenaTypeId, bool)> =
            interface_decl
                .methods
                .iter()
                .map(|m| {
                    let name = m.name;
                    let name_str = interner.resolve(m.name).to_string();
                    let params_id: Vec<ArenaTypeId> = m
                        .params
                        .iter()
                        .map(|p| resolve_type_to_id(&p.ty, &mut type_ctx))
                        .collect();
                    let return_type_id = m
                        .return_type
                        .as_ref()
                        .map(|t| resolve_type_to_id(t, &mut type_ctx))
                        .unwrap_or(void_type);
                    let has_default = m.is_default
                        || m.body.is_some()
                        || default_external_methods.contains(&m.name);
                    (name, name_str, params_id, return_type_id, has_default)
                })
                .collect();

        let _interface_methods: Vec<crate::types::InterfaceMethodType> = method_data
            .iter()
            .map(|(name, _, params_id, return_type_id, has_default)| {
                let method_name_id = self.method_name_id(*name, interner);
                crate::types::InterfaceMethodType {
                    name: method_name_id,
                    has_default: *has_default,
                    params_id: params_id.iter().copied().collect(),
                    return_type_id: *return_type_id,
                }
            })
            .collect();

        // Emit errors for methods with bodies that aren't marked as default
        for (method_name, span) in body_without_default_errors {
            self.add_error(
                SemanticError::InterfaceMethodBodyWithoutDefault {
                    method: method_name,
                    span: span.into(),
                },
                span,
            );
        }

        // Collect method names for external block validation
        let method_names: HashSet<Symbol> = method_data.iter().map(|(name, ..)| *name).collect();

        let mut external_methods: FxHashMap<String, ExternalMethodInfo> = FxHashMap::default();
        for external in &interface_decl.external_blocks {
            for func in &external.functions {
                if !method_names.contains(&func.vole_name) {
                    let ty = interner.resolve(interface_decl.name).to_string();
                    let method = interner.resolve(func.vole_name).to_string();
                    self.add_error(
                        SemanticError::UnknownMethod {
                            ty,
                            method,
                            span: func.span.into(),
                        },
                        func.span,
                    );
                    continue;
                }
                let native_name_str = func
                    .native_name
                    .clone()
                    .unwrap_or_else(|| interner.resolve(func.vole_name).to_string());
                let method_name_str = interner.resolve(func.vole_name).to_string();
                // Extract name IDs before struct literal to avoid overlapping borrows
                let (module_path, native_name) = {
                    let builtin_mod = self.name_table_mut().builtin_module();
                    let mut name_table = self.name_table_mut();
                    (
                        name_table.intern_raw(builtin_mod, &[&external.module_path]),
                        name_table.intern_raw(builtin_mod, &[&native_name_str]),
                    )
                };
                external_methods.insert(
                    method_name_str,
                    ExternalMethodInfo {
                        module_path,
                        native_name,
                    },
                );
            }
        }

        // Set type parameters in EntityRegistry (using NameIds only)
        self.register_type_params_on_entity(entity_type_id, &type_param_scope);

        // Register extends relationships
        // Collect parent type IDs first (separate from mutation to avoid borrow conflicts)
        let extends_parents: Vec<(NameId, Option<TypeDefId>)> = interface_decl
            .extends
            .iter()
            .map(|&parent_sym| {
                let parent_str = interner.resolve(parent_sym);
                let parent_name_id = self
                    .name_table_mut()
                    .intern_raw(self.current_module, &[parent_str]);
                let parent_type_id = self.entity_registry().type_by_name(parent_name_id);
                (parent_name_id, parent_type_id)
            })
            .collect();
        let _extends_type_ids: Vec<TypeDefId> = extends_parents
            .into_iter()
            .filter_map(|(_, parent_type_id)| {
                if let Some(parent_type_id) = parent_type_id {
                    self.entity_registry_mut()
                        .add_extends(entity_type_id, parent_type_id);
                    Some(parent_type_id)
                } else {
                    None
                }
            })
            .collect();

        // Register methods in EntityRegistry (with external bindings)
        for (_, method_name_str, params_id, return_type_id, has_default) in &method_data {
            let builtin_mod = self.name_table_mut().builtin_module();
            let method_name_id = self
                .name_table_mut()
                .intern_raw(builtin_mod, &[method_name_str]);
            let full_method_name_id = self
                .name_table_mut()
                .intern_raw(self.current_module, &[&name_str, method_name_str]);
            let signature_id = FunctionType::from_ids(params_id, *return_type_id, false)
                .intern(&mut self.type_arena_mut());
            // Look up external binding for this method
            let external_binding = external_methods.get(method_name_str).copied();
            self.entity_registry_mut().register_method_with_binding(
                entity_type_id,
                method_name_id,
                full_method_name_id,
                signature_id,
                *has_default,
                external_binding,
            );
        }

        // Register static methods from statics block (if present)
        if let Some(ref statics_block) = interface_decl.statics {
            // Collect static method names with default external bindings
            let default_static_external_methods: HashSet<Symbol> = statics_block
                .external_blocks
                .iter()
                .filter(|ext| ext.is_default)
                .flat_map(|ext| ext.functions.iter().map(|f| f.vole_name))
                .collect();

            // Build external methods map for static methods
            let mut static_external_methods: FxHashMap<String, ExternalMethodInfo> =
                FxHashMap::default();
            for external in &statics_block.external_blocks {
                for func in &external.functions {
                    let native_name_str = func
                        .native_name
                        .clone()
                        .unwrap_or_else(|| interner.resolve(func.vole_name).to_string());
                    let method_name_str = interner.resolve(func.vole_name).to_string();
                    let builtin_mod = self.name_table_mut().builtin_module();
                    static_external_methods.insert(
                        method_name_str,
                        ExternalMethodInfo {
                            module_path: self
                                .name_table_mut()
                                .intern_raw(builtin_mod, &[&external.module_path]),
                            native_name: self
                                .name_table_mut()
                                .intern_raw(builtin_mod, &[&native_name_str]),
                        },
                    );
                }
            }

            // Register static methods
            for method in &statics_block.methods {
                let method_name_str = interner.resolve(method.name).to_string();
                let builtin_mod = self.name_table_mut().builtin_module();
                let method_name_id = self
                    .name_table_mut()
                    .intern_raw(builtin_mod, &[&method_name_str]);
                let full_method_name_id = self
                    .name_table_mut()
                    .intern_raw(self.current_module, &[&name_str, &method_name_str]);

                // Create a fresh type context for each static method
                let mut static_type_ctx = TypeResolutionContext::with_type_params(
                    &self.ctx.db,
                    interner,
                    module_id,
                    &type_param_scope,
                );

                let params_id: Vec<ArenaTypeId> = method
                    .params
                    .iter()
                    .map(|p| resolve_type_to_id(&p.ty, &mut static_type_ctx))
                    .collect();
                let return_type_id = method
                    .return_type
                    .as_ref()
                    .map(|t| resolve_type_to_id(t, &mut static_type_ctx))
                    .unwrap_or_else(|| self.type_arena().void());
                let has_default = method.is_default
                    || method.body.is_some()
                    || default_static_external_methods.contains(&method.name);

                let signature_id = FunctionType::from_ids(&params_id, return_type_id, false)
                    .intern(&mut self.type_arena_mut());

                let external_binding = static_external_methods.get(&method_name_str).copied();
                self.entity_registry_mut()
                    .register_static_method_with_binding(
                        entity_type_id,
                        method_name_id,
                        full_method_name_id,
                        signature_id,
                        has_default,
                        external_binding,
                        Vec::new(), // Interface static methods, no method type params
                    );
            }
        }

        // Register fields in EntityRegistry (for interface field requirements)
        for (i, (field_name, field_type_id)) in resolved_fields.iter().enumerate() {
            let field_name_str = interner.resolve(*field_name).to_string();
            let builtin_mod = self.name_table_mut().builtin_module();
            let field_name_id = self
                .name_table_mut()
                .intern_raw(builtin_mod, &[&field_name_str]);
            let full_field_name_id = self
                .name_table_mut()
                .intern_raw(self.current_module, &[&name_str, &field_name_str]);
            self.entity_registry_mut().register_field(
                entity_type_id,
                field_name_id,
                full_field_name_id,
                *field_type_id,
                i,
            );
        }
    }

    /// Resolve a qualified interface path like `mod.Interface` or `mod.Interface<T>`.
    /// Returns (interface_type_def_id, type_arg_exprs) if successful.
    /// The type_arg_exprs are left unresolved and should be resolved by the caller.
    /// For non-qualified paths, delegates to the standard resolver.
    fn resolve_interface_path<'a>(
        &self,
        trait_type: &'a TypeExpr,
        interner: &Interner,
    ) -> Option<(TypeDefId, &'a [TypeExpr])> {
        match trait_type {
            TypeExpr::QualifiedPath { segments, args } => {
                // Qualified path: mod.Interface or mod.sub.Interface
                if segments.is_empty() {
                    return None;
                }

                // First segment should be a module variable
                let first_sym = segments[0];
                let module_type_id = self.get_variable_type_id(first_sym)?;

                // Walk through the segments
                let mut current_type_id = module_type_id;
                for (i, &segment_sym) in segments.iter().enumerate().skip(1) {
                    let segment_name = interner.resolve(segment_sym);
                    let arena = self.type_arena();

                    // Must be a module type
                    let module_info = arena.unwrap_module(current_type_id);
                    let Some(module) = module_info else {
                        // Not a module - emit error (will be handled by caller)
                        return None;
                    };

                    // Find the export
                    let name_id = self.module_name_id(module.module_id, segment_name)?;
                    let export_type_id = module
                        .exports
                        .iter()
                        .find(|(n, _)| *n == name_id)
                        .map(|&(_, type_id)| type_id)?;

                    // Last segment should be an interface
                    if i == segments.len() - 1 {
                        // This should be an interface
                        let type_def_id = arena.type_def_id(export_type_id)?;

                        // Verify it's an interface (resolve through aliases if needed)
                        let kind = self.entity_registry().type_kind(type_def_id);
                        let aliased_type = self.entity_registry().type_aliased(type_def_id);

                        let final_type_def_id = if kind == TypeDefKind::Alias {
                            // For aliases, check the underlying type
                            if let Some(aliased_type_id) = aliased_type {
                                let arena = self.type_arena();
                                if let Some((underlying_def_id, _)) =
                                    arena.unwrap_interface(aliased_type_id)
                                {
                                    underlying_def_id
                                } else {
                                    return None; // Alias doesn't point to an interface
                                }
                            } else {
                                return None; // Alias has no underlying type
                            }
                        } else if kind == TypeDefKind::Interface {
                            type_def_id
                        } else {
                            return None; // Not an interface
                        };

                        // Return type args as references for caller to resolve
                        return Some((final_type_def_id, args.as_slice()));
                    } else {
                        // Not the last segment - must be a module
                        current_type_id = export_type_id;
                    }
                }
                None
            }
            TypeExpr::Named(sym) | TypeExpr::Generic { name: sym, .. } => {
                // Non-qualified: use standard resolver
                let iface_str = interner.resolve(*sym);
                let type_def_id = self
                    .resolver(interner)
                    .resolve_type_str_or_interface(iface_str, &self.entity_registry())?;

                // Verify it's an interface (resolve through aliases if needed)
                let kind = self.entity_registry().type_kind(type_def_id);
                let aliased_type = self.entity_registry().type_aliased(type_def_id);
                let final_type_def_id = if kind == TypeDefKind::Alias {
                    // For aliases, check the underlying type
                    if let Some(aliased_type_id) = aliased_type {
                        let arena = self.type_arena();
                        if let Some((underlying_def_id, _)) =
                            arena.unwrap_interface(aliased_type_id)
                        {
                            underlying_def_id
                        } else {
                            return None; // Alias doesn't point to an interface
                        }
                    } else {
                        return None; // Alias has no underlying type
                    }
                } else if kind == TypeDefKind::Interface {
                    type_def_id
                } else {
                    return None; // Not an interface
                };
                let type_def_id = final_type_def_id;

                // Return type args as references for caller to resolve
                let type_args: &[TypeExpr] = match trait_type {
                    TypeExpr::Generic { args, .. } => args.as_slice(),
                    _ => &[],
                };

                Some((type_def_id, type_args))
            }
            _ => None,
        }
    }

    fn collect_implement_block(&mut self, impl_block: &ImplementBlock, interner: &Interner) {
        // Extract trait name symbol from trait_type (if present)
        let trait_name = impl_block.trait_type.as_ref().and_then(interface_base_name);

        // Resolve interface from trait_type if specified
        let resolved_interface = impl_block
            .trait_type
            .as_ref()
            .and_then(|trait_type| self.resolve_interface_path(trait_type, interner));

        // Validate trait exists if specified
        if impl_block.trait_type.is_some() && resolved_interface.is_none() {
            let trait_type = impl_block.trait_type.as_ref().unwrap();

            // Provide more specific error for qualified paths
            if is_qualified_path(trait_type) {
                if let TypeExpr::QualifiedPath { segments, .. } = trait_type {
                    let first_sym = segments[0];
                    // Check if first segment is a module
                    if let Some(type_id) = self.get_variable_type_id(first_sym) {
                        if self.type_arena().unwrap_module(type_id).is_none() {
                            // First segment exists but is not a module
                            self.add_error(
                                SemanticError::ExpectedModule {
                                    name: interner.resolve(first_sym).to_string(),
                                    found: self.type_display_id(type_id),
                                    span: impl_block.span.into(),
                                },
                                impl_block.span,
                            );
                        } else {
                            // Module exists but interface not found in exports
                            self.add_error(
                                SemanticError::UnknownInterface {
                                    name: format_type_expr(trait_type, interner),
                                    span: impl_block.span.into(),
                                },
                                impl_block.span,
                            );
                        }
                    } else {
                        // First segment not found
                        self.add_error(
                            SemanticError::UndefinedVariable {
                                name: interner.resolve(first_sym).to_string(),
                                span: impl_block.span.into(),
                            },
                            impl_block.span,
                        );
                    }
                }
            } else {
                self.add_error(
                    SemanticError::UnknownInterface {
                        name: format_type_expr(trait_type, interner),
                        span: impl_block.span.into(),
                    },
                    impl_block.span,
                );
            }
        }

        let target_type_id = self.resolve_type_id(&impl_block.target_type, interner);

        // Validate target type exists
        if target_type_id.is_invalid() {
            let type_name = match &impl_block.target_type {
                TypeExpr::Named(sym) => interner.resolve(*sym).to_string(),
                _ => "unknown".to_string(),
            };
            self.add_error(
                SemanticError::UnknownImplementType {
                    name: type_name,
                    span: impl_block.span.into(),
                },
                impl_block.span,
            );
        }

        // Extract impl_type_id with borrow scoped to just this call
        let impl_type_id = {
            let arena = self.type_arena();
            ImplTypeId::from_type_id(target_type_id, &arena, &self.entity_registry())
        };

        if let Some(impl_type_id) = impl_type_id {
            // Get TypeDefId for the target type (for EntityRegistry updates)
            // Use impl_type_id.name_id() which we already have, avoiding name_id_for_type
            let entity_type_id = self
                .type_arena()
                .type_def_id(target_type_id)
                .or_else(|| self.entity_registry().type_by_name(impl_type_id.name_id()));

            // Get interface TypeDefId if implementing an interface
            // Use resolved_interface if available, otherwise fall back to trait_name lookup
            let (interface_type_id, interface_type_arg_exprs) =
                if let Some((id, args)) = resolved_interface {
                    (Some(id), args)
                } else if let Some(name) = trait_name {
                    let iface_str = interner.resolve(name);
                    let id = self
                        .resolver(interner)
                        .resolve_type_str_or_interface(iface_str, &self.entity_registry());
                    (id, &[] as &[TypeExpr])
                } else {
                    (None, &[] as &[TypeExpr])
                };

            // Resolve interface type arguments (e.g., <i64> from implement Producer<i64>)
            let interface_type_args: Vec<ArenaTypeId> = interface_type_arg_exprs
                .iter()
                .map(|arg| self.resolve_type_id(arg, interner))
                .collect();

            // Extract target type args (e.g., [i64] from Box<i64>)
            let target_type_args: Vec<ArenaTypeId> = {
                let arena = self.type_arena();
                arena
                    .unwrap_nominal(target_type_id)
                    .map(|(_, args, _)| args.to_vec())
                    .unwrap_or_default()
            };

            // Pre-register the implementation with type args so they're available
            // for validate_interface_satisfaction's substitution map
            if let Some(entity_type_id) = entity_type_id
                && let Some(iface_id) = interface_type_id
                && (!interface_type_args.is_empty() || !target_type_args.is_empty())
            {
                self.entity_registry_mut()
                    .add_implementation_with_target_args(
                        entity_type_id,
                        iface_id,
                        interface_type_args,
                        target_type_args,
                    );
            }

            for method in &impl_block.methods {
                // Validate type annotations to emit errors for unknown types
                self.validate_method_types(
                    &method.params,
                    &method.return_type,
                    method.span,
                    interner,
                    None,
                );

                // Use target_type_id as Self when resolving method signatures
                // This ensures `Self` in method params/return types resolves to the implementing type
                let params_id: Vec<ArenaTypeId> = method
                    .params
                    .iter()
                    .map(|p| self.resolve_type_id_with_self(&p.ty, interner, Some(target_type_id)))
                    .collect();
                let return_type_id = method
                    .return_type
                    .as_ref()
                    .map(|t| self.resolve_type_id_with_self(t, interner, Some(target_type_id)))
                    .unwrap_or_else(|| self.type_arena().void());
                let func_type = FunctionType::from_ids(&params_id, return_type_id, false);

                let method_name_id = self.method_name_id(method.name, interner);
                self.implement_registry_mut().register_method(
                    impl_type_id,
                    method_name_id,
                    MethodImpl {
                        trait_name,
                        func_type: func_type.clone(),
                        is_builtin: false,
                        external_info: None,
                    },
                );

                // Register in EntityRegistry.methods_by_type for all implement blocks
                // This enables codegen to look up method signatures via find_method_on_type
                if let Some(entity_type_id) = entity_type_id {
                    // Build full method name for entity registry
                    let type_name_str = match &impl_block.target_type {
                        TypeExpr::Named(sym) | TypeExpr::Generic { name: sym, .. } => {
                            interner.resolve(*sym).to_string()
                        }
                        TypeExpr::Primitive(prim) => {
                            let name_id = self.name_table().primitives.from_ast(*prim);
                            self.name_table().display(name_id)
                        }
                        _ => "unknown".to_string(),
                    };
                    let method_name_str = interner.resolve(method.name);
                    let full_method_name_id = self
                        .name_table_mut()
                        .intern_raw(self.current_module, &[&type_name_str, method_name_str]);

                    // Intern the signature in the arena
                    let signature_id = func_type.clone().intern(&mut self.type_arena_mut());

                    // Register the method in entity_registry.methods_by_type
                    self.entity_registry_mut().register_method(
                        entity_type_id,
                        method_name_id,
                        full_method_name_id,
                        signature_id,
                        false, // implement block methods don't have defaults
                    );

                    // Also add method binding if implementing an interface
                    if let Some(interface_type_id) = interface_type_id {
                        use crate::entity_defs::MethodBinding;
                        self.entity_registry_mut().add_method_binding(
                            entity_type_id,
                            interface_type_id,
                            MethodBinding {
                                method_name: method_name_id,
                                func_type,
                                is_builtin: false,
                                external_info: None,
                            },
                        );
                    }
                }
            }

            // Analyze external block if present
            if let Some(ref external) = impl_block.external {
                self.analyze_external_block(external, target_type_id, trait_name, interner);
            }

            // Register static methods from statics block (if present)
            if let Some(ref statics_block) = impl_block.statics {
                // Get entity type id for registering static methods
                // Use impl_type_id.name_id() which we already have
                let entity_type_id = self
                    .type_arena()
                    .type_def_id(target_type_id)
                    .or_else(|| self.entity_registry().type_by_name(impl_type_id.name_id()));

                if let Some(entity_type_id) = entity_type_id {
                    let type_name_str = match &impl_block.target_type {
                        TypeExpr::Named(sym) | TypeExpr::Generic { name: sym, .. } => {
                            interner.resolve(*sym).to_string()
                        }
                        TypeExpr::Primitive(prim) => {
                            let name_id = self.name_table().primitives.from_ast(*prim);
                            self.name_table_mut().display(name_id)
                        }
                        _ => "unknown".to_string(),
                    };

                    // Register static methods
                    for method in &statics_block.methods {
                        let method_name_str = interner.resolve(method.name).to_string();
                        let builtin_mod = self.name_table_mut().builtin_module();
                        let method_name_id = self
                            .name_table_mut()
                            .intern_raw(builtin_mod, &[&method_name_str]);
                        let full_method_name_id = self
                            .name_table_mut()
                            .intern_raw(self.current_module, &[&type_name_str, &method_name_str]);

                        let params_id: Vec<ArenaTypeId> = method
                            .params
                            .iter()
                            .map(|p| self.resolve_type_id(&p.ty, interner))
                            .collect();
                        let return_type_id = method
                            .return_type
                            .as_ref()
                            .map(|t| self.resolve_type_id(t, interner))
                            .unwrap_or_else(|| self.type_arena().void());

                        let signature_id =
                            FunctionType::from_ids(&params_id, return_type_id, false)
                                .intern(&mut self.type_arena_mut());

                        let required_params =
                            self.validate_param_defaults(&method.params, interner);
                        let param_defaults: Vec<Option<Box<Expr>>> = method
                            .params
                            .iter()
                            .map(|p| p.default_value.clone())
                            .collect();
                        self.entity_registry_mut()
                            .register_static_method_with_defaults(
                                entity_type_id,
                                method_name_id,
                                full_method_name_id,
                                signature_id,
                                false, // has_default refers to interface method default body
                                None,  // no external binding
                                Vec::new(), // implement block static methods, no method type params
                                required_params,
                                param_defaults,
                            );
                    }

                    // Register external static methods
                    for external in &statics_block.external_blocks {
                        for func in &external.functions {
                            let method_name_str = interner.resolve(func.vole_name).to_string();
                            let builtin_mod = self.name_table_mut().builtin_module();
                            let method_name_id = self
                                .name_table_mut()
                                .intern_raw(builtin_mod, &[&method_name_str]);
                            let full_method_name_id = self.name_table_mut().intern_raw(
                                self.current_module,
                                &[&type_name_str, &method_name_str],
                            );

                            let params_id: Vec<ArenaTypeId> = func
                                .params
                                .iter()
                                .map(|p| self.resolve_type_id(&p.ty, interner))
                                .collect();
                            let return_type_id = func
                                .return_type
                                .as_ref()
                                .map(|t| self.resolve_type_id(t, interner))
                                .unwrap_or_else(|| self.type_arena().void());

                            let signature_id =
                                FunctionType::from_ids(&params_id, return_type_id, false)
                                    .intern(&mut self.type_arena_mut());

                            let native_name_str = func
                                .native_name
                                .clone()
                                .unwrap_or_else(|| method_name_str.clone());
                            // Compute NameIds before calling entity_registry_mut to avoid borrow conflicts
                            let builtin_mod = self.name_table_mut().builtin_module();
                            let module_path_id = self
                                .name_table_mut()
                                .intern_raw(builtin_mod, &[&external.module_path]);
                            let native_name_id = self
                                .name_table_mut()
                                .intern_raw(builtin_mod, &[&native_name_str]);

                            self.entity_registry_mut()
                                .register_static_method_with_binding(
                                    entity_type_id,
                                    method_name_id,
                                    full_method_name_id,
                                    signature_id,
                                    false,
                                    Some(ExternalMethodInfo {
                                        module_path: module_path_id,
                                        native_name: native_name_id,
                                    }),
                                    Vec::new(), // External static methods, no method type params
                                );
                        }
                    }
                }
            }
        }
    }

    /// Register external block functions as top-level functions
    /// This is called for standalone external blocks (not inside implement blocks)
    fn collect_external_block(&mut self, ext_block: &ExternalBlock, interner: &Interner) {
        let builtin_mod = self.name_table_mut().builtin_module();

        for func in &ext_block.functions {
            // For generic external functions in prelude, use builtin_mod so they're globally accessible
            // (can be called from any module without import). For non-prelude modules, use the
            // current module so explicit import is required.
            let name_module = if !func.type_params.is_empty() && self.loading_prelude {
                builtin_mod
            } else {
                self.current_module
            };
            let name_id = self
                .name_table_mut()
                .intern(name_module, &[func.vole_name], interner);

            // Validate parameter default ordering and count required params
            let required_params = self.validate_param_defaults(&func.params, interner);

            // Clone the default expressions for storage
            let param_defaults: Vec<Option<Box<Expr>>> = func
                .params
                .iter()
                .map(|p| p.default_value.clone())
                .collect();

            // For generic external functions, set up type param scope and register with GenericFuncInfo
            if !func.type_params.is_empty() {
                // Build type params with resolved constraints
                let type_param_scope =
                    self.build_type_params_with_constraints(&func.type_params, interner);

                // Resolve with type params in scope
                let module_id = self.current_module;
                let mut ctx = TypeResolutionContext::with_type_params(
                    &self.ctx.db,
                    interner,
                    module_id,
                    &type_param_scope,
                );
                // Resolve directly to TypeId
                let param_type_ids: Vec<ArenaTypeId> = func
                    .params
                    .iter()
                    .map(|p| resolve_type_to_id(&p.ty, &mut ctx))
                    .collect();
                let return_type_id = func
                    .return_type
                    .as_ref()
                    .map(|t| resolve_type_to_id(t, &mut ctx))
                    .unwrap_or_else(|| self.type_arena().void());

                // Create signature from TypeIds
                let signature = FunctionType::from_ids(&param_type_ids, return_type_id, false);

                // Register in EntityRegistry with default expressions (like regular generic functions)
                let func_id = self.entity_registry_mut().register_function_full(
                    name_id,
                    name_id,
                    self.current_module,
                    signature.clone(),
                    required_params,
                    param_defaults,
                );
                // Extract type params from scope (consumes scope, avoids clone)
                let type_params = type_param_scope.into_params();
                self.entity_registry_mut().set_function_generic_info(
                    func_id,
                    GenericFuncInfo {
                        type_params,
                        param_types: param_type_ids,
                        return_type: return_type_id,
                    },
                );

                // NOTE: Don't register in self.functions for generic externals!
                // The call handler checks self.functions first without doing type inference.
                // Generic functions must go through EntityRegistry's generic_info path.

                // Store external info for codegen
                let name_str = interner.resolve(func.vole_name).to_string();

                // If the function has type_mappings, register as GenericExternalInfo
                if let Some(ref mappings) = func.type_mappings {
                    let module_path = self
                        .name_table_mut()
                        .intern_raw(builtin_mod, &[&ext_block.module_path]);

                    // Resolve each type mapping to TypeId
                    let type_mappings = self.resolve_type_mappings(mappings, interner);

                    self.implement_registry_mut().register_generic_external(
                        name_str,
                        GenericExternalInfo {
                            module_path,
                            type_mappings,
                        },
                    );
                } else {
                    // No type mappings, use the native_name as before
                    let native_name_str =
                        func.native_name.clone().unwrap_or_else(|| name_str.clone());
                    self.implement_registry_mut().register_external_func(
                        name_str,
                        ExternalMethodInfo {
                            module_path: self
                                .name_table_mut()
                                .intern_raw(builtin_mod, &[&ext_block.module_path]),
                            native_name: self
                                .name_table_mut()
                                .intern_raw(builtin_mod, &[&native_name_str]),
                        },
                    );
                }
            } else {
                // Non-generic external function
                let params_id: Vec<ArenaTypeId> = func
                    .params
                    .iter()
                    .map(|p| self.resolve_type_id(&p.ty, interner))
                    .collect();
                let return_type_id = func
                    .return_type
                    .as_ref()
                    .map(|t| self.resolve_type_id(t, interner))
                    .unwrap_or_else(|| self.type_arena().void());

                let func_type = FunctionType::from_ids(&params_id, return_type_id, false);

                // Register the function with its Vole name (Symbol)
                self.functions.insert(func.vole_name, func_type.clone());

                // Also register by string name for cross-interner lookups (prelude functions)
                let name_str = interner.resolve(func.vole_name).to_string();
                self.functions_by_name
                    .insert(name_str.clone(), func_type.clone());

                // Register in EntityRegistry with default expressions
                self.entity_registry_mut().register_function_full(
                    name_id,
                    name_id,
                    self.current_module,
                    func_type,
                    required_params,
                    param_defaults,
                );

                // Store the external info (module path and native name) for codegen
                let native_name_str = func.native_name.clone().unwrap_or_else(|| name_str.clone());
                // Extract name IDs before calling implement_registry_mut to avoid overlapping borrows
                let (module_path, native_name) = {
                    let mut name_table = self.name_table_mut();
                    (
                        name_table.intern_raw(builtin_mod, &[&ext_block.module_path]),
                        name_table.intern_raw(builtin_mod, &[&native_name_str]),
                    )
                };
                self.implement_registry_mut().register_external_func(
                    name_str,
                    ExternalMethodInfo {
                        module_path,
                        native_name,
                    },
                );
            }
        }
    }

    /// Resolve type mappings from a where block to TypeMappingEntry list.
    /// Each TypeMapping (AST) is converted to TypeMappingEntry (resolved TypeId + key).
    fn resolve_type_mappings(
        &mut self,
        mappings: &[TypeMapping],
        interner: &Interner,
    ) -> Vec<TypeMappingEntry> {
        mappings
            .iter()
            .map(|mapping| {
                let type_id = self.resolve_type_id(&mapping.type_expr, interner);
                TypeMappingEntry {
                    type_id,
                    intrinsic_key: mapping.intrinsic_key.clone(),
                }
            })
            .collect()
    }
}
