// src/sema/analyzer.rs

use crate::errors::SemanticError;
use crate::frontend::*;
use crate::sema::implement_registry::{ImplementRegistry, MethodImpl, TypeId};
use crate::sema::interface_registry::{
    InterfaceDef, InterfaceFieldDef, InterfaceMethodDef, InterfaceRegistry,
};
use crate::sema::resolution::{MethodResolutions, ResolvedMethod};
use crate::sema::{
    ClassType, FunctionType, RecordType, StructField, Type,
    compatibility::{function_compatible_with_interface, literal_fits, types_compatible_core},
    resolve::{TypeResolutionContext, resolve_type},
    scope::{Scope, Variable},
};
use std::collections::{HashMap, HashSet};

/// Information about a captured variable during lambda analysis
#[derive(Debug, Clone)]
struct CaptureInfo {
    name: Symbol,
    is_mutable: bool, // Was the captured variable declared with `let mut`
    is_mutated: bool, // Does the lambda assign to this variable
}

/// A type error wrapping a miette-enabled SemanticError
#[derive(Debug, Clone)]
pub struct TypeError {
    pub error: SemanticError,
    pub span: Span,
}

impl TypeError {
    /// Create a new type error
    pub fn new(error: SemanticError, span: Span) -> Self {
        Self { error, span }
    }
}

pub struct Analyzer {
    scope: Scope,
    functions: HashMap<Symbol, FunctionType>,
    globals: HashMap<Symbol, Type>,
    current_function_return: Option<Type>,
    errors: Vec<TypeError>,
    /// Type overrides from flow-sensitive narrowing (e.g., after `if x is T`)
    type_overrides: HashMap<Symbol, Type>,
    /// Stack of lambda scopes for capture analysis. Each entry is a HashMap
    /// mapping captured variable names to their capture info.
    lambda_captures: Vec<HashMap<Symbol, CaptureInfo>>,
    /// Stack of sets tracking variables defined locally in each lambda
    /// (parameters and let bindings inside the lambda body)
    lambda_locals: Vec<HashSet<Symbol>>,
    /// Stack of side effect flags for currently analyzed lambdas
    lambda_side_effects: Vec<bool>,
    /// Type aliases: `let MyType = i32` stores MyType -> i32
    type_aliases: HashMap<Symbol, Type>,
    /// Registered class types
    classes: HashMap<Symbol, ClassType>,
    /// Registered record types
    records: HashMap<Symbol, RecordType>,
    /// Methods for classes/records: (type_symbol, method_name) -> FunctionType
    methods: HashMap<(Symbol, Symbol), FunctionType>,
    /// Resolved types for each expression node (for codegen)
    /// Maps expression node IDs to their resolved types, including narrowed types
    expr_types: HashMap<NodeId, Type>,
    /// Interface definitions registry
    pub interface_registry: InterfaceRegistry,
    /// Methods added via implement blocks
    pub implement_registry: ImplementRegistry,
    /// Resolved method calls for codegen
    pub method_resolutions: MethodResolutions,
    /// Tracks which interfaces each type implements: type_name -> [interface_names]
    type_implements: HashMap<Symbol, Vec<Symbol>>,
}

impl Analyzer {
    pub fn new(_file: &str, _source: &str) -> Self {
        let mut analyzer = Self {
            scope: Scope::new(),
            functions: HashMap::new(),
            globals: HashMap::new(),
            current_function_return: None,
            errors: Vec::new(),
            type_overrides: HashMap::new(),
            lambda_captures: Vec::new(),
            lambda_locals: Vec::new(),
            lambda_side_effects: Vec::new(),
            type_aliases: HashMap::new(),
            classes: HashMap::new(),
            records: HashMap::new(),
            methods: HashMap::new(),
            expr_types: HashMap::new(),
            interface_registry: InterfaceRegistry::new(),
            implement_registry: ImplementRegistry::new(),
            method_resolutions: MethodResolutions::new(),
            type_implements: HashMap::new(),
        };

        // Register built-in interfaces and implementations
        // NOTE: This is temporary - will eventually come from stdlib/traits.void
        analyzer.register_builtins();

        analyzer
    }

    /// Register built-in interfaces and their implementations
    /// NOTE: This is temporary - will eventually come from stdlib/traits.void
    fn register_builtins(&mut self) {
        // For now, just set up the registries - actual builtin methods
        // will be registered when we have the interner available in a later task
    }

    /// Helper to add a type error
    fn add_error(&mut self, error: SemanticError, span: Span) {
        self.errors.push(TypeError::new(error, span));
    }

    /// Helper to add a type mismatch error
    #[allow(dead_code)] // Will be used in subsequent refactor tasks
    fn type_mismatch(&mut self, expected: &str, found: &str, span: Span) {
        self.add_error(
            SemanticError::TypeMismatch {
                expected: expected.to_string(),
                found: found.to_string(),
                span: span.into(),
            },
            span,
        );
    }

    /// Get the collected type aliases (for use by codegen)
    pub fn type_aliases(&self) -> &HashMap<Symbol, Type> {
        &self.type_aliases
    }

    /// Take ownership of the type aliases (consuming self)
    pub fn into_type_aliases(self) -> HashMap<Symbol, Type> {
        self.type_aliases
    }

    /// Get the resolved expression types (for use by codegen)
    pub fn expr_types(&self) -> &HashMap<NodeId, Type> {
        &self.expr_types
    }

    /// Take ownership of the expression types (consuming self)
    pub fn into_expr_types(self) -> HashMap<NodeId, Type> {
        self.expr_types
    }

    /// Take ownership of type aliases, expression types, method resolutions, interface registry,
    /// and type_implements (consuming self)
    #[allow(clippy::type_complexity)]
    pub fn into_analysis_results(
        self,
    ) -> (
        HashMap<Symbol, Type>,
        HashMap<NodeId, Type>,
        MethodResolutions,
        InterfaceRegistry,
        HashMap<Symbol, Vec<Symbol>>,
    ) {
        (
            self.type_aliases,
            self.expr_types,
            self.method_resolutions,
            self.interface_registry,
            self.type_implements,
        )
    }

    /// Record the resolved type for an expression
    fn record_expr_type(&mut self, expr: &Expr, ty: Type) {
        self.expr_types.insert(expr.id, ty);
    }

    /// Check if we're currently inside a lambda
    fn in_lambda(&self) -> bool {
        !self.lambda_captures.is_empty()
    }

    /// Check if a symbol is a local variable in the current lambda
    fn is_lambda_local(&self, sym: Symbol) -> bool {
        if let Some(locals) = self.lambda_locals.last() {
            locals.contains(&sym)
        } else {
            false
        }
    }

    /// Add a local variable to the current lambda's locals set
    fn add_lambda_local(&mut self, sym: Symbol) {
        if let Some(locals) = self.lambda_locals.last_mut() {
            locals.insert(sym);
        }
    }

    /// Record a captured variable in the current lambda
    fn record_capture(&mut self, sym: Symbol, is_mutable: bool) {
        if let Some(captures) = self.lambda_captures.last_mut() {
            // Only add if not already captured
            captures.entry(sym).or_insert(CaptureInfo {
                name: sym,
                is_mutable,
                is_mutated: false,
            });
        }
    }

    /// Mark a captured variable as mutated
    fn mark_capture_mutated(&mut self, sym: Symbol) {
        if let Some(captures) = self.lambda_captures.last_mut()
            && let Some(info) = captures.get_mut(&sym)
        {
            info.is_mutated = true;
        }
    }

    /// Mark the current lambda as having side effects
    fn mark_lambda_has_side_effects(&mut self) {
        if let Some(flag) = self.lambda_side_effects.last_mut() {
            *flag = true;
        }
    }

    /// Get variable type with flow-sensitive overrides
    fn get_variable_type(&self, sym: Symbol) -> Option<Type> {
        // Check overrides first (for narrowed types inside if-blocks)
        if let Some(ty) = self.type_overrides.get(&sym) {
            return Some(ty.clone());
        }
        // Then check scope
        self.scope.get(sym).map(|v| v.ty.clone())
    }

    pub fn analyze(
        &mut self,
        program: &Program,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Pass 0: Collect type aliases first (so they're available for function signatures)
        // Type aliases are `let` statements where the RHS is a TypeLiteral
        for decl in &program.declarations {
            if let Decl::Let(let_stmt) = decl
                && let ExprKind::TypeLiteral(type_expr) = &let_stmt.init.kind
            {
                let aliased_type = self.resolve_type(type_expr);
                self.type_aliases.insert(let_stmt.name, aliased_type);
            }
        }

        // First pass: collect function signatures
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    let params: Vec<Type> = func
                        .params
                        .iter()
                        .map(|p| self.resolve_type(&p.ty))
                        .collect();
                    let return_type = func
                        .return_type
                        .as_ref()
                        .map(|t| self.resolve_type(t))
                        .unwrap_or(Type::Void);

                    self.functions.insert(
                        func.name,
                        FunctionType {
                            params,
                            return_type: Box::new(return_type),
                            is_closure: false, // Named functions are never closures
                        },
                    );
                }
                Decl::Tests(_) => {
                    // Tests don't need signatures in the first pass
                }
                Decl::Let(_) => {
                    // Let declarations are processed before the second pass
                }
                Decl::Class(class) => {
                    let fields: Vec<StructField> = class
                        .fields
                        .iter()
                        .enumerate()
                        .map(|(i, f)| StructField {
                            name: f.name,
                            ty: self.resolve_type(&f.ty),
                            slot: i,
                        })
                        .collect();
                    self.classes.insert(
                        class.name,
                        ClassType {
                            name: class.name,
                            fields,
                        },
                    );
                    // Register and validate implements list
                    if !class.implements.is_empty() {
                        for iface_sym in &class.implements {
                            if self.interface_registry.get(*iface_sym).is_none() {
                                self.add_error(
                                    SemanticError::UnknownInterface {
                                        name: interner.resolve(*iface_sym).to_string(),
                                        span: class.span.into(),
                                    },
                                    class.span,
                                );
                            }
                        }
                        self.type_implements
                            .insert(class.name, class.implements.clone());
                    }
                    // Register methods
                    for method in &class.methods {
                        let params: Vec<Type> = method
                            .params
                            .iter()
                            .map(|p| self.resolve_type(&p.ty))
                            .collect();
                        let return_type = method
                            .return_type
                            .as_ref()
                            .map(|t| self.resolve_type(t))
                            .unwrap_or(Type::Void);
                        self.methods.insert(
                            (class.name, method.name),
                            FunctionType {
                                params,
                                return_type: Box::new(return_type),
                                is_closure: false,
                            },
                        );
                    }
                }
                Decl::Record(record) => {
                    let fields: Vec<StructField> = record
                        .fields
                        .iter()
                        .enumerate()
                        .map(|(i, f)| StructField {
                            name: f.name,
                            ty: self.resolve_type(&f.ty),
                            slot: i,
                        })
                        .collect();
                    self.records.insert(
                        record.name,
                        RecordType {
                            name: record.name,
                            fields,
                        },
                    );
                    // Register and validate implements list
                    if !record.implements.is_empty() {
                        for iface_sym in &record.implements {
                            if self.interface_registry.get(*iface_sym).is_none() {
                                self.add_error(
                                    SemanticError::UnknownInterface {
                                        name: interner.resolve(*iface_sym).to_string(),
                                        span: record.span.into(),
                                    },
                                    record.span,
                                );
                            }
                        }
                        self.type_implements
                            .insert(record.name, record.implements.clone());
                    }
                    // Register methods
                    for method in &record.methods {
                        let params: Vec<Type> = method
                            .params
                            .iter()
                            .map(|p| self.resolve_type(&p.ty))
                            .collect();
                        let return_type = method
                            .return_type
                            .as_ref()
                            .map(|t| self.resolve_type(t))
                            .unwrap_or(Type::Void);
                        self.methods.insert(
                            (record.name, method.name),
                            FunctionType {
                                params,
                                return_type: Box::new(return_type),
                                is_closure: false,
                            },
                        );
                    }
                }
                Decl::Interface(interface_decl) => {
                    // Convert AST fields to InterfaceFieldDef
                    let fields: Vec<InterfaceFieldDef> = interface_decl
                        .fields
                        .iter()
                        .map(|f| InterfaceFieldDef {
                            name: f.name,
                            ty: self.resolve_type(&f.ty),
                        })
                        .collect();

                    // Convert AST methods to InterfaceMethodDef
                    let methods: Vec<InterfaceMethodDef> = interface_decl
                        .methods
                        .iter()
                        .map(|m| InterfaceMethodDef {
                            name: m.name,
                            params: m.params.iter().map(|p| self.resolve_type(&p.ty)).collect(),
                            return_type: m
                                .return_type
                                .as_ref()
                                .map(|t| self.resolve_type(t))
                                .unwrap_or(Type::Void),
                            has_default: m.body.is_some(),
                        })
                        .collect();

                    let def = InterfaceDef {
                        name: interface_decl.name,
                        extends: interface_decl.extends.clone(),
                        fields,
                        methods,
                    };

                    self.interface_registry.register(def);
                }
                Decl::Implement(impl_block) => {
                    // Validate trait exists if specified
                    if let Some(trait_name) = impl_block.trait_name {
                        if self.interface_registry.get(trait_name).is_none() {
                            self.add_error(
                                SemanticError::UnknownInterface {
                                    name: interner.resolve(trait_name).to_string(),
                                    span: impl_block.span.into(),
                                },
                                impl_block.span,
                            );
                        }
                    }

                    let target_type = self.resolve_type(&impl_block.target_type);

                    if let Some(type_id) = TypeId::from_type(&target_type) {
                        for method in &impl_block.methods {
                            let func_type = FunctionType {
                                params: method
                                    .params
                                    .iter()
                                    .map(|p| self.resolve_type(&p.ty))
                                    .collect(),
                                return_type: Box::new(
                                    method
                                        .return_type
                                        .as_ref()
                                        .map(|t| self.resolve_type(t))
                                        .unwrap_or(Type::Void),
                                ),
                                is_closure: false,
                            };

                            self.implement_registry.register_method(
                                type_id.clone(),
                                method.name,
                                MethodImpl {
                                    trait_name: impl_block.trait_name,
                                    func_type,
                                    is_builtin: false,
                                },
                            );
                        }
                    }
                }
            }
        }

        // Process global let declarations (type check and add to scope)
        for decl in &program.declarations {
            if let Decl::Let(let_stmt) = decl {
                let declared_type = let_stmt.ty.as_ref().map(|t| self.resolve_type(t));
                let init_type =
                    self.check_expr_expecting(&let_stmt.init, declared_type.as_ref(), interner)?;

                // Check if trying to use void return value
                if init_type == Type::Void {
                    self.add_error(
                        SemanticError::VoidReturnUsed {
                            span: let_stmt.init.span.into(),
                        },
                        let_stmt.init.span,
                    );
                }

                let var_type = declared_type.unwrap_or(init_type.clone());

                // If this is a type alias (RHS is a type expression), store it
                if var_type == Type::Type
                    && let ExprKind::TypeLiteral(type_expr) = &let_stmt.init.kind
                {
                    let aliased_type = self.resolve_type(type_expr);
                    self.type_aliases.insert(let_stmt.name, aliased_type);
                }

                self.globals.insert(let_stmt.name, var_type.clone());
                self.scope.define(
                    let_stmt.name,
                    Variable {
                        ty: var_type,
                        mutable: let_stmt.mutable,
                    },
                );
            }
        }

        // Second pass: type check function bodies and tests
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    self.check_function(func, interner)?;
                }
                Decl::Tests(tests_decl) => {
                    self.check_tests(tests_decl, interner)?;
                }
                Decl::Let(_) => {
                    // Already processed above
                }
                Decl::Class(class) => {
                    for method in &class.methods {
                        self.check_method(method, class.name, interner)?;
                    }
                }
                Decl::Record(record) => {
                    for method in &record.methods {
                        self.check_method(method, record.name, interner)?;
                    }
                }
                Decl::Interface(_) => {
                    // TODO: Type check interface method signatures
                }
                Decl::Implement(impl_block) => {
                    // Methods will be type-checked when called
                    // Could add validation here later (e.g., verify trait satisfaction)
                    let _ = impl_block; // suppress warning
                }
            }
        }

        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(std::mem::take(&mut self.errors))
        }
    }

    fn resolve_type(&self, ty: &TypeExpr) -> Type {
        let ctx = TypeResolutionContext::new(
            &self.type_aliases,
            &self.classes,
            &self.records,
            &self.interface_registry,
        );
        resolve_type(ty, &ctx)
    }

    fn check_function(
        &mut self,
        func: &FuncDecl,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        let func_type = self.functions.get(&func.name).cloned().unwrap();
        self.current_function_return = Some(*func_type.return_type.clone());

        // Create new scope with parameters
        let parent_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(parent_scope);

        for (param, ty) in func.params.iter().zip(func_type.params.iter()) {
            self.scope.define(
                param.name,
                Variable {
                    ty: ty.clone(),
                    mutable: false,
                },
            );
        }

        // Check body
        self.check_block(&func.body, interner)?;

        // Restore scope
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }
        self.current_function_return = None;

        Ok(())
    }

    fn check_method(
        &mut self,
        method: &FuncDecl,
        type_name: Symbol,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        let method_key = (type_name, method.name);
        let method_type = self.methods.get(&method_key).cloned().unwrap();
        self.current_function_return = Some(*method_type.return_type.clone());

        // Create scope with 'self' and parameters
        let parent_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(parent_scope);

        // Add 'self' to scope
        // Note: "self" should already be interned by the parser when it parses method bodies
        let self_sym = interner
            .lookup("self")
            .expect("'self' should be interned during parsing");
        let self_type = if let Some(class_type) = self.classes.get(&type_name) {
            Type::Class(class_type.clone())
        } else {
            Type::Record(self.records.get(&type_name).unwrap().clone())
        };
        self.scope.define(
            self_sym,
            Variable {
                ty: self_type,
                mutable: false,
            },
        );

        // Add parameters
        for (param, ty) in method.params.iter().zip(method_type.params.iter()) {
            self.scope.define(
                param.name,
                Variable {
                    ty: ty.clone(),
                    mutable: false,
                },
            );
        }

        // Check body
        self.check_block(&method.body, interner)?;

        // Restore scope
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }
        self.current_function_return = None;

        Ok(())
    }

    fn check_tests(
        &mut self,
        tests_decl: &TestsDecl,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        for test_case in &tests_decl.tests {
            // Each test gets its own scope
            let parent_scope = std::mem::take(&mut self.scope);
            self.scope = Scope::with_parent(parent_scope);

            // Tests implicitly return void
            self.current_function_return = Some(Type::Void);

            // Type check all statements in the test body
            self.check_block(&test_case.body, interner)?;

            // Restore scope
            if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                self.scope = parent;
            }
            self.current_function_return = None;
        }

        Ok(())
    }

    fn is_assert_call(&self, callee: &Expr, interner: &Interner) -> bool {
        if let ExprKind::Identifier(sym) = &callee.kind {
            interner.resolve(*sym) == "assert"
        } else {
            false
        }
    }

    fn check_block(&mut self, block: &Block, interner: &Interner) -> Result<(), Vec<TypeError>> {
        for stmt in &block.stmts {
            self.check_stmt(stmt, interner)?;
        }
        Ok(())
    }

    fn check_stmt(&mut self, stmt: &Stmt, interner: &Interner) -> Result<(), Vec<TypeError>> {
        match stmt {
            Stmt::Let(let_stmt) => {
                let declared_type = let_stmt.ty.as_ref().map(|t| self.resolve_type(t));
                let init_type =
                    self.check_expr_expecting(&let_stmt.init, declared_type.as_ref(), interner)?;

                // Check if trying to use void return value
                if init_type == Type::Void {
                    self.add_error(
                        SemanticError::VoidReturnUsed {
                            span: let_stmt.init.span.into(),
                        },
                        let_stmt.init.span,
                    );
                }

                let var_type = declared_type.unwrap_or(init_type);

                // If this is a type alias (RHS is a type expression), store it
                if var_type == Type::Type
                    && let ExprKind::TypeLiteral(type_expr) = &let_stmt.init.kind
                {
                    let aliased_type = self.resolve_type(type_expr);
                    self.type_aliases.insert(let_stmt.name, aliased_type);
                }

                self.scope.define(
                    let_stmt.name,
                    Variable {
                        ty: var_type,
                        mutable: let_stmt.mutable,
                    },
                );

                // Track as a local if inside a lambda
                self.add_lambda_local(let_stmt.name);
            }
            Stmt::Expr(expr_stmt) => {
                self.check_expr(&expr_stmt.expr, interner)?;
            }
            Stmt::While(while_stmt) => {
                let cond_type = self.check_expr(&while_stmt.condition, interner)?;
                if cond_type != Type::Bool && !cond_type.is_numeric() {
                    self.add_error(
                        SemanticError::ConditionNotBool {
                            found: cond_type.name().to_string(),
                            span: while_stmt.condition.span.into(),
                        },
                        while_stmt.condition.span,
                    );
                }

                let parent = std::mem::take(&mut self.scope);
                self.scope = Scope::with_parent(parent);
                self.check_block(&while_stmt.body, interner)?;
                if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                    self.scope = parent;
                }
            }
            Stmt::If(if_stmt) => {
                let cond_type = self.check_expr(&if_stmt.condition, interner)?;
                if cond_type != Type::Bool && !cond_type.is_numeric() {
                    self.add_error(
                        SemanticError::ConditionNotBool {
                            found: cond_type.name().to_string(),
                            span: if_stmt.condition.span.into(),
                        },
                        if_stmt.condition.span,
                    );
                }

                // Check if condition is `x is T` for flow-sensitive narrowing
                let narrowing_info = if let ExprKind::Is(is_expr) = &if_stmt.condition.kind {
                    if let ExprKind::Identifier(sym) = &is_expr.value.kind {
                        let tested_type = self.resolve_type(&is_expr.type_expr);
                        Some((*sym, tested_type))
                    } else {
                        None
                    }
                } else {
                    None
                };

                // Save current overrides
                let saved_overrides = self.type_overrides.clone();

                // Then branch (with narrowing if applicable)
                let parent = std::mem::take(&mut self.scope);
                self.scope = Scope::with_parent(parent);
                if let Some((sym, narrowed_type)) = &narrowing_info {
                    self.type_overrides.insert(*sym, narrowed_type.clone());
                }
                self.check_block(&if_stmt.then_branch, interner)?;
                if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                    self.scope = parent;
                }

                // Restore overrides for else branch (no narrowing there for now)
                self.type_overrides = saved_overrides.clone();

                if let Some(else_branch) = &if_stmt.else_branch {
                    let parent = std::mem::take(&mut self.scope);
                    self.scope = Scope::with_parent(parent);
                    self.check_block(else_branch, interner)?;
                    if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                        self.scope = parent;
                    }
                }

                // Restore original overrides after the entire if statement
                self.type_overrides = saved_overrides;
            }
            Stmt::For(for_stmt) => {
                let iterable_ty = self.check_expr(&for_stmt.iterable, interner)?;

                let elem_ty = match iterable_ty {
                    Type::Range => Type::I64,
                    Type::Array(elem) => *elem,
                    _ => {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "iterable (range or array)".to_string(),
                                found: iterable_ty.name().to_string(),
                                span: for_stmt.iterable.span.into(),
                            },
                            for_stmt.iterable.span,
                        );
                        Type::Error
                    }
                };

                let parent = std::mem::take(&mut self.scope);
                self.scope = Scope::with_parent(parent);
                self.scope.define(
                    for_stmt.var_name,
                    Variable {
                        ty: elem_ty,
                        mutable: false,
                    },
                );

                self.check_block(&for_stmt.body, interner)?;

                if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                    self.scope = parent;
                }
            }
            Stmt::Break(_) => {
                // Could check we're in a loop, but skipping for Phase 1
            }
            Stmt::Continue(_) => {
                // Could validate we're in a loop, skip for now
            }
            Stmt::Return(ret) => {
                let ret_type = if let Some(value) = &ret.value {
                    self.check_expr(value, interner)?
                } else {
                    Type::Void
                };

                if let Some(expected) = &self.current_function_return
                    && !self.types_compatible(&ret_type, expected)
                {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: expected.name().to_string(),
                            found: ret_type.name().to_string(),
                            span: ret.span.into(),
                        },
                        ret.span,
                    );
                }
            }
        }
        Ok(())
    }

    /// Check expression against an expected type (bidirectional type checking)
    /// If expected is None, falls back to inference mode.
    fn check_expr_expecting(
        &mut self,
        expr: &Expr,
        expected: Option<&Type>,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        let ty = self.check_expr_expecting_inner(expr, expected, interner)?;
        self.record_expr_type(expr, ty.clone());
        Ok(ty)
    }

    fn check_expr_expecting_inner(
        &mut self,
        expr: &Expr,
        expected: Option<&Type>,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        match &expr.kind {
            ExprKind::IntLiteral(value) => match expected {
                Some(ty) if literal_fits(*value, ty) => Ok(ty.clone()),
                Some(ty) => {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: ty.name().to_string(),
                            found: "integer literal".to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    Ok(ty.clone())
                }
                None => Ok(Type::I64),
            },
            ExprKind::TypeLiteral(_) => match expected {
                Some(Type::Type) | None => Ok(Type::Type),
                Some(ty) => {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: ty.name().to_string(),
                            found: "type".to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    Ok(Type::Type)
                }
            },
            ExprKind::FloatLiteral(_) => match expected {
                Some(ty) if ty == &Type::F64 => Ok(Type::F64),
                Some(ty) if ty.is_numeric() => Ok(ty.clone()),
                // Float literals can be assigned to unions containing f64
                Some(Type::Union(variants)) if variants.contains(&Type::F64) => Ok(Type::F64),
                Some(ty) => {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: ty.name().to_string(),
                            found: "f64".to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    Ok(Type::F64)
                }
                None => Ok(Type::F64),
            },
            ExprKind::Binary(bin) => {
                match bin.op {
                    // Arithmetic ops: propagate expected type to both operands
                    BinaryOp::Add
                    | BinaryOp::Sub
                    | BinaryOp::Mul
                    | BinaryOp::Div
                    | BinaryOp::Mod => {
                        let left_ty = self.check_expr_expecting(&bin.left, expected, interner)?;
                        let right_ty = self.check_expr_expecting(&bin.right, expected, interner)?;

                        if left_ty.is_numeric() && right_ty.is_numeric() {
                            // If we have an expected type and both sides match, use it
                            if let Some(exp) = expected
                                && self.types_compatible(&left_ty, exp)
                                && self.types_compatible(&right_ty, exp)
                            {
                                return Ok(exp.clone());
                            }
                            // Otherwise return wider type
                            if left_ty == Type::F64 || right_ty == Type::F64 {
                                Ok(Type::F64)
                            } else if left_ty == Type::I64 || right_ty == Type::I64 {
                                Ok(Type::I64)
                            } else {
                                Ok(Type::I32)
                            }
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "numeric".to_string(),
                                    found: format!("{} and {}", left_ty.name(), right_ty.name()),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    // Comparison ops: infer left, check right against left
                    BinaryOp::Eq
                    | BinaryOp::Ne
                    | BinaryOp::Lt
                    | BinaryOp::Gt
                    | BinaryOp::Le
                    | BinaryOp::Ge => {
                        let left_ty = self.check_expr_expecting(&bin.left, None, interner)?;
                        self.check_expr_expecting(&bin.right, Some(&left_ty), interner)?;
                        Ok(Type::Bool)
                    }
                    // Logical ops: both sides must be bool
                    BinaryOp::And | BinaryOp::Or => {
                        let left_ty =
                            self.check_expr_expecting(&bin.left, Some(&Type::Bool), interner)?;
                        let right_ty =
                            self.check_expr_expecting(&bin.right, Some(&Type::Bool), interner)?;
                        if left_ty == Type::Bool && right_ty == Type::Bool {
                            Ok(Type::Bool)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "bool".to_string(),
                                    found: format!("{} and {}", left_ty.name(), right_ty.name()),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    // Bitwise ops: both sides must be integer
                    BinaryOp::BitAnd
                    | BinaryOp::BitOr
                    | BinaryOp::BitXor
                    | BinaryOp::Shl
                    | BinaryOp::Shr => {
                        let left_ty = self.check_expr_expecting(&bin.left, expected, interner)?;
                        let right_ty = self.check_expr_expecting(&bin.right, expected, interner)?;

                        if left_ty.is_integer() && right_ty.is_integer() {
                            if let Some(exp) = expected
                                && self.types_compatible(&left_ty, exp)
                                && self.types_compatible(&right_ty, exp)
                            {
                                return Ok(exp.clone());
                            }
                            if left_ty == Type::I64 || right_ty == Type::I64 {
                                Ok(Type::I64)
                            } else {
                                Ok(Type::I32)
                            }
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "integer".to_string(),
                                    found: format!("{} and {}", left_ty.name(), right_ty.name()),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                }
            }
            ExprKind::Unary(un) => {
                match un.op {
                    UnaryOp::Neg => {
                        // Propagate expected type through negation
                        let operand_ty =
                            self.check_expr_expecting(&un.operand, expected, interner)?;
                        if operand_ty.is_numeric() {
                            Ok(operand_ty)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "numeric".to_string(),
                                    found: operand_ty.name().to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    UnaryOp::Not => {
                        // Not always expects and returns bool
                        let operand_ty =
                            self.check_expr_expecting(&un.operand, Some(&Type::Bool), interner)?;
                        if operand_ty == Type::Bool {
                            Ok(Type::Bool)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "bool".to_string(),
                                    found: operand_ty.name().to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    UnaryOp::BitNot => {
                        // Bitwise not: propagate expected type, requires integer
                        let operand_ty =
                            self.check_expr_expecting(&un.operand, expected, interner)?;
                        if operand_ty.is_integer() {
                            Ok(operand_ty)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "integer".to_string(),
                                    found: operand_ty.name().to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                }
            }
            ExprKind::Grouping(inner) => self.check_expr_expecting(inner, expected, interner),
            ExprKind::ArrayLiteral(elements) => {
                let elem_expected = match expected {
                    Some(Type::Array(elem)) => Some(elem.as_ref()),
                    _ => None,
                };

                if elements.is_empty() {
                    if let Some(Type::Array(elem)) = expected {
                        return Ok(Type::Array(elem.clone()));
                    }
                    return Ok(Type::Array(Box::new(Type::Unknown)));
                }

                let elem_ty = self.check_expr_expecting(&elements[0], elem_expected, interner)?;

                for elem in elements.iter().skip(1) {
                    self.check_expr_expecting(elem, Some(&elem_ty), interner)?;
                }

                Ok(Type::Array(Box::new(elem_ty)))
            }
            ExprKind::Index(_) => {
                // Index expressions just delegate to check_expr
                self.check_expr(expr, interner)
            }
            ExprKind::Lambda(lambda) => {
                // Extract expected function type if available
                // Support both direct function types and functional interfaces
                let expected_fn = expected.and_then(|t| {
                    if let Type::Function(ft) = t {
                        Some(ft.clone())
                    } else if let Type::Interface(iface) = t {
                        // Check if it's a functional interface (single abstract method, no fields)
                        self.get_functional_interface_type(iface.name)
                    } else {
                        None
                    }
                });
                Ok(self.analyze_lambda(lambda, expected_fn.as_ref(), interner))
            }
            // All other cases: infer type, then check compatibility
            _ => {
                let inferred = self.check_expr(expr, interner)?;
                if let Some(expected_ty) = expected
                    && !self.types_compatible(&inferred, expected_ty)
                {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: expected_ty.name().to_string(),
                            found: inferred.name().to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                }
                Ok(inferred)
            }
        }
    }

    fn check_expr(&mut self, expr: &Expr, interner: &Interner) -> Result<Type, Vec<TypeError>> {
        let ty = self.check_expr_inner(expr, interner)?;
        self.record_expr_type(expr, ty.clone());
        Ok(ty)
    }

    fn check_expr_inner(
        &mut self,
        expr: &Expr,
        interner: &Interner,
    ) -> Result<Type, Vec<TypeError>> {
        match &expr.kind {
            ExprKind::IntLiteral(_) => Ok(Type::I64), // Default to i64 for now
            ExprKind::FloatLiteral(_) => Ok(Type::F64),
            ExprKind::BoolLiteral(_) => Ok(Type::Bool),
            ExprKind::StringLiteral(_) => Ok(Type::String),
            ExprKind::InterpolatedString(_) => Ok(Type::String),
            ExprKind::TypeLiteral(_) => Ok(Type::Type), // Type values have metatype `type`

            ExprKind::Identifier(sym) => {
                // Use get_variable_type to respect flow-sensitive narrowing
                if let Some(ty) = self.get_variable_type(*sym) {
                    // Check if this is a capture (inside lambda, not a local)
                    if self.in_lambda() && !self.is_lambda_local(*sym) {
                        // Look up variable info to get mutability
                        if let Some(var) = self.scope.get(*sym) {
                            self.record_capture(*sym, var.mutable);
                        }
                    }
                    Ok(ty)
                } else {
                    let name = interner.resolve(*sym);
                    self.add_error(
                        SemanticError::UndefinedVariable {
                            name: name.to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                    Ok(Type::Error)
                }
            }

            ExprKind::Binary(bin) => {
                let left_ty = self.check_expr(&bin.left, interner)?;
                let right_ty = self.check_expr(&bin.right, interner)?;

                match bin.op {
                    BinaryOp::Add
                    | BinaryOp::Sub
                    | BinaryOp::Mul
                    | BinaryOp::Div
                    | BinaryOp::Mod => {
                        if left_ty.is_numeric() && right_ty.is_numeric() {
                            // Return wider type
                            if left_ty == Type::F64 || right_ty == Type::F64 {
                                Ok(Type::F64)
                            } else if left_ty == Type::I64 || right_ty == Type::I64 {
                                Ok(Type::I64)
                            } else {
                                Ok(Type::I32)
                            }
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "numeric".to_string(),
                                    found: format!("{} and {}", left_ty.name(), right_ty.name()),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    BinaryOp::Eq
                    | BinaryOp::Ne
                    | BinaryOp::Lt
                    | BinaryOp::Gt
                    | BinaryOp::Le
                    | BinaryOp::Ge => Ok(Type::Bool),
                    BinaryOp::And | BinaryOp::Or => {
                        if left_ty == Type::Bool && right_ty == Type::Bool {
                            Ok(Type::Bool)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "bool".to_string(),
                                    found: format!("{} and {}", left_ty.name(), right_ty.name()),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    BinaryOp::BitAnd
                    | BinaryOp::BitOr
                    | BinaryOp::BitXor
                    | BinaryOp::Shl
                    | BinaryOp::Shr => {
                        if left_ty.is_integer() && right_ty.is_integer() {
                            if left_ty == Type::I64 || right_ty == Type::I64 {
                                Ok(Type::I64)
                            } else {
                                Ok(Type::I32)
                            }
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "integer".to_string(),
                                    found: format!("{} and {}", left_ty.name(), right_ty.name()),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                }
            }

            ExprKind::Unary(un) => {
                let operand_ty = self.check_expr(&un.operand, interner)?;
                match un.op {
                    UnaryOp::Neg => {
                        if operand_ty.is_numeric() {
                            Ok(operand_ty)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "numeric".to_string(),
                                    found: operand_ty.name().to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    UnaryOp::Not => {
                        if operand_ty == Type::Bool {
                            Ok(Type::Bool)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "bool".to_string(),
                                    found: operand_ty.name().to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    UnaryOp::BitNot => {
                        if operand_ty.is_integer() {
                            Ok(operand_ty)
                        } else {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "integer".to_string(),
                                    found: operand_ty.name().to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                }
            }

            ExprKind::Call(call) => {
                // Handle assert specially
                if self.is_assert_call(&call.callee, interner) {
                    // Assert is an impure builtin - mark side effects if inside lambda
                    if self.in_lambda() {
                        self.mark_lambda_has_side_effects();
                    }

                    if call.args.len() != 1 {
                        self.add_error(
                            SemanticError::WrongArgumentCount {
                                expected: 1,
                                found: call.args.len(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                        return Ok(Type::Void);
                    }

                    let arg_ty = self.check_expr(&call.args[0], interner)?;
                    if arg_ty != Type::Bool && arg_ty != Type::Error {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "bool".to_string(),
                                found: arg_ty.name().to_string(),
                                span: call.args[0].span.into(),
                            },
                            call.args[0].span,
                        );
                    }

                    return Ok(Type::Void);
                }

                if let ExprKind::Identifier(sym) = &call.callee.kind {
                    // First check if it's a top-level function
                    if let Some(func_type) = self.functions.get(sym).cloned() {
                        // Calling a user-defined function - conservatively mark side effects
                        if self.in_lambda() {
                            self.mark_lambda_has_side_effects();
                        }
                        self.check_call_args(
                            &call.args,
                            &func_type.params,
                            expr.span,
                            true, // with_inference
                            interner,
                        )?;
                        return Ok(*func_type.return_type);
                    }

                    // Check if it's a variable with a function type
                    if let Some(Type::Function(func_type)) = self.get_variable_type(*sym) {
                        // Calling a function-typed variable - conservatively mark side effects
                        if self.in_lambda() {
                            self.mark_lambda_has_side_effects();
                        }
                        self.check_call_args(
                            &call.args,
                            &func_type.params,
                            expr.span,
                            true, // with_inference
                            interner,
                        )?;
                        return Ok(*func_type.return_type);
                    }

                    // Check if it's a variable with a functional interface type
                    if let Some(Type::Interface(iface)) = self.get_variable_type(*sym)
                        && let Some(func_type) = self.get_functional_interface_type(iface.name)
                    {
                        // Calling a functional interface - treat like a closure call
                        if self.in_lambda() {
                            self.mark_lambda_has_side_effects();
                        }
                        self.check_call_args(
                            &call.args,
                            &func_type.params,
                            expr.span,
                            true, // with_inference
                            interner,
                        )?;
                        return Ok(*func_type.return_type);
                    }

                    // Check if it's a known builtin function
                    let name = interner.resolve(*sym);
                    if name == "println"
                        || name == "print_char"
                        || name == "flush"
                        || name == "print"
                    {
                        // Impure builtins - mark side effects if inside lambda
                        if self.in_lambda() {
                            self.mark_lambda_has_side_effects();
                        }
                        for arg in &call.args {
                            self.check_expr(arg, interner)?;
                        }
                        return Ok(Type::Void);
                    }

                    // Check if it's a variable with a non-function type
                    if let Some(var_ty) = self.get_variable_type(*sym) {
                        self.add_error(
                            SemanticError::NotCallable {
                                ty: var_ty.name().to_string(),
                                span: call.callee.span.into(),
                            },
                            call.callee.span,
                        );
                        // Still check args for more errors
                        for arg in &call.args {
                            self.check_expr(arg, interner)?;
                        }
                        return Ok(Type::Error);
                    }

                    // Unknown identifier - might be an undefined function
                    // (will be caught by codegen or other checks)
                    for arg in &call.args {
                        self.check_expr(arg, interner)?;
                    }
                    return Ok(Type::Void);
                }

                // Non-identifier callee (e.g., a lambda expression being called directly)
                let callee_ty = self.check_expr(&call.callee, interner)?;
                if let Type::Function(func_type) = callee_ty {
                    // Calling a function-typed expression - conservatively mark side effects
                    if self.in_lambda() {
                        self.mark_lambda_has_side_effects();
                    }
                    self.check_call_args(
                        &call.args,
                        &func_type.params,
                        expr.span,
                        false, // without inference (callee was just an expression)
                        interner,
                    )?;
                    return Ok(*func_type.return_type);
                }

                // Non-callable type
                if callee_ty != Type::Error {
                    self.add_error(
                        SemanticError::NotCallable {
                            ty: callee_ty.name().to_string(),
                            span: call.callee.span.into(),
                        },
                        call.callee.span,
                    );
                }
                Ok(Type::Error)
            }

            ExprKind::Assign(assign) => {
                let value_ty = self.check_expr(&assign.value, interner)?;

                match &assign.target {
                    AssignTarget::Variable(sym) => {
                        if let Some(var) = self.scope.get(*sym) {
                            let is_mutable = var.mutable;
                            let var_ty = var.ty.clone();

                            // Check if this is a mutation of a captured variable
                            if self.in_lambda() && !self.is_lambda_local(*sym) {
                                // Record as capture and mark as mutated
                                self.record_capture(*sym, is_mutable);
                                self.mark_capture_mutated(*sym);
                            }

                            if !is_mutable {
                                let name = interner.resolve(*sym);
                                self.add_error(
                                    SemanticError::ImmutableAssignment {
                                        name: name.to_string(),
                                        span: expr.span.into(),
                                        declaration: expr.span.into(), // TODO: track declaration span
                                    },
                                    expr.span,
                                );
                            }
                            if !self.types_compatible(&value_ty, &var_ty) {
                                self.add_error(
                                    SemanticError::TypeMismatch {
                                        expected: var_ty.name().to_string(),
                                        found: value_ty.name().to_string(),
                                        span: expr.span.into(),
                                    },
                                    expr.span,
                                );
                            }
                            Ok(var_ty)
                        } else {
                            let name = interner.resolve(*sym);
                            self.add_error(
                                SemanticError::UndefinedVariable {
                                    name: name.to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            Ok(Type::Error)
                        }
                    }
                    AssignTarget::Field {
                        object,
                        field,
                        field_span,
                    } => {
                        let obj_ty = self.check_expr(object, interner)?;

                        match &obj_ty {
                            Type::Class(c) => {
                                if let Some(field_def) = c.fields.iter().find(|f| f.name == *field)
                                {
                                    if !self.types_compatible(&value_ty, &field_def.ty) {
                                        self.add_error(
                                            SemanticError::TypeMismatch {
                                                expected: field_def.ty.name().to_string(),
                                                found: value_ty.name().to_string(),
                                                span: assign.value.span.into(),
                                            },
                                            assign.value.span,
                                        );
                                    }
                                    Ok(field_def.ty.clone())
                                } else {
                                    self.add_error(
                                        SemanticError::UnknownField {
                                            ty: interner.resolve(c.name).to_string(),
                                            field: interner.resolve(*field).to_string(),
                                            span: (*field_span).into(),
                                        },
                                        *field_span,
                                    );
                                    Ok(Type::Error)
                                }
                            }
                            Type::Record(r) => {
                                // Records are immutable - reject field assignment
                                self.add_error(
                                    SemanticError::RecordFieldMutation {
                                        record: interner.resolve(r.name).to_string(),
                                        field: interner.resolve(*field).to_string(),
                                        span: (*field_span).into(),
                                    },
                                    *field_span,
                                );
                                Ok(Type::Error)
                            }
                            _ => {
                                if obj_ty != Type::Error {
                                    self.add_error(
                                        SemanticError::UnknownField {
                                            ty: obj_ty.name().to_string(),
                                            field: interner.resolve(*field).to_string(),
                                            span: (*field_span).into(),
                                        },
                                        *field_span,
                                    );
                                }
                                Ok(Type::Error)
                            }
                        }
                    }
                    AssignTarget::Index { object, index } => {
                        // Type-check object as array
                        let obj_type = self.check_expr(object, interner)?;
                        let idx_type = self.check_expr(index, interner)?;

                        // Check index is integer
                        if !matches!(
                            idx_type,
                            Type::I32 | Type::I64 | Type::U8 | Type::U16 | Type::U32 | Type::U64
                        ) {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "integer".to_string(),
                                    found: idx_type.name().to_string(),
                                    span: index.span.into(),
                                },
                                index.span,
                            );
                        }

                        // Get element type and check assignment compatibility
                        match obj_type {
                            Type::Array(elem_ty) => {
                                if !self.types_compatible(&value_ty, &elem_ty) {
                                    self.add_error(
                                        SemanticError::TypeMismatch {
                                            expected: elem_ty.name().to_string(),
                                            found: value_ty.name().to_string(),
                                            span: assign.value.span.into(),
                                        },
                                        assign.value.span,
                                    );
                                }
                                Ok(*elem_ty)
                            }
                            _ => {
                                if obj_type != Type::Error {
                                    self.add_error(
                                        SemanticError::TypeMismatch {
                                            expected: "array".to_string(),
                                            found: obj_type.name().to_string(),
                                            span: object.span.into(),
                                        },
                                        object.span,
                                    );
                                }
                                Ok(Type::Error)
                            }
                        }
                    }
                }
            }

            ExprKind::CompoundAssign(compound) => {
                // Get target type and check mutability
                let target_type = match &compound.target {
                    AssignTarget::Variable(sym) => {
                        if let Some(var) = self.scope.get(*sym) {
                            let is_mutable = var.mutable;
                            let var_ty = var.ty.clone();

                            // Check if this is a mutation of a captured variable
                            if self.in_lambda() && !self.is_lambda_local(*sym) {
                                self.record_capture(*sym, is_mutable);
                                self.mark_capture_mutated(*sym);
                            }

                            if !is_mutable {
                                let name = interner.resolve(*sym);
                                self.add_error(
                                    SemanticError::ImmutableAssignment {
                                        name: name.to_string(),
                                        span: expr.span.into(),
                                        declaration: expr.span.into(),
                                    },
                                    expr.span,
                                );
                            }
                            var_ty
                        } else {
                            let name = interner.resolve(*sym);
                            self.add_error(
                                SemanticError::UndefinedVariable {
                                    name: name.to_string(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                            return Ok(Type::Error);
                        }
                    }
                    AssignTarget::Index { object, index } => {
                        // Type-check object as array
                        let obj_type = self.check_expr(object, interner)?;
                        let idx_type = self.check_expr(index, interner)?;

                        // Check index is integer
                        if !matches!(
                            idx_type,
                            Type::I32 | Type::I64 | Type::U8 | Type::U16 | Type::U32 | Type::U64
                        ) {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: "integer".to_string(),
                                    found: idx_type.name().to_string(),
                                    span: index.span.into(),
                                },
                                index.span,
                            );
                        }

                        // Get element type
                        match obj_type {
                            Type::Array(elem_ty) => *elem_ty,
                            _ => {
                                if obj_type != Type::Error {
                                    self.add_error(
                                        SemanticError::TypeMismatch {
                                            expected: "array".to_string(),
                                            found: obj_type.name().to_string(),
                                            span: object.span.into(),
                                        },
                                        object.span,
                                    );
                                }
                                Type::Error
                            }
                        }
                    }
                    AssignTarget::Field {
                        object,
                        field,
                        field_span,
                    } => {
                        let obj_ty = self.check_expr(object, interner)?;

                        match &obj_ty {
                            Type::Class(c) => {
                                if let Some(field_def) = c.fields.iter().find(|f| f.name == *field)
                                {
                                    field_def.ty.clone()
                                } else {
                                    self.add_error(
                                        SemanticError::UnknownField {
                                            ty: interner.resolve(c.name).to_string(),
                                            field: interner.resolve(*field).to_string(),
                                            span: (*field_span).into(),
                                        },
                                        *field_span,
                                    );
                                    Type::Error
                                }
                            }
                            Type::Record(r) => {
                                // Records are immutable - reject field assignment
                                self.add_error(
                                    SemanticError::RecordFieldMutation {
                                        record: interner.resolve(r.name).to_string(),
                                        field: interner.resolve(*field).to_string(),
                                        span: (*field_span).into(),
                                    },
                                    *field_span,
                                );
                                Type::Error
                            }
                            _ => {
                                if obj_ty != Type::Error {
                                    self.add_error(
                                        SemanticError::UnknownField {
                                            ty: obj_ty.name().to_string(),
                                            field: interner.resolve(*field).to_string(),
                                            span: (*field_span).into(),
                                        },
                                        *field_span,
                                    );
                                }
                                Type::Error
                            }
                        }
                    }
                };

                // Type-check the value expression
                let value_type = self.check_expr(&compound.value, interner)?;

                // Check operator compatibility - compound assignment operators are arithmetic
                // For +=, -=, *=, /=, %= both operands must be numeric
                if target_type != Type::Error
                    && value_type != Type::Error
                    && (!target_type.is_numeric() || !value_type.is_numeric())
                {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "numeric".to_string(),
                            found: format!("{} and {}", target_type.name(), value_type.name()),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                }

                Ok(target_type)
            }

            ExprKind::Grouping(inner) => self.check_expr(inner, interner),

            ExprKind::ArrayLiteral(elements) => {
                if elements.is_empty() {
                    // Empty array needs type annotation or we use Unknown
                    Ok(Type::Array(Box::new(Type::Unknown)))
                } else {
                    // Infer element type from first element
                    let elem_ty = self.check_expr(&elements[0], interner)?;

                    // Check remaining elements match
                    for elem in elements.iter().skip(1) {
                        let ty = self.check_expr(elem, interner)?;
                        if !self.types_compatible(&ty, &elem_ty) {
                            self.add_error(
                                SemanticError::TypeMismatch {
                                    expected: elem_ty.name().to_string(),
                                    found: ty.name().to_string(),
                                    span: elem.span.into(),
                                },
                                elem.span,
                            );
                        }
                    }

                    Ok(Type::Array(Box::new(elem_ty)))
                }
            }

            ExprKind::Index(idx) => {
                let obj_ty = self.check_expr(&idx.object, interner)?;
                let index_ty = self.check_expr(&idx.index, interner)?;

                // Index must be integer
                if !index_ty.is_integer() {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "integer".to_string(),
                            found: index_ty.name().to_string(),
                            span: idx.index.span.into(),
                        },
                        idx.index.span,
                    );
                }

                // Object must be array
                match obj_ty {
                    Type::Array(elem_ty) => Ok(*elem_ty),
                    _ => {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "array".to_string(),
                                found: obj_ty.name().to_string(),
                                span: idx.object.span.into(),
                            },
                            idx.object.span,
                        );
                        Ok(Type::Error)
                    }
                }
            }

            ExprKind::Range(range) => {
                let start_ty = self.check_expr(&range.start, interner)?;
                let end_ty = self.check_expr(&range.end, interner)?;

                if !start_ty.is_integer() || !end_ty.is_integer() {
                    self.add_error(
                        SemanticError::TypeMismatch {
                            expected: "integer".to_string(),
                            found: format!("{} and {}", start_ty.name(), end_ty.name()),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                }
                Ok(Type::Range)
            }

            ExprKind::Match(match_expr) => {
                // Check scrutinee type
                let scrutinee_type = self.check_expr(&match_expr.scrutinee, interner)?;

                // Check exhaustiveness - must have wildcard or identifier catch-all
                let has_catch_all = match_expr.arms.iter().any(|arm| {
                    matches!(
                        arm.pattern,
                        Pattern::Wildcard(_) | Pattern::Identifier { .. }
                    )
                });
                if !has_catch_all {
                    self.add_error(
                        SemanticError::NonExhaustiveMatch {
                            span: match_expr.span.into(),
                        },
                        match_expr.span,
                    );
                }

                // Check each arm, collect result types
                let mut result_type: Option<Type> = None;
                let mut first_arm_span: Option<Span> = None;

                for arm in &match_expr.arms {
                    // Enter new scope for arm (bindings live here)
                    self.scope = Scope::with_parent(std::mem::take(&mut self.scope));

                    // Check pattern
                    self.check_pattern(&arm.pattern, &scrutinee_type, interner);

                    // Check guard if present (must be bool)
                    if let Some(guard) = &arm.guard {
                        let guard_type = self.check_expr(guard, interner)?;
                        if guard_type != Type::Bool && !guard_type.is_numeric() {
                            self.add_error(
                                SemanticError::MatchGuardNotBool {
                                    found: guard_type.name().to_string(),
                                    span: guard.span.into(),
                                },
                                guard.span,
                            );
                        }
                    }

                    // Check body expression
                    let body_type = self.check_expr(&arm.body, interner)?;

                    // Unify with previous arms
                    match &result_type {
                        None => {
                            result_type = Some(body_type);
                            first_arm_span = Some(arm.span);
                        }
                        Some(expected) if *expected != body_type => {
                            self.add_error(
                                SemanticError::MatchArmTypeMismatch {
                                    expected: expected.name().to_string(),
                                    found: body_type.name().to_string(),
                                    first_arm: first_arm_span.unwrap().into(),
                                    span: arm.body.span.into(),
                                },
                                arm.body.span,
                            );
                        }
                        _ => {}
                    }

                    // Exit arm scope
                    if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                        self.scope = parent;
                    }
                }

                Ok(result_type.unwrap_or(Type::Void))
            }

            ExprKind::Nil => Ok(Type::Nil),

            ExprKind::NullCoalesce(nc) => {
                let value_type = self.check_expr(&nc.value, interner)?;

                // Value must be an optional (union containing Nil)
                if !value_type.is_optional() {
                    self.add_error(
                        SemanticError::NullCoalesceNotOptional {
                            found: format!("{}", value_type),
                            span: nc.value.span.into(),
                        },
                        nc.value.span,
                    );
                    return Ok(Type::Error);
                }

                // Get the non-nil type
                let unwrapped = value_type.unwrap_optional().unwrap_or(Type::Error);

                // Default must match the unwrapped type
                let _default_type =
                    self.check_expr_expecting(&nc.default, Some(&unwrapped), interner)?;

                // Result is the non-nil type
                Ok(unwrapped)
            }

            ExprKind::Is(is_expr) => {
                let value_type = self.check_expr(&is_expr.value, interner)?;
                let tested_type = self.resolve_type(&is_expr.type_expr);

                // Warn/error if tested type is not a variant of value's union
                if let Type::Union(variants) = &value_type
                    && !variants.contains(&tested_type)
                {
                    self.add_error(
                        SemanticError::IsNotVariant {
                            tested: format!("{}", tested_type),
                            union_type: format!("{}", value_type),
                            span: is_expr.type_span.into(),
                        },
                        is_expr.type_span,
                    );
                }

                // Result is always bool
                Ok(Type::Bool)
            }

            ExprKind::Lambda(lambda) => {
                // For now, analyze without expected type context
                // (Context will be passed when we have assignment/call context)
                Ok(self.analyze_lambda(lambda, None, interner))
            }

            ExprKind::StructLiteral(struct_lit) => {
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
                let provided_fields: HashSet<Symbol> =
                    struct_lit.fields.iter().map(|f| f.name).collect();

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
                    if let Some(expected_field) = fields.iter().find(|f| f.name == field_init.name)
                    {
                        // check_expr_expecting will report errors if types don't match
                        self.check_expr_expecting(
                            &field_init.value,
                            Some(&expected_field.ty),
                            interner,
                        )?;
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

            ExprKind::FieldAccess(field_access) => {
                let object_type = self.check_expr(&field_access.object, interner)?;

                // Get fields from object type
                let (type_name, fields) = match &object_type {
                    Type::Class(class_type) => (
                        interner.resolve(class_type.name).to_string(),
                        &class_type.fields,
                    ),
                    Type::Record(record_type) => (
                        interner.resolve(record_type.name).to_string(),
                        &record_type.fields,
                    ),
                    Type::Error => return Ok(Type::Error),
                    _ => {
                        self.add_error(
                            SemanticError::TypeMismatch {
                                expected: "class or record".to_string(),
                                found: object_type.name().to_string(),
                                span: field_access.object.span.into(),
                            },
                            field_access.object.span,
                        );
                        return Ok(Type::Error);
                    }
                };

                // Find the field
                if let Some(field) = fields.iter().find(|f| f.name == field_access.field) {
                    Ok(field.ty.clone())
                } else {
                    self.add_error(
                        SemanticError::UnknownField {
                            ty: type_name,
                            field: interner.resolve(field_access.field).to_string(),
                            span: field_access.field_span.into(),
                        },
                        field_access.field_span,
                    );
                    Ok(Type::Error)
                }
            }

            ExprKind::MethodCall(method_call) => {
                let object_type = self.check_expr(&method_call.object, interner)?;
                let method_name = interner.resolve(method_call.method);

                // Handle built-in methods for primitive types
                if let Some(return_type) = self.check_builtin_method(
                    &object_type,
                    method_name,
                    &method_call.args,
                    interner,
                ) {
                    // Record the resolution for codegen
                    let resolved = ResolvedMethod::Implemented {
                        trait_name: None,
                        func_type: FunctionType {
                            params: vec![],
                            return_type: Box::new(return_type.clone()),
                            is_closure: false,
                        },
                        is_builtin: true,
                    };
                    self.method_resolutions.insert(expr.id, resolved);
                    return Ok(return_type);
                }

                // Handle Type::Error early
                if matches!(object_type, Type::Error) {
                    return Ok(Type::Error);
                }

                // Get a descriptive type name for error messages
                let type_name = if let Some(type_id) = TypeId::from_type(&object_type) {
                    type_id.type_name(interner)
                } else {
                    object_type.name().to_string()
                };

                // First, check implement registry for ANY type (primitives, arrays, classes, records)
                // This allows implement blocks to work for all types
                if let Some(type_id) = TypeId::from_type(&object_type)
                    && let Some(impl_) = self
                        .implement_registry
                        .get_method(&type_id, method_call.method)
                {
                    let func_type = impl_.func_type.clone();

                    // Record resolution
                    self.method_resolutions.insert(
                        expr.id,
                        ResolvedMethod::Implemented {
                            trait_name: impl_.trait_name,
                            func_type: func_type.clone(),
                            is_builtin: impl_.is_builtin,
                        },
                    );

                    // Mark side effects if inside lambda
                    if self.in_lambda() {
                        self.mark_lambda_has_side_effects();
                    }

                    // Check argument count
                    if method_call.args.len() != func_type.params.len() {
                        self.add_error(
                            SemanticError::WrongArgumentCount {
                                expected: func_type.params.len(),
                                found: method_call.args.len(),
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                    }

                    // Check argument types
                    for (arg, param_ty) in method_call.args.iter().zip(func_type.params.iter()) {
                        let arg_ty = self.check_expr_expecting(arg, Some(param_ty), interner)?;
                        if !self.types_compatible(&arg_ty, param_ty) {
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

                    return Ok(*func_type.return_type);
                }

                // Check if object is a functional interface and method matches its single method
                if let Type::Interface(iface) = &object_type {
                    // Check if interface is functional and method matches its abstract method
                    if let Some(iface_def) = self.interface_registry.get(iface.name) {
                        // For functional interfaces, check if the method matches
                        if let Some(method_def) = self.interface_registry.is_functional(iface.name)
                            && method_def.name == method_call.method
                        {
                            let func_type = FunctionType {
                                params: method_def.params.clone(),
                                return_type: Box::new(method_def.return_type.clone()),
                                is_closure: true,
                            };

                            // Mark side effects if inside lambda
                            if self.in_lambda() {
                                self.mark_lambda_has_side_effects();
                            }

                            // Check argument count
                            if method_call.args.len() != func_type.params.len() {
                                self.add_error(
                                    SemanticError::WrongArgumentCount {
                                        expected: func_type.params.len(),
                                        found: method_call.args.len(),
                                        span: expr.span.into(),
                                    },
                                    expr.span,
                                );
                            }

                            // Check argument types
                            for (arg, param_ty) in
                                method_call.args.iter().zip(func_type.params.iter())
                            {
                                let arg_ty =
                                    self.check_expr_expecting(arg, Some(param_ty), interner)?;
                                if !self.types_compatible(&arg_ty, param_ty) {
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

                            // Record resolution for functional interface method
                            self.method_resolutions.insert(
                                expr.id,
                                ResolvedMethod::FunctionalInterface {
                                    func_type: func_type.clone(),
                                },
                            );

                            return Ok(*func_type.return_type);
                        }

                        // For non-functional interfaces, check if method is defined
                        for method_def in &iface_def.methods {
                            if method_def.name == method_call.method {
                                // TODO: Support method calls on non-functional interfaces
                                // For now, we just allow the call
                                let func_type = FunctionType {
                                    params: method_def.params.clone(),
                                    return_type: Box::new(method_def.return_type.clone()),
                                    is_closure: false,
                                };
                                return Ok(*func_type.return_type);
                            }
                        }
                    }
                }

                // Next, check direct methods for class/record types
                let type_sym = match &object_type {
                    Type::Class(class_type) => Some(class_type.name),
                    Type::Record(record_type) => Some(record_type.name),
                    _ => None,
                };

                if let Some(type_sym) = type_sym {
                    let method_key = (type_sym, method_call.method);
                    if let Some(method_type) = self.methods.get(&method_key).cloned() {
                        // Mark side effects if inside lambda
                        if self.in_lambda() {
                            self.mark_lambda_has_side_effects();
                        }

                        // Check argument count
                        if method_call.args.len() != method_type.params.len() {
                            self.add_error(
                                SemanticError::WrongArgumentCount {
                                    expected: method_type.params.len(),
                                    found: method_call.args.len(),
                                    span: expr.span.into(),
                                },
                                expr.span,
                            );
                        }

                        // Check argument types
                        for (arg, param_ty) in
                            method_call.args.iter().zip(method_type.params.iter())
                        {
                            let arg_ty =
                                self.check_expr_expecting(arg, Some(param_ty), interner)?;
                            if !self.types_compatible(&arg_ty, param_ty) {
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

                        // Record resolution for direct method
                        self.method_resolutions.insert(
                            expr.id,
                            ResolvedMethod::Direct {
                                func_type: method_type.clone(),
                            },
                        );

                        return Ok(*method_type.return_type);
                    }

                    // Check for default method from implemented interfaces
                    if let Some(interfaces) = self.type_implements.get(&type_sym).cloned() {
                        for interface_name in &interfaces {
                            if let Some(interface_def) =
                                self.interface_registry.get(*interface_name)
                            {
                                // Look for a default method with matching name
                                for method_def in &interface_def.methods {
                                    if method_def.name == method_call.method
                                        && method_def.has_default
                                    {
                                        let func_type = FunctionType {
                                            params: method_def.params.clone(),
                                            return_type: Box::new(method_def.return_type.clone()),
                                            is_closure: false,
                                        };

                                        // Mark side effects if inside lambda
                                        if self.in_lambda() {
                                            self.mark_lambda_has_side_effects();
                                        }

                                        // Check argument count
                                        if method_call.args.len() != func_type.params.len() {
                                            self.add_error(
                                                SemanticError::WrongArgumentCount {
                                                    expected: func_type.params.len(),
                                                    found: method_call.args.len(),
                                                    span: expr.span.into(),
                                                },
                                                expr.span,
                                            );
                                        }

                                        // Check argument types
                                        for (arg, param_ty) in
                                            method_call.args.iter().zip(func_type.params.iter())
                                        {
                                            let arg_ty = self.check_expr_expecting(
                                                arg,
                                                Some(param_ty),
                                                interner,
                                            )?;
                                            if !self.types_compatible(&arg_ty, param_ty) {
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

                                        // Record resolution for default method
                                        self.method_resolutions.insert(
                                            expr.id,
                                            ResolvedMethod::DefaultMethod {
                                                interface_name: *interface_name,
                                                type_name: type_sym,
                                                method_name: method_call.method,
                                                func_type: func_type.clone(),
                                            },
                                        );

                                        return Ok(*func_type.return_type);
                                    }
                                }
                            }
                        }
                    }
                }

                // No method found - report error
                self.add_error(
                    SemanticError::UnknownMethod {
                        ty: type_name,
                        method: interner.resolve(method_call.method).to_string(),
                        span: method_call.method_span.into(),
                    },
                    method_call.method_span,
                );
                // Still check args for more errors
                for arg in &method_call.args {
                    self.check_expr(arg, interner)?;
                }
                Ok(Type::Error)
            }
        }
    }

    /// Check a pattern against the scrutinee type
    fn check_pattern(&mut self, pattern: &Pattern, scrutinee_type: &Type, interner: &Interner) {
        match pattern {
            Pattern::Wildcard(_) => {
                // Wildcard always matches, nothing to check
            }
            Pattern::Literal(expr) => {
                // Check literal type matches scrutinee type
                if let Ok(lit_type) = self.check_expr(expr, interner)
                    && !self.types_compatible(&lit_type, scrutinee_type)
                    && !self.types_compatible(scrutinee_type, &lit_type)
                {
                    self.add_error(
                        SemanticError::PatternTypeMismatch {
                            expected: scrutinee_type.name().to_string(),
                            found: lit_type.name().to_string(),
                            span: expr.span.into(),
                        },
                        expr.span,
                    );
                }
            }
            Pattern::Identifier { name, span: _ } => {
                // Bind identifier to scrutinee's type in current scope
                self.scope.define(
                    *name,
                    Variable {
                        ty: scrutinee_type.clone(),
                        mutable: false,
                    },
                );
            }
        }
    }

    /// Analyze a lambda expression, optionally with an expected function type for inference
    fn analyze_lambda(
        &mut self,
        lambda: &LambdaExpr,
        expected_type: Option<&FunctionType>,
        interner: &Interner,
    ) -> Type {
        // Push capture analysis stacks and side effects flag
        self.lambda_captures.push(HashMap::new());
        self.lambda_locals.push(HashSet::new());
        self.lambda_side_effects.push(false);

        // Resolve parameter types
        let mut param_types = Vec::new();

        for (i, param) in lambda.params.iter().enumerate() {
            let ty = if let Some(type_expr) = &param.ty {
                // Explicit type annotation
                self.resolve_type(type_expr)
            } else if let Some(expected) = expected_type {
                // Infer from expected type
                if i < expected.params.len() {
                    expected.params[i].clone()
                } else {
                    self.add_error(
                        SemanticError::CannotInferLambdaParam {
                            name: interner.resolve(param.name).to_string(),
                            span: param.span.into(),
                        },
                        param.span,
                    );
                    Type::Error
                }
            } else {
                // No type info available
                self.add_error(
                    SemanticError::CannotInferLambdaParam {
                        name: interner.resolve(param.name).to_string(),
                        span: param.span.into(),
                    },
                    param.span,
                );
                Type::Error
            };
            param_types.push(ty);
        }

        // Push new scope for lambda body
        let outer_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(outer_scope);

        // Define parameters in scope and track as locals
        for (param, ty) in lambda.params.iter().zip(param_types.iter()) {
            self.scope.define(
                param.name,
                Variable {
                    ty: ty.clone(),
                    mutable: false,
                },
            );
            // Parameters are locals, not captures
            self.add_lambda_local(param.name);
        }

        // Determine return type
        let declared_return = lambda.return_type.as_ref().map(|t| self.resolve_type(t));
        let expected_return = expected_type.map(|ft| (*ft.return_type).clone());

        // Analyze body and infer return type
        let body_type = match &lambda.body {
            LambdaBody::Expr(expr) => {
                // For expression body, analyze and use as return type
                match self.check_expr(expr, interner) {
                    Ok(ty) => ty,
                    Err(_) => Type::Error,
                }
            }
            LambdaBody::Block(block) => {
                // For blocks, set up return type context
                let old_return = self.current_function_return.take();
                self.current_function_return = declared_return.clone().or(expected_return.clone());

                let _ = self.check_block(block, interner);

                let ret = self.current_function_return.take().unwrap_or(Type::Void);
                self.current_function_return = old_return;
                ret
            }
        };

        // Restore outer scope
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }

        // Pop capture stacks, side effects flag, and store results in the lambda
        self.lambda_locals.pop();
        let has_side_effects = self.lambda_side_effects.pop().unwrap_or(false);
        lambda.has_side_effects.set(has_side_effects);

        let has_captures = if let Some(captures) = self.lambda_captures.pop() {
            let capture_list: Vec<Capture> = captures
                .into_values()
                .map(|info| Capture {
                    name: info.name,
                    is_mutable: info.is_mutable,
                    is_mutated: info.is_mutated,
                })
                .collect();
            let has_captures = !capture_list.is_empty();
            *lambda.captures.borrow_mut() = capture_list;
            has_captures
        } else {
            false
        };

        // Determine final return type
        let return_type = declared_return.or(expected_return).unwrap_or(body_type);

        Type::Function(FunctionType {
            params: param_types,
            return_type: Box::new(return_type),
            is_closure: has_captures,
        })
    }

    fn types_compatible(&self, from: &Type, to: &Type) -> bool {
        // Use the core compatibility check for most cases
        if types_compatible_core(from, to) {
            return true;
        }

        // Function type is compatible with functional interface if signatures match
        if let Type::Function(fn_type) = from
            && let Type::Interface(iface) = to
            && let Some(iface_fn) = self.get_functional_interface_type(iface.name)
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
    fn check_call_args(
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

            if !self.types_compatible(&arg_ty, param_ty) {
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
    fn check_builtin_method(
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
    fn resolve_method_call(
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
            };
            self.method_resolutions
                .insert(call_node_id, resolved.clone());
            return Some(resolved);
        }

        None
    }

    /// Simple check for builtin methods, returns return type if found
    fn check_builtin_method_for_resolution(
        &self,
        object_type: &Type,
        method_name: &str,
    ) -> Option<Type> {
        match (object_type, method_name) {
            (Type::Array(_), "length") => Some(Type::I64),
            (Type::String, "length") => Some(Type::I64),
            _ => None,
        }
    }

    /// Get the function type for a functional interface (single abstract method, no fields)
    fn get_functional_interface_type(&self, interface_name: Symbol) -> Option<FunctionType> {
        let method = self.interface_registry.is_functional(interface_name)?;
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
    pub fn satisfies_interface(&self, ty: &Type, interface_name: Symbol) -> bool {
        let Some(interface) = self.interface_registry.get(interface_name) else {
            return false;
        };

        // Check required fields
        for field in &interface.fields {
            if !self.type_has_field(ty, field.name, &field.ty) {
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
            if !self.satisfies_interface(ty, *parent) {
                return false;
            }
        }

        true
    }

    /// Check if a type has a field with the given name and compatible type
    fn type_has_field(&self, ty: &Type, field_name: Symbol, expected_type: &Type) -> bool {
        match ty {
            Type::Record(r) => r
                .fields
                .iter()
                .any(|f| f.name == field_name && self.types_compatible(&f.ty, expected_type)),
            Type::Class(c) => c
                .fields
                .iter()
                .any(|f| f.name == field_name && self.types_compatible(&f.ty, expected_type)),
            _ => false,
        }
    }

    /// Check if a type has a method that matches the interface method signature
    fn type_has_method(&self, ty: &Type, interface_method: &InterfaceMethodDef) -> bool {
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
}

// Note: Default is not implemented because Analyzer requires file and source parameters

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::Parser;
    use crate::frontend::ast::LambdaPurity;

    fn check(source: &str) -> Result<(), Vec<TypeError>> {
        let mut parser = Parser::new(source);
        let program = parser.parse_program().unwrap();
        let interner = parser.into_interner();
        let mut analyzer = Analyzer::new("test.vole", source);
        analyzer.analyze(&program, &interner)
    }

    // Tests for miette error integration
    #[test]
    fn type_error_contains_semantic_error() {
        let source = "func main() { let x: bool = 42 }";
        let result = check(source);
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(matches!(
            errors[0].error,
            SemanticError::TypeMismatch { .. }
        ));
    }

    #[test]
    fn undefined_variable_has_correct_error_type() {
        let source = "func main() { let x = y }";
        let result = check(source);
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(matches!(
            errors[0].error,
            SemanticError::UndefinedVariable { .. }
        ));
    }

    #[test]
    fn immutable_assignment_has_correct_error_type() {
        let source = "func main() { let x = 1\n x = 2 }";
        let result = check(source);
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(matches!(
            errors[0].error,
            SemanticError::ImmutableAssignment { .. }
        ));
    }

    #[test]
    fn wrong_argument_count_has_correct_error_type() {
        let source = "func main() { assert(true, false) }";
        let result = check(source);
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(matches!(
            errors[0].error,
            SemanticError::WrongArgumentCount { .. }
        ));
    }

    #[test]
    fn condition_not_bool_has_correct_error_type() {
        // Use a string literal which is definitely not a bool or numeric
        let source = r#"func main() { if "hello" { } }"#;
        let result = check(source);
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(matches!(
            errors[0].error,
            SemanticError::ConditionNotBool { .. }
        ));
    }

    #[test]
    fn type_error_has_span() {
        let source = "func main() { let x = y }";
        let result = check(source);
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(errors[0].span.line > 0);
    }

    #[test]
    fn analyze_simple_function() {
        let source = "func main() { let x = 42 }";
        assert!(check(source).is_ok());
    }

    #[test]
    fn analyze_type_mismatch() {
        let source = "func main() { let x: bool = 42 }";
        assert!(check(source).is_err());
    }

    #[test]
    fn analyze_undefined_variable() {
        let source = "func main() { let x = y }";
        assert!(check(source).is_err());
    }

    #[test]
    fn analyze_immutable_assignment() {
        let source = "func main() { let x = 1\n x = 2 }";
        assert!(check(source).is_err());
    }

    #[test]
    fn analyze_mutable_assignment() {
        let source = "func main() { let mut x = 1\n x = 2 }";
        assert!(check(source).is_ok());
    }

    #[test]
    fn analyze_assert_requires_bool() {
        // assert(42) should fail - argument must be bool
        let source = "func main() { assert(42) }";
        let result = check(source);
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(matches!(
            errors[0].error,
            SemanticError::TypeMismatch { ref expected, .. } if expected == "bool"
        ));
    }

    #[test]
    fn analyze_assert_valid() {
        // assert(1 == 1) should pass - comparison returns bool
        let source = "func main() { assert(1 == 1) }";
        assert!(check(source).is_ok());
    }

    #[test]
    fn analyze_assert_with_bool_literal() {
        let source = "func main() { assert(true) }";
        assert!(check(source).is_ok());
    }

    #[test]
    fn analyze_assert_wrong_arg_count() {
        let source = "func main() { assert(true, false) }";
        let result = check(source);
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert!(matches!(
            errors[0].error,
            SemanticError::WrongArgumentCount {
                expected: 1,
                found: 2,
                ..
            }
        ));
    }

    #[test]
    fn analyze_tests_block() {
        let source = r#"
            tests {
                test "simple assertion" {
                    assert(true)
                }
            }
        "#;
        assert!(check(source).is_ok());
    }

    #[test]
    fn analyze_tests_block_with_invalid_assert() {
        let source = r#"
            tests {
                test "bad assertion" {
                    assert(42)
                }
            }
        "#;
        let result = check(source);
        assert!(result.is_err());
    }

    #[test]
    fn analyze_i32_literal_coercion() {
        let source = "func main() { let x: i32 = 42 }";
        assert!(check(source).is_ok());
    }

    #[test]
    fn analyze_i32_binary_coercion() {
        let source = "func main() { let x: i32 = 42 * 3 }";
        assert!(check(source).is_ok());
    }

    #[test]
    fn analyze_i32_to_i64_widening() {
        let source = "func main() { let x: i32 = 42\n let y: i64 = x }";
        assert!(check(source).is_ok());
    }

    #[test]
    fn analyze_i64_to_i32_narrowing_error() {
        let source = "func main() { let x: i64 = 42\n let y: i32 = x }";
        let result = check(source);
        assert!(result.is_err());
    }

    // Helper to parse and analyze, returning the AST for capture inspection
    fn parse_and_analyze(source: &str) -> (Program, Interner) {
        let mut parser = Parser::new(source);
        let program = parser.parse_program().unwrap();
        let interner = parser.into_interner();
        let mut analyzer = Analyzer::new("test.vole", source);
        analyzer.analyze(&program, &interner).unwrap();
        (program, interner)
    }

    // Helper to extract lambda from first statement of main function
    fn get_first_lambda(program: &Program) -> &LambdaExpr {
        for decl in &program.declarations {
            if let Decl::Function(func) = decl {
                for stmt in &func.body.stmts {
                    if let Stmt::Let(let_stmt) = stmt
                        && let ExprKind::Lambda(lambda) = &let_stmt.init.kind
                    {
                        return lambda;
                    }
                }
            }
        }
        panic!("No lambda found in program");
    }

    #[test]
    fn lambda_no_captures_when_only_params() {
        let source = r#"
            func apply(f: (i64) -> i64, x: i64) -> i64 { return f(x) }
            func main() {
                let f = (x: i64) => x + 1
                apply(f, 10)
            }
        "#;
        let (program, _interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        assert!(lambda.captures.borrow().is_empty());
    }

    #[test]
    fn lambda_captures_outer_variable() {
        let source = r#"
            func apply(f: () -> i64) -> i64 { return f() }
            func main() {
                let x = 10
                let f = () => x + 1
                apply(f)
            }
        "#;
        let (program, interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        let captures = lambda.captures.borrow();
        assert_eq!(captures.len(), 1);
        let name = interner.resolve(captures[0].name);
        assert_eq!(name, "x");
        assert!(!captures[0].is_mutable);
        assert!(!captures[0].is_mutated);
    }

    #[test]
    fn lambda_captures_mutable_variable() {
        let source = r#"
            func apply(f: () -> i64) -> i64 { return f() }
            func main() {
                let mut x = 10
                let f = () => x + 1
                apply(f)
            }
        "#;
        let (program, interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        let captures = lambda.captures.borrow();
        assert_eq!(captures.len(), 1);
        let name = interner.resolve(captures[0].name);
        assert_eq!(name, "x");
        assert!(captures[0].is_mutable);
        assert!(!captures[0].is_mutated);
    }

    #[test]
    fn lambda_captures_and_mutates_variable() {
        let source = r#"
            func apply(f: () -> i64) -> i64 { return f() }
            func main() {
                let mut x = 10
                let f: () -> i64 = () => {
                    x = x + 1
                    return x
                }
                apply(f)
            }
        "#;
        let (program, interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        let captures = lambda.captures.borrow();
        assert_eq!(captures.len(), 1);
        let name = interner.resolve(captures[0].name);
        assert_eq!(name, "x");
        assert!(captures[0].is_mutable);
        assert!(captures[0].is_mutated);
    }

    #[test]
    fn lambda_does_not_capture_its_own_params() {
        let source = r#"
            func apply(f: (i64) -> i64, v: i64) -> i64 { return f(v) }
            func main() {
                let f = (x: i64) => x * 2
                apply(f, 5)
            }
        "#;
        let (program, _interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        assert!(lambda.captures.borrow().is_empty());
    }

    #[test]
    fn lambda_does_not_capture_its_own_locals() {
        // Test with expression body that uses a local-like pattern
        // Note: this test verifies that locals defined in lambdas are not treated as captures
        let source = r#"
            func apply(f: (i64) -> i64, v: i64) -> i64 { return f(v) }
            func main() {
                let f = (y: i64) => y * 2
                apply(f, 5)
            }
        "#;
        let (program, _interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        // Parameters should not be treated as captures
        assert!(lambda.captures.borrow().is_empty());
    }

    #[test]
    fn lambda_block_body_with_local() {
        // Test block body with local let binding
        let source = r#"
            func apply(f: () -> i64) -> i64 { return f() }
            func main() {
                let f: () -> i64 = () => {
                    let y = 5
                    return y * 2
                }
                apply(f)
            }
        "#;
        let (program, _interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        // Local y should not be captured
        assert!(lambda.captures.borrow().is_empty());
    }

    // Tests for side effect tracking and purity

    #[test]
    fn lambda_pure_no_captures_no_side_effects() {
        let source = r#"
            func apply(f: (i64) -> i64, v: i64) -> i64 { return f(v) }
            func main() {
                let f = (x: i64) => x + 1
                apply(f, 10)
            }
        "#;
        let (program, _interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        assert!(!lambda.has_side_effects.get());
        assert_eq!(lambda.purity(), LambdaPurity::Pure);
    }

    #[test]
    fn lambda_has_side_effects_println() {
        let source = r#"
            func apply(f: () -> i64) -> i64 { return f() }
            func main() {
                let f: () -> i64 = () => {
                    println("hello")
                    return 42
                }
                apply(f)
            }
        "#;
        let (program, _interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        assert!(lambda.has_side_effects.get());
        assert_eq!(lambda.purity(), LambdaPurity::HasSideEffects);
    }

    #[test]
    fn lambda_has_side_effects_print() {
        let source = r#"
            func apply(f: () -> i64) -> i64 { return f() }
            func main() {
                let f: () -> i64 = () => {
                    print("hello")
                    return 42
                }
                apply(f)
            }
        "#;
        let (program, _interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        assert!(lambda.has_side_effects.get());
        assert_eq!(lambda.purity(), LambdaPurity::HasSideEffects);
    }

    #[test]
    fn lambda_has_side_effects_assert() {
        let source = r#"
            func apply(f: () -> i64) -> i64 { return f() }
            func main() {
                let f: () -> i64 = () => {
                    assert(true)
                    return 42
                }
                apply(f)
            }
        "#;
        let (program, _interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        assert!(lambda.has_side_effects.get());
        assert_eq!(lambda.purity(), LambdaPurity::HasSideEffects);
    }

    #[test]
    fn lambda_has_side_effects_calling_user_function() {
        let source = r#"
            func helper() -> i64 { return 42 }
            func apply(f: () -> i64) -> i64 { return f() }
            func main() {
                let f = () => helper()
                apply(f)
            }
        "#;
        let (program, _interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        assert!(lambda.has_side_effects.get());
        assert_eq!(lambda.purity(), LambdaPurity::HasSideEffects);
    }

    #[test]
    fn lambda_purity_captures_immutable() {
        let source = r#"
            func apply(f: () -> i64) -> i64 { return f() }
            func main() {
                let x = 10
                let f = () => x + 1
                apply(f)
            }
        "#;
        let (program, _interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        assert!(!lambda.has_side_effects.get());
        assert_eq!(lambda.purity(), LambdaPurity::CapturesImmutable);
    }

    #[test]
    fn lambda_purity_captures_mutable() {
        let source = r#"
            func apply(f: () -> i64) -> i64 { return f() }
            func main() {
                let mut x = 10
                let f = () => x + 1
                apply(f)
            }
        "#;
        let (program, _interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        assert!(!lambda.has_side_effects.get());
        assert_eq!(lambda.purity(), LambdaPurity::CapturesMutable);
    }

    #[test]
    fn lambda_purity_mutates_captures() {
        let source = r#"
            func apply(f: () -> i64) -> i64 { return f() }
            func main() {
                let mut x = 10
                let f: () -> i64 = () => {
                    x = x + 1
                    return x
                }
                apply(f)
            }
        "#;
        let (program, _interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        assert!(!lambda.has_side_effects.get());
        assert_eq!(lambda.purity(), LambdaPurity::MutatesCaptures);
    }

    #[test]
    fn lambda_side_effects_take_precedence_over_captures() {
        // Even though we capture and mutate, side effects take precedence
        let source = r#"
            func apply(f: () -> i64) -> i64 { return f() }
            func main() {
                let mut x = 10
                let f: () -> i64 = () => {
                    println("hello")
                    x = x + 1
                    return x
                }
                apply(f)
            }
        "#;
        let (program, _interner) = parse_and_analyze(source);
        let lambda = get_first_lambda(&program);
        assert!(lambda.has_side_effects.get());
        assert_eq!(lambda.purity(), LambdaPurity::HasSideEffects);
    }

    // Helper for satisfies_interface tests
    fn analyze_and_check_interface(source: &str) -> Analyzer {
        let mut parser = Parser::new(source);
        let program = parser.parse_program().unwrap();
        let interner = parser.into_interner();
        let mut analyzer = Analyzer::new("test.vole", source);
        let _ = analyzer.analyze(&program, &interner);
        analyzer
    }

    #[test]
    fn satisfies_interface_with_field() {
        let source = r#"
            interface Named {
                name: string
            }

            record Person {
                name: string,
                age: i64,
            }
        "#;
        let analyzer = analyze_and_check_interface(source);

        // Get the symbols for Person and Named
        let mut parser = Parser::new(source);
        let _ = parser.parse_program().unwrap();
        let mut interner = parser.into_interner();
        let person_sym = interner.intern("Person");
        let named_sym = interner.intern("Named");

        // Get the Person type
        let person_type = analyzer.records.get(&person_sym).unwrap();
        let ty = Type::Record(person_type.clone());

        // Check if Person satisfies Named
        assert!(analyzer.satisfies_interface(&ty, named_sym));
    }

    #[test]
    fn satisfies_interface_missing_field() {
        let source = r#"
            interface Named {
                name: string
            }

            record Point {
                x: i64,
                y: i64,
            }
        "#;
        let analyzer = analyze_and_check_interface(source);

        let mut parser = Parser::new(source);
        let _ = parser.parse_program().unwrap();
        let mut interner = parser.into_interner();
        let point_sym = interner.intern("Point");
        let named_sym = interner.intern("Named");

        let point_type = analyzer.records.get(&point_sym).unwrap();
        let ty = Type::Record(point_type.clone());

        // Point does NOT satisfy Named (missing name field)
        assert!(!analyzer.satisfies_interface(&ty, named_sym));
    }

    #[test]
    fn satisfies_interface_with_method() {
        let source = r#"
            interface Hashable {
                func hash() -> i64
            }

            record User {
                id: i64,
                func hash() -> i64 {
                    return self.id
                }
            }
        "#;
        let analyzer = analyze_and_check_interface(source);

        let mut parser = Parser::new(source);
        let _ = parser.parse_program().unwrap();
        let mut interner = parser.into_interner();
        let user_sym = interner.intern("User");
        let hashable_sym = interner.intern("Hashable");

        let user_type = analyzer.records.get(&user_sym).unwrap();
        let ty = Type::Record(user_type.clone());

        assert!(analyzer.satisfies_interface(&ty, hashable_sym));
    }
}
