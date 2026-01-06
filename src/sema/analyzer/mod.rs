// src/sema/analyzer/mod.rs

mod expr;
mod lambda;
mod methods;
mod patterns;
mod stmt;

use crate::errors::SemanticError;
use crate::frontend::*;
use crate::module::ModuleLoader;
use crate::sema::implement_registry::{ExternalMethodInfo, ImplementRegistry, MethodImpl, TypeId};
use crate::sema::interface_registry::{
    InterfaceDef, InterfaceFieldDef, InterfaceMethodDef, InterfaceRegistry,
};
use crate::sema::resolution::{MethodResolutions, ResolvedMethod};
use crate::sema::types::{ConstantValue, ModuleType};
use crate::sema::{
    ClassType, ErrorTypeInfo, FunctionType, RecordType, StructField, Type,
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
    /// Current function's error type (if fallible)
    current_function_error_type: Option<Type>,
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
    /// Registered error types (e.g., DivByZero, OutOfRange)
    error_types: HashMap<Symbol, ErrorTypeInfo>,
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
    /// Module loader for handling imports
    module_loader: ModuleLoader,
    /// Analyzed module types by import path
    module_types: HashMap<String, ModuleType>,
    /// Parsed module programs and their interners (for compiling pure Vole functions)
    module_programs: HashMap<String, (Program, Interner)>,
    /// Flag to prevent recursive prelude loading
    loading_prelude: bool,
}

impl Analyzer {
    pub fn new(_file: &str, _source: &str) -> Self {
        let mut analyzer = Self {
            scope: Scope::new(),
            functions: HashMap::new(),
            globals: HashMap::new(),
            current_function_return: None,
            current_function_error_type: None,
            errors: Vec::new(),
            type_overrides: HashMap::new(),
            lambda_captures: Vec::new(),
            lambda_locals: Vec::new(),
            lambda_side_effects: Vec::new(),
            type_aliases: HashMap::new(),
            classes: HashMap::new(),
            records: HashMap::new(),
            error_types: HashMap::new(),
            methods: HashMap::new(),
            expr_types: HashMap::new(),
            interface_registry: InterfaceRegistry::new(),
            implement_registry: ImplementRegistry::new(),
            method_resolutions: MethodResolutions::new(),
            type_implements: HashMap::new(),
            module_loader: ModuleLoader::new(),
            module_types: HashMap::new(),
            module_programs: HashMap::new(),
            loading_prelude: false,
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

    /// Load prelude files (trait definitions and primitive type implementations)
    /// This is called at the start of analyze() to make stdlib methods available.
    fn load_prelude(&mut self, interner: &Interner) {
        // Don't load prelude if we're already loading it (prevents recursion)
        if self.loading_prelude {
            return;
        }

        // Check if stdlib is available
        if self.module_loader.stdlib_root().is_none() {
            return;
        }

        self.loading_prelude = true;

        // Load traits first (defines interfaces like Sized)
        self.load_prelude_file("std:prelude/traits", interner);

        // Load type preludes (implement blocks for primitive types)
        for path in [
            "std:prelude/string",
            "std:prelude/i64",
            "std:prelude/i32",
            "std:prelude/f64",
            "std:prelude/bool",
        ] {
            self.load_prelude_file(path, interner);
        }

        self.loading_prelude = false;
    }

    /// Load a single prelude file and merge its registries
    fn load_prelude_file(&mut self, import_path: &str, _interner: &Interner) {
        // Load source via module_loader
        let module_info = match self.module_loader.load(import_path) {
            Ok(info) => info,
            Err(_) => return, // Silently ignore missing prelude files
        };

        // Parse the module
        let mut parser = Parser::new(&module_info.source);
        let program = match parser.parse_program() {
            Ok(p) => p,
            Err(_) => return, // Silently ignore parse errors in prelude
        };

        let prelude_interner = parser.into_interner();

        // Create a sub-analyzer to analyze the prelude
        // Note: We don't call new() because that would try to load prelude again
        let mut sub_analyzer = Analyzer {
            scope: Scope::new(),
            functions: HashMap::new(),
            globals: HashMap::new(),
            current_function_return: None,
            current_function_error_type: None,
            errors: Vec::new(),
            type_overrides: HashMap::new(),
            lambda_captures: Vec::new(),
            lambda_locals: Vec::new(),
            lambda_side_effects: Vec::new(),
            type_aliases: HashMap::new(),
            classes: HashMap::new(),
            records: HashMap::new(),
            error_types: HashMap::new(),
            methods: HashMap::new(),
            expr_types: HashMap::new(),
            interface_registry: InterfaceRegistry::new(),
            implement_registry: ImplementRegistry::new(),
            method_resolutions: MethodResolutions::new(),
            type_implements: HashMap::new(),
            module_loader: ModuleLoader::new(),
            module_types: HashMap::new(),
            module_programs: HashMap::new(),
            loading_prelude: true, // Prevent sub-analyzer from loading prelude
        };

        // Copy existing interface registry so prelude files can reference earlier definitions
        sub_analyzer.interface_registry = self.interface_registry.clone();

        // Analyze the prelude file
        if sub_analyzer.analyze(&program, &prelude_interner).is_ok() {
            // TODO: Merge registries once symbol remapping is implemented
            // Currently, symbols from prelude files don't match symbols in user code
            // because each Parser has its own Interner. Until we implement symbol
            // remapping during merge, merging would cause false positive interface
            // lookups where Symbol(N) from prelude matches Symbol(N) from user code
            // even though they represent different strings.
            //
            // For now, the infrastructure is in place but actual merging is disabled.
            // A later task will implement proper symbol remapping.
            //
            // self.interface_registry.merge(&sub_analyzer.interface_registry);
            // self.implement_registry.merge(&sub_analyzer.implement_registry);
            let _ = sub_analyzer; // Suppress unused warning
        }
        // Silently ignore analysis errors in prelude
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
    /// type_implements, error_types, and module_programs (consuming self)
    #[allow(clippy::type_complexity)]
    pub fn into_analysis_results(
        self,
    ) -> (
        HashMap<Symbol, Type>,
        HashMap<NodeId, Type>,
        MethodResolutions,
        InterfaceRegistry,
        HashMap<Symbol, Vec<Symbol>>,
        HashMap<Symbol, ErrorTypeInfo>,
        HashMap<String, (Program, Interner)>,
    ) {
        (
            self.type_aliases,
            self.expr_types,
            self.method_resolutions,
            self.interface_registry,
            self.type_implements,
            self.error_types,
            self.module_programs,
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
        // Load prelude (trait definitions and primitive type implementations)
        // This makes stdlib methods like "hello".length() available without explicit imports
        self.load_prelude(interner);

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
                    if let Some(trait_name) = impl_block.trait_name
                        && self.interface_registry.get(trait_name).is_none()
                    {
                        self.add_error(
                            SemanticError::UnknownInterface {
                                name: interner.resolve(trait_name).to_string(),
                                span: impl_block.span.into(),
                            },
                            impl_block.span,
                        );
                    }

                    let target_type = self.resolve_type(&impl_block.target_type);

                    // Validate target type exists
                    if matches!(target_type, Type::Error) {
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
                                    external_info: None,
                                },
                            );
                        }

                        // Analyze external block if present
                        if let Some(ref external) = impl_block.external {
                            self.analyze_external_block(
                                external,
                                &target_type,
                                impl_block.trait_name,
                                interner,
                            );
                        }
                    }
                }
                Decl::Error(decl) => {
                    self.analyze_error_decl(decl);
                }
                Decl::External(_) => {
                    // External blocks are processed during code generation
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
                    // Validate interface satisfaction
                    if let Some(interfaces) = self.type_implements.get(&class.name).cloned() {
                        let type_methods = self.get_type_method_signatures(class.name);
                        for iface_name in interfaces {
                            self.validate_interface_satisfaction(
                                class.name,
                                iface_name,
                                &type_methods,
                                class.span,
                                interner,
                            );
                        }
                    }
                }
                Decl::Record(record) => {
                    for method in &record.methods {
                        self.check_method(method, record.name, interner)?;
                    }
                    // Validate interface satisfaction
                    if let Some(interfaces) = self.type_implements.get(&record.name).cloned() {
                        let type_methods = self.get_type_method_signatures(record.name);
                        for iface_name in interfaces {
                            self.validate_interface_satisfaction(
                                record.name,
                                iface_name,
                                &type_methods,
                                record.span,
                                interner,
                            );
                        }
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
                Decl::Error(_) => {
                    // Error declarations fully processed in first pass
                }
                Decl::External(_) => {
                    // External blocks are processed during code generation
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
        let ctx = TypeResolutionContext {
            type_aliases: &self.type_aliases,
            classes: &self.classes,
            records: &self.records,
            error_types: &self.error_types,
            interface_registry: &self.interface_registry,
        };
        resolve_type(ty, &ctx)
    }

    fn analyze_error_decl(&mut self, decl: &ErrorDecl) {
        let mut fields = Vec::new();

        for (slot, field) in decl.fields.iter().enumerate() {
            let ctx = TypeResolutionContext {
                type_aliases: &self.type_aliases,
                classes: &self.classes,
                records: &self.records,
                error_types: &self.error_types,
                interface_registry: &self.interface_registry,
            };
            let ty = resolve_type(&field.ty, &ctx);

            fields.push(StructField {
                name: field.name,
                ty,
                slot,
            });
        }

        let error_info = ErrorTypeInfo {
            name: decl.name,
            fields,
        };

        self.error_types.insert(decl.name, error_info);
    }

    /// Analyze external block and register external methods in the implement registry
    fn analyze_external_block(
        &mut self,
        external: &ExternalBlock,
        target_type: &Type,
        trait_name: Option<Symbol>,
        interner: &Interner,
    ) {
        let type_id = match TypeId::from_type(target_type) {
            Some(id) => id,
            None => return, // Skip non-registerable types
        };

        for func in &external.functions {
            // Resolve parameter types
            let param_types: Vec<Type> = func
                .params
                .iter()
                .map(|p| self.resolve_type(&p.ty))
                .collect();

            // Resolve return type
            let return_type = match &func.return_type {
                Some(te) => self.resolve_type(te),
                None => Type::Void,
            };

            let func_type = FunctionType {
                params: param_types,
                return_type: Box::new(return_type),
                is_closure: false,
            };

            // Determine native name: explicit or default to vole_name
            let native_name = func
                .native_name
                .clone()
                .unwrap_or_else(|| interner.resolve(func.vole_name).to_string());

            // Register in implement registry
            self.implement_registry.register_method(
                type_id.clone(),
                func.vole_name,
                MethodImpl {
                    trait_name,
                    func_type,
                    is_builtin: false,
                    external_info: Some(ExternalMethodInfo {
                        module_path: external.module_path.clone(),
                        native_name,
                    }),
                },
            );
        }
    }

    fn check_function(
        &mut self,
        func: &FuncDecl,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        let func_type = self.functions.get(&func.name).cloned().unwrap();
        let return_type = *func_type.return_type.clone();
        self.current_function_return = Some(return_type.clone());

        // Set error type context if this is a fallible function
        if let Type::Fallible(ref ft) = return_type {
            self.current_function_error_type = Some((*ft.error_type).clone());
        } else {
            self.current_function_error_type = None;
        }

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
        self.current_function_error_type = None;

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
        let return_type = *method_type.return_type.clone();
        self.current_function_return = Some(return_type.clone());

        // Set error type context if this is a fallible method
        if let Type::Fallible(ref ft) = return_type {
            self.current_function_error_type = Some((*ft.error_type).clone());
        } else {
            self.current_function_error_type = None;
        }

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
        self.current_function_error_type = None;

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

    /// Analyze an imported module and return its type
    #[allow(clippy::result_unit_err)] // Error is added to self.errors vector
    pub fn analyze_module(
        &mut self,
        import_path: &str,
        span: Span,
        _interner: &Interner,
    ) -> Result<Type, ()> {
        // Check cache first
        if let Some(module_type) = self.module_types.get(import_path) {
            return Ok(Type::Module(module_type.clone()));
        }

        // Load the module
        let module_info = match self.module_loader.load(import_path) {
            Ok(info) => info,
            Err(e) => {
                self.add_error(
                    SemanticError::ModuleNotFound {
                        path: import_path.to_string(),
                        message: e.to_string(),
                        span: span.into(),
                    },
                    span,
                );
                return Err(());
            }
        };

        // Parse the module
        let mut parser = Parser::new(&module_info.source);
        let program = match parser.parse_program() {
            Ok(p) => p,
            Err(e) => {
                self.add_error(
                    SemanticError::ModuleParseError {
                        path: import_path.to_string(),
                        message: format!("{:?}", e.error),
                        span: span.into(),
                    },
                    span,
                );
                return Err(());
            }
        };

        // Collect exports, constants, and track external functions
        let mut exports = HashMap::new();
        let mut constants = HashMap::new();
        let mut external_funcs = HashSet::new();
        let module_interner = parser.into_interner();

        for decl in &program.declarations {
            match decl {
                Decl::Function(f) => {
                    // Build function type from signature
                    let ctx = TypeResolutionContext {
                        type_aliases: &self.type_aliases,
                        classes: &self.classes,
                        records: &self.records,
                        error_types: &self.error_types,
                        interface_registry: &self.interface_registry,
                    };
                    let params: Vec<Type> =
                        f.params.iter().map(|p| resolve_type(&p.ty, &ctx)).collect();
                    let return_type = f
                        .return_type
                        .as_ref()
                        .map(|rt| resolve_type(rt, &ctx))
                        .unwrap_or(Type::Void);

                    let func_type = Type::Function(FunctionType {
                        params,
                        return_type: Box::new(return_type),
                        is_closure: false,
                    });

                    // Store export by name string
                    let name_str = module_interner.resolve(f.name).to_string();
                    exports.insert(name_str, func_type);
                }
                Decl::Let(l) if !l.mutable => {
                    // Only export immutable let bindings
                    // Infer type from literal for constants and store the value
                    let name_str = module_interner.resolve(l.name).to_string();
                    let (ty, const_val) = match &l.init.kind {
                        ExprKind::FloatLiteral(v) => (Type::F64, Some(ConstantValue::F64(*v))),
                        ExprKind::IntLiteral(v) => (Type::I64, Some(ConstantValue::I64(*v))),
                        ExprKind::BoolLiteral(v) => (Type::Bool, Some(ConstantValue::Bool(*v))),
                        ExprKind::StringLiteral(v) => {
                            (Type::String, Some(ConstantValue::String(v.clone())))
                        }
                        _ => (Type::Unknown, None), // Complex expressions need full analysis
                    };
                    exports.insert(name_str.clone(), ty);
                    if let Some(cv) = const_val {
                        constants.insert(name_str, cv);
                    }
                }
                Decl::External(ext) => {
                    // External block functions become exports and are marked as external
                    let ctx = TypeResolutionContext {
                        type_aliases: &self.type_aliases,
                        classes: &self.classes,
                        records: &self.records,
                        error_types: &self.error_types,
                        interface_registry: &self.interface_registry,
                    };
                    for func in &ext.functions {
                        let params: Vec<Type> = func
                            .params
                            .iter()
                            .map(|p| resolve_type(&p.ty, &ctx))
                            .collect();
                        let return_type = func
                            .return_type
                            .as_ref()
                            .map(|rt| resolve_type(rt, &ctx))
                            .unwrap_or(Type::Void);

                        let func_type = Type::Function(FunctionType {
                            params,
                            return_type: Box::new(return_type),
                            is_closure: false,
                        });

                        let name_str = module_interner.resolve(func.vole_name).to_string();
                        exports.insert(name_str.clone(), func_type);
                        // Mark as external function (FFI)
                        external_funcs.insert(name_str);
                    }
                }
                _ => {} // Skip other declarations for now
            }
        }

        let module_type = ModuleType {
            path: import_path.to_string(),
            exports,
            constants,
            external_funcs,
        };

        self.module_types
            .insert(import_path.to_string(), module_type.clone());

        // Store the program and interner for compiling pure Vole functions
        self.module_programs
            .insert(import_path.to_string(), (program, module_interner));

        Ok(Type::Module(module_type))
    }
}

// Note: Default is not implemented because Analyzer requires file and source parameters

#[cfg(test)]
mod tests;
