// src/sema/analyzer/mod.rs

mod declarations;
mod expr;
mod lambda;
mod methods;
mod patterns;
mod stmt;

use crate::errors::SemanticError;
use crate::frontend::*;
use crate::identity::{self, ModuleId, NameId, NameTable, Namer, Resolver};
use crate::module::ModuleLoader;
use crate::sema::EntityRegistry;
use crate::sema::entity_defs::TypeDefKind;
use crate::sema::generic::{
    GenericFuncDef, GenericRecordDef, MonomorphCache, MonomorphInstance, MonomorphKey,
    TypeParamInfo, TypeParamScope, substitute_type,
};
use crate::sema::implement_registry::{
    ExternalMethodInfo, ImplementRegistry, MethodImpl, PrimitiveTypeId, TypeId,
};
use crate::sema::resolution::{MethodResolutions, ResolvedMethod};
use crate::sema::types::{ConstantValue, ModuleType};
use crate::sema::{
    ErrorTypeInfo, FunctionType, RecordType, StructField, Type, TypeKey, WellKnownTypes,
    compatibility::{function_compatible_with_interface, literal_fits, types_compatible_core},
    resolve::{TypeResolutionContext, resolve_type},
    scope::{Scope, Variable},
    type_table::TypeTable,
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
    /// Functions registered by string name (for prelude functions that cross interner boundaries)
    functions_by_name: HashMap<String, FunctionType>,
    /// External function info by string name (module path and native name)
    pub external_func_info: HashMap<String, ExternalMethodInfo>,
    globals: HashMap<Symbol, Type>,
    current_function_return: Option<Type>,
    /// Current function's error type (if fallible)
    current_function_error_type: Option<Type>,
    /// Generator context: if inside a generator function, this holds the Iterator element type.
    /// None means we're not in a generator (or not in a function at all).
    current_generator_element_type: Option<Type>,
    /// If we're inside a static method, this holds the method name (for error reporting).
    /// None means we're not in a static method.
    current_static_method: Option<String>,
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
    /// Registered error types (e.g., DivByZero, OutOfRange)
    error_types: HashMap<Symbol, ErrorTypeInfo>,
    /// Resolved types for each expression node (for codegen)
    /// Maps expression node IDs to their resolved types, including narrowed types
    expr_types: HashMap<NodeId, Type>,
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
    /// Generic function definitions (with type params)
    generic_functions: HashMap<Symbol, GenericFuncDef>,
    /// Generic record definitions (with type params)
    generic_records: HashMap<Symbol, GenericRecordDef>,
    /// Cache of monomorphized function instances
    pub monomorph_cache: MonomorphCache,
    /// Mapping from call expression NodeId to MonomorphKey (for generic function calls)
    generic_calls: HashMap<NodeId, MonomorphKey>,
    /// Fully-qualified name interner for printable identities
    name_table: NameTable,
    /// Opaque type identities for named types
    type_table: TypeTable,
    /// Current module being analyzed (for proper NameId registration)
    current_module: ModuleId,
    /// Well-known stdlib type NameIds for fast comparison
    pub well_known: WellKnownTypes,
    /// Entity registry for first-class type/method/field/function identity
    pub entity_registry: EntityRegistry,
}

impl Analyzer {
    pub fn new(_file: &str, _source: &str) -> Self {
        // Create name_table first to get main_module
        let name_table = NameTable::new();
        let main_module = name_table.main_module();

        let mut analyzer = Self {
            scope: Scope::new(),
            functions: HashMap::new(),
            functions_by_name: HashMap::new(),
            external_func_info: HashMap::new(),
            globals: HashMap::new(),
            current_function_return: None,
            current_function_error_type: None,
            current_generator_element_type: None,
            current_static_method: None,
            errors: Vec::new(),
            type_overrides: HashMap::new(),
            lambda_captures: Vec::new(),
            lambda_locals: Vec::new(),
            lambda_side_effects: Vec::new(),
            type_aliases: HashMap::new(),
            error_types: HashMap::new(),
            expr_types: HashMap::new(),
            implement_registry: ImplementRegistry::new(),
            method_resolutions: MethodResolutions::new(),
            type_implements: HashMap::new(),
            module_loader: ModuleLoader::new(),
            module_types: HashMap::new(),
            module_programs: HashMap::new(),
            loading_prelude: false,
            generic_functions: HashMap::new(),
            generic_records: HashMap::new(),
            monomorph_cache: MonomorphCache::new(),
            generic_calls: HashMap::new(),
            name_table,
            type_table: TypeTable::new(),
            current_module: main_module,
            well_known: WellKnownTypes::new(),
            entity_registry: EntityRegistry::new(),
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

    fn register_builtin_methods(&mut self, interner: &Interner) {
        macro_rules! register_builtin {
            ($type_id:expr, $method_id:expr, $func_type:expr) => {
                self.implement_registry.register_method(
                    $type_id,
                    $method_id,
                    MethodImpl {
                        trait_name: None,
                        func_type: $func_type,
                        is_builtin: true,
                        external_info: None,
                    },
                );
            };
            ($type_id:expr, $method_id:expr, $func_type:expr, $external_info:expr) => {
                self.implement_registry.register_method(
                    $type_id,
                    $method_id,
                    MethodImpl {
                        trait_name: None,
                        func_type: $func_type,
                        is_builtin: true,
                        external_info: $external_info,
                    },
                );
            };
        }

        let builtin_module = self.name_table.builtin_module();
        let mut namer = Namer::new(&mut self.name_table, interner);
        let mut method_id = |name: &str| namer.intern_raw(builtin_module, &[name]);
        let method_len = method_id("length");
        let method_iter = method_id("iter");
        let array_id = self.type_table.array_name_id().map(TypeId::from_name_id);
        let string_id = self
            .type_table
            .primitive_name_id(PrimitiveTypeId::String)
            .map(TypeId::from_name_id);

        if let Some(type_id) = array_id {
            register_builtin!(
                type_id,
                method_len,
                FunctionType {
                    params: vec![],
                    return_type: Box::new(Type::I64),
                    is_closure: false,
                }
            );
            register_builtin!(
                type_id,
                method_iter,
                FunctionType {
                    params: vec![],
                    return_type: Box::new(Type::Unknown),
                    is_closure: false,
                },
                Some(ExternalMethodInfo {
                    module_path: "std:intrinsics".to_string(),
                    native_name: "array_iter".to_string(),
                    return_type: None, // Refined by check_builtin_method
                })
            );
        }

        if let Some(type_id) = string_id {
            register_builtin!(
                type_id,
                method_len,
                FunctionType {
                    params: vec![],
                    return_type: Box::new(Type::I64),
                    is_closure: false,
                }
            );
            register_builtin!(
                type_id,
                method_iter,
                FunctionType {
                    params: vec![],
                    return_type: Box::new(Type::Unknown), // Will be refined by check_builtin_method
                    is_closure: false,
                },
                Some(ExternalMethodInfo {
                    module_path: "std:intrinsics".to_string(),
                    native_name: "string_chars_iter".to_string(),
                    return_type: None, // Refined by check_builtin_method
                })
            );
        }

        // Range.iter() -> Iterator<i64>
        let range_id = self
            .type_table
            .primitive_name_id(PrimitiveTypeId::Range)
            .map(TypeId::from_name_id);
        if let Some(type_id) = range_id {
            register_builtin!(
                type_id,
                method_iter,
                FunctionType {
                    params: vec![],
                    return_type: Box::new(Type::Unknown), // Will be refined by check_builtin_method
                    is_closure: false,
                },
                Some(ExternalMethodInfo {
                    module_path: "std:intrinsics".to_string(),
                    native_name: "range_iter".to_string(),
                    return_type: None, // Refined by check_builtin_method
                })
            );
        }

        // Iterator methods are resolved via interface declarations in the prelude.
    }

    fn register_primitive_name_ids(&mut self, interner: &Interner) {
        let builtin_module = self.name_table.builtin_module();
        let mut namer = Namer::new(&mut self.name_table, interner);
        for prim in [
            PrimitiveTypeId::I8,
            PrimitiveTypeId::I16,
            PrimitiveTypeId::I32,
            PrimitiveTypeId::I64,
            PrimitiveTypeId::I128,
            PrimitiveTypeId::U8,
            PrimitiveTypeId::U16,
            PrimitiveTypeId::U32,
            PrimitiveTypeId::U64,
            PrimitiveTypeId::F32,
            PrimitiveTypeId::F64,
            PrimitiveTypeId::Bool,
            PrimitiveTypeId::String,
            PrimitiveTypeId::Range,
        ] {
            let name_id = if let Some(sym) = interner.lookup(prim.name()) {
                namer.intern_symbol(builtin_module, sym)
            } else {
                namer.intern_raw(builtin_module, &[prim.name()])
            };
            self.type_table.register_primitive_name(prim, name_id);
        }
        let array_name = namer.intern_raw(builtin_module, &["array"]);
        self.type_table.register_array_name(array_name);
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
            "std:prelude/iterators",
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

        let mut prelude_interner = parser.into_interner();
        prelude_interner.seed_builtin_symbols();

        // Get the module ID for this prelude file path
        let prelude_module = self.name_table.module_id(import_path);

        // Create a sub-analyzer to analyze the prelude
        // Note: We don't call new() because that would try to load prelude again
        let mut sub_analyzer = Analyzer {
            scope: Scope::new(),
            functions: HashMap::new(),
            functions_by_name: HashMap::new(),
            external_func_info: HashMap::new(),
            globals: HashMap::new(),
            current_function_return: None,
            current_function_error_type: None,
            current_generator_element_type: None,
            current_static_method: None,
            errors: Vec::new(),
            type_overrides: HashMap::new(),
            lambda_captures: Vec::new(),
            lambda_locals: Vec::new(),
            lambda_side_effects: Vec::new(),
            type_aliases: HashMap::new(),
            error_types: HashMap::new(),
            expr_types: HashMap::new(),
            implement_registry: ImplementRegistry::new(),
            method_resolutions: MethodResolutions::new(),
            type_implements: HashMap::new(),
            module_loader: ModuleLoader::new(),
            module_types: HashMap::new(),
            module_programs: HashMap::new(),
            loading_prelude: true, // Prevent sub-analyzer from loading prelude
            generic_functions: HashMap::new(),
            generic_records: HashMap::new(),
            monomorph_cache: MonomorphCache::new(),
            generic_calls: HashMap::new(),
            name_table: NameTable::new(),
            type_table: TypeTable::new(),
            current_module: prelude_module, // Use the prelude module path!
            well_known: WellKnownTypes::new(),
            entity_registry: EntityRegistry::new(),
        };

        // Copy existing registries so prelude files can reference earlier definitions
        sub_analyzer.name_table = self.name_table.clone();
        sub_analyzer.type_table = self.type_table.clone();
        sub_analyzer.entity_registry = self.entity_registry.clone();

        // Analyze the prelude file
        if sub_analyzer.analyze(&program, &prelude_interner).is_ok() {
            // Merge the entity registry (types, methods, fields)
            self.entity_registry.merge(&sub_analyzer.entity_registry);
            // Merge the implement registry
            self.implement_registry
                .merge(&sub_analyzer.implement_registry);
            // Merge functions by name (for standalone external function declarations)
            // We use by_name because the Symbol lookup won't work across interners
            for (name, func_type) in sub_analyzer.functions_by_name {
                self.functions_by_name.insert(name, func_type);
            }
            // Merge external function info (module path and native name)
            for (name, info) in sub_analyzer.external_func_info {
                self.external_func_info.insert(name, info);
            }
            // Keep name/type tables in sync with prelude interned ids.
            self.name_table = sub_analyzer.name_table;
            self.type_table = sub_analyzer.type_table;
        }
        // Silently ignore analysis errors in prelude
    }

    /// Helper to add a type error
    fn add_error(&mut self, error: SemanticError, span: Span) {
        self.errors.push(TypeError::new(error, span));
    }

    fn type_key_for(&mut self, ty: &Type) -> TypeKey {
        self.type_table.key_for_type(ty)
    }

    fn type_display(&mut self, ty: &Type) -> String {
        self.type_table.display_type(ty, &mut self.name_table)
    }

    fn type_display_pair(&mut self, left: &Type, right: &Type) -> String {
        format!(
            "{} and {}",
            self.type_display(left),
            self.type_display(right)
        )
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

    /// Infer type parameters from argument types.
    /// Given type params like [T, U], param types like [T, [U]], and arg types like [i64, [string]],
    /// returns a map {NameId -> Type} for substitution.
    pub(crate) fn infer_type_params(
        &self,
        type_params: &[TypeParamInfo],
        param_types: &[Type],
        arg_types: &[Type],
    ) -> HashMap<NameId, Type> {
        let mut inferred = HashMap::new();

        // For each parameter, try to match its type against the argument type
        for (param_type, arg_type) in param_types.iter().zip(arg_types.iter()) {
            self.unify_types(param_type, arg_type, type_params, &mut inferred);
        }

        inferred
    }

    /// Unify a parameter type pattern with an argument type, extracting type param bindings.
    fn unify_types(
        &self,
        pattern: &Type,
        actual: &Type,
        type_params: &[TypeParamInfo],
        inferred: &mut HashMap<NameId, Type>,
    ) {
        match (pattern, actual) {
            // If the pattern is a type param, bind it
            (Type::TypeParam(name_id), actual) => {
                // Only bind if it's one of our type params
                if type_params.iter().any(|tp| tp.name_id == *name_id) {
                    // Only bind if not already bound (first binding wins)
                    inferred.entry(*name_id).or_insert_with(|| actual.clone());
                }
            }
            // Array: unify element types
            (Type::Array(p_elem), Type::Array(a_elem)) => {
                self.unify_types(p_elem, a_elem, type_params, inferred);
            }
            // Interface types: unify type args for the same interface
            (Type::Interface(p_iface), Type::Interface(a_iface))
                if p_iface.name_id == a_iface.name_id =>
            {
                for (p_arg, a_arg) in p_iface.type_args.iter().zip(a_iface.type_args.iter()) {
                    self.unify_types(p_arg, a_arg, type_params, inferred);
                }
            }
            // Union: try to match each pattern variant
            (Type::Union(p_types), Type::Union(a_types)) => {
                for (p, a) in p_types.iter().zip(a_types.iter()) {
                    self.unify_types(p, a, type_params, inferred);
                }
            }
            // Function types: unify params and return
            (Type::Function(p_ft), Type::Function(a_ft)) => {
                for (p, a) in p_ft.params.iter().zip(a_ft.params.iter()) {
                    self.unify_types(p, a, type_params, inferred);
                }
                self.unify_types(&p_ft.return_type, &a_ft.return_type, type_params, inferred);
            }
            // GenericInstance: unify type args
            (
                Type::GenericInstance { args: p_args, .. },
                Type::GenericInstance { args: a_args, .. },
            ) => {
                for (p, a) in p_args.iter().zip(a_args.iter()) {
                    self.unify_types(p, a, type_params, inferred);
                }
            }
            // Everything else: no type params to extract
            _ => {}
        }
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

    /// Get a resolver configured for the current module context.
    /// Uses the resolution chain: primitives -> current module -> builtin module.
    pub fn resolver<'a>(&'a self, interner: &'a Interner) -> Resolver<'a> {
        // For now, we don't track imports at the Analyzer level.
        // The resolver will check: primitives, current module, then builtin module.
        Resolver::new(interner, &self.name_table, self.current_module, &[])
    }

    /// Take ownership of the expression types (consuming self)
    pub fn into_expr_types(self) -> HashMap<NodeId, Type> {
        self.expr_types
    }

    /// Take ownership of analysis results (consuming self)
    #[allow(clippy::type_complexity)]
    pub fn into_analysis_results(
        self,
    ) -> (
        HashMap<Symbol, Type>,
        HashMap<NodeId, Type>,
        MethodResolutions,
        ImplementRegistry,
        HashMap<Symbol, Vec<Symbol>>,
        HashMap<Symbol, ErrorTypeInfo>,
        HashMap<String, (Program, Interner)>,
        HashMap<Symbol, GenericFuncDef>,
        HashMap<Symbol, GenericRecordDef>,
        MonomorphCache,
        HashMap<NodeId, MonomorphKey>,
        HashMap<String, ExternalMethodInfo>,
        NameTable,
        TypeTable,
        WellKnownTypes,
        EntityRegistry,
    ) {
        (
            self.type_aliases,
            self.expr_types,
            self.method_resolutions,
            self.implement_registry,
            self.type_implements,
            self.error_types,
            self.module_programs,
            self.generic_functions,
            self.generic_records,
            self.monomorph_cache,
            self.generic_calls,
            self.external_func_info,
            self.name_table,
            self.type_table,
            self.well_known,
            self.entity_registry,
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

    fn register_named_type(&mut self, name: Symbol, ty: Type, interner: &Interner) {
        let name_id = self
            .name_table
            .intern(self.current_module, &[name], interner);
        self.type_table.insert_named(ty, name_id);
    }

    fn module_name_id(&self, module_id: ModuleId, name: &str) -> Option<NameId> {
        let module_path = self.name_table.module_path(module_id);
        let (_, module_interner) = self.module_programs.get(module_path)?;
        let sym = module_interner.lookup(name)?;
        self.name_table.name_id(module_id, &[sym], module_interner)
    }

    fn interface_type(
        &mut self,
        name: &str,
        type_args: Vec<Type>,
        interner: &Interner,
    ) -> Option<Type> {
        // Look up interface by string name using resolver with interface fallback
        let type_def_id = self
            .resolver(interner)
            .resolve_type_str_or_interface(name, &self.entity_registry)?;
        let type_def = self.entity_registry.get_type(type_def_id);

        // Check type params match
        if !type_def.type_params.is_empty() && type_def.type_params.len() != type_args.len() {
            return Some(Type::Error);
        }

        // Build substitution map using type param NameIds
        let mut substitutions = HashMap::new();
        for (name_id, arg) in type_def.type_params.iter().zip(type_args.iter()) {
            substitutions.insert(*name_id, arg.clone());
        }

        // Build methods with substituted types
        let methods: Vec<crate::sema::types::InterfaceMethodType> = type_def
            .methods
            .iter()
            .map(|&method_id| {
                let method = self.entity_registry.get_method(method_id);
                crate::sema::types::InterfaceMethodType {
                    name: method.name_id,
                    params: method
                        .signature
                        .params
                        .iter()
                        .map(|t| substitute_type(t, &substitutions))
                        .collect(),
                    return_type: Box::new(substitute_type(
                        &method.signature.return_type,
                        &substitutions,
                    )),
                    has_default: method.has_default,
                }
            })
            .collect();

        // Build extends from TypeDefIds -> NameIds
        let extends: Vec<NameId> = type_def
            .extends
            .iter()
            .map(|&parent_id| self.entity_registry.get_type(parent_id).name_id)
            .collect();

        Some(Type::Interface(crate::sema::types::InterfaceType {
            name_id: type_def.name_id,
            type_args,
            methods,
            extends,
        }))
    }

    fn method_name_id(&mut self, name: Symbol, interner: &Interner) -> NameId {
        let mut namer = Namer::new(&mut self.name_table, interner);
        namer.method(name)
    }

    /// Look up a method NameId by string name (cross-interner safe)
    fn method_name_id_by_str(&self, name_str: &str, interner: &Interner) -> Option<NameId> {
        identity::method_name_id_by_str(&self.name_table, interner, name_str)
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

    /// Get function type if the symbol refers to a top-level function.
    /// Returns None if the symbol is not a function name.
    fn get_function_type(&self, sym: Symbol, interner: &Interner) -> Option<FunctionType> {
        // Check by Symbol first (same interner)
        if let Some(func_type) = self.functions.get(&sym) {
            return Some(func_type.clone());
        }
        // Check by name for prelude functions (cross-interner lookup)
        let name = interner.resolve(sym);
        self.functions_by_name.get(name).cloned()
    }

    pub fn analyze(
        &mut self,
        program: &Program,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        self.register_primitive_name_ids(interner);
        self.register_builtin_methods(interner);

        // Load prelude (trait definitions and primitive type implementations)
        // This makes stdlib methods like "hello".length() available without explicit imports
        self.load_prelude(interner);

        // Populate well-known types after prelude has registered all interfaces
        self.well_known.populate(&mut self.name_table);

        // Pass 0: Collect type aliases first (so they're available for function signatures)
        self.collect_type_aliases(program, interner);

        // Pass 1: Collect signatures for all declarations
        self.collect_signatures(program, interner);

        // Process global let declarations
        self.process_global_lets(program, interner)?;

        // Pass 2: type check function bodies and tests
        self.check_declaration_bodies(program, interner)?;

        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(std::mem::take(&mut self.errors))
        }
    }

    fn resolve_type(&mut self, ty: &TypeExpr, interner: &Interner) -> Type {
        self.resolve_type_with_self(ty, interner, None)
    }

    /// Resolve a type expression with an optional Self type for method signatures
    fn resolve_type_with_self(
        &mut self,
        ty: &TypeExpr,
        interner: &Interner,
        self_type: Option<Type>,
    ) -> Type {
        let module_id = self.current_module;
        let mut ctx = TypeResolutionContext {
            type_aliases: &self.type_aliases,
            error_types: &self.error_types,
            entity_registry: &self.entity_registry,
            interner,
            name_table: &mut self.name_table,
            module_id,
            type_params: None,
            self_type,
        };
        resolve_type(ty, &mut ctx)
    }

    /// Pass 0: Collect type aliases (so they're available for function signatures)
    fn collect_type_aliases(&mut self, program: &Program, interner: &Interner) {
        for decl in &program.declarations {
            if let Decl::Let(let_stmt) = decl
                && let ExprKind::TypeLiteral(type_expr) = &let_stmt.init.kind
            {
                let aliased_type = self.resolve_type(type_expr, interner);
                self.type_aliases
                    .insert(let_stmt.name, aliased_type.clone());
                self.register_named_type(let_stmt.name, aliased_type, interner);
            }
        }
    }

    /// Process global let declarations (type check and add to scope)
    fn process_global_lets(
        &mut self,
        program: &Program,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        for decl in &program.declarations {
            if let Decl::Let(let_stmt) = decl {
                let declared_type = let_stmt.ty.as_ref().map(|t| self.resolve_type(t, interner));
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
                    let aliased_type = self.resolve_type(type_expr, interner);
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
        Ok(())
    }

    /// Pass 2: Type check function bodies, tests, and methods
    fn check_declaration_bodies(
        &mut self,
        program: &Program,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    self.check_function(func, interner)?;
                }
                Decl::Tests(tests_decl) => {
                    self.check_tests(tests_decl, interner)?;
                }
                Decl::Let(_) => {
                    // Already processed in process_global_lets
                }
                Decl::Class(class) => {
                    for method in &class.methods {
                        self.check_method(method, class.name, interner)?;
                    }
                    // Check static methods if present
                    if let Some(ref statics) = class.statics {
                        for method in &statics.methods {
                            self.check_static_method(method, class.name, interner)?;
                        }
                    }
                    // Validate interface satisfaction
                    if let Some(interfaces) = self.type_implements.get(&class.name).cloned() {
                        let type_methods = self.get_type_method_signatures(class.name, interner);
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
                    // Check static methods if present
                    if let Some(ref statics) = record.statics {
                        for method in &statics.methods {
                            self.check_static_method(method, record.name, interner)?;
                        }
                    }
                    // Validate interface satisfaction
                    if let Some(interfaces) = self.type_implements.get(&record.name).cloned() {
                        let type_methods = self.get_type_method_signatures(record.name, interner);
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
                Decl::Interface(interface_decl) => {
                    // Check static method default bodies
                    if let Some(ref statics) = interface_decl.statics {
                        for method in &statics.methods {
                            self.check_static_method(method, interface_decl.name, interner)?;
                        }
                    }
                }
                Decl::Implement(impl_block) => {
                    // Check static methods in implement blocks
                    if let Some(ref statics) = impl_block.statics {
                        // Get the target type name
                        if let TypeExpr::Named(type_name) = &impl_block.target_type {
                            for method in &statics.methods {
                                self.check_static_method(method, *type_name, interner)?;
                            }
                        }
                    }
                }
                Decl::Error(_) => {
                    // Error declarations fully processed in first pass
                }
                Decl::External(_) => {
                    // External blocks are processed during code generation
                }
            }
        }
        Ok(())
    }

    fn analyze_error_decl(&mut self, decl: &ErrorDecl, interner: &Interner) {
        let mut fields = Vec::new();

        for (slot, field) in decl.fields.iter().enumerate() {
            let module_id = self.current_module;
            let mut ctx = TypeResolutionContext {
                type_aliases: &self.type_aliases,
                error_types: &self.error_types,
                entity_registry: &self.entity_registry,
                interner,
                name_table: &mut self.name_table,
                module_id,
                type_params: None,
                self_type: None,
            };
            let ty = resolve_type(&field.ty, &mut ctx);

            fields.push(StructField {
                name: interner.resolve(field.name).to_string(),
                ty,
                slot,
            });
        }

        let name_id = self
            .name_table
            .intern(self.current_module, &[decl.name], interner);

        let error_info = ErrorTypeInfo {
            name: decl.name,
            name_id,
            fields: fields.clone(),
        };

        self.error_types.insert(decl.name, error_info.clone());
        self.register_named_type(decl.name, Type::ErrorType(error_info), interner);

        // Register in EntityRegistry (parallel migration)
        let entity_type_id = self.entity_registry.register_type(
            name_id,
            TypeDefKind::ErrorType,
            self.current_module,
        );

        // Register fields in EntityRegistry
        let builtin_module = self.name_table.builtin_module();
        let type_name_str = interner.resolve(decl.name);
        for (i, field) in decl.fields.iter().enumerate() {
            let field_name_str = interner.resolve(field.name);
            let field_name_id = self
                .name_table
                .intern_raw(builtin_module, &[field_name_str]);
            let full_field_name_id = self
                .name_table
                .intern_raw(self.current_module, &[type_name_str, field_name_str]);
            let field_ty = fields[i].ty.clone();
            self.entity_registry.register_field(
                entity_type_id,
                field_name_id,
                full_field_name_id,
                field_ty,
                i,
            );
        }
    }

    fn resolve_type_param_constraint(
        &mut self,
        constraint: &TypeConstraint,
        type_param_scope: &TypeParamScope,
        interner: &Interner,
        span: Span,
    ) -> Option<crate::sema::generic::TypeConstraint> {
        match constraint {
            TypeConstraint::Interface(sym) => {
                // Validate interface exists via EntityRegistry using resolver
                let iface_str = interner.resolve(*sym);
                let iface_exists = self
                    .resolver(interner)
                    .resolve_type_str_or_interface(iface_str, &self.entity_registry)
                    .is_some();

                if !iface_exists {
                    self.add_error(
                        SemanticError::UnknownInterface {
                            name: interner.resolve(*sym).to_string(),
                            span: span.into(),
                        },
                        span,
                    );
                    return None;
                }
                Some(crate::sema::generic::TypeConstraint::Interface(*sym))
            }
            TypeConstraint::Union(types) => {
                let module_id = self.current_module;
                let mut ctx = TypeResolutionContext::with_type_params(
                    &self.type_aliases,
                    &self.error_types,
                    &self.entity_registry,
                    interner,
                    &mut self.name_table,
                    module_id,
                    type_param_scope,
                );
                let resolved = types.iter().map(|ty| resolve_type(ty, &mut ctx)).collect();
                Some(crate::sema::generic::TypeConstraint::Union(resolved))
            }
        }
    }

    fn check_type_param_constraints(
        &mut self,
        type_params: &[TypeParamInfo],
        inferred: &HashMap<NameId, Type>,
        span: Span,
        interner: &Interner,
    ) {
        for param in type_params {
            let Some(constraint) = &param.constraint else {
                continue;
            };
            let Some(found) = inferred.get(&param.name_id) else {
                continue;
            };
            match constraint {
                crate::sema::generic::TypeConstraint::Interface(interface_name) => {
                    if !self.satisfies_interface(found, *interface_name, interner) {
                        let found_display = self.type_display(found);
                        self.add_error(
                            SemanticError::TypeParamConstraintMismatch {
                                type_param: interner.resolve(param.name).to_string(),
                                expected: interner.resolve(*interface_name).to_string(),
                                found: found_display,
                                span: span.into(),
                            },
                            span,
                        );
                    }
                }
                crate::sema::generic::TypeConstraint::Union(variants) => {
                    let expected = Type::normalize_union(variants.clone());
                    if !types_compatible_core(found, &expected) {
                        let expected_display = self.type_display(&expected);
                        let found_display = self.type_display(found);
                        self.add_error(
                            SemanticError::TypeParamConstraintMismatch {
                                type_param: interner.resolve(param.name).to_string(),
                                expected: expected_display,
                                found: found_display,
                                span: span.into(),
                            },
                            span,
                        );
                    }
                }
            }
        }
    }

    /// Analyze external block and register external methods in the implement registry
    fn analyze_external_block(
        &mut self,
        external: &ExternalBlock,
        target_type: &Type,
        trait_name: Option<Symbol>,
        interner: &Interner,
    ) {
        let type_id = match TypeId::from_type(target_type, &self.type_table) {
            Some(id) => id,
            None => return, // Skip non-registerable types
        };

        for func in &external.functions {
            // Resolve parameter types
            let param_types: Vec<Type> = func
                .params
                .iter()
                .map(|p| self.resolve_type(&p.ty, interner))
                .collect();

            // Resolve return type
            let return_type = match &func.return_type {
                Some(te) => self.resolve_type(te, interner),
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
            let method_id = self.method_name_id(func.vole_name, interner);
            let return_type = (*func_type.return_type).clone();
            self.implement_registry.register_method(
                type_id,
                method_id,
                MethodImpl {
                    trait_name,
                    func_type,
                    is_builtin: false,
                    external_info: Some(ExternalMethodInfo {
                        module_path: external.module_path.clone(),
                        native_name,
                        return_type: Some(Box::new(return_type)),
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
        // Skip generic functions - they will be type-checked when monomorphized
        // TODO: In M4+, we could type-check with abstract type params
        if !func.type_params.is_empty() {
            return Ok(());
        }

        let func_type = self.functions.get(&func.name).cloned().unwrap();
        let return_type = *func_type.return_type.clone();
        self.current_function_return = Some(return_type.clone());

        // Set error type context if this is a fallible function
        if let Type::Fallible(ref ft) = return_type {
            self.current_function_error_type = Some((*ft.error_type).clone());
        } else {
            self.current_function_error_type = None;
        }

        // Set generator context if return type is Iterator<T>
        self.current_generator_element_type =
            self.extract_iterator_element_type(&return_type, interner);

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
        self.current_generator_element_type = None;

        Ok(())
    }

    /// Extract the element type from an Iterator<T> type, or None if not an iterator type
    fn extract_iterator_element_type(&self, ty: &Type, _interner: &Interner) -> Option<Type> {
        let Type::Interface(interface_type) = ty else {
            return None;
        };
        if !self.well_known.is_iterator(interface_type.name_id) {
            return None;
        }
        interface_type.type_args.first().cloned()
    }

    fn check_method(
        &mut self,
        method: &FuncDecl,
        type_name: Symbol,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Look up method type via Resolver
        let type_def_id = self
            .resolver(interner)
            .resolve_type(type_name, &self.entity_registry)
            .expect("type should be registered in EntityRegistry");
        let method_name_id = self.method_name_id(method.name, interner);
        let method_id = self
            .entity_registry
            .find_method_on_type(type_def_id, method_name_id)
            .expect("method should be registered in EntityRegistry");
        let method_def = self.entity_registry.get_method(method_id);
        let method_type = method_def.signature.clone();
        let return_type = *method_type.return_type.clone();
        self.current_function_return = Some(return_type.clone());

        // Set error type context if this is a fallible method
        if let Type::Fallible(ref ft) = return_type {
            self.current_function_error_type = Some((*ft.error_type).clone());
        } else {
            self.current_function_error_type = None;
        }

        // Set generator context if return type is Iterator<T>
        self.current_generator_element_type =
            self.extract_iterator_element_type(&return_type, interner);

        // Create scope with 'self' and parameters
        let parent_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(parent_scope);

        // Add 'self' to scope
        // Note: "self" should already be interned by the parser when it parses method bodies
        let self_sym = interner
            .lookup("self")
            .expect("'self' should be interned during parsing");
        // Get self type via EntityRegistry
        let type_def = self.entity_registry.get_type(type_def_id);
        let self_type = match type_def.kind {
            TypeDefKind::Class => self
                .entity_registry
                .build_class_type(type_def_id, &self.name_table)
                .map(Type::Class)
                .unwrap_or(Type::Error),
            TypeDefKind::Record => self
                .entity_registry
                .build_record_type(type_def_id, &self.name_table)
                .map(Type::Record)
                .unwrap_or(Type::Error),
            _ => Type::Error,
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
        self.current_generator_element_type = None;

        Ok(())
    }

    /// Check a static method body (no `self` access allowed)
    fn check_static_method(
        &mut self,
        method: &InterfaceMethod,
        type_name: Symbol,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Only check methods with bodies
        let Some(ref body) = method.body else {
            return Ok(());
        };

        // Look up static method type via Resolver
        let type_def_id = self
            .resolver(interner)
            .resolve_type(type_name, &self.entity_registry)
            .expect("type should be registered in EntityRegistry");
        let method_name_id = self.method_name_id(method.name, interner);
        let method_id = self
            .entity_registry
            .find_static_method_on_type(type_def_id, method_name_id)
            .expect("static method should be registered in EntityRegistry");
        let method_def = self.entity_registry.get_method(method_id);
        let method_type = method_def.signature.clone();
        let return_type = *method_type.return_type.clone();
        self.current_function_return = Some(return_type.clone());

        // Set error type context if this is a fallible method
        if let Type::Fallible(ref ft) = return_type {
            self.current_function_error_type = Some((*ft.error_type).clone());
        } else {
            self.current_function_error_type = None;
        }

        // Set generator context if return type is Iterator<T>
        self.current_generator_element_type =
            self.extract_iterator_element_type(&return_type, interner);

        // Mark that we're in a static method (for self-usage detection)
        let method_name_str = interner.resolve(method.name).to_string();
        self.current_static_method = Some(method_name_str);

        // Create scope WITHOUT 'self'
        let parent_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(parent_scope);

        // Add parameters (no 'self' for static methods)
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
        self.check_block(body, interner)?;

        // Restore scope and context
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }
        self.current_function_return = None;
        self.current_function_error_type = None;
        self.current_generator_element_type = None;
        self.current_static_method = None;

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

        let module_id = self.name_table.module_id(import_path);

        for decl in &program.declarations {
            match decl {
                Decl::Function(f) => {
                    // Build function type from signature
                    let (params, return_type) = {
                        let mut ctx = TypeResolutionContext {
                            type_aliases: &self.type_aliases,
                            error_types: &self.error_types,
                            entity_registry: &self.entity_registry,
                            interner: &module_interner,
                            name_table: &mut self.name_table,
                            module_id,
                            type_params: None,
                            self_type: None,
                        };
                        let params: Vec<Type> = f
                            .params
                            .iter()
                            .map(|p| resolve_type(&p.ty, &mut ctx))
                            .collect();
                        let return_type = f
                            .return_type
                            .as_ref()
                            .map(|rt| resolve_type(rt, &mut ctx))
                            .unwrap_or(Type::Void);
                        (params, return_type)
                    };

                    let func_type = Type::Function(FunctionType {
                        params,
                        return_type: Box::new(return_type),
                        is_closure: false,
                    });

                    // Store export by name string
                    let name_id = self
                        .name_table
                        .intern(module_id, &[f.name], &module_interner);
                    exports.insert(name_id, func_type);
                }
                Decl::Let(l) if !l.mutable => {
                    // Only export immutable let bindings
                    // Infer type from literal for constants and store the value
                    let name_id = self
                        .name_table
                        .intern(module_id, &[l.name], &module_interner);
                    let (ty, const_val) = match &l.init.kind {
                        ExprKind::FloatLiteral(v) => (Type::F64, Some(ConstantValue::F64(*v))),
                        ExprKind::IntLiteral(v) => (Type::I64, Some(ConstantValue::I64(*v))),
                        ExprKind::BoolLiteral(v) => (Type::Bool, Some(ConstantValue::Bool(*v))),
                        ExprKind::StringLiteral(v) => {
                            (Type::String, Some(ConstantValue::String(v.clone())))
                        }
                        _ => (Type::Unknown, None), // Complex expressions need full analysis
                    };
                    exports.insert(name_id, ty);
                    if let Some(cv) = const_val {
                        constants.insert(name_id, cv);
                    }
                }
                Decl::External(ext) => {
                    // External block functions become exports and are marked as external
                    for func in &ext.functions {
                        let (params, return_type) = {
                            let mut ctx = TypeResolutionContext {
                                type_aliases: &self.type_aliases,
                                error_types: &self.error_types,
                                entity_registry: &self.entity_registry,
                                interner: &module_interner,
                                name_table: &mut self.name_table,
                                module_id,
                                type_params: None,
                                self_type: None,
                            };
                            let params: Vec<Type> = func
                                .params
                                .iter()
                                .map(|p| resolve_type(&p.ty, &mut ctx))
                                .collect();
                            let return_type = func
                                .return_type
                                .as_ref()
                                .map(|rt| resolve_type(rt, &mut ctx))
                                .unwrap_or(Type::Void);
                            (params, return_type)
                        };

                        let func_type = Type::Function(FunctionType {
                            params,
                            return_type: Box::new(return_type),
                            is_closure: false,
                        });

                        let name_id =
                            self.name_table
                                .intern(module_id, &[func.vole_name], &module_interner);
                        exports.insert(name_id, func_type);
                        // Mark as external function (FFI)
                        external_funcs.insert(name_id);
                    }
                }
                _ => {} // Skip other declarations for now
            }
        }

        let module_type = ModuleType {
            module_id,
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
