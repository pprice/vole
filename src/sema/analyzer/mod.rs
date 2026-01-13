// src/sema/analyzer/mod.rs

mod declarations;
mod expr;
mod lambda;
mod methods;
mod patterns;
mod stmt;

use crate::errors::{SemanticError, SemanticWarning};
use crate::frontend::*;
use crate::identity::{self, ModuleId, NameId, NameTable, Namer, Resolver, TypeDefId};
use crate::module::ModuleLoader;
use crate::sema::EntityRegistry;
use crate::sema::ExpressionData;
use crate::sema::entity_defs::TypeDefKind;
use crate::sema::generic::{
    ClassMethodMonomorphKey, MonomorphInstance, MonomorphKey, StaticMethodMonomorphKey,
    TypeParamInfo, TypeParamScope, substitute_type,
};
use crate::sema::implement_registry::{
    ExternalMethodInfo, ImplementRegistry, MethodImpl, PrimitiveTypeId, TypeId,
};
use crate::sema::resolution::{MethodResolutions, ResolvedMethod};
use crate::sema::types::{ConstantValue, ModuleType, StructuralType};
use crate::sema::{
    ClassType, ErrorTypeInfo, FunctionType, RecordType, StructField, Type, TypeKey,
    compatibility::{function_compatible_with_interface, literal_fits, types_compatible_core},
    resolve::{TypeResolutionContext, resolve_type},
    scope::{Scope, Variable},
};
use rustc_hash::FxHashMap;
use std::collections::{HashMap, HashSet};

/// Check if a type param's constraint (found) satisfies a required constraint.
/// Returns true if found has at least as strong constraints as required.
fn constraint_satisfied(
    found: &Option<crate::sema::generic::TypeConstraint>,
    required: &crate::sema::generic::TypeConstraint,
) -> bool {
    use crate::sema::generic::TypeConstraint;

    let Some(found) = found else {
        // Found has no constraint - can only satisfy if required is empty
        return false;
    };

    match (found, required) {
        // Interface constraints: found must have all interfaces that required has
        (
            TypeConstraint::Interface(found_interfaces),
            TypeConstraint::Interface(required_interfaces),
        ) => {
            // All required interfaces must be in the found interfaces
            required_interfaces
                .iter()
                .all(|req| found_interfaces.contains(req))
        }
        // Union constraints: found must be a subset of or equal to required
        (TypeConstraint::Union(found_types), TypeConstraint::Union(required_types)) => {
            // All found types must be in the required types
            found_types
                .iter()
                .all(|f| required_types.iter().any(|r| f == r))
        }
        // Structural constraints: more complex matching needed, for now require exact match
        (TypeConstraint::Structural(found_struct), TypeConstraint::Structural(required_struct)) => {
            found_struct == required_struct
        }
        // Different constraint kinds don't satisfy each other
        _ => false,
    }
}

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

/// A type warning wrapping a miette-enabled SemanticWarning
#[derive(Debug, Clone)]
pub struct TypeWarning {
    pub warning: SemanticWarning,
    pub span: Span,
}

impl TypeWarning {
    /// Create a new type warning
    pub fn new(warning: SemanticWarning, span: Span) -> Self {
        Self { warning, span }
    }
}

/// Output from semantic analysis, bundling all analysis results.
/// Used to construct AnalyzedProgram with program and interner.
pub struct AnalysisOutput {
    /// All expression-level metadata (types, method resolutions, generic calls)
    pub expression_data: ExpressionData,
    /// Methods added via implement blocks (includes external_func_info)
    pub implement_registry: ImplementRegistry,
    /// Parsed module programs and their interners (for compiling pure Vole functions)
    pub module_programs: FxHashMap<String, (Program, Interner)>,
    /// Fully-qualified name interner for printable identities
    pub name_table: NameTable,
    /// Entity registry for first-class type/method/field/function identity (includes type_table)
    pub entity_registry: EntityRegistry,
}

pub struct Analyzer {
    scope: Scope,
    functions: HashMap<Symbol, FunctionType>,
    /// Functions registered by string name (for prelude functions that cross interner boundaries)
    functions_by_name: FxHashMap<String, FunctionType>,
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
    warnings: Vec<TypeWarning>,
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
    /// Resolved types for each expression node (for codegen)
    /// Maps expression node IDs to their resolved types, including narrowed types
    expr_types: HashMap<NodeId, Type>,
    /// Methods added via implement blocks
    pub implement_registry: ImplementRegistry,
    /// Resolved method calls for codegen
    pub method_resolutions: MethodResolutions,
    /// Module loader for handling imports
    module_loader: ModuleLoader,
    /// Analyzed module types by import path
    module_types: FxHashMap<String, ModuleType>,
    /// Parsed module programs and their interners (for compiling pure Vole functions)
    module_programs: FxHashMap<String, (Program, Interner)>,
    /// Expression types for module programs (keyed by module path -> NodeId -> Type)
    /// Stored separately since NodeIds are per-program and can't be merged into main expr_types
    pub module_expr_types: FxHashMap<String, HashMap<NodeId, Type>>,
    /// Method resolutions for module programs (keyed by module path -> NodeId -> ResolvedMethod)
    /// Stored separately since NodeIds are per-program and can't be merged into main method_resolutions
    pub module_method_resolutions: FxHashMap<String, HashMap<NodeId, ResolvedMethod>>,
    /// Flag to prevent recursive prelude loading
    loading_prelude: bool,
    /// Mapping from call expression NodeId to MonomorphKey (for generic function calls)
    generic_calls: HashMap<NodeId, MonomorphKey>,
    /// Mapping from method call expression NodeId to ClassMethodMonomorphKey (for generic class method calls)
    class_method_calls: HashMap<NodeId, ClassMethodMonomorphKey>,
    /// Mapping from static method call expression NodeId to StaticMethodMonomorphKey (for generic static method calls)
    static_method_calls: HashMap<NodeId, StaticMethodMonomorphKey>,
    /// Fully-qualified name interner for printable identities
    name_table: NameTable,
    /// Current module being analyzed (for proper NameId registration)
    current_module: ModuleId,
    /// Entity registry for first-class type/method/field/function identity (includes type_table)
    pub entity_registry: EntityRegistry,
    /// Current type parameter scope (set when analyzing methods in generic classes/records)
    /// Used for resolving methods on Type::TypeParam via constraint interfaces
    current_type_param_scope: Option<TypeParamScope>,
}

impl Analyzer {
    pub fn new(_file: &str, _source: &str) -> Self {
        // Create name_table first to get main_module
        let name_table = NameTable::new();
        let main_module = name_table.main_module();

        let mut analyzer = Self {
            scope: Scope::new(),
            functions: HashMap::new(),
            functions_by_name: FxHashMap::default(),
            globals: HashMap::new(),
            current_function_return: None,
            current_function_error_type: None,
            current_generator_element_type: None,
            current_static_method: None,
            errors: Vec::new(),
            warnings: Vec::new(),
            type_overrides: HashMap::new(),
            lambda_captures: Vec::new(),
            lambda_locals: Vec::new(),
            lambda_side_effects: Vec::new(),
            expr_types: HashMap::new(),
            implement_registry: ImplementRegistry::new(),
            method_resolutions: MethodResolutions::new(),
            module_loader: ModuleLoader::new(),
            module_types: FxHashMap::default(),
            module_programs: FxHashMap::default(),
            module_expr_types: FxHashMap::default(),
            module_method_resolutions: FxHashMap::default(),
            loading_prelude: false,
            generic_calls: HashMap::new(),
            class_method_calls: HashMap::new(),
            static_method_calls: HashMap::new(),
            name_table,
            current_module: main_module,
            entity_registry: EntityRegistry::new(),
            current_type_param_scope: None,
        };

        // Register primitives in EntityRegistry so they can have static methods
        analyzer
            .entity_registry
            .register_primitives(&analyzer.name_table);

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
        let array_id = self
            .entity_registry
            .type_table
            .array_name_id()
            .map(TypeId::from_name_id);
        let string_id = self
            .entity_registry
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
                    return_type: Box::new(Type::unknown()),
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
                    return_type: Box::new(Type::unknown()), // Will be refined by check_builtin_method
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
            .entity_registry
            .type_table
            .primitive_name_id(PrimitiveTypeId::Range)
            .map(TypeId::from_name_id);
        if let Some(type_id) = range_id {
            register_builtin!(
                type_id,
                method_iter,
                FunctionType {
                    params: vec![],
                    return_type: Box::new(Type::unknown()), // Will be refined by check_builtin_method
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
            self.entity_registry
                .type_table
                .register_primitive_name(prim, name_id);
        }
        let array_name = namer.intern_raw(builtin_module, &["array"]);
        self.entity_registry
            .type_table
            .register_array_name(array_name);
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
            "std:prelude/map",
            "std:prelude/set",
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
            functions_by_name: FxHashMap::default(),
            globals: HashMap::new(),
            current_function_return: None,
            current_function_error_type: None,
            current_generator_element_type: None,
            current_static_method: None,
            errors: Vec::new(),
            warnings: Vec::new(),
            type_overrides: HashMap::new(),
            lambda_captures: Vec::new(),
            lambda_locals: Vec::new(),
            lambda_side_effects: Vec::new(),
            expr_types: HashMap::new(),
            implement_registry: ImplementRegistry::new(),
            method_resolutions: MethodResolutions::new(),
            module_loader: ModuleLoader::new(),
            module_types: FxHashMap::default(),
            module_programs: FxHashMap::default(),
            module_expr_types: FxHashMap::default(),
            module_method_resolutions: FxHashMap::default(),
            loading_prelude: true, // Prevent sub-analyzer from loading prelude
            generic_calls: HashMap::new(),
            class_method_calls: HashMap::new(),
            static_method_calls: HashMap::new(),
            name_table: NameTable::new(),
            current_module: prelude_module, // Use the prelude module path!
            entity_registry: EntityRegistry::new(),
            current_type_param_scope: None,
        };

        // Copy existing registries so prelude files can reference earlier definitions
        sub_analyzer.name_table = self.name_table.clone();
        sub_analyzer.entity_registry = self.entity_registry.clone();
        sub_analyzer.implement_registry = self.implement_registry.clone();

        // Analyze the prelude file
        let analyze_result = sub_analyzer.analyze(&program, &prelude_interner);
        if let Err(ref errors) = analyze_result {
            tracing::warn!(import_path, ?errors, "prelude analysis errors");
        }
        if analyze_result.is_ok() {
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
            // Note: external_func_info is now part of implement_registry and merged via merge() above
            // Keep name table in sync with prelude interned ids.
            // Note: type_table is now in entity_registry and merged via merge() above
            self.name_table = sub_analyzer.name_table;

            // Store prelude program for codegen (needed for implement block compilation)
            self.module_programs
                .insert(import_path.to_string(), (program, prelude_interner));
            // Store module-specific expr_types separately (NodeIds are per-program)
            self.module_expr_types
                .insert(import_path.to_string(), sub_analyzer.expr_types);
            // Store module-specific method_resolutions separately (NodeIds are per-program)
            self.module_method_resolutions.insert(
                import_path.to_string(),
                sub_analyzer.method_resolutions.into_inner(),
            );
        }
        // Silently ignore analysis errors in prelude
    }

    /// Helper to add a type error
    fn add_error(&mut self, error: SemanticError, span: Span) {
        self.errors.push(TypeError::new(error, span));
    }

    /// Helper to add a type warning
    #[allow(dead_code)] // Infrastructure for future warnings
    fn add_warning(&mut self, warning: SemanticWarning, span: Span) {
        self.warnings.push(TypeWarning::new(warning, span));
    }

    fn type_key_for(&mut self, ty: &Type) -> TypeKey {
        self.entity_registry.type_table.key_for_type(ty)
    }

    fn type_display(&self, ty: &Type) -> String {
        self.entity_registry
            .type_table
            .display_type(ty, &self.name_table, &self.entity_registry)
    }

    fn type_display_pair(&mut self, left: &Type, right: &Type) -> String {
        format!(
            "{} and {}",
            self.type_display(left),
            self.type_display(right)
        )
    }

    /// Format a structural type for warning messages
    #[allow(dead_code)] // Infrastructure for future warnings
    fn format_structural_type(&mut self, structural: &StructuralType) -> String {
        let mut parts = Vec::new();

        for field in &structural.fields {
            let name = self
                .name_table
                .last_segment_str(field.name)
                .unwrap_or_else(|| "<unknown>".to_string());
            let ty = self.type_display(&field.ty);
            parts.push(format!("{}: {}", name, ty));
        }

        for method in &structural.methods {
            let name = self
                .name_table
                .last_segment_str(method.name)
                .unwrap_or_else(|| "<unknown>".to_string());
            let params: Vec<String> = method.params.iter().map(|p| self.type_display(p)).collect();
            let ret = self.type_display(&method.return_type);
            parts.push(format!("func {}({}) -> {}", name, params.join(", "), ret));
        }

        parts.join(", ")
    }

    /// Helper to add a type mismatch error (string version)
    #[allow(dead_code)]
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

    /// Helper to add a type mismatch error with automatic type display
    pub(crate) fn type_error(&mut self, expected: &str, found: &Type, span: Span) {
        let found_str = self.type_display(found);
        self.add_error(
            SemanticError::TypeMismatch {
                expected: expected.to_string(),
                found: found_str,
                span: span.into(),
            },
            span,
        );
    }

    /// Helper to add a type mismatch error for binary operations
    pub(crate) fn type_error_pair(
        &mut self,
        expected: &str,
        left: &Type,
        right: &Type,
        span: Span,
    ) {
        let found = self.type_display_pair(left, right);
        self.add_error(
            SemanticError::TypeMismatch {
                expected: expected.to_string(),
                found,
                span: span.into(),
            },
            span,
        );
    }

    /// Helper to add a type mismatch error with two Type arguments
    pub(crate) fn add_type_mismatch(&mut self, expected: &Type, found: &Type, span: Span) {
        let expected_str = self.type_display(expected);
        let found_str = self.type_display(found);
        self.add_error(
            SemanticError::TypeMismatch {
                expected: expected_str,
                found: found_str,
                span: span.into(),
            },
            span,
        );
    }

    /// Helper to add a wrong argument count error
    pub(crate) fn add_wrong_arg_count(&mut self, expected: usize, found: usize, span: Span) {
        self.add_error(
            SemanticError::WrongArgumentCount {
                expected,
                found,
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
                    // Special case: if actual is Nil, check if the type param is already in
                    // scope with the same name_id. If so, bind to the type param instead of Nil.
                    // This preserves type params in generic contexts (e.g., Box { value: nil }).
                    let actual_to_bind = if matches!(actual, Type::Nil) {
                        // Check if this type param is in our current scope - if so, preserve it
                        if let Some(ref scope) = self.current_type_param_scope
                            && scope.get_by_name_id(*name_id).is_some()
                        {
                            // Preserve the type param
                            Type::TypeParam(*name_id)
                        } else {
                            actual.clone()
                        }
                    } else if let Type::TypeParam(actual_name_id) = actual {
                        // If actual is also a type param, check if it's in our scope
                        if let Some(ref scope) = self.current_type_param_scope
                            && scope.get_by_name_id(*actual_name_id).is_some()
                        {
                            // Preserve the actual type param
                            actual.clone()
                        } else {
                            actual.clone()
                        }
                    } else {
                        actual.clone()
                    };

                    // Only bind if not already bound (first binding wins)
                    inferred.entry(*name_id).or_insert(actual_to_bind);
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
            // Class: unify type args (for generic class parameters)
            (Type::Class(p_class), Type::Class(a_class))
                if p_class.type_def_id == a_class.type_def_id =>
            {
                for (p, a) in p_class.type_args.iter().zip(a_class.type_args.iter()) {
                    self.unify_types(p, a, type_params, inferred);
                }
            }
            // Record: unify type args (for generic record parameters)
            (Type::Record(p_rec), Type::Record(a_rec))
                if p_rec.type_def_id == a_rec.type_def_id =>
            {
                for (p, a) in p_rec.type_args.iter().zip(a_rec.type_args.iter()) {
                    self.unify_types(p, a, type_params, inferred);
                }
            }
            // Everything else: no type params to extract
            _ => {}
        }
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

    /// Take accumulated warnings, leaving the warnings list empty
    pub fn take_warnings(&mut self) -> Vec<TypeWarning> {
        std::mem::take(&mut self.warnings)
    }

    /// Take ownership of analysis results (consuming self)
    pub fn into_analysis_results(self) -> AnalysisOutput {
        let expression_data = ExpressionData::from_analysis(
            self.expr_types,
            self.method_resolutions.into_inner(),
            self.generic_calls,
            self.class_method_calls,
            self.static_method_calls,
            self.module_expr_types,
            self.module_method_resolutions,
        );
        AnalysisOutput {
            expression_data,
            implement_registry: self.implement_registry,
            module_programs: self.module_programs,
            name_table: self.name_table,
            entity_registry: self.entity_registry,
        }
    }

    /// Record the resolved type for an expression, returning the type for chaining
    fn record_expr_type(&mut self, expr: &Expr, ty: Type) -> Type {
        self.expr_types.insert(expr.id, ty.clone());
        ty
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
        self.entity_registry.type_table.insert_named(ty, name_id);
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
            return Some(Type::invalid("propagate"));
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

    #[tracing::instrument(skip(self, program, interner))]
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
        self.name_table.populate_well_known();

        // Pass 0.5: Register type shells for forward reference support
        // This allows types to reference each other regardless of declaration order
        self.register_all_type_shells(program, interner);

        // Pass 0: Resolve type aliases (now that shells exist, can reference forward types)
        self.collect_type_aliases(program, interner);

        // Pass 1: Collect signatures for all declarations (shells already exist)
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
            if let Decl::Let(let_stmt) = decl {
                match &let_stmt.init {
                    LetInit::TypeAlias(type_expr) => {
                        let aliased_type = self.resolve_type(type_expr, interner);
                        self.register_type_alias(let_stmt.name, aliased_type, interner);
                    }
                    LetInit::Expr(init_expr) => {
                        // Legacy: handle let X: type = SomeType
                        if let ExprKind::TypeLiteral(type_expr) = &init_expr.kind {
                            let aliased_type = self.resolve_type(type_expr, interner);
                            self.register_type_alias(let_stmt.name, aliased_type, interner);
                        }
                    }
                }
            }
        }
    }

    /// Register a type alias in EntityRegistry
    fn register_type_alias(&mut self, name: Symbol, aliased_type: Type, interner: &Interner) {
        // Lookup shell registered in register_all_type_shells
        let name_id = self
            .name_table
            .intern(self.current_module, &[name], interner);
        let type_id = self
            .entity_registry
            .type_by_name(name_id)
            .expect("alias shell registered in register_all_type_shells");
        let type_key = self.entity_registry.type_table.key_for_type(&aliased_type);
        self.entity_registry
            .set_aliased_type(type_id, aliased_type.clone(), type_key);
        // Also in type_table for display
        self.entity_registry
            .type_table
            .insert_named(aliased_type, name_id);
    }

    /// Process global let declarations (type check and add to scope)
    fn process_global_lets(
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
                        // Check for ambiguous type alias: let Alias = TypeName
                        if let ExprKind::Identifier(ident_sym) = &init_expr.kind {
                            let ident_name = interner.resolve(*ident_sym);
                            if self
                                .resolver(interner)
                                .resolve_type(*ident_sym, &self.entity_registry)
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

                        let declared_type =
                            let_stmt.ty.as_ref().map(|t| self.resolve_type(t, interner));
                        let init_type =
                            self.check_expr_expecting(init_expr, declared_type.as_ref(), interner)?;

                        // Check if trying to use void return value
                        if init_type == Type::Void {
                            self.add_error(
                                SemanticError::VoidReturnUsed {
                                    span: init_expr.span.into(),
                                },
                                init_expr.span,
                            );
                        }

                        let var_type = declared_type.unwrap_or(init_type.clone());

                        // If this is a type alias (RHS is a type expression), store it
                        if var_type == Type::Type
                            && let ExprKind::TypeLiteral(type_expr) = &init_expr.kind
                        {
                            let aliased_type = self.resolve_type(type_expr, interner);
                            self.register_type_alias(let_stmt.name, aliased_type, interner);
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
                    // Set up type param scope for generic class methods
                    // This allows method resolution to use constraint interfaces
                    if !class.type_params.is_empty()
                        && let Some(class_name_id) =
                            self.name_table
                                .name_id(self.current_module, &[class.name], interner)
                        && let Some(type_def_id) = self.entity_registry.type_by_name(class_name_id)
                        && let Some(generic_info) =
                            self.entity_registry.get_generic_info(type_def_id)
                    {
                        let mut scope = TypeParamScope::new();
                        for tp in &generic_info.type_params {
                            scope.add(tp.clone());
                        }
                        self.current_type_param_scope = Some(scope);
                    }

                    for method in &class.methods {
                        self.check_method(method, class.name, interner)?;
                    }
                    // Check static methods if present
                    if let Some(ref statics) = class.statics {
                        for method in &statics.methods {
                            self.check_static_method(method, class.name, interner)?;
                        }
                    }

                    // Clear type param scope after checking methods
                    self.current_type_param_scope = None;
                    // Validate interface satisfaction via EntityRegistry
                    if let Some(class_name_id) =
                        self.name_table
                            .name_id(self.current_module, &[class.name], interner)
                        && let Some(type_def_id) = self.entity_registry.type_by_name(class_name_id)
                    {
                        let type_methods = self.get_type_method_signatures(class.name, interner);
                        for interface_id in
                            self.entity_registry.get_implemented_interfaces(type_def_id)
                        {
                            let interface_def = self.entity_registry.get_type(interface_id);
                            if let Some(iface_name_str) =
                                self.name_table.last_segment_str(interface_def.name_id)
                                && let Some(iface_name) = interner.lookup(&iface_name_str)
                            {
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
                }
                Decl::Record(record) => {
                    // Set up type param scope for generic record methods
                    // This allows method resolution to use constraint interfaces
                    if !record.type_params.is_empty()
                        && let Some(record_name_id) =
                            self.name_table
                                .name_id(self.current_module, &[record.name], interner)
                        && let Some(type_def_id) = self.entity_registry.type_by_name(record_name_id)
                        && let Some(generic_info) =
                            self.entity_registry.get_generic_info(type_def_id)
                    {
                        let mut scope = TypeParamScope::new();
                        for tp in &generic_info.type_params {
                            scope.add(tp.clone());
                        }
                        self.current_type_param_scope = Some(scope);
                    }

                    for method in &record.methods {
                        self.check_method(method, record.name, interner)?;
                    }
                    // Check static methods if present
                    if let Some(ref statics) = record.statics {
                        for method in &statics.methods {
                            self.check_static_method(method, record.name, interner)?;
                        }
                    }

                    // Clear type param scope after checking methods
                    self.current_type_param_scope = None;

                    // Validate interface satisfaction via EntityRegistry
                    if let Some(record_name_id) =
                        self.name_table
                            .name_id(self.current_module, &[record.name], interner)
                        && let Some(type_def_id) = self.entity_registry.type_by_name(record_name_id)
                    {
                        let type_methods = self.get_type_method_signatures(record.name, interner);
                        for interface_id in
                            self.entity_registry.get_implemented_interfaces(type_def_id)
                        {
                            let interface_def = self.entity_registry.get_type(interface_id);
                            if let Some(iface_name_str) =
                                self.name_table.last_segment_str(interface_def.name_id)
                                && let Some(iface_name) = interner.lookup(&iface_name_str)
                            {
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
                        match &impl_block.target_type {
                            TypeExpr::Named(type_name) => {
                                for method in &statics.methods {
                                    self.check_static_method(method, *type_name, interner)?;
                                }
                            }
                            TypeExpr::Primitive(prim) => {
                                // Get TypeDefId for primitive
                                let name_id = self.name_table.primitives.from_ast(*prim);
                                if let Some(type_def_id) =
                                    self.entity_registry.type_by_name(name_id)
                                {
                                    for method in &statics.methods {
                                        self.check_static_method_with_type_def(
                                            method,
                                            type_def_id,
                                            interner,
                                        )?;
                                    }
                                }
                            }
                            _ => {}
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

        self.register_named_type(decl.name, Type::ErrorType(error_info.clone()), interner);

        // Register in EntityRegistry (parallel migration)
        let entity_type_id = self.entity_registry.register_type(
            name_id,
            TypeDefKind::ErrorType,
            self.current_module,
        );

        // Set error info for lookup
        self.entity_registry
            .set_error_info(entity_type_id, error_info);

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
        tracing::debug!(?constraint, "resolve_type_param_constraint");
        match constraint {
            TypeConstraint::Interface(syms) => {
                tracing::debug!(
                    num_interfaces = syms.len(),
                    "processing interface constraint"
                );
                // For single interface, check if it's a type alias first
                if syms.len() == 1 {
                    let sym = syms[0];
                    if let Some(type_def_id) = self
                        .resolver(interner)
                        .resolve_type(sym, &self.entity_registry)
                    {
                        let type_def = self.entity_registry.get_type(type_def_id);
                        if type_def.kind == TypeDefKind::Alias
                            && let Some(ref aliased_type) = type_def.aliased_type
                        {
                            // Convert the aliased type to a union constraint
                            let types = match aliased_type {
                                Type::Union(types) => types.clone(),
                                other => vec![other.clone()],
                            };
                            return Some(crate::sema::generic::TypeConstraint::Union(types));
                        }
                    }
                }

                // Validate all interfaces exist via EntityRegistry using resolver
                for sym in syms {
                    let iface_str = interner.resolve(*sym);
                    let iface_exists = self
                        .resolver(interner)
                        .resolve_type_str_or_interface(iface_str, &self.entity_registry)
                        .is_some();

                    if !iface_exists {
                        self.add_error(
                            SemanticError::UnknownInterface {
                                name: iface_str.to_string(),
                                span: span.into(),
                            },
                            span,
                        );
                        return None;
                    }
                }
                Some(crate::sema::generic::TypeConstraint::Interface(
                    syms.clone(),
                ))
            }
            TypeConstraint::Union(types) => {
                let module_id = self.current_module;
                let mut ctx = TypeResolutionContext::with_type_params(
                    &self.entity_registry,
                    interner,
                    &mut self.name_table,
                    module_id,
                    type_param_scope,
                );
                let resolved = types.iter().map(|ty| resolve_type(ty, &mut ctx)).collect();
                Some(crate::sema::generic::TypeConstraint::Union(resolved))
            }
            TypeConstraint::Structural { fields, methods } => {
                let module_id = self.current_module;
                let mut ctx = TypeResolutionContext::with_type_params(
                    &self.entity_registry,
                    interner,
                    &mut self.name_table,
                    module_id,
                    type_param_scope,
                );
                // Convert AST structural to sema structural
                let resolved_fields = fields
                    .iter()
                    .map(|f| crate::sema::types::StructuralFieldType {
                        name: ctx
                            .name_table
                            .intern(ctx.module_id, &[f.name], ctx.interner),
                        ty: resolve_type(&f.ty, &mut ctx),
                    })
                    .collect();
                let resolved_methods = methods
                    .iter()
                    .map(|m| crate::sema::types::StructuralMethodType {
                        name: ctx
                            .name_table
                            .intern(ctx.module_id, &[m.name], ctx.interner),
                        params: m.params.iter().map(|p| resolve_type(p, &mut ctx)).collect(),
                        return_type: resolve_type(&m.return_type, &mut ctx),
                    })
                    .collect();
                Some(crate::sema::generic::TypeConstraint::Structural(
                    StructuralType {
                        fields: resolved_fields,
                        methods: resolved_methods,
                    },
                ))
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

            // If the inferred type is itself a type param that has a matching or stronger constraint,
            // the constraint is satisfied. Check if it's a type param in our current scope.
            if let Type::TypeParam(found_name_id) = found
                && let Some(ref scope) = self.current_type_param_scope
                && let Some(found_param) = scope.get_by_name_id(*found_name_id)
                && constraint_satisfied(&found_param.constraint, constraint)
            {
                continue; // Constraint is satisfied
            }

            match constraint {
                crate::sema::generic::TypeConstraint::Interface(interface_names) => {
                    // Must satisfy all interfaces in the constraint
                    for interface_name in interface_names {
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
                crate::sema::generic::TypeConstraint::Structural(structural) => {
                    if let Some(mismatch) =
                        self.check_structural_constraint(found, structural, interner)
                    {
                        let found_display = self.type_display(found);
                        self.add_error(
                            SemanticError::StructuralConstraintMismatch {
                                type_param: interner.resolve(param.name).to_string(),
                                found: found_display,
                                mismatch,
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
        let type_id = match TypeId::from_type(
            target_type,
            &self.entity_registry.type_table,
            &self.entity_registry,
        ) {
            Some(id) => id,
            None => return, // Skip non-registerable types
        };

        // Get EntityRegistry TypeDefId for the target type
        let entity_type_id = match target_type {
            Type::Record(r) => Some(r.type_def_id),
            Type::Class(c) => Some(c.type_def_id),
            Type::I8 => self
                .entity_registry
                .type_by_name(self.name_table.primitives.i8),
            Type::I16 => self
                .entity_registry
                .type_by_name(self.name_table.primitives.i16),
            Type::I32 => self
                .entity_registry
                .type_by_name(self.name_table.primitives.i32),
            Type::I64 => self
                .entity_registry
                .type_by_name(self.name_table.primitives.i64),
            Type::I128 => self
                .entity_registry
                .type_by_name(self.name_table.primitives.i128),
            Type::U8 => self
                .entity_registry
                .type_by_name(self.name_table.primitives.u8),
            Type::U16 => self
                .entity_registry
                .type_by_name(self.name_table.primitives.u16),
            Type::U32 => self
                .entity_registry
                .type_by_name(self.name_table.primitives.u32),
            Type::U64 => self
                .entity_registry
                .type_by_name(self.name_table.primitives.u64),
            Type::F32 => self
                .entity_registry
                .type_by_name(self.name_table.primitives.f32),
            Type::F64 => self
                .entity_registry
                .type_by_name(self.name_table.primitives.f64),
            Type::Bool => self
                .entity_registry
                .type_by_name(self.name_table.primitives.bool),
            Type::String => self
                .entity_registry
                .type_by_name(self.name_table.primitives.string),
            _ => None,
        };

        // Get interface TypeDefId if implementing an interface
        let interface_type_id = trait_name.and_then(|name| {
            let iface_str = interner.resolve(name);
            self.resolver(interner)
                .resolve_type_str_or_interface(iface_str, &self.entity_registry)
        });

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
            let return_type_clone = (*func_type.return_type).clone();
            let external_info = ExternalMethodInfo {
                module_path: external.module_path.clone(),
                native_name,
                return_type: Some(Box::new(return_type_clone)),
            };
            self.implement_registry.register_method(
                type_id,
                method_id,
                MethodImpl {
                    trait_name,
                    func_type: func_type.clone(),
                    is_builtin: false,
                    external_info: Some(external_info.clone()),
                },
            );

            // Also register in EntityRegistry if we have both type and interface
            if let (Some(entity_type_id), Some(interface_type_id)) =
                (entity_type_id, interface_type_id)
            {
                use crate::sema::entity_defs::MethodBinding;
                self.entity_registry.add_method_binding(
                    entity_type_id,
                    interface_type_id,
                    MethodBinding {
                        method_name: method_id,
                        func_type,
                        is_builtin: false,
                        external_info: Some(external_info),
                    },
                );
            }
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

        let func_type = self
            .functions
            .get(&func.name)
            .cloned()
            .expect("function registered in signature collection pass");
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
        if !self
            .name_table
            .well_known
            .is_iterator(interface_type.name_id)
        {
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
                .build_class_type(type_def_id)
                .map(Type::Class)
                .unwrap_or_else(|| Type::invalid("unwrap_failed")),
            TypeDefKind::Record => self
                .entity_registry
                .build_record_type(type_def_id)
                .map(Type::Record)
                .unwrap_or_else(|| Type::invalid("unwrap_failed")),
            _ => Type::invalid("fallback"),
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
        let method_type_params = method_def.method_type_params.clone();
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

        // Add method-level type params to the current type param scope (if any)
        // This allows constraints on method type params to be checked
        let saved_type_param_scope = self.current_type_param_scope.clone();
        if !method_type_params.is_empty() {
            let mut scope = self.current_type_param_scope.take().unwrap_or_default();
            for tp in &method_type_params {
                scope.add(tp.clone());
            }
            self.current_type_param_scope = Some(scope);
        }

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

        // Restore type param scope (remove method type params)
        self.current_type_param_scope = saved_type_param_scope;

        Ok(())
    }

    /// Check a static method body with the type already resolved to a TypeDefId.
    /// This is used for primitive types where we can't resolve via Symbol.
    fn check_static_method_with_type_def(
        &mut self,
        method: &InterfaceMethod,
        type_def_id: TypeDefId,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Only check methods with bodies
        let Some(ref body) = method.body else {
            return Ok(());
        };

        let method_name_id = self.method_name_id(method.name, interner);
        let method_id = self
            .entity_registry
            .find_static_method_on_type(type_def_id, method_name_id)
            .expect("static method should be registered in EntityRegistry");
        let method_def = self.entity_registry.get_method(method_id);
        let method_type = method_def.signature.clone();
        let method_type_params = method_def.method_type_params.clone();
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

        // Add method-level type params to the current type param scope (if any)
        // This allows constraints on method type params to be checked
        let saved_type_param_scope = self.current_type_param_scope.clone();
        if !method_type_params.is_empty() {
            let mut scope = self.current_type_param_scope.take().unwrap_or_default();
            for tp in &method_type_params {
                scope.add(tp.clone());
            }
            self.current_type_param_scope = Some(scope);
        }

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

        // Restore type param scope (remove method type params)
        self.current_type_param_scope = saved_type_param_scope;

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
    #[tracing::instrument(skip(self, span, _interner), fields(path = %import_path))]
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
                    // Only export immutable let bindings (skip type aliases for now)
                    let init_expr = match &l.init {
                        LetInit::Expr(e) => e,
                        LetInit::TypeAlias(_) => continue, // Type aliases handled separately
                    };
                    // Infer type from literal for constants and store the value
                    let name_id = self
                        .name_table
                        .intern(module_id, &[l.name], &module_interner);
                    let (ty, const_val) = match &init_expr.kind {
                        ExprKind::FloatLiteral(v) => (Type::F64, Some(ConstantValue::F64(*v))),
                        ExprKind::IntLiteral(v) => (Type::I64, Some(ConstantValue::I64(*v))),
                        ExprKind::BoolLiteral(v) => (Type::Bool, Some(ConstantValue::Bool(*v))),
                        ExprKind::StringLiteral(v) => {
                            (Type::String, Some(ConstantValue::String(v.clone())))
                        }
                        _ => (Type::unknown(), None), // Complex expressions need full analysis
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
