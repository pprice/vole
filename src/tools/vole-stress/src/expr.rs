//! Grammar-based expression generation.
//!
//! This module generates type-correct Vole expressions using grammar rules.
//! Expressions are generated with depth limits to prevent infinite recursion.

use rand::Rng;

use crate::symbols::{
    FieldInfo, InterfaceInfo, MethodInfo, ModuleId, ParamInfo, PrimitiveType, SymbolId, SymbolKind,
    SymbolTable, TypeInfo, TypeParam,
};

/// Configuration for expression generation.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct ExprConfig {
    /// Maximum nesting depth for expressions.
    pub max_depth: usize,
    /// Probability of generating a binary expression vs simpler form.
    pub binary_probability: f64,
    /// Probability of generating a when expression.
    pub when_probability: f64,
    /// Probability of generating a match expression.
    pub match_probability: f64,
    /// Probability of generating an if expression.
    pub if_expr_probability: f64,
    /// Probability of generating a lambda expression.
    pub lambda_probability: f64,
    /// Probability of chaining another method call when the return type supports it.
    pub method_chain_probability: f64,
    /// Maximum depth of method chains (e.g., 2 means a.b().c() is allowed).
    pub max_chain_depth: usize,
    /// Probability of using `unreachable` in match/when wildcard arms.
    /// Only used when the arm is provably unreachable (e.g., all cases covered).
    pub unreachable_probability: f64,
    /// Maximum number of arms in match/when expressions (excluding wildcard).
    /// Default 4. Higher values stress-test pattern matching codegen.
    pub max_match_arms: usize,
    /// Probability of generating a `when` or `if` expression in argument/field-value
    /// positions instead of a simple literal or variable reference.
    /// Exercises the compiler's handling of complex expressions in call arguments
    /// and struct/class field initializers. Set to 0.0 to disable.
    pub inline_expr_arg_probability: f64,
    /// Probability of generating a tuple index expression (`tupleVar[index]`)
    /// when a tuple-typed variable with a matching element type is in scope.
    /// Set to 0.0 to disable.
    pub tuple_index_probability: f64,
    /// Probability of chaining multiple optional variables in a null coalescing
    /// expression when 2+ optional variables of matching type are in scope.
    /// Produces patterns like `optA ?? optB ?? defaultExpr`. Set to 0.0 to
    /// always use single `opt ?? default` form.
    pub chained_coalesce_probability: f64,
    /// Probability of generating a string method call when a string-typed
    /// variable is in scope and the target type matches a string method's
    /// return type.  Controls `.length()` (returns i64), `.contains()` /
    /// `.starts_with()` / `.ends_with()` (returns bool), and `.trim()` /
    /// `.to_upper()` / `.to_lower()` (returns string).  Set to 0.0 to disable.
    pub string_method_probability: f64,
    /// Probability of generating a multi-arm when expression (3-4 arms)
    /// instead of a 2-arm when expression (1 condition + wildcard).
    /// When this fires, generates 3-4 total arms (2-3 conditions + wildcard).
    /// Set to 0.0 to always use 2-arm when expressions.
    pub multi_arm_when_probability: f64,
    /// Probability of generating a match guard on the wildcard arm.
    /// When this fires, the wildcard arm `_ => expr` is replaced by
    /// `_ if <condition> => <guarded_result>, _ => <fallback_result>`.
    /// Set to 0.0 to disable.
    pub match_guard_probability: f64,
    /// Probability that a generated closure captures variables from
    /// the enclosing scope.  When this fires, primitive-typed locals
    /// and parameters from the outer context are made visible inside
    /// the closure body so the expression generator can reference them.
    /// Set to 0.0 to disable.
    pub closure_capture_probability: f64,
    /// Probability of constructing a concrete class instance when an
    /// interface type is expected, instead of reusing an existing
    /// interface-typed variable in scope.  This exercises the implicit
    /// upcast codegen path (class -> interface coercion at the call
    /// site).  Set to 0.0 to always prefer existing interface variables.
    pub interface_upcast_probability: f64,
}

impl Default for ExprConfig {
    fn default() -> Self {
        Self {
            max_depth: 3,
            binary_probability: 0.4,
            when_probability: 0.1,
            match_probability: 0.1,
            if_expr_probability: 0.15,
            lambda_probability: 0.05,
            method_chain_probability: 0.20,
            max_chain_depth: 2,
            unreachable_probability: 0.05,
            max_match_arms: 4,
            inline_expr_arg_probability: 0.12,
            tuple_index_probability: 0.15,
            chained_coalesce_probability: 0.30,
            string_method_probability: 0.15,
            multi_arm_when_probability: 0.30,
            match_guard_probability: 0.10,
            // Default 0.0; profiles override (cross-module bug fixed in 3573bef5)
            closure_capture_probability: 0.0,
            interface_upcast_probability: 0.25,
        }
    }
}

/// Context for expression generation within a scope.
#[allow(dead_code)]
pub struct ExprContext<'a> {
    /// Available parameters in scope.
    pub params: &'a [ParamInfo],
    /// Available local variables (name, type).
    pub locals: &'a [(String, TypeInfo)],
    /// Symbol table for type lookups.
    pub table: &'a SymbolTable,
    /// Type parameters in scope (for generic functions/classes).
    /// Each TypeParam may have interface constraints that allow method calls.
    pub type_params: &'a [TypeParam],
}

#[allow(dead_code)]
impl<'a> ExprContext<'a> {
    /// Create a new expression context.
    pub fn new(
        params: &'a [ParamInfo],
        locals: &'a [(String, TypeInfo)],
        table: &'a SymbolTable,
    ) -> Self {
        Self {
            params,
            locals,
            table,
            type_params: &[],
        }
    }

    /// Create a new expression context with type parameters.
    pub fn with_type_params(
        params: &'a [ParamInfo],
        locals: &'a [(String, TypeInfo)],
        table: &'a SymbolTable,
        type_params: &'a [TypeParam],
    ) -> Self {
        Self {
            params,
            locals,
            table,
            type_params,
        }
    }

    /// Find a variable in scope matching the given type.
    pub fn find_matching_var(&self, target_type: &TypeInfo) -> Option<String> {
        // Check locals first
        for (name, ty) in self.locals {
            if types_compatible(ty, target_type) {
                return Some(name.clone());
            }
        }
        // Check params
        for param in self.params {
            if types_compatible(&param.param_type, target_type) {
                return Some(param.name.clone());
            }
        }
        None
    }

    /// Get all numeric variables in scope.
    pub fn numeric_vars(&self) -> Vec<String> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            if is_numeric_type(ty) {
                vars.push(name.clone());
            }
        }
        for param in self.params {
            if is_numeric_type(&param.param_type) {
                vars.push(param.name.clone());
            }
        }
        vars
    }

    /// Get all integer (non-float, non-bool) variables in scope.
    pub fn integer_vars(&self) -> Vec<String> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            if is_integer_type(ty) {
                vars.push(name.clone());
            }
        }
        for param in self.params {
            if is_integer_type(&param.param_type) {
                vars.push(param.name.clone());
            }
        }
        vars
    }

    /// Get all boolean variables in scope.
    pub fn bool_vars(&self) -> Vec<String> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            if matches!(ty, TypeInfo::Primitive(PrimitiveType::Bool)) {
                vars.push(name.clone());
            }
        }
        for param in self.params {
            if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::Bool)) {
                vars.push(param.name.clone());
            }
        }
        vars
    }

    /// Get all variables in scope that support `.to_string()`.
    ///
    /// Only i64, i32, f64, and bool have `.to_string()` registered in the runtime.
    pub fn to_string_candidate_vars(&self) -> Vec<String> {
        fn supports_to_string(ty: &TypeInfo) -> bool {
            matches!(
                ty,
                TypeInfo::Primitive(
                    PrimitiveType::I64
                        | PrimitiveType::I32
                        | PrimitiveType::F64
                        | PrimitiveType::Bool
                )
            )
        }
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            if supports_to_string(ty) {
                vars.push(name.clone());
            }
        }
        for param in self.params {
            if supports_to_string(&param.param_type) {
                vars.push(param.name.clone());
            }
        }
        vars
    }

    /// Get all array-typed variables in scope, along with their element type.
    ///
    /// Returns `(name, element_type)` pairs for variables of type `[T]`.
    pub fn array_vars(&self) -> Vec<(String, TypeInfo)> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            if let TypeInfo::Array(elem) = ty {
                vars.push((name.clone(), *elem.clone()));
            }
        }
        for param in self.params {
            if let TypeInfo::Array(elem) = &param.param_type {
                vars.push((param.name.clone(), *elem.clone()));
            }
        }
        vars
    }

    /// Get all fixed-size array-typed variables in scope.
    ///
    /// Returns `(name, element_type, size)` tuples for variables of type `[T; N]`.
    pub fn fixed_array_vars(&self) -> Vec<(String, TypeInfo, usize)> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            if let TypeInfo::FixedArray(elem, size) = ty {
                vars.push((name.clone(), *elem.clone(), *size));
            }
        }
        for param in self.params {
            if let TypeInfo::FixedArray(elem, size) = &param.param_type {
                vars.push((param.name.clone(), *elem.clone(), *size));
            }
        }
        vars
    }

    /// Get all optional-typed variables in scope whose inner type matches.
    ///
    /// Returns `(name, inner_type)` pairs for variables of type `T?` where T
    /// matches the given target.
    pub fn optional_vars_matching(&self, target: &TypeInfo) -> Vec<(String, TypeInfo)> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            if let TypeInfo::Optional(inner) = ty {
                if types_compatible(inner, target) {
                    vars.push((name.clone(), *inner.clone()));
                }
            }
        }
        for param in self.params {
            if let TypeInfo::Optional(inner) = &param.param_type {
                if types_compatible(inner, target) {
                    vars.push((param.name.clone(), *inner.clone()));
                }
            }
        }
        vars
    }

    /// Get all optional-typed variables in scope whose inner type is a class.
    ///
    /// Returns `(name, mod_id, sym_id)` triples for variables of type `ClassName?`.
    pub fn optional_class_vars(&self) -> Vec<(String, ModuleId, SymbolId)> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            if let TypeInfo::Optional(inner) = ty {
                if let TypeInfo::Class(mod_id, sym_id) = inner.as_ref() {
                    vars.push((name.clone(), *mod_id, *sym_id));
                }
            }
        }
        for param in self.params {
            if let TypeInfo::Optional(inner) = &param.param_type {
                if let TypeInfo::Class(mod_id, sym_id) = inner.as_ref() {
                    vars.push((param.name.clone(), *mod_id, *sym_id));
                }
            }
        }
        vars
    }

    /// Get all tuple-typed variables in scope, along with their element types.
    pub fn tuple_vars(&self) -> Vec<(String, Vec<TypeInfo>)> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            if let TypeInfo::Tuple(elems) = ty {
                vars.push((name.clone(), elems.clone()));
            }
        }
        for param in self.params {
            if let TypeInfo::Tuple(elems) = &param.param_type {
                vars.push((param.name.clone(), elems.clone()));
            }
        }
        vars
    }

    /// Get all union-typed variables in scope, along with their variant types.
    pub fn union_typed_vars(&self) -> Vec<(&str, &[TypeInfo])> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            if let TypeInfo::Union(variants) = ty {
                vars.push((name.as_str(), variants.as_slice()));
            }
        }
        for param in self.params {
            if let TypeInfo::Union(variants) = &param.param_type {
                vars.push((param.name.as_str(), variants.as_slice()));
            }
        }
        vars
    }

    /// Get all string-typed variables in scope.
    pub fn string_vars(&self) -> Vec<String> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            if matches!(ty, TypeInfo::Primitive(PrimitiveType::String)) {
                vars.push(name.clone());
            }
        }
        for param in self.params {
            if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::String)) {
                vars.push(param.name.clone());
            }
        }
        vars
    }

    /// Get all variables in scope (any type), for use in string interpolation.
    pub fn all_vars(&self) -> Vec<(&str, &TypeInfo)> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            vars.push((name.as_str(), ty));
        }
        for param in self.params {
            vars.push((param.name.as_str(), &param.param_type));
        }
        vars
    }

    /// Get all class-typed variables in scope.
    ///
    /// Returns `(name, mod_id, sym_id)` triples for variables of class type.
    /// Only includes non-generic classes.
    pub fn class_vars(&self) -> Vec<(String, ModuleId, SymbolId)> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            if let TypeInfo::Class(mod_id, sym_id) = ty {
                // Check if the class is non-generic
                if let Some(sym) = self.table.get_symbol(*mod_id, *sym_id) {
                    if let SymbolKind::Class(ref info) = sym.kind {
                        if info.type_params.is_empty() {
                            vars.push((name.clone(), *mod_id, *sym_id));
                        }
                    }
                }
            }
        }
        for param in self.params {
            if let TypeInfo::Class(mod_id, sym_id) = &param.param_type {
                if let Some(sym) = self.table.get_symbol(*mod_id, *sym_id) {
                    if let SymbolKind::Class(ref info) = sym.kind {
                        if info.type_params.is_empty() {
                            vars.push((param.name.clone(), *mod_id, *sym_id));
                        }
                    }
                }
            }
        }
        vars
    }

    /// Get all struct-typed variables in scope.
    ///
    /// Returns `(name, mod_id, sym_id)` triples for variables of struct type.
    /// Structs are value types and never generic.
    pub fn struct_vars(&self) -> Vec<(String, ModuleId, SymbolId)> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            if let TypeInfo::Struct(mod_id, sym_id) = ty {
                vars.push((name.clone(), *mod_id, *sym_id));
            }
        }
        for param in self.params {
            if let TypeInfo::Struct(mod_id, sym_id) = &param.param_type {
                vars.push((param.name.clone(), *mod_id, *sym_id));
            }
        }
        vars
    }

    /// Get all interface-typed variables in scope.
    ///
    /// Returns `(name, mod_id, sym_id)` triples for variables of interface type.
    /// Used to generate vtable-dispatch method calls on interface-typed locals/params.
    pub fn interface_typed_vars(&self) -> Vec<(String, ModuleId, SymbolId)> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            if let TypeInfo::Interface(mod_id, sym_id) = ty {
                vars.push((name.clone(), *mod_id, *sym_id));
            }
        }
        for param in self.params {
            if let TypeInfo::Interface(mod_id, sym_id) = &param.param_type {
                vars.push((param.name.clone(), *mod_id, *sym_id));
            }
        }
        vars
    }

    /// Get all type-param-typed variables in scope that have interface constraints.
    ///
    /// Returns `(var_name, type_param_name, constraints)` tuples for variables
    /// whose type is a type parameter with at least one interface constraint.
    /// Only returns variables where the corresponding type param has constraints.
    pub fn constrained_type_param_vars(&self) -> Vec<(String, String, Vec<(ModuleId, SymbolId)>)> {
        let mut vars = Vec::new();

        // Check parameters for type-param-typed variables
        for param in self.params {
            if let TypeInfo::TypeParam(ref tp_name) = param.param_type {
                // Look up the type param in our type_params to get its constraints
                if let Some(tp) = self.type_params.iter().find(|tp| &tp.name == tp_name) {
                    if !tp.constraints.is_empty() {
                        vars.push((param.name.clone(), tp_name.clone(), tp.constraints.clone()));
                    }
                }
            }
        }

        // Check locals for type-param-typed variables
        for (name, ty) in self.locals {
            if let TypeInfo::TypeParam(tp_name) = ty {
                if let Some(tp) = self.type_params.iter().find(|tp| &tp.name == tp_name) {
                    if !tp.constraints.is_empty() {
                        vars.push((name.clone(), tp_name.clone(), tp.constraints.clone()));
                    }
                }
            }
        }

        vars
    }
}

/// Information about a chainable method on a class.
#[derive(Debug, Clone)]
pub struct ChainableMethod {
    /// The method name.
    pub name: String,
    /// The method parameters (excluding self).
    pub params: Vec<ParamInfo>,
    /// Whether this method returns Self (can be chained further).
    pub returns_self: bool,
}

/// Get all chainable methods for a class.
///
/// Returns methods from:
/// 1. The class's own methods (ClassInfo.methods)
/// 2. Standalone implement blocks targeting this class
///
/// Methods that return Self (from standalone implement blocks) are marked as chainable.
pub fn get_chainable_methods(
    table: &SymbolTable,
    mod_id: ModuleId,
    class_id: SymbolId,
) -> Vec<ChainableMethod> {
    let mut methods = Vec::new();

    // Get the class info
    let Some(class_sym) = table.get_symbol(mod_id, class_id) else {
        return methods;
    };
    let SymbolKind::Class(ref class_info) = class_sym.kind else {
        return methods;
    };

    // Add methods from the class itself (these don't return Self)
    for method in &class_info.methods {
        methods.push(ChainableMethod {
            name: method.name.clone(),
            params: method.params.clone(),
            returns_self: false,
        });
    }

    // Find standalone implement blocks targeting this class
    let Some(module) = table.get_module(mod_id) else {
        return methods;
    };

    for impl_sym in module.implement_blocks() {
        let SymbolKind::ImplementBlock(ref impl_info) = impl_sym.kind else {
            continue;
        };

        // Check if this is a standalone implement block (no interface) for our class
        if impl_info.interface.is_some() {
            continue;
        }
        if impl_info.target_type != (mod_id, class_id) {
            continue;
        }

        // Add methods from this standalone implement block (these return Self)
        for method in &impl_info.methods {
            methods.push(ChainableMethod {
                name: method.name.clone(),
                params: method.params.clone(),
                returns_self: true, // Methods in standalone impl blocks return Self
            });
        }
    }

    methods
}

/// Get all methods from an interface, including inherited methods from parent interfaces.
///
/// Returns all MethodInfo for the interface and any interfaces it extends.
pub fn get_interface_methods(
    table: &SymbolTable,
    mod_id: ModuleId,
    iface_id: SymbolId,
) -> Vec<MethodInfo> {
    let mut all_methods = Vec::new();
    let mut seen_names = std::collections::HashSet::new();
    let mut stack = vec![(mod_id, iface_id)];
    let mut visited = std::collections::HashSet::new();

    while let Some((mid, sid)) = stack.pop() {
        if !visited.insert((mid, sid)) {
            continue; // Avoid infinite loops from cycles
        }

        if let Some(symbol) = table.get_symbol(mid, sid) {
            if let SymbolKind::Interface(ref info) = symbol.kind {
                // Add this interface's own methods
                for method in &info.methods {
                    if seen_names.insert(method.name.clone()) {
                        all_methods.push(method.clone());
                    }
                }

                // Queue parent interfaces
                for &(parent_mid, parent_sid) in &info.extends {
                    stack.push((parent_mid, parent_sid));
                }
            }
        }
    }

    all_methods
}

/// Get methods callable on a type parameter based on its interface constraints.
///
/// Returns all methods from all constraining interfaces.
pub fn get_type_param_constraint_methods(
    table: &SymbolTable,
    constraints: &[(ModuleId, SymbolId)],
) -> Vec<(InterfaceInfo, MethodInfo)> {
    let mut methods = Vec::new();
    let mut seen_names = std::collections::HashSet::new();

    for &(mod_id, iface_id) in constraints {
        if let Some(symbol) = table.get_symbol(mod_id, iface_id) {
            if let SymbolKind::Interface(ref iface_info) = symbol.kind {
                let iface_methods = get_interface_methods(table, mod_id, iface_id);
                for method in iface_methods {
                    if seen_names.insert(method.name.clone()) {
                        methods.push((iface_info.clone(), method));
                    }
                }
            }
        }
    }

    methods
}

/// Check if two types are compatible for expression generation.
fn types_compatible(actual: &TypeInfo, expected: &TypeInfo) -> bool {
    match (actual, expected) {
        (TypeInfo::Primitive(a), TypeInfo::Primitive(e)) => a == e,
        (TypeInfo::Void, TypeInfo::Void) => true,
        (TypeInfo::Optional(a), TypeInfo::Optional(e)) => types_compatible(a, e),
        (TypeInfo::Array(a), TypeInfo::Array(e)) => types_compatible(a, e),
        (TypeInfo::FixedArray(a, sa), TypeInfo::FixedArray(e, se)) => {
            sa == se && types_compatible(a, e)
        }
        (TypeInfo::Tuple(a), TypeInfo::Tuple(e)) => {
            a.len() == e.len()
                && a.iter()
                    .zip(e.iter())
                    .all(|(ai, ei)| types_compatible(ai, ei))
        }
        (TypeInfo::Struct(ma, sa), TypeInfo::Struct(me, se)) => ma == me && sa == se,
        (TypeInfo::Class(ma, sa), TypeInfo::Class(me, se)) => ma == me && sa == se,
        (TypeInfo::Interface(ma, sa), TypeInfo::Interface(me, se)) => ma == me && sa == se,
        _ => false,
    }
}

/// Check if a type is numeric.
#[allow(dead_code)]
fn is_numeric_type(ty: &TypeInfo) -> bool {
    matches!(
        ty,
        TypeInfo::Primitive(PrimitiveType::I8)
            | TypeInfo::Primitive(PrimitiveType::I16)
            | TypeInfo::Primitive(PrimitiveType::I32)
            | TypeInfo::Primitive(PrimitiveType::I64)
            | TypeInfo::Primitive(PrimitiveType::I128)
            | TypeInfo::Primitive(PrimitiveType::U8)
            | TypeInfo::Primitive(PrimitiveType::U16)
            | TypeInfo::Primitive(PrimitiveType::U32)
            | TypeInfo::Primitive(PrimitiveType::U64)
            | TypeInfo::Primitive(PrimitiveType::F32)
            | TypeInfo::Primitive(PrimitiveType::F64)
    )
}

fn is_integer_type(ty: &TypeInfo) -> bool {
    matches!(
        ty,
        TypeInfo::Primitive(PrimitiveType::I8)
            | TypeInfo::Primitive(PrimitiveType::I16)
            | TypeInfo::Primitive(PrimitiveType::I32)
            | TypeInfo::Primitive(PrimitiveType::I64)
            | TypeInfo::Primitive(PrimitiveType::I128)
            | TypeInfo::Primitive(PrimitiveType::U8)
            | TypeInfo::Primitive(PrimitiveType::U16)
            | TypeInfo::Primitive(PrimitiveType::U32)
            | TypeInfo::Primitive(PrimitiveType::U64)
    )
}

/// Check whether a type is safe to capture in a closure.
///
/// Only primitive types are capturable to avoid complex reference-counting
/// interactions and type inference issues with class/struct/interface captures
/// in generated code.
fn is_capturable_type(ty: &TypeInfo) -> bool {
    matches!(ty, TypeInfo::Primitive(_))
}

/// Check whether a type can be safely used inside string interpolation.
///
/// Primitives (i32, i64, f64, bool, string) and arrays of primitives are
/// safe because the runtime knows how to stringify them.  Class/struct
/// types are NOT safe (no automatic `.to_string()` conversion).
fn is_printable_in_interpolation(ty: &TypeInfo) -> bool {
    match ty {
        TypeInfo::Primitive(_) => true,
        TypeInfo::Array(elem) => matches!(elem.as_ref(), TypeInfo::Primitive(_)),
        _ => false,
    }
}

/// Expression generator.
pub struct ExprGenerator<'a, R> {
    rng: &'a mut R,
    config: &'a ExprConfig,
}

impl<'a, R: Rng> ExprGenerator<'a, R> {
    /// Create a new expression generator.
    pub fn new(rng: &'a mut R, config: &'a ExprConfig) -> Self {
        Self { rng, config }
    }

    /// Generate an expression of the given type.
    pub fn generate(&mut self, ty: &TypeInfo, ctx: &ExprContext, depth: usize) -> String {
        // At max depth, always return a simple expression
        if depth >= self.config.max_depth {
            return self.generate_simple(ty, ctx);
        }

        // Chance to generate tuple indexing for any type:
        // when a tuple-typed variable with a matching element is in scope,
        // emit `tupleVar[index]` instead of constructing a new value.
        if self.config.tuple_index_probability > 0.0
            && self.rng.gen_bool(self.config.tuple_index_probability)
        {
            if let Some(expr) = self.try_generate_tuple_index_for_type(ty, ctx) {
                return expr;
            }
        }

        match ty {
            TypeInfo::Primitive(prim) => self.generate_primitive(*prim, ctx, depth),
            TypeInfo::Optional(inner) => self.generate_optional(inner, ctx, depth),
            TypeInfo::Void => "nil".to_string(),
            TypeInfo::Array(elem) => self.generate_array(elem, ctx, depth),
            TypeInfo::FixedArray(elem, size) => self.generate_fixed_array(elem, *size, ctx, depth),
            TypeInfo::TypeParam(name) => {
                // For type params, try to find a matching parameter, else use panic
                for param in ctx.params {
                    if let TypeInfo::TypeParam(param_type_name) = &param.param_type
                        && param_type_name == name
                    {
                        return param.name.clone();
                    }
                }
                // No matching parameter found - use panic (this shouldn't happen with good planning)
                "panic(\"unreachable: type parameter has no source\")".to_string()
            }
            TypeInfo::Tuple(elem_types) => self.generate_tuple(elem_types, ctx, depth),
            TypeInfo::Union(variants) => {
                // For union types, generate a value for a random variant
                if variants.is_empty() {
                    "nil".to_string()
                } else {
                    let idx = self.rng.gen_range(0..variants.len());
                    self.generate(&variants[idx].clone(), ctx, depth)
                }
            }
            TypeInfo::Function {
                param_types,
                return_type,
            } => {
                // Generate a lambda expression matching the function type
                let param_types = param_types.clone();
                let return_type = return_type.as_ref().clone();
                self.generate_lambda(&param_types, &return_type, ctx, depth)
            }
            TypeInfo::Class(mod_id, sym_id) => {
                // For class types, try method chaining if there's a matching variable
                self.generate_class_expr(*mod_id, *sym_id, ctx)
            }
            TypeInfo::Struct(mod_id, sym_id) => {
                // For struct types, try to find an existing variable or construct
                self.generate_struct_expr(*mod_id, *sym_id, ctx)
            }
            TypeInfo::Interface(mod_id, sym_id) => {
                // For interface types, try to find an existing variable or construct
                if let Some(var) = ctx.find_matching_var(ty)
                    && self.rng.gen_bool(0.7)
                {
                    var
                } else {
                    self.generate_interface_value(*mod_id, *sym_id, ctx)
                }
            }
            _ => self.generate_simple(ty, ctx),
        }
    }

    /// Generate an expression of a class type.
    ///
    /// Tries to find an existing variable of this class type and optionally
    /// chain method calls on it (if methods return Self).
    fn generate_class_expr(
        &mut self,
        mod_id: ModuleId,
        sym_id: SymbolId,
        ctx: &ExprContext,
    ) -> String {
        // Find variables of this class type
        let class_vars: Vec<_> = ctx
            .class_vars()
            .into_iter()
            .filter(|(_, m, s)| *m == mod_id && *s == sym_id)
            .collect();

        if class_vars.is_empty() {
            // No variable of this type, fall back to literal-style generation
            return self.generate_simple(&TypeInfo::Class(mod_id, sym_id), ctx);
        }

        // Pick a random variable
        let var_idx = self.rng.gen_range(0..class_vars.len());
        let (var_name, _, _) = &class_vars[var_idx];

        // Decide whether to chain methods
        if self.rng.gen_bool(self.config.method_chain_probability) {
            // Get chainable methods for this class
            let methods = get_chainable_methods(ctx.table, mod_id, sym_id);

            // Only chain if there are Self-returning methods
            let self_returning: Vec<_> = methods.iter().filter(|m| m.returns_self).collect();
            if !self_returning.is_empty() {
                // Build a method chain
                let mut expr = var_name.clone();
                let mut chain_depth = 0;

                while chain_depth < self.config.max_chain_depth {
                    // Pick a Self-returning method
                    let method_idx = self.rng.gen_range(0..self_returning.len());
                    let method = self_returning[method_idx];

                    // Generate arguments
                    let args = self.generate_method_args(&method.params, ctx);
                    expr = format!("{}.{}({})", expr, method.name, args);
                    chain_depth += 1;

                    // Probabilistically stop chaining
                    if !self.rng.gen_bool(self.config.method_chain_probability) {
                        break;
                    }
                }

                return expr;
            }
        }

        // No chaining, just return the variable
        var_name.clone()
    }

    /// Generate an expression of a struct type.
    ///
    /// Tries to find an existing variable of this struct type, or falls back
    /// to constructing a new struct instance. Structs are value types and
    /// can be freely copied, so returning an existing variable is safe.
    fn generate_struct_expr(
        &mut self,
        mod_id: ModuleId,
        sym_id: SymbolId,
        ctx: &ExprContext,
    ) -> String {
        // Find variables of this struct type
        let struct_vars: Vec<_> = ctx
            .struct_vars()
            .into_iter()
            .filter(|(_, m, s)| *m == mod_id && *s == sym_id)
            .collect();

        // 60% chance to use an existing variable if one exists
        if !struct_vars.is_empty() && self.rng.gen_bool(0.6) {
            let var_idx = self.rng.gen_range(0..struct_vars.len());
            let (var_name, _, _) = &struct_vars[var_idx];
            return var_name.clone();
        }

        // Fall back to constructing a new struct
        self.generate_struct_construction(mod_id, sym_id, ctx)
    }

    /// Generate a struct construction expression.
    ///
    /// Constructs an instance of the struct with all fields initialized.
    fn generate_struct_construction(
        &mut self,
        mod_id: ModuleId,
        sym_id: SymbolId,
        ctx: &ExprContext,
    ) -> String {
        let Some(symbol) = ctx.table.get_symbol(mod_id, sym_id) else {
            return "nil".to_string();
        };
        let SymbolKind::Struct(ref struct_info) = symbol.kind else {
            return "nil".to_string();
        };

        let struct_name = symbol.name.clone();
        let fields = struct_info.fields.clone();

        // Generate field values — occasionally use inline expressions
        let field_values: Vec<String> = fields
            .iter()
            .map(|f| {
                let value = self.generate_arg_expr(&f.field_type, ctx);
                format!("{}: {}", f.name, value)
            })
            .collect();

        format!("{} {{ {} }}", struct_name, field_values.join(", "))
    }

    /// Generate a value of an interface type by constructing an implementing class.
    ///
    /// Finds a non-generic class in the same module that implements the given
    /// interface and constructs it. Falls back to an i64 literal if no implementor
    /// is found (callers should avoid passing interface types when no implementor
    /// exists, but this provides a safe fallback).
    fn generate_interface_value(
        &mut self,
        iface_mod: ModuleId,
        iface_sym: SymbolId,
        ctx: &ExprContext,
    ) -> String {
        let module = match ctx.table.get_module(iface_mod) {
            Some(m) => m,
            None => return self.literal_for_primitive(PrimitiveType::I64),
        };

        // Find a non-generic class implementing this interface
        for class_sym in module.classes() {
            if let SymbolKind::Class(ref class_info) = class_sym.kind {
                if class_info.type_params.is_empty()
                    && class_info
                        .implements
                        .iter()
                        .any(|&(m, s)| m == iface_mod && s == iface_sym)
                {
                    return self.generate_class_construction(iface_mod, class_sym.id, ctx);
                }
            }
        }

        self.literal_for_primitive(PrimitiveType::I64)
    }

    /// Try to generate an array index expression on an array-typed local.
    ///
    /// Looks for array-typed variables in scope whose element type matches
    /// the target primitive type. Returns `Some("arrayVar[index]")` on success,
    /// using a small constant index (0..=1) to stay within bounds of typical
    /// small arrays (which have 2-4 elements).
    fn try_generate_array_index(
        &mut self,
        prim: PrimitiveType,
        ctx: &ExprContext,
    ) -> Option<String> {
        let target = TypeInfo::Primitive(prim);
        let array_vars = ctx.array_vars();

        // Filter to arrays whose element type matches the target
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| types_compatible(elem_ty, &target))
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, _) = &candidates[idx];

        // Use a small constant index to stay within bounds of small arrays.
        // Arrays generated in stmt.rs have 2-4 elements, so use 0..=1 to be safe.
        let index = self.rng.gen_range(0..=1);
        let suffix = match prim {
            PrimitiveType::I32 => "_i32",
            PrimitiveType::I64 => "_i64",
            _ => "_i64", // default index type
        };
        Some(format!("{}[{}{}]", var_name, index, suffix))
    }

    /// Try to generate a fixed array index expression on a fixed-array-typed local.
    ///
    /// Looks for fixed-array-typed variables in scope whose element type matches
    /// the target primitive type. Returns `Some("fixedArrayVar[index]")` on success,
    /// using a constant index within bounds of the array size.
    fn try_generate_fixed_array_index(
        &mut self,
        prim: PrimitiveType,
        ctx: &ExprContext,
    ) -> Option<String> {
        let target = TypeInfo::Primitive(prim);
        let fixed_array_vars = ctx.fixed_array_vars();

        // Filter to fixed arrays whose element type matches the target
        let candidates: Vec<_> = fixed_array_vars
            .iter()
            .filter(|(_, elem_ty, _)| types_compatible(elem_ty, &target))
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, _, size) = &candidates[idx];

        // Use a constant index within bounds of the fixed array.
        // Clamp to 0..=(size-1) to stay within bounds.
        let max_index = size.saturating_sub(1).max(0);
        let index = self.rng.gen_range(0..=max_index);
        let suffix = match prim {
            PrimitiveType::I32 => "_i32",
            PrimitiveType::I64 => "_i64",
            _ => "_i64", // default index type
        };
        Some(format!("{}[{}{}]", var_name, index, suffix))
    }

    /// Try to generate a tuple index expression on a tuple-typed local.
    ///
    /// Looks for tuple-typed variables in scope that contain an element
    /// matching the target primitive type. Returns `Some("tupleVar[index]")`
    /// using a constant integer literal index. Tuple indexing requires a
    /// compile-time constant index in Vole (non-constant indices are rejected
    /// by codegen).
    fn try_generate_tuple_index_for_type(
        &mut self,
        target: &TypeInfo,
        ctx: &ExprContext,
    ) -> Option<String> {
        let tuple_vars = ctx.tuple_vars();

        // Build candidates: (var_name, index) pairs where elem type matches target
        let mut candidates: Vec<(&str, usize)> = Vec::new();
        for (name, elem_types) in &tuple_vars {
            for (i, elem_ty) in elem_types.iter().enumerate() {
                if types_compatible(elem_ty, target) {
                    candidates.push((name.as_str(), i));
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, elem_index) = candidates[idx];
        Some(format!("{}[{}]", var_name, elem_index))
    }

    /// Try to generate a field access expression on a class-typed local.
    ///
    /// Looks for local variables with class type whose fields match the
    /// target primitive type. Returns `Some("local.field")` on success.
    /// Also supports nested field access through class-typed fields, e.g.,
    /// `local.inner.field` where `inner` is a class-typed field.
    /// Only considers non-generic classes (generic field types are too
    /// complex to resolve).
    fn try_generate_field_access(
        &mut self,
        prim: PrimitiveType,
        ctx: &ExprContext,
    ) -> Option<String> {
        let target = TypeInfo::Primitive(prim);

        // Collect full access paths (e.g., "obj.field" or "obj.inner.field")
        let mut candidates: Vec<String> = Vec::new();

        for (name, ty) in ctx.locals {
            match ty {
                TypeInfo::Class(mod_id, sym_id) => {
                    self.collect_field_paths(
                        ctx.table,
                        *mod_id,
                        *sym_id,
                        name.clone(),
                        &target,
                        &mut candidates,
                        0, // depth
                    );
                }
                TypeInfo::Struct(mod_id, sym_id) => {
                    self.collect_field_paths(
                        ctx.table,
                        *mod_id,
                        *sym_id,
                        name.clone(),
                        &target,
                        &mut candidates,
                        0, // depth
                    );
                }
                _ => {}
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        Some(candidates[idx].clone())
    }

    /// Recursively collect field access paths that lead to the target type.
    ///
    /// This enables nested field access like `obj.inner.field` where `inner`
    /// is a class-typed field. Depth is limited to prevent infinite recursion
    /// in case of any cyclic references (though planning should prevent these).
    fn collect_field_paths(
        &self,
        table: &SymbolTable,
        mod_id: ModuleId,
        sym_id: SymbolId,
        prefix: String,
        target: &TypeInfo,
        candidates: &mut Vec<String>,
        depth: usize,
    ) {
        // Limit depth to prevent excessive nesting (and handle any cycles)
        const MAX_DEPTH: usize = 3;
        if depth >= MAX_DEPTH {
            return;
        }

        let Some(sym) = table.get_symbol(mod_id, sym_id) else {
            return;
        };

        let fields = match &sym.kind {
            SymbolKind::Class(info) => {
                // Skip generic classes
                if !info.type_params.is_empty() {
                    return;
                }
                &info.fields
            }
            SymbolKind::Struct(info) => &info.fields,
            _ => return,
        };

        for field in fields {
            let field_path = format!("{}.{}", prefix, field.name);

            // Check if this field matches the target type
            if &field.field_type == target {
                candidates.push(field_path.clone());
            }

            // If this field is a class or struct type, recurse into it
            match &field.field_type {
                TypeInfo::Class(nested_mod_id, nested_sym_id)
                | TypeInfo::Struct(nested_mod_id, nested_sym_id) => {
                    self.collect_field_paths(
                        table,
                        *nested_mod_id,
                        *nested_sym_id,
                        field_path,
                        target,
                        candidates,
                        depth + 1,
                    );
                }
                _ => {}
            }
        }
    }

    /// Try to generate a null coalescing expression (`optVar ?? defaultExpr`).
    ///
    /// Looks for optional-typed variables in scope whose inner type matches
    /// the target type. Returns `Some("optVar ?? defaultExpr")` on success.
    /// The result type is the inner type T (not T?).
    ///
    /// When multiple optional variables of matching type are in scope,
    /// generates a chained coalescing expression like
    /// `optA ?? optB ?? defaultExpr` (up to 3 optionals in the chain)
    /// with probability controlled by `config.chained_coalesce_probability`.
    fn try_generate_null_coalesce(
        &mut self,
        target: &TypeInfo,
        ctx: &ExprContext,
        depth: usize,
    ) -> Option<String> {
        let candidates = ctx.optional_vars_matching(target);
        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (first_var, _inner_ty) = &candidates[idx];

        // When 2+ optional vars match, sometimes chain them: a ?? b ?? default
        if candidates.len() >= 2
            && self.config.chained_coalesce_probability > 0.0
            && self.rng.gen_bool(self.config.chained_coalesce_probability)
        {
            // Pick 1-2 additional optional vars for the chain (up to 3 total)
            let max_extra = (candidates.len() - 1).min(2);
            let extra_count = self.rng.gen_range(1..=max_extra);

            let mut chain_parts = vec![first_var.clone()];
            let mut used = std::collections::HashSet::new();
            used.insert(idx);

            for _ in 0..extra_count {
                // Pick a different candidate
                let remaining: Vec<usize> = (0..candidates.len())
                    .filter(|i| !used.contains(i))
                    .collect();
                if remaining.is_empty() {
                    break;
                }
                let pick = self.rng.gen_range(0..remaining.len());
                let chosen_idx = remaining[pick];
                used.insert(chosen_idx);
                chain_parts.push(candidates[chosen_idx].0.clone());
            }

            // Generate a default value of the inner type as the final fallback
            let default_expr = self.generate(target, ctx, depth + 1);
            chain_parts.push(default_expr);

            return Some(format!("({})", chain_parts.join(" ?? ")));
        }

        // Generate a default value of the inner type
        let default_expr = self.generate(target, ctx, depth + 1);

        Some(format!("({} ?? {})", first_var, default_expr))
    }

    /// Generate a simple string→string method call suffix for chaining.
    ///
    /// Returns a suffix like `.trim()`, `.to_upper()`, or `.to_lower()`.
    /// These are safe to chain onto any string expression without arguments,
    /// keeping the generated code simple and avoiding issues with nested
    /// `replace`/`substring` calls.
    fn random_simple_string_chain_suffix(&mut self) -> &'static str {
        let methods = [".trim()", ".to_upper()", ".to_lower()"];
        methods[self.rng.gen_range(0..methods.len())]
    }

    /// Try to generate a `str.length()` call for an i64 expression.
    ///
    /// Looks for string-typed variables in scope and returns
    /// `Some("strVar.length()")` on success.
    fn try_generate_string_length(&mut self, ctx: &ExprContext) -> Option<String> {
        let candidates = ctx.string_vars();
        if candidates.is_empty() {
            return None;
        }
        let idx = self.rng.gen_range(0..candidates.len());
        let var = &candidates[idx];

        // ~25% chance to prepend a string→string transform before .length()
        // e.g. str.trim().length()
        if self.rng.gen_bool(self.config.method_chain_probability) {
            let chain = self.random_simple_string_chain_suffix();
            Some(format!("{}{}.length()", var, chain))
        } else {
            Some(format!("{}.length()", var))
        }
    }

    /// Try to generate a bool-returning string method call.
    ///
    /// Randomly picks one of `contains`, `starts_with`, or `ends_with`.
    /// Looks for string-typed variables in scope and returns
    /// `Some("strVar.method(\"literal\")")` on success. The argument is
    /// always a short string literal to keep the expression simple.
    fn try_generate_string_bool_method(&mut self, ctx: &ExprContext) -> Option<String> {
        let candidates = ctx.string_vars();
        if candidates.is_empty() {
            return None;
        }
        let idx = self.rng.gen_range(0..candidates.len());
        let var = &candidates[idx];

        // ~25% chance to prepend a string→string transform before the bool method
        // e.g. str.to_lower().contains("x")
        let chain = if self.rng.gen_bool(self.config.method_chain_probability) {
            self.random_simple_string_chain_suffix()
        } else {
            ""
        };

        // Pick a bool-returning string method
        let methods = ["contains", "starts_with", "ends_with"];
        let method = methods[self.rng.gen_range(0..methods.len())];

        // Use a short literal substring as the argument
        let substrings = ["str", "hello", "a", "test", "x", ""];
        let sub_idx = self.rng.gen_range(0..substrings.len());
        Some(format!(
            "{}{}.{}(\"{}\")",
            var, chain, method, substrings[sub_idx]
        ))
    }

    /// Try to generate a string-returning string method call.
    ///
    /// Randomly picks one of `to_upper`, `to_lower`, `trim`, `replace`,
    /// or `replace_all`. Looks for string-typed variables in scope and
    /// returns `Some("strVar.method(...)")` on success.
    ///
    /// For `replace`/`replace_all`, uses fixed string literal arguments
    /// to keep RNG consumption constant (exactly 2 RNG calls: one for
    /// the variable, one for the method) regardless of which method is
    /// selected.
    fn try_generate_string_transform_method(&mut self, ctx: &ExprContext) -> Option<String> {
        let candidates = ctx.string_vars();
        if candidates.is_empty() {
            return None;
        }
        let idx = self.rng.gen_range(0..candidates.len());
        let var = &candidates[idx];

        // Pick a string-returning string method.
        // replace/replace_all take (old, new) string args; substring takes (start, end) i64 args;
        // others take no args.
        let methods = [
            "to_upper",
            "to_lower",
            "trim",
            "replace",
            "replace_all",
            "substring",
        ];
        let method = methods[self.rng.gen_range(0..methods.len())];

        let base = match method {
            "replace" | "replace_all" => {
                // Use fixed literal arguments so no extra RNG is consumed.
                // These patterns exercise search-and-replace without
                // changing downstream RNG state.
                format!("{}.{}(\"str\", \"val\")", var, method)
            }
            "substring" => {
                // substring(start, end) takes two i64 arguments.
                // Use small non-negative literals to stay in bounds for typical strings.
                // Using fixed values keeps RNG consumption constant.
                format!("{}.substring(0, 3)", var)
            }
            _ => format!("{}.{}()", var, method),
        };

        // ~25% chance to chain another simple string→string transform
        // e.g. str.trim().to_upper()
        if self.rng.gen_bool(self.config.method_chain_probability) {
            let chain = self.random_simple_string_chain_suffix();
            Some(format!("{}{}", base, chain))
        } else {
            Some(base)
        }
    }

    /// Try to generate a `.to_string()` call on a numeric or boolean variable.
    ///
    /// Looks for numeric (i8..u64, f32, f64) and bool variables in scope and
    /// returns `Some("var.to_string()")` on success. This produces a string-typed
    /// expression that exercises primitive method dispatch.
    fn try_generate_to_string_call(&mut self, ctx: &ExprContext) -> Option<String> {
        let candidates = ctx.to_string_candidate_vars();
        if candidates.is_empty() {
            return None;
        }
        let idx = self.rng.gen_range(0..candidates.len());
        let var = &candidates[idx];
        Some(format!("{}.to_string()", var))
    }

    /// Try to generate a string interpolation containing a method call.
    ///
    /// Looks for string-typed or array-typed variables in scope and generates
    /// an interpolated string that includes a method call on the variable.
    /// For strings: `.to_upper()`, `.to_lower()`, `.trim()`, `.length()`.
    /// For arrays: `.length()`.
    /// Returns `None` if no suitable variables are in scope.
    fn try_generate_method_call_interpolation(&mut self, ctx: &ExprContext) -> Option<String> {
        // Collect candidate variables: strings and arrays
        let string_vars = ctx.string_vars();
        let array_vars = ctx.array_vars();

        if string_vars.is_empty() && array_vars.is_empty() {
            return None;
        }

        // Build a flat list of (name, is_string) candidates
        let mut candidates: Vec<(&str, bool)> = Vec::new();
        for name in &string_vars {
            candidates.push((name.as_str(), true));
        }
        for (name, _elem_ty) in &array_vars {
            candidates.push((name.as_str(), false));
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, is_string) = candidates[idx];

        // Generate the method call expression
        let method_expr = if is_string {
            match self.rng.gen_range(0..4) {
                0 => format!("{}.to_upper()", var_name),
                1 => format!("{}.to_lower()", var_name),
                2 => format!("{}.trim()", var_name),
                _ => format!("{}.length()", var_name),
            }
        } else {
            format!("{}.length()", var_name)
        };

        // Wrap in an interpolated string with optional prefix text
        let prefixes = ["len: ", "upper: ", "result: ", "val: ", "got ", ""];
        let prefix = prefixes[self.rng.gen_range(0..prefixes.len())];
        Some(format!("\"{}{{{}}}\"", prefix, method_expr))
    }

    /// Try to generate a `str.split(",").collect()` call for a `[string]` expression.
    ///
    /// Looks for string-typed variables in scope and returns
    /// `Some("strVar.split(\"delim\").collect()")` on success.
    fn try_generate_string_split(&mut self, ctx: &ExprContext) -> Option<String> {
        let candidates = ctx.string_vars();
        if candidates.is_empty() {
            return None;
        }
        let idx = self.rng.gen_range(0..candidates.len());
        let var = &candidates[idx];

        // Use a short literal delimiter
        let delimiters = [",", " ", ":", ";", "-", "::"];
        let delim = delimiters[self.rng.gen_range(0..delimiters.len())];

        Some(format!("{}.split(\"{}\").collect()", var, delim))
    }

    /// Try to generate a `str.chars().collect()` call for a `[i32]` expression.
    ///
    /// `.chars()` returns character codepoints as i32 values, so
    /// `.chars().collect()` produces `[i32]`. Looks for string-typed
    /// variables in scope and returns `Some("strVar.chars().collect()")`
    /// on success. Optionally chains a simple string transform before `.chars()`.
    fn try_generate_string_chars_collect(&mut self, ctx: &ExprContext) -> Option<String> {
        let candidates = ctx.string_vars();
        if candidates.is_empty() {
            return None;
        }
        let idx = self.rng.gen_range(0..candidates.len());
        let var = &candidates[idx];

        // ~25% chance to prepend a string→string transform before .chars()
        // e.g. str.trim().chars().collect()
        if self.rng.gen_bool(self.config.method_chain_probability) {
            let chain = self.random_simple_string_chain_suffix();
            Some(format!("{}{}.chars().collect()", var, chain))
        } else {
            Some(format!("{}.chars().collect()", var))
        }
    }

    /// Generate a string concatenation expression using the `+` operator.
    ///
    /// Produces expressions like `"hello" + " world"`, `str_var + " suffix"`,
    /// `str_var + num.to_string()`, or `str_var + other_var`. Concatenates 2-3
    /// operands, each of which is a string variable, string literal, or a
    /// `.to_string()` call on a numeric/bool variable.
    fn generate_string_concat(&mut self, ctx: &ExprContext, depth: usize) -> String {
        let str_ty = TypeInfo::Primitive(PrimitiveType::String);
        let operand_count = self.rng.gen_range(2..=3);
        let mut parts = Vec::new();

        for _ in 0..operand_count {
            // ~30% chance: use .to_string() on a numeric/bool variable
            if self.rng.gen_bool(0.3) {
                if let Some(expr) = self.try_generate_to_string_call(ctx) {
                    parts.push(expr);
                    continue;
                }
            }
            // Use a simple string expression (variable or literal) to avoid
            // deep nesting of complex sub-expressions in concatenation.
            parts.push(self.generate_simple(&str_ty, ctx));
        }

        let _ = depth; // depth reserved for future nested concat support
        format!("({})", parts.join(" + "))
    }

    /// Try to generate an interface method call on a type-param-typed variable.
    ///
    /// Looks for variables in scope whose type is a type parameter with interface
    /// constraints. If found, picks a method from one of the constraining interfaces
    /// whose return type matches the target type and generates a method call.
    ///
    /// Returns `Some("varName.methodName(args)")` on success.
    fn try_generate_type_param_method_call(
        &mut self,
        target: &TypeInfo,
        ctx: &ExprContext,
    ) -> Option<String> {
        let constrained_vars = ctx.constrained_type_param_vars();
        if constrained_vars.is_empty() {
            return None;
        }

        // Collect all (var_name, method_name, params) candidates where method returns target type
        let mut candidates: Vec<(String, String, Vec<ParamInfo>)> = Vec::new();

        for (var_name, _tp_name, constraints) in &constrained_vars {
            let methods = get_type_param_constraint_methods(ctx.table, constraints);
            for (_iface_info, method) in methods {
                // Check if return type matches target (only check non-generic interfaces)
                if types_compatible(&method.return_type, target) {
                    candidates.push((var_name.clone(), method.name.clone(), method.params.clone()));
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, method_name, params) = &candidates[idx];

        // Generate arguments for the method call
        let args = self.generate_method_args(params, ctx);
        Some(format!("{}.{}({})", var_name, method_name, args))
    }

    /// Try to generate an optional chaining expression (`optVar?.fieldName`).
    ///
    /// Looks for optional-typed variables in scope whose inner type is a class
    /// with accessible fields. Returns `Some(("optVar?.fieldName", field_type?))`
    /// where the result type is `Optional(field_type)`.
    /// Only considers non-generic classes.
    fn try_generate_optional_chaining(&mut self, ctx: &ExprContext) -> Option<(String, TypeInfo)> {
        let opt_class_vars = ctx.optional_class_vars();
        if opt_class_vars.is_empty() {
            return None;
        }

        // Collect (var_name, field_name, field_type) candidates
        let mut candidates: Vec<(String, String, TypeInfo)> = Vec::new();

        for (var_name, mod_id, sym_id) in &opt_class_vars {
            if let Some(sym) = ctx.table.get_symbol(*mod_id, *sym_id) {
                if let SymbolKind::Class(ref info) = sym.kind {
                    // Skip generic classes
                    if !info.type_params.is_empty() {
                        continue;
                    }
                    for field in &info.fields {
                        candidates.push((
                            var_name.clone(),
                            field.name.clone(),
                            field.field_type.clone(),
                        ));
                    }
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, field_name, field_type) = &candidates[idx];

        // The result of ?. is always optional
        let result_type = TypeInfo::Optional(Box::new(field_type.clone()));
        Some((format!("{}?.{}", var_name, field_name), result_type))
    }

    /// Try to generate an iterator `.any()` or `.all()` expression.
    ///
    /// Looks for array-typed variables in scope with primitive element types
    /// and generates `arrVar.iter().any((x) => PRED)` or
    /// `arrVar.iter().all((x) => PRED)`. Returns a bool-typed expression.
    ///
    /// Predicates are type-appropriate:
    /// - Numeric (i64, f64): comparisons like `x > 3`, `x < 10`, `x % 2 == 0`
    /// - Bool: `x` or `!x`
    /// - String: `x.length() > N`
    fn try_generate_iter_any_all(&mut self, ctx: &ExprContext) -> Option<String> {
        let array_vars = ctx.array_vars();

        // Filter to arrays with primitive element types that support predicates
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| {
                matches!(
                    elem_ty,
                    TypeInfo::Primitive(
                        PrimitiveType::I64
                            | PrimitiveType::F64
                            | PrimitiveType::Bool
                            | PrimitiveType::String
                    )
                )
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, elem_ty) = candidates[idx];

        // Pick any() or all()
        let method = if self.rng.gen_bool(0.5) { "any" } else { "all" };

        // Generate a type-appropriate predicate body
        let pred = match elem_ty {
            TypeInfo::Primitive(PrimitiveType::I64) => match self.rng.gen_range(0..4) {
                0 => {
                    let n = self.rng.gen_range(0..=5);
                    format!("x > {}", n)
                }
                1 => {
                    let n = self.rng.gen_range(0..=10);
                    format!("x < {}", n)
                }
                2 => "x % 2 == 0".to_string(),
                _ => {
                    let n = self.rng.gen_range(0..=5);
                    format!("x != {}", n)
                }
            },
            TypeInfo::Primitive(PrimitiveType::F64) => {
                let n = self.rng.gen_range(0..=50);
                format!("x > {}.0", n)
            }
            TypeInfo::Primitive(PrimitiveType::Bool) => {
                if self.rng.gen_bool(0.5) {
                    "x".to_string()
                } else {
                    "!x".to_string()
                }
            }
            TypeInfo::Primitive(PrimitiveType::String) => {
                let n = self.rng.gen_range(0..=3);
                format!("x.length() > {}", n)
            }
            _ => return None,
        };

        Some(format!("{}.iter().{}((x) => {})", var_name, method, pred))
    }

    /// Try to generate an iterator `.map().collect()` expression for array generation.
    ///
    /// Looks for array-typed variables in scope with primitive element types and
    /// generates `arrVar.iter().map((x) => body).collect()` where the mapping
    /// closure transforms the source element type into the target element type.
    ///
    /// Supported same-type mappings:
    /// - `i64 -> i64`: `x * 2`, `x + 1`, `x % 10`, `-x`
    /// - `f64 -> f64`: `x * 2.0`, `x + 1.0`, `-x`
    /// - `i32 -> i32`: `x * 2`, `x + 1`
    /// - `string -> string`: `x.trim()`, `x.to_upper()`, `x.to_lower()`
    /// - `bool -> bool`: `!x`
    ///
    /// Supported cross-type mappings:
    /// - `i64 -> bool`: `x > 0`, `x % 2 == 0`
    /// - `string -> i64`: `x.length()`
    fn try_generate_iter_map_collect(
        &mut self,
        target_elem: &TypeInfo,
        ctx: &ExprContext,
    ) -> Option<String> {
        let array_vars = ctx.array_vars();

        // Build candidates: (var_name, source_elem_ty) where we can map source -> target
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, src_elem)| self.can_map_types(src_elem, target_elem))
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, src_elem) = candidates[idx];

        let body = self.generate_map_body(src_elem, target_elem)?;

        Some(format!(
            "{}.iter().map((x) => {}).collect()",
            var_name, body
        ))
    }

    /// Check whether we can generate a map closure from `src` to `target`.
    fn can_map_types(&self, src: &TypeInfo, target: &TypeInfo) -> bool {
        use PrimitiveType::*;
        match (src, target) {
            // Same-type mappings
            (TypeInfo::Primitive(I64), TypeInfo::Primitive(I64)) => true,
            (TypeInfo::Primitive(F64), TypeInfo::Primitive(F64)) => true,
            (TypeInfo::Primitive(I32), TypeInfo::Primitive(I32)) => true,
            (TypeInfo::Primitive(String), TypeInfo::Primitive(String)) => true,
            (TypeInfo::Primitive(Bool), TypeInfo::Primitive(Bool)) => true,
            // Cross-type mappings
            (TypeInfo::Primitive(I64), TypeInfo::Primitive(Bool)) => true,
            (TypeInfo::Primitive(String), TypeInfo::Primitive(I64)) => true,
            _ => false,
        }
    }

    /// Generate the body of a map closure that transforms `src` type to `target` type.
    fn generate_map_body(&mut self, src: &TypeInfo, target: &TypeInfo) -> Option<String> {
        use PrimitiveType::*;
        match (src, target) {
            (TypeInfo::Primitive(I64), TypeInfo::Primitive(I64)) => {
                Some(match self.rng.gen_range(0..4) {
                    0 => "x * 2".to_string(),
                    1 => "x + 1".to_string(),
                    2 => "x % 10".to_string(),
                    _ => "-x".to_string(),
                })
            }
            (TypeInfo::Primitive(F64), TypeInfo::Primitive(F64)) => {
                Some(match self.rng.gen_range(0..3) {
                    0 => "x * 2.0".to_string(),
                    1 => "x + 1.0".to_string(),
                    _ => "-x".to_string(),
                })
            }
            (TypeInfo::Primitive(I32), TypeInfo::Primitive(I32)) => {
                Some(match self.rng.gen_range(0..2) {
                    0 => "x * 2_i32".to_string(),
                    _ => "x + 1_i32".to_string(),
                })
            }
            (TypeInfo::Primitive(String), TypeInfo::Primitive(String)) => {
                Some(match self.rng.gen_range(0..3) {
                    0 => "x.trim()".to_string(),
                    1 => "x.to_upper()".to_string(),
                    _ => "x.to_lower()".to_string(),
                })
            }
            (TypeInfo::Primitive(Bool), TypeInfo::Primitive(Bool)) => Some("!x".to_string()),
            (TypeInfo::Primitive(I64), TypeInfo::Primitive(Bool)) => {
                Some(match self.rng.gen_range(0..2) {
                    0 => "x > 0".to_string(),
                    _ => "x % 2 == 0".to_string(),
                })
            }
            (TypeInfo::Primitive(String), TypeInfo::Primitive(I64)) => {
                Some("x.length()".to_string())
            }
            _ => None,
        }
    }

    /// Try to generate an iterator `.filter().collect()` expression for array generation.
    ///
    /// Looks for array-typed variables in scope whose element type matches the
    /// target element type and generates `arrVar.iter().filter((x) => pred).collect()`.
    /// The predicate is type-appropriate, reusing the same patterns as `try_generate_iter_any_all`.
    fn try_generate_iter_filter_collect(
        &mut self,
        target_elem: &TypeInfo,
        ctx: &ExprContext,
    ) -> Option<String> {
        let array_vars = ctx.array_vars();

        // Filter to arrays whose element type matches and is a supported primitive
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| {
                elem_ty == target_elem
                    && matches!(
                        elem_ty,
                        TypeInfo::Primitive(
                            PrimitiveType::I64
                                | PrimitiveType::F64
                                | PrimitiveType::I32
                                | PrimitiveType::Bool
                                | PrimitiveType::String
                        )
                    )
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, elem_ty) = candidates[idx];

        // Generate a type-appropriate predicate (same patterns as any/all)
        let pred = match elem_ty {
            TypeInfo::Primitive(PrimitiveType::I64) => match self.rng.gen_range(0..4) {
                0 => {
                    let n = self.rng.gen_range(0..=5);
                    format!("x > {}", n)
                }
                1 => {
                    let n = self.rng.gen_range(0..=10);
                    format!("x < {}", n)
                }
                2 => "x % 2 == 0".to_string(),
                _ => {
                    let n = self.rng.gen_range(0..=5);
                    format!("x != {}", n)
                }
            },
            TypeInfo::Primitive(PrimitiveType::F64) => {
                let n = self.rng.gen_range(0..=50);
                format!("x > {}.0", n)
            }
            TypeInfo::Primitive(PrimitiveType::I32) => match self.rng.gen_range(0..3) {
                0 => {
                    let n = self.rng.gen_range(0..=5);
                    format!("x > {}", n)
                }
                1 => {
                    let n = self.rng.gen_range(0..=10);
                    format!("x < {}", n)
                }
                _ => "x % 2 == 0".to_string(),
            },
            TypeInfo::Primitive(PrimitiveType::Bool) => {
                if self.rng.gen_bool(0.5) {
                    "x".to_string()
                } else {
                    "!x".to_string()
                }
            }
            TypeInfo::Primitive(PrimitiveType::String) => {
                let n = self.rng.gen_range(0..=3);
                format!("x.length() > {}", n)
            }
            _ => return None,
        };

        Some(format!(
            "{}.iter().filter((x) => {}).collect()",
            var_name, pred
        ))
    }

    /// Try to generate an `.iter().count()` expression for i64 generation.
    ///
    /// Looks for array-typed variables in scope and generates `arrVar.iter().count()`.
    /// Optionally chains a `.filter()` before `.count()` for more interesting expressions.
    /// Returns an i64-typed expression.
    fn try_generate_iter_count(&mut self, ctx: &ExprContext) -> Option<String> {
        let array_vars = ctx.array_vars();
        if array_vars.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..array_vars.len());
        let (var_name, elem_ty) = &array_vars[idx];

        // ~40% chance to chain a .filter() before .count()
        if self.rng.gen_bool(0.4) {
            let pred = match elem_ty {
                TypeInfo::Primitive(PrimitiveType::I64) => {
                    let n = self.rng.gen_range(0..=5);
                    Some(format!("x > {}", n))
                }
                TypeInfo::Primitive(PrimitiveType::F64) => {
                    let n = self.rng.gen_range(0..=50);
                    Some(format!("x > {}.0", n))
                }
                TypeInfo::Primitive(PrimitiveType::I32) => {
                    let n = self.rng.gen_range(0..=5);
                    Some(format!("x > {}", n))
                }
                TypeInfo::Primitive(PrimitiveType::Bool) => Some("x".to_string()),
                TypeInfo::Primitive(PrimitiveType::String) => {
                    let n = self.rng.gen_range(0..=3);
                    Some(format!("x.length() > {}", n))
                }
                _ => None,
            };
            if let Some(pred) = pred {
                return Some(format!(
                    "{}.iter().filter((x) => {}).count()",
                    var_name, pred
                ));
            }
        }

        Some(format!("{}.iter().count()", var_name))
    }

    /// Try to generate an `.iter().reduce()` expression.
    ///
    /// Looks for array-typed variables in scope and generates reduce expressions
    /// based on the target type:
    /// - `i64` target from `[i64]`: `arr.iter().reduce(0, (acc, x) => acc + x)` (sum)
    /// - `string` target from `[string]`: `arr.iter().reduce("", (acc, x) => acc + x + " ")` (join)
    /// - `string` target from `[i64]`: `arr.iter().map((x) => "" + x).reduce("", (acc, s) => acc + s + ",")` (stringify+join)
    fn try_generate_iter_reduce(&mut self, target: &TypeInfo, ctx: &ExprContext) -> Option<String> {
        let array_vars = ctx.array_vars();
        if array_vars.is_empty() {
            return None;
        }

        // Collect candidates: (var_name, elem_type) pairs that can produce target
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| match target {
                TypeInfo::Primitive(PrimitiveType::I64) => {
                    matches!(elem_ty, TypeInfo::Primitive(PrimitiveType::I64))
                }
                TypeInfo::Primitive(PrimitiveType::String) => {
                    matches!(
                        elem_ty,
                        TypeInfo::Primitive(PrimitiveType::String | PrimitiveType::I64)
                    )
                }
                _ => false,
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, elem_ty) = candidates[idx];

        match (target, elem_ty) {
            // i64 from [i64]: sum via reduce
            (TypeInfo::Primitive(PrimitiveType::I64), TypeInfo::Primitive(PrimitiveType::I64)) => {
                Some(format!(
                    "{}.iter().reduce(0, (acc, x) => acc + x)",
                    var_name
                ))
            }
            // string from [string]: join with space
            (
                TypeInfo::Primitive(PrimitiveType::String),
                TypeInfo::Primitive(PrimitiveType::String),
            ) => Some(format!(
                "{}.iter().reduce(\"\", (acc, x) => acc + x + \" \")",
                var_name
            )),
            // string from [i64]: map to string then join with comma
            (
                TypeInfo::Primitive(PrimitiveType::String),
                TypeInfo::Primitive(PrimitiveType::I64),
            ) => Some(format!(
                "{}.iter().map((x) => \"\" + x).reduce(\"\", (acc, s) => acc + s + \",\")",
                var_name
            )),
            _ => None,
        }
    }

    /// Try to generate an `.iter().sum()` expression for numeric types.
    ///
    /// Looks for array-typed variables in scope with numeric element types (i64, f64)
    /// and generates `arrVar.iter().sum()`. Optionally chains a `.filter()` or `.map()`
    /// before `.sum()` for more interesting expressions.
    fn try_generate_iter_sum(
        &mut self,
        target_prim: PrimitiveType,
        ctx: &ExprContext,
    ) -> Option<String> {
        let array_vars = ctx.array_vars();

        // Filter to arrays whose element type matches target numeric type
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| *elem_ty == TypeInfo::Primitive(target_prim))
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, _) = candidates[idx];

        // ~30% chance: chain a .filter() before .sum()
        if self.rng.gen_bool(0.3) {
            let pred = match target_prim {
                PrimitiveType::I64 => {
                    let n = self.rng.gen_range(0..=5);
                    format!("x > {}", n)
                }
                PrimitiveType::F64 => {
                    let n = self.rng.gen_range(0..=10);
                    format!("x > {}.0", n)
                }
                _ => return Some(format!("{}.iter().sum()", var_name)),
            };
            return Some(format!("{}.iter().filter((x) => {}).sum()", var_name, pred));
        }

        // ~20% chance: chain a .map() before .sum() (same type)
        if self.rng.gen_bool(0.2) {
            let body = match target_prim {
                PrimitiveType::I64 => match self.rng.gen_range(0..3) {
                    0 => "x * 2",
                    1 => "x + 1",
                    _ => "-x",
                },
                PrimitiveType::F64 => match self.rng.gen_range(0..2) {
                    0 => "x * 2.0",
                    _ => "x + 1.0",
                },
                _ => return Some(format!("{}.iter().sum()", var_name)),
            };
            return Some(format!("{}.iter().map((x) => {}).sum()", var_name, body));
        }

        Some(format!("{}.iter().sum()", var_name))
    }

    /// Try to generate an `.iter().skip(N).take(M).collect()` expression for array generation.
    ///
    /// Looks for array-typed variables in scope whose element type matches the
    /// target element type and generates `arrVar.iter().skip(N).take(M).collect()`.
    /// Uses small skip/take values to avoid producing empty arrays.
    fn try_generate_iter_skip_take_collect(
        &mut self,
        target_elem: &TypeInfo,
        ctx: &ExprContext,
    ) -> Option<String> {
        let array_vars = ctx.array_vars();

        // Filter to arrays whose element type matches
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| elem_ty == target_elem)
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (var_name, _) = candidates[idx];

        // Use small values to keep results non-empty (arrays have min 2 elements)
        let skip = self.rng.gen_range(0..=1);
        let take = self.rng.gen_range(1..=2);

        Some(format!(
            "{}.iter().skip({}).take({}).collect()",
            var_name, skip, take
        ))
    }

    /// Generate arguments for a method call.
    ///
    /// With probability `inline_expr_arg_probability`, each argument may be a
    /// `when`/`if` expression rather than a plain literal or variable reference.
    fn generate_method_args(&mut self, params: &[ParamInfo], ctx: &ExprContext) -> String {
        params
            .iter()
            .map(|p| self.generate_arg_expr(&p.param_type, ctx))
            .collect::<Vec<_>>()
            .join(", ")
    }

    /// Generate an expression suitable for an argument or field-value position.
    ///
    /// Most of the time this produces a simple expression (literal or variable
    /// reference via `generate_simple`). With probability `inline_expr_arg_probability`,
    /// it generates a richer inline expression — a two-arm `when` conditional — to
    /// exercise the compiler's handling of complex expressions in call arguments
    /// and struct/class field initializers.
    ///
    /// Only generates inline expressions for primitive types (i32, i64, f64, bool,
    /// string) to avoid deeply nested class/struct constructions in argument position.
    pub fn generate_arg_expr(&mut self, ty: &TypeInfo, ctx: &ExprContext) -> String {
        let is_primitive = matches!(ty, TypeInfo::Primitive(_));
        if is_primitive && self.rng.gen_bool(self.config.inline_expr_arg_probability) {
            // Generate a two-arm `when { cond => val, _ => val }` expression.
            // Use max_depth to keep the sub-expressions shallow.
            self.generate_if_expr(ty, ctx, self.config.max_depth.saturating_sub(1))
        } else {
            self.generate_simple(ty, ctx)
        }
    }

    /// Generate a simple expression (literal or variable reference).
    pub fn generate_simple(&mut self, ty: &TypeInfo, ctx: &ExprContext) -> String {
        // For interface types, sometimes construct a concrete class instance
        // (upcast) instead of reusing an existing interface-typed variable.
        // This exercises the implicit class -> interface coercion codegen path.
        let force_upcast = matches!(ty, TypeInfo::Interface(..))
            && self.rng.gen_bool(self.config.interface_upcast_probability);

        // Try to find a matching variable first (skip if forcing upcast)
        if !force_upcast
            && let Some(var) = ctx.find_matching_var(ty)
            && self.rng.gen_bool(0.6)
        {
            return var;
        }

        // Otherwise generate a literal (or simple method call)
        match ty {
            TypeInfo::Primitive(PrimitiveType::Bool) => {
                // String bool method: contains/starts_with/ends_with
                if self.rng.gen_bool(self.config.string_method_probability) {
                    if let Some(expr) = self.try_generate_string_bool_method(ctx) {
                        return expr;
                    }
                }
                self.literal_for_primitive(PrimitiveType::Bool)
            }
            TypeInfo::Primitive(p) => self.literal_for_primitive(*p),
            TypeInfo::Optional(inner) => {
                // Generate a typed inner value instead of nil so that
                // containers like [T?] can infer the element type.
                self.generate_simple(inner, ctx)
            }
            TypeInfo::Void => "nil".to_string(),
            TypeInfo::Tuple(elem_types) => {
                // Generate a simple tuple with literal elements
                let elements: Vec<String> = elem_types
                    .iter()
                    .map(|t| self.generate_simple(t, ctx))
                    .collect();
                format!("[{}]", elements.join(", "))
            }
            TypeInfo::FixedArray(elem, size) => {
                // Generate a simple repeat literal
                let value = self.generate_simple(elem, ctx);
                format!("[{}; {}]", value, size)
            }
            TypeInfo::Array(elem) => {
                // Generate a simple array with 2 literal elements
                let v1 = self.generate_simple(elem, ctx);
                let v2 = self.generate_simple(elem, ctx);
                format!("[{}, {}]", v1, v2)
            }
            TypeInfo::Union(variants) => {
                // Generate a literal for a random variant
                if let Some(first) = variants.first() {
                    self.generate_simple(first, ctx)
                } else {
                    "nil".to_string()
                }
            }
            TypeInfo::Function {
                param_types,
                return_type,
            } => {
                // Generate a simple lambda expression
                let param_types = param_types.clone();
                let return_type = return_type.as_ref().clone();
                self.generate_lambda(&param_types, &return_type, ctx, self.config.max_depth)
            }
            TypeInfo::Class(mod_id, sym_id) => {
                // Generate a class construction expression
                self.generate_class_construction(*mod_id, *sym_id, ctx)
            }
            TypeInfo::Struct(mod_id, sym_id) => {
                // Generate a struct construction expression
                self.generate_struct_construction(*mod_id, *sym_id, ctx)
            }
            TypeInfo::Interface(mod_id, sym_id) => {
                // Generate a class that implements this interface
                self.generate_interface_value(*mod_id, *sym_id, ctx)
            }
            _ => self.literal_for_primitive(PrimitiveType::I64),
        }
    }

    /// Generate a class construction expression.
    ///
    /// Constructs an instance of the class with all fields initialized.
    /// For fields that are themselves class-typed, recursively constructs
    /// nested instances.
    fn generate_class_construction(
        &mut self,
        mod_id: ModuleId,
        sym_id: SymbolId,
        ctx: &ExprContext,
    ) -> String {
        let Some(symbol) = ctx.table.get_symbol(mod_id, sym_id) else {
            return "nil".to_string();
        };
        let SymbolKind::Class(ref class_info) = symbol.kind else {
            return "nil".to_string();
        };

        // Skip generic classes - they require type arguments we don't track
        if !class_info.type_params.is_empty() {
            return "nil".to_string();
        }

        let class_name = symbol.name.clone();
        let fields = class_info.fields.clone();

        // Generate field values — occasionally use inline expressions
        let field_values: Vec<String> = fields
            .iter()
            .map(|f| {
                let value = self.generate_arg_expr(&f.field_type, ctx);
                format!("{}: {}", f.name, value)
            })
            .collect();

        format!("{} {{ {} }}", class_name, field_values.join(", "))
    }

    /// Generate a primitive expression.
    fn generate_primitive(
        &mut self,
        prim: PrimitiveType,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        // ~18% chance to generate a field access if a class-typed local
        // has a field of the target primitive type
        if self.rng.gen_bool(0.18) {
            if let Some(access) = self.try_generate_field_access(prim, ctx) {
                return access;
            }
        }

        // ~15% chance to generate array indexing: `arrVar[index]`
        // when an array-typed variable with matching element type is in scope
        if self.rng.gen_bool(0.15) {
            if let Some(expr) = self.try_generate_array_index(prim, ctx) {
                return expr;
            }
        }

        // ~12% chance to generate fixed array indexing: `fixedArrVar[index]`
        // when a fixed-array-typed variable with matching element type is in scope
        if self.rng.gen_bool(0.12) {
            if let Some(expr) = self.try_generate_fixed_array_index(prim, ctx) {
                return expr;
            }
        }

        // Chance to generate tuple indexing: `tupleVar[index]`
        // when a tuple-typed variable with a matching element type is in scope
        if self.config.tuple_index_probability > 0.0
            && self.rng.gen_bool(self.config.tuple_index_probability)
        {
            if let Some(expr) =
                self.try_generate_tuple_index_for_type(&TypeInfo::Primitive(prim), ctx)
            {
                return expr;
            }
        }

        // ~15% chance to generate null coalescing: `optVar ?? defaultExpr`
        // when an optional-typed variable with matching inner type is in scope
        if self.rng.gen_bool(0.15) {
            if let Some(expr) =
                self.try_generate_null_coalesce(&TypeInfo::Primitive(prim), ctx, depth)
            {
                return expr;
            }
        }

        // String method: str.length() for i64 expressions.
        // (No arguments, so vole-fmt never wraps the call across lines.)
        if prim == PrimitiveType::I64 && self.rng.gen_bool(self.config.string_method_probability) {
            if let Some(expr) = self.try_generate_string_length(ctx) {
                return expr;
            }
        }

        // ~10% chance to generate arr.iter().count() for i64 expressions
        if prim == PrimitiveType::I64 && self.rng.gen_bool(0.10) {
            if let Some(expr) = self.try_generate_iter_count(ctx) {
                return expr;
            }
        }

        // ~8% chance to generate arr.iter().reduce(0, (acc, x) => acc + x) for i64 expressions
        if prim == PrimitiveType::I64 && self.rng.gen_bool(0.08) {
            if let Some(expr) =
                self.try_generate_iter_reduce(&TypeInfo::Primitive(PrimitiveType::I64), ctx)
            {
                return expr;
            }
        }

        // ~10% chance to generate arr.iter().sum() for i64/f64 expressions
        if (prim == PrimitiveType::I64 || prim == PrimitiveType::F64) && self.rng.gen_bool(0.10) {
            if let Some(expr) = self.try_generate_iter_sum(prim, ctx) {
                return expr;
            }
        }

        // ~15% chance to call an interface method on a type-param-typed variable
        // when the method's return type matches our target primitive type.
        if self.rng.gen_bool(0.15) {
            if let Some(expr) =
                self.try_generate_type_param_method_call(&TypeInfo::Primitive(prim), ctx)
            {
                return expr;
            }
        }

        let choice = self.rng.gen_range(0..12);

        match prim {
            PrimitiveType::I32 | PrimitiveType::I64 | PrimitiveType::F64 => {
                match choice {
                    0..=3 => {
                        // Binary arithmetic expression
                        self.generate_binary_arith(prim, ctx, depth)
                    }
                    4 => {
                        // Unary: negation or bitwise NOT (integer only)
                        if prim != PrimitiveType::F64 && self.rng.gen_bool(0.5) {
                            // Bitwise NOT on integer operand
                            let inner = self.generate_simple(&TypeInfo::Primitive(prim), ctx);
                            format!("(~{})", inner)
                        } else {
                            // Unary negation
                            let suffix = match prim {
                                PrimitiveType::I32 => "_i32",
                                PrimitiveType::I64 => "_i64",
                                PrimitiveType::F64 => "_f64",
                                _ => "",
                            };
                            let val = self.rng.gen_range(1..100);
                            format!("(-{}{})", val, suffix)
                        }
                    }
                    5..=6 => {
                        // Multi-arm when expression
                        self.generate_when_expr(&TypeInfo::Primitive(prim), ctx, depth)
                    }
                    7 => {
                        // Match expression
                        let ty = TypeInfo::Primitive(prim);
                        self.generate_match_expr(&ty, &ty, ctx, depth)
                    }
                    8 => {
                        // Two-arm conditional (if-expression equivalent)
                        self.generate_if_expr(&TypeInfo::Primitive(prim), ctx, depth)
                    }
                    _ => self.generate_simple(&TypeInfo::Primitive(prim), ctx),
                }
            }
            PrimitiveType::Bool => {
                // ~10% chance to generate arr.iter().any/all((x) => PRED)
                // when an array with primitive elements is in scope
                if self.rng.gen_bool(0.10) {
                    if let Some(expr) = self.try_generate_iter_any_all(ctx) {
                        return expr;
                    }
                }
                match choice {
                    0..=2 => {
                        // Comparison expression
                        self.generate_comparison(ctx, depth)
                    }
                    3..=4 => {
                        // Boolean binary (and/or)
                        self.generate_binary_bool(ctx, depth)
                    }
                    5 => {
                        // Unary not - only negate simple expressions
                        let inner =
                            self.generate_simple(&TypeInfo::Primitive(PrimitiveType::Bool), ctx);
                        format!("(!{})", inner)
                    }
                    6 => {
                        // Match expression
                        let ty = TypeInfo::Primitive(prim);
                        self.generate_match_expr(&ty, &ty, ctx, depth)
                    }
                    7 => {
                        // Two-arm conditional (if-expression equivalent)
                        self.generate_if_expr(&TypeInfo::Primitive(prim), ctx, depth)
                    }
                    8 => {
                        // Type test (is) expression on union-typed variable
                        self.generate_is_expr(ctx).unwrap_or_else(|| {
                            self.generate_simple(&TypeInfo::Primitive(prim), ctx)
                        })
                    }
                    9 => {
                        // Negated compound boolean: !(a > b), !(a && b), !(a || b)
                        self.generate_negated_compound_bool(ctx, depth)
                    }
                    10 => {
                        // Compound boolean: (a > 0 && b < 10) || c
                        self.generate_compound_bool(ctx, depth)
                    }
                    _ => self.generate_simple(&TypeInfo::Primitive(prim), ctx),
                }
            }
            PrimitiveType::String => {
                // ~15% chance: .to_string() on numeric/bool variable
                if self.rng.gen_bool(0.15) {
                    if let Some(expr) = self.try_generate_to_string_call(ctx) {
                        return expr;
                    }
                }
                // String method: to_upper/to_lower/trim/replace/replace_all/substring
                if self.rng.gen_bool(self.config.string_method_probability) {
                    if let Some(expr) = self.try_generate_string_transform_method(ctx) {
                        return expr;
                    }
                }
                // ~12% chance: interpolated string with a method call
                if self.rng.gen_bool(0.12) {
                    if let Some(expr) = self.try_generate_method_call_interpolation(ctx) {
                        return expr;
                    }
                }
                // ~10% chance: arr.iter().reduce("", ...) for string expressions
                if self.rng.gen_bool(0.10) {
                    if let Some(expr) = self
                        .try_generate_iter_reduce(&TypeInfo::Primitive(PrimitiveType::String), ctx)
                    {
                        return expr;
                    }
                }
                match choice {
                    0..=1 => {
                        // Multi-arm when expression returning string
                        self.generate_when_expr(&TypeInfo::Primitive(prim), ctx, depth)
                    }
                    2..=3 => {
                        // Match expression
                        let ty = TypeInfo::Primitive(prim);
                        self.generate_match_expr(&ty, &ty, ctx, depth)
                    }
                    4..=5 => {
                        // Two-arm conditional (if-expression equivalent)
                        self.generate_if_expr(&TypeInfo::Primitive(prim), ctx, depth)
                    }
                    6..=8 => {
                        // Interpolated string (~30%)
                        self.generate_interpolated_string(ctx)
                    }
                    9 => {
                        // String concatenation with + operator
                        self.generate_string_concat(ctx, depth)
                    }
                    _ => {
                        // ~10%: string transform method (to_upper/to_lower/trim)
                        if let Some(expr) = self.try_generate_string_transform_method(ctx) {
                            expr
                        } else {
                            self.generate_simple(&TypeInfo::Primitive(prim), ctx)
                        }
                    }
                }
            }
            // Wider integer and float types: generate simpler expressions
            // (no binary arith/bitwise since those only support i32/i64/f64)
            PrimitiveType::I8
            | PrimitiveType::I16
            | PrimitiveType::I128
            | PrimitiveType::U8
            | PrimitiveType::U16
            | PrimitiveType::U32
            | PrimitiveType::U64
            | PrimitiveType::F32 => {
                match choice {
                    0..=3 => {
                        // Literal
                        self.generate_simple(&TypeInfo::Primitive(prim), ctx)
                    }
                    4 => {
                        // Bitwise NOT (integer types only, not F32)
                        if prim != PrimitiveType::F32 {
                            let inner = self.generate_simple(&TypeInfo::Primitive(prim), ctx);
                            format!("(~{})", inner)
                        } else {
                            self.generate_simple(&TypeInfo::Primitive(prim), ctx)
                        }
                    }
                    5..=6 => {
                        // Multi-arm when expression
                        self.generate_when_expr(&TypeInfo::Primitive(prim), ctx, depth)
                    }
                    7 => {
                        // Match expression
                        let ty = TypeInfo::Primitive(prim);
                        self.generate_match_expr(&ty, &ty, ctx, depth)
                    }
                    8 => {
                        // Two-arm conditional (if-expression equivalent)
                        self.generate_if_expr(&TypeInfo::Primitive(prim), ctx, depth)
                    }
                    _ => self.generate_simple(&TypeInfo::Primitive(prim), ctx),
                }
            }
            PrimitiveType::Nil => "nil".to_string(),
        }
    }

    /// Generate a binary arithmetic expression.
    fn generate_binary_arith(
        &mut self,
        prim: PrimitiveType,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        // For integer types, 25% chance to generate a bitwise op instead
        if matches!(prim, PrimitiveType::I32 | PrimitiveType::I64) && self.rng.gen_bool(0.25) {
            return self.generate_binary_bitwise(prim, ctx, depth);
        }

        let ty = TypeInfo::Primitive(prim);
        let left = self.generate(&ty, ctx, depth + 1);
        let right = self.generate(&ty, ctx, depth + 1);

        // ~20% chance to generate modulo with a safe non-zero RHS
        if self.rng.gen_bool(0.20) {
            let rhs = self.nonzero_literal_for_primitive(prim);
            return format!("({} % {})", left, rhs);
        }

        let op = match self.rng.gen_range(0..4) {
            0 => "+",
            1 => "-",
            2 => "*",
            // Avoid division by zero by using addition instead
            _ => "+",
        };

        format!("({} {} {})", left, op, right)
    }

    /// Generate a binary bitwise expression (integer types only).
    ///
    /// Produces `&`, `|`, `^`, `<<`, or `>>`. For shift operators the RHS
    /// is constrained to a small literal to avoid undefined behaviour.
    fn generate_binary_bitwise(
        &mut self,
        prim: PrimitiveType,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        let ty = TypeInfo::Primitive(prim);
        let left = self.generate(&ty, ctx, depth + 1);

        let op = match self.rng.gen_range(0..5) {
            0 => "&",
            1 => "|",
            2 => "^",
            3 => "<<",
            _ => ">>",
        };

        // For shift operators, use a small literal RHS to avoid UB
        let right = if op == "<<" || op == ">>" {
            let max_shift = match prim {
                PrimitiveType::I32 => 15,
                PrimitiveType::I64 => 31,
                _ => unreachable!(),
            };
            let shift_amount = self.rng.gen_range(0..=max_shift);
            let suffix = match prim {
                PrimitiveType::I32 => "_i32",
                PrimitiveType::I64 => "_i64",
                _ => unreachable!(),
            };
            format!("{}{}", shift_amount, suffix)
        } else {
            self.generate(&ty, ctx, depth + 1)
        };

        format!("({} {} {})", left, op, right)
    }

    /// Generate a comparison expression.
    fn generate_comparison(&mut self, ctx: &ExprContext, depth: usize) -> String {
        let prim = match self.rng.gen_range(0..3) {
            0 => PrimitiveType::I32,
            1 => PrimitiveType::I64,
            _ => PrimitiveType::F64,
        };
        let ty = TypeInfo::Primitive(prim);
        let left = self.generate(&ty, ctx, depth + 1);
        let right = self.generate(&ty, ctx, depth + 1);

        let op = match self.rng.gen_range(0..6) {
            0 => "==",
            1 => "!=",
            2 => "<",
            3 => ">",
            4 => "<=",
            _ => ">=",
        };

        format!("({} {} {})", left, op, right)
    }

    /// Generate a binary boolean expression.
    fn generate_binary_bool(&mut self, ctx: &ExprContext, depth: usize) -> String {
        let ty = TypeInfo::Primitive(PrimitiveType::Bool);
        let left = self.generate(&ty, ctx, depth + 1);
        let right = self.generate(&ty, ctx, depth + 1);

        let op = if self.rng.gen_bool(0.5) { "&&" } else { "||" };

        format!("({} {} {})", left, op, right)
    }

    /// Generate a negated compound boolean expression.
    ///
    /// Produces expressions like `!(a > b)`, `!(a && b)`, or `!(a || b)`.
    /// This exercises the combination of boolean negation with compound
    /// sub-expressions (comparisons and binary boolean operators), which
    /// differs from the simple unary-not case that only negates literals
    /// or variable references.
    fn generate_negated_compound_bool(&mut self, ctx: &ExprContext, depth: usize) -> String {
        let inner = if self.rng.gen_bool(0.5) {
            // Negate a comparison: !(x > y), !(a == b), etc.
            self.generate_comparison(ctx, depth + 1)
        } else {
            // Negate a binary boolean: !(a && b), !(a || b)
            self.generate_binary_bool(ctx, depth + 1)
        };

        format!("(!{})", inner)
    }

    /// Generate a compound boolean expression with mixed `&&` and `||` operators.
    ///
    /// Produces expressions like `(a > 0 && b < 10) || c`, `(x || y) && (z > 5)`,
    /// or `(a && b) || (c && d)`. This exercises the compiler's short-circuit
    /// evaluation across parenthesized sub-groups with different operators,
    /// which is more complex than the single-operator `generate_binary_bool`.
    fn generate_compound_bool(&mut self, ctx: &ExprContext, depth: usize) -> String {
        // Pick the top-level operator; sub-groups use the opposite to ensure mixing.
        let top_op = if self.rng.gen_bool(0.5) { "||" } else { "&&" };
        let inner_op = if top_op == "||" { "&&" } else { "||" };

        // Generate 2-3 sub-groups joined by top_op.
        let group_count = self.rng.gen_range(2..=3_usize);
        let groups: Vec<String> = (0..group_count)
            .map(|_| {
                // Each sub-group is either a parenthesized pair joined by inner_op,
                // or a single boolean atom (comparison or simple bool).
                if self.rng.gen_bool(0.65) {
                    // Parenthesized pair with the inner operator
                    let a = self.generate_bool_atom(ctx, depth + 1);
                    let b = self.generate_bool_atom(ctx, depth + 1);
                    format!("({} {} {})", a, inner_op, b)
                } else {
                    // Single atom (no extra parens needed; generate wraps if needed)
                    self.generate_bool_atom(ctx, depth + 1)
                }
            })
            .collect();

        format!("({})", groups.join(&format!(" {} ", top_op)))
    }

    /// Generate a simple boolean atom for use in compound expressions.
    ///
    /// Produces either a comparison (`x > 5`), a simple bool variable/literal,
    /// or a negated simple bool. Avoids recursive compound generation to keep
    /// the output bounded.
    fn generate_bool_atom(&mut self, ctx: &ExprContext, depth: usize) -> String {
        match self.rng.gen_range(0..4_u32) {
            0..=1 => {
                // Comparison: (a > b), (x == y), etc.
                self.generate_comparison(ctx, depth)
            }
            2 => {
                // Simple bool variable or literal
                self.generate_simple(&TypeInfo::Primitive(PrimitiveType::Bool), ctx)
            }
            _ => {
                // Negated simple bool: !x, !true
                let inner = self.generate_simple(&TypeInfo::Primitive(PrimitiveType::Bool), ctx);
                format!("(!{})", inner)
            }
        }
    }

    /// Generate a type test (`is`) expression on a union-typed variable.
    ///
    /// Returns `Some("varName is TypeName")` if a union-typed variable is in scope,
    /// or `None` if no union-typed variables are available.
    pub fn generate_is_expr(&mut self, ctx: &ExprContext) -> Option<String> {
        let union_vars = ctx.union_typed_vars();
        if union_vars.is_empty() {
            return None;
        }

        let var_idx = self.rng.gen_range(0..union_vars.len());
        let (var_name, variants) = union_vars[var_idx];

        if variants.is_empty() {
            return None;
        }

        let variant_idx = self.rng.gen_range(0..variants.len());
        let variant = &variants[variant_idx];

        // Only generate `is` for primitive variants (type name is straightforward)
        match variant {
            TypeInfo::Primitive(prim) => Some(format!("({} is {})", var_name, prim.as_str())),
            _ => None,
        }
    }

    /// Generate a conditional expression using when (Vole's if-expression equivalent).
    ///
    /// Produces a 2-arm when expression: `when { cond => then, _ => else }`.
    /// This is distinct from generate_when_expr which produces 2-4 arms.
    fn generate_if_expr(&mut self, ty: &TypeInfo, ctx: &ExprContext, depth: usize) -> String {
        let cond = self.generate(&TypeInfo::Primitive(PrimitiveType::Bool), ctx, depth + 1);
        let then_expr = self.generate(ty, ctx, depth + 1);
        let else_expr = self.generate(ty, ctx, depth + 1);

        format!("when {{ {} => {}, _ => {} }}", cond, then_expr, else_expr)
    }

    /// Generate a when expression.
    ///
    /// Optionally uses `unreachable` in the wildcard arm when one of the
    /// preceding conditions is guaranteed to be true (e.g., `true => ...`).
    fn generate_when_expr(&mut self, ty: &TypeInfo, ctx: &ExprContext, depth: usize) -> String {
        // Decide if we want to use unreachable in the default arm
        let use_unreachable = self.rng.gen_bool(self.config.unreachable_probability);

        // Decide arm count: either 2 (1 condition + wildcard) or 3-4 (multi-arm)
        let arm_count = if self.rng.gen_bool(self.config.multi_arm_when_probability) {
            // Multi-arm: 3-4 total arms (2-3 conditions + wildcard)
            self.rng.gen_range(3..=4)
        } else {
            // Simple: 2 total arms (1 condition + wildcard)
            2
        };
        let mut arms = Vec::new();

        if use_unreachable {
            // Generate a "true" condition to guarantee the default arm is unreachable
            let value = self.generate(ty, ctx, depth + 1);
            arms.push(format!("true => {}", value));

            // Generate additional arms (will never execute, but syntactically valid)
            for _ in 1..arm_count - 1 {
                let cond = self.generate(&TypeInfo::Primitive(PrimitiveType::Bool), ctx, depth + 1);
                let arm_value = self.generate(ty, ctx, depth + 1);
                arms.push(format!("{} => {}", cond, arm_value));
            }

            // Default arm with unreachable
            arms.push("_ => unreachable".to_string());
        } else {
            // Normal when expression
            for _ in 0..arm_count - 1 {
                let cond = self.generate(&TypeInfo::Primitive(PrimitiveType::Bool), ctx, depth + 1);
                let value = self.generate(ty, ctx, depth + 1);
                arms.push(format!("{} => {}", cond, value));
            }

            // Default arm with a value
            let default_value = self.generate(ty, ctx, depth + 1);
            arms.push(format!("_ => {}", default_value));
        }

        format!("when {{ {} }}", arms.join(", "))
    }

    /// Generate an optional expression.
    fn generate_optional(&mut self, inner: &TypeInfo, ctx: &ExprContext, depth: usize) -> String {
        // ~20% chance to generate optional chaining (optVar?.field) when
        // an optional class-typed variable with a field matching inner is in scope.
        // The result of ?. is Optional(field_type).
        if self.rng.gen_bool(0.20) {
            if let Some((expr, result_ty)) = self.try_generate_optional_chaining(ctx) {
                // result_ty is Optional(field_type); check if field_type matches inner
                if let TypeInfo::Optional(ref chained_inner) = result_ty {
                    if types_compatible(chained_inner, inner) {
                        return expr;
                    }
                }
            }
        }

        // ~20% chance to reference an existing optional variable in scope
        if self.rng.gen_bool(0.20) {
            let opt_ty = TypeInfo::Optional(Box::new(inner.clone()));
            if let Some(var) = ctx.find_matching_var(&opt_ty) {
                return var;
            }
        }

        // 50% chance of nil, 50% chance of value
        if self.rng.gen_bool(0.5) {
            "nil".to_string()
        } else {
            self.generate(inner, ctx, depth)
        }
    }

    /// Generate an array expression.
    fn generate_array(&mut self, elem: &TypeInfo, ctx: &ExprContext, depth: usize) -> String {
        // ~15% chance to generate str.split(",").collect() for [string] arrays
        if *elem == TypeInfo::Primitive(PrimitiveType::String) && self.rng.gen_bool(0.15) {
            if let Some(expr) = self.try_generate_string_split(ctx) {
                return expr;
            }
        }

        // ~15% chance to generate str.chars().collect() for [i32] arrays
        // (.chars() returns character codepoints as i32)
        if *elem == TypeInfo::Primitive(PrimitiveType::I32) && self.rng.gen_bool(0.15) {
            if let Some(expr) = self.try_generate_string_chars_collect(ctx) {
                return expr;
            }
        }

        // ~15% chance to generate arr.iter().map((x) => expr).collect()
        if self.rng.gen_bool(0.15) {
            if let Some(expr) = self.try_generate_iter_map_collect(elem, ctx) {
                return expr;
            }
        }

        // ~10% chance to generate arr.iter().filter((x) => pred).collect()
        if self.rng.gen_bool(0.10) {
            if let Some(expr) = self.try_generate_iter_filter_collect(elem, ctx) {
                return expr;
            }
        }

        // ~8% chance to generate arr.iter().skip(N).take(M).collect()
        if self.rng.gen_bool(0.08) {
            if let Some(expr) = self.try_generate_iter_skip_take_collect(elem, ctx) {
                return expr;
            }
        }

        // Minimum 2 elements: array index generation uses 0..=1 hardcoded indices,
        // so arrays must always have at least 2 elements to prevent OOB panics.
        let len = self.rng.gen_range(2..=4);

        let elements: Vec<String> = (0..len)
            .map(|_| self.generate(elem, ctx, depth + 1))
            .collect();

        format!("[{}]", elements.join(", "))
    }

    /// Generate a fixed-size array expression using repeat literal syntax.
    ///
    /// Produces `[value; count]` where `value` is a simple expression of the
    /// element type. Uses simple expressions only (literals and variable refs)
    /// to keep the repeat literal on a single line.
    fn generate_fixed_array(
        &mut self,
        elem: &TypeInfo,
        size: usize,
        ctx: &ExprContext,
        _depth: usize,
    ) -> String {
        // Generate a simple value expression for the repeat literal
        let value = self.generate_simple(elem, ctx);
        format!("[{}; {}]", value, size)
    }

    /// Generate a tuple literal expression.
    ///
    /// Produces `[expr1, expr2, ...]` where each element matches its
    /// corresponding type in `elem_types`. Uses simple expressions only
    /// (literals and variable references) to keep the tuple on a single
    /// line and avoid parse issues with multi-line expressions inside
    /// square brackets.
    fn generate_tuple(
        &mut self,
        elem_types: &[TypeInfo],
        ctx: &ExprContext,
        _depth: usize,
    ) -> String {
        let elem_types = elem_types.to_vec();
        let elements: Vec<String> = elem_types
            .iter()
            .map(|ty| self.generate_simple(ty, ctx))
            .collect();

        format!("[{}]", elements.join(", "))
    }

    /// Generate an interpolated string expression.
    ///
    /// Produces strings like `"value is {param0}"` or `"sum: {a + 1_i64}"`.
    /// Falls back to a plain string literal if no variables are in scope.
    fn generate_interpolated_string(&mut self, ctx: &ExprContext) -> String {
        let vars = ctx.all_vars();
        if vars.is_empty() {
            let id = self.rng.gen_range(0..100);
            return format!("\"str{}\"", id);
        }

        let interp_count = self.rng.gen_range(1..=2.min(vars.len()));
        let mut parts = Vec::new();

        // Optional leading text
        if self.rng.gen_bool(0.6) {
            let prefixes = ["val: ", "result: ", "got ", "x=", ""];
            let idx = self.rng.gen_range(0..prefixes.len());
            let prefix = prefixes[idx];
            if !prefix.is_empty() {
                parts.push(prefix.to_string());
            }
        }

        for i in 0..interp_count {
            let var_idx = self.rng.gen_range(0..vars.len());
            let (name, ty) = vars[var_idx];

            let interp_expr = self.interp_expr_for_var(name, ty, ctx);
            parts.push(format!("{{{}}}", interp_expr));

            // Add separator text between interpolations
            if i + 1 < interp_count {
                let seps = [", ", " | ", " and ", " - "];
                let idx = self.rng.gen_range(0..seps.len());
                parts.push(seps[idx].to_string());
            }
        }

        // Optional trailing text
        if self.rng.gen_bool(0.4) {
            let suffixes = [" done", "!", " ok", ""];
            let idx = self.rng.gen_range(0..suffixes.len());
            let suffix = suffixes[idx];
            if !suffix.is_empty() {
                parts.push(suffix.to_string());
            }
        }

        format!("\"{}\"", parts.join(""))
    }

    /// Generate an interpolation expression for a variable.
    ///
    /// For numeric types, sometimes wraps in arithmetic (e.g. `param0 + 1_i64`,
    /// `param0 - 3_i32`, `param0 * 2_i64`).
    /// For boolean types, sometimes wraps in negation (e.g. `!flag`).
    /// For array and string types, sometimes generates `.length()` calls.
    /// For class/struct types, sometimes generates field access (e.g. `obj.name`).
    /// For other types, just references the variable directly.
    fn interp_expr_for_var(&mut self, name: &str, ty: &TypeInfo, ctx: &ExprContext) -> String {
        match ty {
            TypeInfo::Primitive(PrimitiveType::I32) if self.rng.gen_bool(0.3) => {
                let n = self.rng.gen_range(1..10);
                let op = match self.rng.gen_range(0..3) {
                    0 => "+",
                    1 => "-",
                    _ => "*",
                };
                format!("{} {} {}_i32", name, op, n)
            }
            TypeInfo::Primitive(PrimitiveType::I64) if self.rng.gen_bool(0.3) => {
                let n = self.rng.gen_range(1..10);
                let op = match self.rng.gen_range(0..3) {
                    0 => "+",
                    1 => "-",
                    _ => "*",
                };
                format!("{} {} {}_i64", name, op, n)
            }
            // ~25% chance to use arithmetic on f64 inside interpolation
            TypeInfo::Primitive(PrimitiveType::F64) if self.rng.gen_bool(0.25) => {
                let n = self.rng.gen_range(1..10);
                let op = match self.rng.gen_range(0..3) {
                    0 => "+",
                    1 => "-",
                    _ => "*",
                };
                format!("{} {} {}.0_f64", name, op, n)
            }
            // ~25% chance to use negation on booleans inside interpolation
            TypeInfo::Primitive(PrimitiveType::Bool) if self.rng.gen_bool(0.25) => {
                format!("!{}", name)
            }
            // ~30% chance to use .length() on arrays inside interpolation
            TypeInfo::Array(_) if self.rng.gen_bool(0.3) => {
                format!("{}.length()", name)
            }
            // ~30% chance to use a string method inside interpolation
            TypeInfo::Primitive(PrimitiveType::String) if self.rng.gen_bool(0.3) => {
                // Pick from .length(), .to_upper(), .to_lower(), .trim(), .substring()
                let base = match self.rng.gen_range(0..5) {
                    0 => format!("{}.length()", name),
                    1 => format!("{}.to_upper()", name),
                    2 => format!("{}.to_lower()", name),
                    3 => format!("{}.trim()", name),
                    _ => format!("{}.substring(0, 3)", name),
                };
                // ~25% chance to chain when the base returns string (not .length())
                if !base.ends_with(".length()")
                    && self.rng.gen_bool(self.config.method_chain_probability)
                {
                    let chain = self.random_simple_string_chain_suffix();
                    format!("{}{}", base, chain)
                } else {
                    base
                }
            }
            // ~30% chance to use field access on class-typed variables inside interpolation
            TypeInfo::Class(mod_id, sym_id) if self.rng.gen_bool(0.3) => {
                if let Some(field_name) = self.pick_printable_field(ctx, *mod_id, *sym_id) {
                    format!("{}.{}", name, field_name)
                } else {
                    name.to_string()
                }
            }
            // ~30% chance to use field access on struct-typed variables inside interpolation
            TypeInfo::Struct(mod_id, sym_id) if self.rng.gen_bool(0.3) => {
                if let Some(field_name) = self.pick_printable_field(ctx, *mod_id, *sym_id) {
                    format!("{}.{}", name, field_name)
                } else {
                    name.to_string()
                }
            }
            _ => name.to_string(),
        }
    }

    /// Pick a field from a class or struct that has a printable (interpolatable) type.
    ///
    /// Returns the field name if one exists with a type that can be stringified
    /// in interpolation (primitives, arrays, optionals of primitives).
    /// Returns `None` if no suitable field is found.
    fn pick_printable_field(
        &mut self,
        ctx: &ExprContext,
        mod_id: ModuleId,
        sym_id: SymbolId,
    ) -> Option<String> {
        let sym = ctx.table.get_symbol(mod_id, sym_id)?;
        let fields: &[FieldInfo] = match &sym.kind {
            SymbolKind::Class(info) => &info.fields,
            SymbolKind::Struct(info) => &info.fields,
            _ => return None,
        };
        // Collect fields whose types are safe for interpolation (primitive or array)
        let printable: Vec<&FieldInfo> = fields
            .iter()
            .filter(|f| is_printable_in_interpolation(&f.field_type))
            .collect();
        if printable.is_empty() {
            return None;
        }
        let idx = self.rng.gen_range(0..printable.len());
        Some(printable[idx].name.clone())
    }

    /// Generate a literal for a primitive type.
    /// Generate a non-zero numeric literal of the given type.
    ///
    /// Used as the RHS of modulo (`%`) and modulo-assign (`%=`) to avoid
    /// division-by-zero at runtime.  Falls back to `literal_for_primitive`
    /// for non-numeric types (where modulo wouldn't apply anyway).
    pub fn nonzero_literal_for_primitive(&mut self, prim: PrimitiveType) -> String {
        match prim {
            PrimitiveType::I8 => {
                let val: i8 = self.rng.gen_range(1..=127);
                format!("{}_i8", val)
            }
            PrimitiveType::I16 => {
                let val: i16 = self.rng.gen_range(1..=1000);
                format!("{}_i16", val)
            }
            PrimitiveType::I32 => {
                let val: i32 = self.rng.gen_range(1..=100);
                format!("{}_i32", val)
            }
            PrimitiveType::I64 => {
                let val: i64 = self.rng.gen_range(1..=1000);
                format!("{}_i64", val)
            }
            PrimitiveType::I128 => {
                let val: i64 = self.rng.gen_range(1..=10000);
                format!("{}_i128", val)
            }
            PrimitiveType::U8 => {
                let val: u8 = self.rng.gen_range(1..=255);
                format!("{}_u8", val)
            }
            PrimitiveType::U16 => {
                let val: u16 = self.rng.gen_range(1..=1000);
                format!("{}_u16", val)
            }
            PrimitiveType::U32 => {
                let val: u32 = self.rng.gen_range(1..=1000);
                format!("{}_u32", val)
            }
            PrimitiveType::U64 => {
                let val: u64 = self.rng.gen_range(1..=10000);
                format!("{}_u64", val)
            }
            PrimitiveType::F32 => {
                let val: f32 = self.rng.gen_range(1.0_f32..100.0_f32);
                format!("{:.2}_f32", val)
            }
            PrimitiveType::F64 => {
                let val: f64 = self.rng.gen_range(1.0..100.0);
                format!("{:.2}_f64", val)
            }
            _ => self.literal_for_primitive(prim),
        }
    }

    pub fn literal_for_primitive(&mut self, prim: PrimitiveType) -> String {
        match prim {
            PrimitiveType::I8 => {
                let val: i8 = self.rng.gen_range(-128..=127);
                format!("{}_i8", val)
            }
            PrimitiveType::I16 => {
                let val: i16 = self.rng.gen_range(-1000..=1000);
                format!("{}_i16", val)
            }
            PrimitiveType::I32 => {
                let val: i32 = self.rng.gen_range(0..100);
                format!("{}_i32", val)
            }
            PrimitiveType::I64 => {
                let val: i64 = self.rng.gen_range(0..1000);
                format!("{}_i64", val)
            }
            PrimitiveType::I128 => {
                let val: i64 = self.rng.gen_range(0..10000);
                format!("{}_i128", val)
            }
            PrimitiveType::U8 => {
                let val: u8 = self.rng.gen_range(0..=255);
                format!("{}_u8", val)
            }
            PrimitiveType::U16 => {
                let val: u16 = self.rng.gen_range(0..=1000);
                format!("{}_u16", val)
            }
            PrimitiveType::U32 => {
                let val: u32 = self.rng.gen_range(0..1000);
                format!("{}_u32", val)
            }
            PrimitiveType::U64 => {
                let val: u64 = self.rng.gen_range(0..10000);
                format!("{}_u64", val)
            }
            PrimitiveType::F32 => {
                let val: f32 = self.rng.gen_range(0.0_f32..100.0_f32);
                format!("{:.2}_f32", val)
            }
            PrimitiveType::F64 => {
                let val: f64 = self.rng.gen_range(0.0..100.0);
                format!("{:.2}_f64", val)
            }
            PrimitiveType::Bool => {
                if self.rng.gen_bool(0.5) {
                    "true".to_string()
                } else {
                    "false".to_string()
                }
            }
            PrimitiveType::String => {
                let id = self.rng.gen_range(0..100);
                format!("\"str{}\"", id)
            }
            PrimitiveType::Nil => "nil".to_string(),
        }
    }

    /// Generate a literal value for a primitive type that is safe for use as a
    /// module-level constant (i.e. will be parsed as a single literal token, not
    /// a unary negation expression). Only produces non-negative values.
    pub fn constant_literal_for_primitive(&mut self, prim: PrimitiveType) -> String {
        match prim {
            PrimitiveType::I8 => {
                let val: i8 = self.rng.gen_range(0..=127);
                format!("{}_i8", val)
            }
            PrimitiveType::I16 => {
                let val: i16 = self.rng.gen_range(0..=1000);
                format!("{}_i16", val)
            }
            PrimitiveType::I32 => {
                let val: i32 = self.rng.gen_range(0..100);
                format!("{}_i32", val)
            }
            PrimitiveType::I64 => {
                let val: i64 = self.rng.gen_range(0..1000);
                format!("{}_i64", val)
            }
            PrimitiveType::I128 => {
                let val: i64 = self.rng.gen_range(0..10000);
                format!("{}_i128", val)
            }
            // Unsigned types are already non-negative
            PrimitiveType::U8 => {
                let val: u8 = self.rng.gen_range(0..=255);
                format!("{}_u8", val)
            }
            PrimitiveType::U16 => {
                let val: u16 = self.rng.gen_range(0..=1000);
                format!("{}_u16", val)
            }
            PrimitiveType::U32 => {
                let val: u32 = self.rng.gen_range(0..1000);
                format!("{}_u32", val)
            }
            PrimitiveType::U64 => {
                let val: u64 = self.rng.gen_range(0..10000);
                format!("{}_u64", val)
            }
            PrimitiveType::F32 => {
                let val: f32 = self.rng.gen_range(0.0_f32..100.0_f32);
                format!("{:.2}_f32", val)
            }
            PrimitiveType::F64 => {
                let val: f64 = self.rng.gen_range(0.0..100.0);
                format!("{:.2}_f64", val)
            }
            PrimitiveType::Bool => {
                if self.rng.gen_bool(0.5) {
                    "true".to_string()
                } else {
                    "false".to_string()
                }
            }
            PrimitiveType::String => {
                let id = self.rng.gen_range(0..100);
                format!("\"str{}\"", id)
            }
            PrimitiveType::Nil => "nil".to_string(),
        }
    }

    /// Generate a match expression.
    ///
    /// Optionally uses `unreachable` in the wildcard arm when the subject is
    /// a known literal value and one of the preceding patterns matches it.
    pub fn generate_match_expr(
        &mut self,
        subject_type: &TypeInfo,
        result_type: &TypeInfo,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        // Decide if we want to use unreachable in the default arm
        let use_unreachable = self.rng.gen_bool(self.config.unreachable_probability);

        if use_unreachable {
            // Generate a match where the default arm is provably unreachable
            // by matching on a known literal and including a pattern for it
            return self.generate_match_with_unreachable(subject_type, result_type, ctx, depth);
        }

        // Normal match expression
        let subject = self.generate(subject_type, ctx, depth + 1);
        let max_arms = self.config.max_match_arms.max(2);
        let arm_count = self.rng.gen_range(2..=max_arms);
        let mut arms = Vec::new();

        // Generate some literal or guarded arms
        for _ in 0..arm_count - 1 {
            let pattern = self.generate_pattern(subject_type, Some(ctx), depth);
            let value = self.generate(result_type, ctx, depth + 1);
            arms.push(format!("{} => {}", pattern, value));
        }

        // Always end with wildcard for exhaustiveness.
        // Sometimes generate a guarded wildcard arm before the bare wildcard.
        if self.rng.gen_bool(self.config.match_guard_probability) {
            let guard_cond = self.generate_guard_condition(Some(ctx), depth);
            let guarded_value = self.generate(result_type, ctx, depth + 1);
            arms.push(format!("_ if {} => {}", guard_cond, guarded_value));
        }
        let default_value = self.generate(result_type, ctx, depth + 1);
        arms.push(format!("_ => {}", default_value));

        format!("match {} {{ {} }}", subject, arms.join(", "))
    }

    /// Generate a match expression where the default arm uses `unreachable`.
    ///
    /// Creates a pattern like:
    /// ```vole
    /// match 5 {
    ///     5 => "five",
    ///     _ => unreachable
    /// }
    /// ```
    fn generate_match_with_unreachable(
        &mut self,
        subject_type: &TypeInfo,
        result_type: &TypeInfo,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        // Generate a known literal subject for primitive types
        let (subject_literal, pattern) = match subject_type {
            TypeInfo::Primitive(prim) => {
                let lit = self.literal_for_primitive(*prim);
                (lit.clone(), lit)
            }
            _ => {
                // For non-primitive types, fall back to a normal match
                return self.generate_match_expr_normal(subject_type, result_type, ctx, depth);
            }
        };

        let max_arms = self.config.max_match_arms.max(2);
        let arm_count = self.rng.gen_range(2..=max_arms);
        let mut arms = Vec::new();

        // First arm matches the known subject value
        let first_value = self.generate(result_type, ctx, depth + 1);
        arms.push(format!("{} => {}", pattern, first_value));

        // Generate additional non-matching arms (won't execute but valid syntax)
        for _ in 1..arm_count - 1 {
            let other_pattern = self.generate_pattern(subject_type, Some(ctx), depth);
            let value = self.generate(result_type, ctx, depth + 1);
            arms.push(format!("{} => {}", other_pattern, value));
        }

        // Default arm with unreachable
        arms.push("_ => unreachable".to_string());

        format!("match {} {{ {} }}", subject_literal, arms.join(", "))
    }

    /// Generate a normal match expression (internal helper for fallback).
    fn generate_match_expr_normal(
        &mut self,
        subject_type: &TypeInfo,
        result_type: &TypeInfo,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        let subject = self.generate(subject_type, ctx, depth + 1);
        let max_arms = self.config.max_match_arms.max(2);
        let arm_count = self.rng.gen_range(2..=max_arms);
        let mut arms = Vec::new();

        for _ in 0..arm_count - 1 {
            let pattern = self.generate_pattern(subject_type, Some(ctx), depth);
            let value = self.generate(result_type, ctx, depth + 1);
            arms.push(format!("{} => {}", pattern, value));
        }

        // Sometimes generate a guarded wildcard arm before the bare wildcard.
        if self.rng.gen_bool(self.config.match_guard_probability) {
            let guard_cond = self.generate_guard_condition(Some(ctx), depth);
            let guarded_value = self.generate(result_type, ctx, depth + 1);
            arms.push(format!("_ if {} => {}", guard_cond, guarded_value));
        }
        let default_value = self.generate(result_type, ctx, depth + 1);
        arms.push(format!("_ => {}", default_value));

        format!("match {} {{ {} }}", subject, arms.join(", "))
    }

    /// Generate a match pattern.
    ///
    /// Accepts an optional `ExprContext` and `depth` to generate richer guard
    /// expressions that reference variables in scope (comparisons, compound
    /// booleans, `val` patterns). When `ctx` is `None`, falls back to simple
    /// literal guards.
    fn generate_pattern(
        &mut self,
        ty: &TypeInfo,
        ctx: Option<&ExprContext>,
        depth: usize,
    ) -> String {
        match ty {
            TypeInfo::Primitive(prim) => {
                // With context available, we can generate richer patterns
                let range = if ctx.is_some() { 5 } else { 3 };
                match self.rng.gen_range(0..range) {
                    0 => "_".to_string(), // Wildcard
                    1 => {
                        // Literal pattern
                        self.literal_for_primitive(*prim)
                    }
                    2 => {
                        // Guarded wildcard with expression
                        let cond = self.generate_guard_condition(ctx, depth);
                        format!("_ if {}", cond)
                    }
                    3 => {
                        // `val` pattern: compare against an existing variable
                        // in scope of the same type (exercises the val-pattern codepath)
                        if let Some(ctx) = ctx {
                            if let Some(var) = ctx.find_matching_var(&TypeInfo::Primitive(*prim)) {
                                return format!("val {}", var);
                            }
                        }
                        // Fallback to literal
                        self.literal_for_primitive(*prim)
                    }
                    _ => {
                        // `val` pattern with guard: `val x if cond => ...`
                        if let Some(ctx) = ctx {
                            if let Some(var) = ctx.find_matching_var(&TypeInfo::Primitive(*prim)) {
                                let cond = self.generate_guard_condition(Some(ctx), depth);
                                return format!("val {} if {}", var, cond);
                            }
                        }
                        // Fallback to guarded wildcard
                        let cond = self.generate_guard_condition(ctx, depth);
                        format!("_ if {}", cond)
                    }
                }
            }
            _ => "_".to_string(),
        }
    }

    /// Generate a guard condition for a match arm.
    ///
    /// When an `ExprContext` is available, produces comparison-based conditions
    /// referencing numeric variables in scope (e.g. `x > 42`, `x >= 10 && x < 100`).
    /// Falls back to boolean literals when no variables are available.
    pub fn generate_guard_condition(&mut self, ctx: Option<&ExprContext>, depth: usize) -> String {
        if let Some(ctx) = ctx {
            // Use integer-only vars for comparisons with integer literals
            let numeric = ctx.integer_vars();
            if !numeric.is_empty() {
                let var_idx = self.rng.gen_range(0..numeric.len());
                let var = &numeric[var_idx];

                match self.rng.gen_range(0..4) {
                    0 => {
                        // Simple comparison: x > literal
                        let op = match self.rng.gen_range(0..4) {
                            0 => ">",
                            1 => "<",
                            2 => ">=",
                            _ => "<=",
                        };
                        let lit = self.rng.gen_range(0..100);
                        return format!("{} {} {}", var, op, lit);
                    }
                    1 => {
                        // Equality check: x == literal
                        let lit = self.rng.gen_range(0..50);
                        return format!("{} == {}", var, lit);
                    }
                    2 => {
                        // Compound range check: x > low && x < high
                        let low = self.rng.gen_range(0..50);
                        let high = low + self.rng.gen_range(10..100);
                        return format!("{} > {} && {} < {}", var, low, var, high);
                    }
                    _ => {
                        // Inequality: x != literal
                        let lit = self.rng.gen_range(0..50);
                        return format!("{} != {}", var, lit);
                    }
                }
            }

            // Try boolean variables
            let bools = ctx.bool_vars();
            if !bools.is_empty() {
                let var_idx = self.rng.gen_range(0..bools.len());
                let var = &bools[var_idx];
                if self.rng.gen_bool(0.5) {
                    return var.clone();
                } else {
                    return format!("!{}", var);
                }
            }

            // Fall back to a full bool expression generation if we have depth budget
            if depth + 1 < 3 {
                return self.generate(&TypeInfo::Primitive(PrimitiveType::Bool), ctx, depth + 1);
            }
        }

        // Ultimate fallback: literal boolean
        self.literal_for_primitive(PrimitiveType::Bool)
    }

    /// Generate a lambda expression.
    ///
    /// When `closure_capture_probability` fires, primitive-typed variables
    /// from the enclosing scope are made visible inside the lambda body so
    /// the expression generator can reference them, producing closures that
    /// capture outer variables.
    pub fn generate_lambda(
        &mut self,
        param_types: &[TypeInfo],
        return_type: &TypeInfo,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        // Generate parameter names
        let params: Vec<String> = param_types
            .iter()
            .enumerate()
            .map(|(i, ty)| format!("p{}: {}", i, ty.to_vole_syntax(ctx.table)))
            .collect();

        // Create a new context with the lambda parameters
        let lambda_params: Vec<ParamInfo> = param_types
            .iter()
            .enumerate()
            .map(|(i, ty)| ParamInfo {
                name: format!("p{}", i),
                param_type: ty.clone(),
            })
            .collect();

        // Optionally capture outer scope variables so the closure body can
        // reference them.  Only primitive-typed variables are captured to
        // avoid complex type interactions.
        let captured_locals: Vec<(String, TypeInfo)> = if self.config.closure_capture_probability
            > 0.0
            && self.rng.gen_bool(self.config.closure_capture_probability)
        {
            let mut captures = Vec::new();
            for (name, ty) in ctx.locals {
                if is_capturable_type(ty) {
                    captures.push((name.clone(), ty.clone()));
                }
            }
            for param in ctx.params {
                if is_capturable_type(&param.param_type) {
                    captures.push((param.name.clone(), param.param_type.clone()));
                }
            }
            captures
        } else {
            Vec::new()
        };

        let lambda_ctx = ExprContext::new(&lambda_params, &captured_locals, ctx.table);

        // Generate the body expression
        let body = self.generate(return_type, &lambda_ctx, depth + 1);

        let return_annotation = match return_type {
            TypeInfo::Void => String::new(),
            _ => format!(" -> {}", return_type.to_vole_syntax(ctx.table)),
        };

        format!("({}){} => {}", params.join(", "), return_annotation, body)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbols::{ClassInfo, FieldInfo};
    use rand::SeedableRng;

    #[test]
    fn test_literal_generation() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = ExprConfig::default();
        let mut generator = ExprGenerator::new(&mut rng, &config);

        let i64_lit = generator.literal_for_primitive(PrimitiveType::I64);
        assert!(!i64_lit.is_empty());

        let bool_lit = generator.literal_for_primitive(PrimitiveType::Bool);
        assert!(bool_lit == "true" || bool_lit == "false");

        let str_lit = generator.literal_for_primitive(PrimitiveType::String);
        assert!(str_lit.starts_with('"'));
    }

    #[test]
    fn test_expr_generation() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = ExprConfig::default();
        let mut generator = ExprGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let ctx = ExprContext::new(&[], &[], &table);

        let i64_expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
        assert!(!i64_expr.is_empty());

        let bool_expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &ctx, 0);
        assert!(!bool_expr.is_empty());
    }

    #[test]
    fn test_when_expr_generation() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = ExprConfig::default();
        let mut generator = ExprGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let ctx = ExprContext::new(&[], &[], &table);

        let when_expr =
            generator.generate_when_expr(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
        assert!(when_expr.contains("when"));
        assert!(when_expr.contains("=>"));
    }

    #[test]
    fn test_interpolated_string_generation() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(99);
        let config = ExprConfig::default();
        let mut generator = ExprGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let params = vec![
            ParamInfo {
                name: "count".to_string(),
                param_type: TypeInfo::Primitive(PrimitiveType::I64),
            },
            ParamInfo {
                name: "label".to_string(),
                param_type: TypeInfo::Primitive(PrimitiveType::String),
            },
        ];
        let ctx = ExprContext::new(&params, &[], &table);

        let interp = generator.generate_interpolated_string(&ctx);
        assert!(interp.starts_with('"'));
        assert!(interp.ends_with('"'));
        // Should contain at least one interpolation brace
        assert!(interp.contains('{'));
        assert!(interp.contains('}'));
    }

    #[test]
    fn test_interpolated_string_no_vars_fallback() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = ExprConfig::default();
        let mut generator = ExprGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let ctx = ExprContext::new(&[], &[], &table);

        // With no variables in scope, should fall back to plain string
        let result = generator.generate_interpolated_string(&ctx);
        assert!(result.starts_with('"'));
        assert!(result.ends_with('"'));
        // Should NOT contain interpolation braces (it's a plain "strN" literal)
        assert!(!result.contains('{'));
    }

    #[test]
    fn test_interpolated_string_length_calls() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();

        // Set up an array and a string variable in scope
        let locals = vec![
            (
                "items".to_string(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            ),
            (
                "text".to_string(),
                TypeInfo::Primitive(PrimitiveType::String),
            ),
        ];

        let mut found_array_length = false;
        let mut found_string_length = false;

        // Run across many seeds to exercise the 30% probability branches
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            let result = generator.generate_interpolated_string(&ctx);

            if result.contains("items.length()") {
                found_array_length = true;
            }
            if result.contains("text.length()") {
                found_string_length = true;
            }
            if found_array_length && found_string_length {
                break;
            }
        }

        assert!(
            found_array_length,
            "Expected at least one array .length() call in interpolation across 500 seeds"
        );
        assert!(
            found_string_length,
            "Expected at least one string .length() call in interpolation across 500 seeds"
        );
    }

    #[test]
    fn test_interpolated_string_arithmetic_ops() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();

        let locals = vec![
            ("count".to_string(), TypeInfo::Primitive(PrimitiveType::I64)),
            ("flag".to_string(), TypeInfo::Primitive(PrimitiveType::Bool)),
            ("rate".to_string(), TypeInfo::Primitive(PrimitiveType::F64)),
        ];

        let mut found_sub = false;
        let mut found_mul = false;
        let mut found_bool_neg = false;
        let mut found_f64_arith = false;

        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            let result = generator.generate_interpolated_string(&ctx);

            if result.contains("count -") || result.contains("count *") {
                if result.contains("count -") {
                    found_sub = true;
                }
                if result.contains("count *") {
                    found_mul = true;
                }
            }
            if result.contains("!flag") {
                found_bool_neg = true;
            }
            if result.contains("rate +") || result.contains("rate -") || result.contains("rate *") {
                found_f64_arith = true;
            }
            if found_sub && found_mul && found_bool_neg && found_f64_arith {
                break;
            }
        }

        assert!(
            found_sub,
            "Expected at least one subtraction in interpolation across 500 seeds"
        );
        assert!(
            found_mul,
            "Expected at least one multiplication in interpolation across 500 seeds"
        );
        assert!(
            found_bool_neg,
            "Expected at least one boolean negation in interpolation across 500 seeds"
        );
        assert!(
            found_f64_arith,
            "Expected at least one f64 arithmetic in interpolation across 500 seeds"
        );
    }

    #[test]
    fn test_interpolated_string_class_field_access() {
        use crate::symbols::StructInfo;

        let config = ExprConfig::default();
        let mut table = SymbolTable::new();

        // Create a module with a class and a struct that have printable fields
        let mod_id = table.add_module("test_mod".to_string(), "test_mod.vole".to_string());
        let module = table.get_module_mut(mod_id).unwrap();

        let class_id = module.add_symbol(
            "MyClass".to_string(),
            SymbolKind::Class(ClassInfo {
                type_params: vec![],
                fields: vec![
                    FieldInfo {
                        name: "name".to_string(),
                        field_type: TypeInfo::Primitive(PrimitiveType::String),
                    },
                    FieldInfo {
                        name: "count".to_string(),
                        field_type: TypeInfo::Primitive(PrimitiveType::I64),
                    },
                ],
                methods: vec![],
                implements: vec![],
                static_methods: vec![],
            }),
        );

        let struct_id = module.add_symbol(
            "MyStruct".to_string(),
            SymbolKind::Struct(StructInfo {
                fields: vec![
                    FieldInfo {
                        name: "label".to_string(),
                        field_type: TypeInfo::Primitive(PrimitiveType::String),
                    },
                    FieldInfo {
                        name: "value".to_string(),
                        field_type: TypeInfo::Primitive(PrimitiveType::I32),
                    },
                ],
                static_methods: vec![],
            }),
        );

        // Locals: one class instance and one struct instance
        let locals = vec![
            ("obj".to_string(), TypeInfo::Class(mod_id, class_id)),
            ("rec".to_string(), TypeInfo::Struct(mod_id, struct_id)),
        ];

        let mut found_class_field = false;
        let mut found_struct_field = false;

        // Run across many seeds to exercise the 30% probability branch
        for seed in 0..2000 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            let result = generator.generate_interpolated_string(&ctx);

            if result.contains("obj.name") || result.contains("obj.count") {
                found_class_field = true;
            }
            if result.contains("rec.label") || result.contains("rec.value") {
                found_struct_field = true;
            }
            if found_class_field && found_struct_field {
                break;
            }
        }

        assert!(
            found_class_field,
            "Expected at least one class field access in interpolation across 2000 seeds"
        );
        assert!(
            found_struct_field,
            "Expected at least one struct field access in interpolation across 2000 seeds"
        );
    }

    #[test]
    fn test_method_call_interpolation() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();

        // Set up a string and an array variable in scope
        let locals = vec![
            (
                "msg".to_string(),
                TypeInfo::Primitive(PrimitiveType::String),
            ),
            (
                "nums".to_string(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            ),
        ];

        let mut found_string_method = false;
        let mut found_array_length = false;

        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);

            if let Some(result) = generator.try_generate_method_call_interpolation(&ctx) {
                assert!(result.starts_with('"'), "Should be a string: {}", result);
                assert!(result.ends_with('"'), "Should be a string: {}", result);
                assert!(
                    result.contains('{'),
                    "Should have interpolation: {}",
                    result
                );

                if result.contains("msg.to_upper()")
                    || result.contains("msg.to_lower()")
                    || result.contains("msg.trim()")
                    || result.contains("msg.length()")
                {
                    found_string_method = true;
                }
                if result.contains("nums.length()") {
                    found_array_length = true;
                }
            }
            if found_string_method && found_array_length {
                break;
            }
        }

        assert!(
            found_string_method,
            "Expected at least one string method call interpolation across 500 seeds"
        );
        assert!(
            found_array_length,
            "Expected at least one array .length() interpolation across 500 seeds"
        );
    }

    #[test]
    fn test_method_call_interpolation_no_candidates() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();

        // Only numeric variables - no strings or arrays
        let locals = vec![
            ("x".to_string(), TypeInfo::Primitive(PrimitiveType::I64)),
            ("y".to_string(), TypeInfo::Primitive(PrimitiveType::Bool)),
        ];

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);

        assert!(
            generator
                .try_generate_method_call_interpolation(&ctx)
                .is_none()
        );
    }

    #[test]
    fn test_bitwise_generation() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let ctx = ExprContext::new(&[], &[], &table);

        let bitwise_ops = ["&", "|", "^", "<<", ">>"];
        let mut found = std::collections::HashSet::new();

        // Generate many expressions across different seeds to find bitwise ops
        for seed in 0..200 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
            for op in &bitwise_ops {
                if expr.contains(op) {
                    found.insert(*op);
                }
            }
        }

        // We should find at least some bitwise ops across 200 seeds
        assert!(
            found.len() >= 3,
            "Expected at least 3 bitwise ops, found: {:?}",
            found,
        );
    }

    #[test]
    fn test_bitwise_shift_rhs_is_small_literal() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let ctx = ExprContext::new(&[], &[], &table);

        // Generate many bitwise expressions directly and check shift RHS
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let expr = generator.generate_binary_bitwise(PrimitiveType::I64, &ctx, 2);

            // If it's a shift expression, the RHS should be a small literal
            if expr.contains("<<") || expr.contains(">>") {
                // The expression is like "(LHS << N_i64)" or "(LHS >> N_i64)"
                let shift_op = if expr.contains("<<") { "<<" } else { ">>" };
                if let Some(rhs_start) = expr.rfind(shift_op) {
                    let rhs = &expr[rhs_start + shift_op.len()..].trim();
                    // RHS should end with "_i64)" and the number should be 0-31
                    let rhs = rhs.trim_end_matches(')').trim();
                    let num_str = rhs.trim_end_matches("_i64").trim_end_matches("_i32");
                    let num: i64 = num_str.parse().expect(&format!(
                        "Failed to parse shift RHS '{}' from expr '{}'",
                        num_str, expr
                    ));
                    assert!(
                        num >= 0 && num <= 31,
                        "Shift amount {} out of range in expr: {}",
                        num,
                        expr,
                    );
                }
            }
        }
    }

    #[test]
    fn test_bitwise_not_generation() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let ctx = ExprContext::new(&[], &[], &table);

        // Check that bitwise NOT appears in i64 expressions
        let mut found_i64 = false;
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
            if expr.contains('~') {
                found_i64 = true;
                break;
            }
        }
        assert!(
            found_i64,
            "Expected at least one bitwise NOT (~) expression for i64 across 500 seeds",
        );

        // Check that bitwise NOT appears in wider integer types (e.g. u8)
        let mut found_u8 = false;
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::U8), &ctx, 0);
            if expr.contains('~') {
                found_u8 = true;
                break;
            }
        }
        assert!(
            found_u8,
            "Expected at least one bitwise NOT (~) expression for u8 across 500 seeds",
        );
    }

    #[test]
    fn test_determinism() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let ctx = ExprContext::new(&[], &[], &table);

        let mut rng1 = rand::rngs::StdRng::seed_from_u64(12345);
        let mut gen1 = ExprGenerator::new(&mut rng1, &config);
        let expr1 = gen1.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);

        let mut rng2 = rand::rngs::StdRng::seed_from_u64(12345);
        let mut gen2 = ExprGenerator::new(&mut rng2, &config);
        let expr2 = gen2.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);

        assert_eq!(expr1, expr2);
    }

    #[test]
    fn test_is_expr_with_union_param() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let params = vec![ParamInfo {
            name: "val".to_string(),
            param_type: TypeInfo::Union(vec![
                TypeInfo::Primitive(PrimitiveType::I32),
                TypeInfo::Primitive(PrimitiveType::String),
            ]),
        }];

        let mut found_is = false;
        for seed in 0..100 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&params, &[], &table);
            if let Some(expr) = generator.generate_is_expr(&ctx) {
                assert!(
                    expr.contains("val is "),
                    "Expected 'val is ...', got: {}",
                    expr
                );
                assert!(
                    expr == "(val is i32)" || expr == "(val is string)",
                    "Unexpected is expr: {}",
                    expr,
                );
                found_is = true;
            }
        }
        assert!(found_is, "Expected to generate at least one is expression");
    }

    #[test]
    fn test_is_expr_no_union_vars() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = ExprConfig::default();
        let mut generator = ExprGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let ctx = ExprContext::new(&[], &[], &table);

        // With no union-typed vars, should return None
        assert!(generator.generate_is_expr(&ctx).is_none());
    }

    #[test]
    fn test_is_expr_in_bool_generation() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let params = vec![ParamInfo {
            name: "x".to_string(),
            param_type: TypeInfo::Union(vec![
                TypeInfo::Primitive(PrimitiveType::I64),
                TypeInfo::Primitive(PrimitiveType::Bool),
            ]),
        }];

        let mut found_is = false;
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&params, &[], &table);
            let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &ctx, 0);
            if expr.contains(" is ") {
                found_is = true;
                break;
            }
        }
        assert!(
            found_is,
            "Expected at least one 'is' expression in bool generation across 500 seeds",
        );
    }

    #[test]
    fn test_union_type_expr_generation() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();

        let union_ty = TypeInfo::Union(vec![
            TypeInfo::Primitive(PrimitiveType::I32),
            TypeInfo::Primitive(PrimitiveType::String),
        ]);

        // Should generate valid expressions for union types
        for seed in 0..50 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &[], &table);
            let expr = generator.generate(&union_ty, &ctx, 0);
            assert!(
                !expr.is_empty(),
                "Union type expression should not be empty"
            );
        }
    }

    #[test]
    fn test_null_coalesce_with_optional_var() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let locals = vec![(
            "opt_val".to_string(),
            TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        )];

        let mut found_coalesce = false;
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
            if expr.contains("??") {
                assert!(
                    expr.contains("opt_val"),
                    "Null coalesce should reference the optional variable, got: {}",
                    expr,
                );
                found_coalesce = true;
                break;
            }
        }
        assert!(
            found_coalesce,
            "Expected at least one null coalescing expression across 500 seeds",
        );
    }

    #[test]
    fn test_null_coalesce_no_optional_vars() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let locals = vec![(
            "plain_val".to_string(),
            TypeInfo::Primitive(PrimitiveType::I64),
        )];

        // With no optional-typed vars, ?? should never appear
        for seed in 0..200 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
            assert!(
                !expr.contains("??"),
                "Should not generate ?? without optional vars, got: {}",
                expr,
            );
        }
    }

    #[test]
    fn test_null_coalesce_type_mismatch_not_generated() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        // Optional<String> should NOT produce ?? when generating i64
        let locals = vec![(
            "opt_str".to_string(),
            TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
        )];

        for seed in 0..200 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
            assert!(
                !expr.contains("??"),
                "Should not generate ?? with mismatched inner type, got: {}",
                expr,
            );
        }
    }

    #[test]
    fn test_null_coalesce_chained_with_multiple_optionals() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        // Multiple optional<i64> variables to enable chained coalescing
        let locals = vec![
            (
                "opt_a".to_string(),
                TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            ),
            (
                "opt_b".to_string(),
                TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            ),
            (
                "opt_c".to_string(),
                TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            ),
        ];

        let mut found_chained = false;
        for seed in 0..2000 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            if let Some(expr) = generator.try_generate_null_coalesce(
                &TypeInfo::Primitive(PrimitiveType::I64),
                &ctx,
                0,
            ) {
                // Count the number of ?? operators in the expression
                let coalesce_count = expr.matches("??").count();
                if coalesce_count >= 2 {
                    // Chained: e.g. (opt_a ?? opt_b ?? 42_i64)
                    found_chained = true;
                    break;
                }
            }
        }
        assert!(
            found_chained,
            "Expected at least one chained null coalescing expression (2+ ??) across 2000 seeds",
        );
    }

    #[test]
    fn test_null_coalesce_single_optional_never_chains() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        // Only one optional variable - the top-level pattern should be
        // `(only_opt ?? <default>)` with exactly one leading `??` from
        // our coalesce.  (The default sub-expression may itself contain
        // `??` from recursive generation, so we only check the prefix.)
        let locals = vec![(
            "only_opt".to_string(),
            TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        )];

        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            if let Some(expr) = generator.try_generate_null_coalesce(
                &TypeInfo::Primitive(PrimitiveType::I64),
                &ctx,
                0,
            ) {
                // The expression should start with `(only_opt ?? ` --
                // i.e. only one optional var before the default.
                assert!(
                    expr.starts_with("(only_opt ?? "),
                    "With one optional var, chain should start with '(only_opt ?? ', got: {}",
                    expr,
                );
                // Ensure there's no second optional chained before the default
                // (strip the first `(only_opt ?? ` prefix, the remainder should
                // not start with another `only_opt ??`)
                let rest = &expr["(only_opt ?? ".len()..];
                assert!(
                    !rest.starts_with("only_opt ?? "),
                    "Should not chain the same optional var twice at top level, got: {}",
                    expr,
                );
            }
        }
    }

    #[test]
    fn test_optional_chaining_with_class_optional() {
        let config = ExprConfig::default();
        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test_mod".to_string(), "test_mod.vole".to_string());

        // Create a class with an i64 field
        let sym_id = table.get_module_mut(mod_id).unwrap().add_symbol(
            "Point".to_string(),
            SymbolKind::Class(ClassInfo {
                type_params: vec![],
                fields: vec![FieldInfo {
                    name: "x".to_string(),
                    field_type: TypeInfo::Primitive(PrimitiveType::I64),
                }],
                methods: vec![],
                implements: vec![],
                static_methods: vec![],
            }),
        );

        // Local variable of type Point?
        let locals = vec![(
            "opt_point".to_string(),
            TypeInfo::Optional(Box::new(TypeInfo::Class(mod_id, sym_id))),
        )];

        let mut found_chaining = false;
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            // Generate Optional<i64> - the result of ?.x on Point?
            let expr = generator.generate(
                &TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                &ctx,
                0,
            );
            if expr.contains("?.") {
                assert!(
                    expr.contains("opt_point?.x"),
                    "Optional chaining should reference opt_point?.x, got: {}",
                    expr,
                );
                found_chaining = true;
                break;
            }
        }
        assert!(
            found_chaining,
            "Expected at least one optional chaining expression across 500 seeds",
        );
    }

    #[test]
    fn test_optional_chaining_no_class_optionals() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        // Only a plain optional, no class-typed optional
        let locals = vec![(
            "opt_num".to_string(),
            TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        )];

        for seed in 0..200 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            let expr = generator.generate(
                &TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                &ctx,
                0,
            );
            assert!(
                !expr.contains("?."),
                "Should not generate ?. without class-typed optional, got: {}",
                expr,
            );
        }
    }

    #[test]
    fn test_null_coalesce_direct() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let locals = vec![(
            "maybe".to_string(),
            TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::Bool))),
        )];

        let mut found = false;
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            if let Some(expr) = generator.try_generate_null_coalesce(
                &TypeInfo::Primitive(PrimitiveType::Bool),
                &ctx,
                0,
            ) {
                assert!(
                    expr.contains("maybe"),
                    "Should reference 'maybe', got: {}",
                    expr
                );
                assert!(expr.contains("??"), "Should contain '??', got: {}", expr);
                found = true;
                break;
            }
        }
        assert!(
            found,
            "Expected try_generate_null_coalesce to succeed at least once"
        );
    }

    #[test]
    fn test_optional_chaining_direct() {
        let config = ExprConfig::default();
        let mut table = SymbolTable::new();
        let mod_id = table.add_module("m".to_string(), "m.vole".to_string());
        let sym_id = table.get_module_mut(mod_id).unwrap().add_symbol(
            "Rec".to_string(),
            SymbolKind::Class(ClassInfo {
                type_params: vec![],
                fields: vec![
                    FieldInfo {
                        name: "val".to_string(),
                        field_type: TypeInfo::Primitive(PrimitiveType::I32),
                    },
                    FieldInfo {
                        name: "name".to_string(),
                        field_type: TypeInfo::Primitive(PrimitiveType::String),
                    },
                ],
                methods: vec![],
                implements: vec![],
                static_methods: vec![],
            }),
        );

        let locals = vec![(
            "opt_rec".to_string(),
            TypeInfo::Optional(Box::new(TypeInfo::Class(mod_id, sym_id))),
        )];

        let mut found = false;
        for seed in 0..100 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            if let Some((expr, result_ty)) = generator.try_generate_optional_chaining(&ctx) {
                assert!(
                    expr.starts_with("opt_rec?."),
                    "Should start with 'opt_rec?.', got: {}",
                    expr,
                );
                assert!(
                    expr == "opt_rec?.val" || expr == "opt_rec?.name",
                    "Should reference a field, got: {}",
                    expr,
                );
                // Result type should be Optional
                assert!(
                    matches!(result_ty, TypeInfo::Optional(_)),
                    "Result type should be Optional, got: {:?}",
                    result_ty,
                );
                found = true;
                break;
            }
        }
        assert!(
            found,
            "Expected try_generate_optional_chaining to succeed at least once"
        );
    }

    #[test]
    fn test_array_index_with_matching_array_var() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let locals = vec![(
            "nums".to_string(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        )];

        let mut found_index = false;
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
            if expr.contains("nums[") {
                // Index should be 0 or 1 with _i64 suffix
                assert!(
                    expr.contains("nums[0_i64]") || expr.contains("nums[1_i64]"),
                    "Array index should use small constant index (0 or 1), got: {}",
                    expr,
                );
                found_index = true;
                break;
            }
        }
        assert!(
            found_index,
            "Expected at least one array index expression across 500 seeds",
        );
    }

    #[test]
    fn test_array_index_no_matching_array_vars() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        // Array of strings should NOT produce array index when generating i64
        let locals = vec![(
            "strs".to_string(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
        )];

        for seed in 0..200 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
            assert!(
                !expr.contains("strs["),
                "Should not generate array index with mismatched element type, got: {}",
                expr,
            );
        }
    }

    #[test]
    fn test_array_index_direct() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let locals = vec![(
            "arr".to_string(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I32))),
        )];

        let mut found = false;
        for seed in 0..100 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            if let Some(expr) = generator.try_generate_array_index(PrimitiveType::I32, &ctx) {
                assert!(
                    expr.starts_with("arr["),
                    "Should start with 'arr[', got: {}",
                    expr,
                );
                // Verify index is a small constant with proper suffix
                assert!(
                    expr.contains("_i32]"),
                    "Index should have _i32 suffix, got: {}",
                    expr,
                );
                found = true;
                break;
            }
        }
        assert!(
            found,
            "Expected try_generate_array_index to succeed at least once"
        );
    }

    #[test]
    fn test_array_index_no_arrays_in_scope() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = ExprConfig::default();
        let mut generator = ExprGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let ctx = ExprContext::new(&[], &[], &table);

        // With no array-typed vars, should return None
        assert!(
            generator
                .try_generate_array_index(PrimitiveType::I64, &ctx)
                .is_none()
        );
    }

    #[test]
    fn test_array_vars_helper() {
        let table = SymbolTable::new();
        let locals = vec![
            (
                "nums".to_string(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            ),
            ("plain".to_string(), TypeInfo::Primitive(PrimitiveType::I64)),
            (
                "strs".to_string(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
            ),
        ];

        let params = vec![ParamInfo {
            name: "param_arr".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::Bool))),
        }];

        let ctx = ExprContext::new(&params, &locals, &table);
        let arr_vars = ctx.array_vars();

        assert_eq!(arr_vars.len(), 3);
        assert_eq!(arr_vars[0].0, "nums");
        assert_eq!(arr_vars[0].1, TypeInfo::Primitive(PrimitiveType::I64));
        assert_eq!(arr_vars[1].0, "strs");
        assert_eq!(arr_vars[1].1, TypeInfo::Primitive(PrimitiveType::String));
        assert_eq!(arr_vars[2].0, "param_arr");
        assert_eq!(arr_vars[2].1, TypeInfo::Primitive(PrimitiveType::Bool));
    }

    #[test]
    fn test_string_vars_helper() {
        let table = SymbolTable::new();
        let locals = vec![
            (
                "name".to_string(),
                TypeInfo::Primitive(PrimitiveType::String),
            ),
            ("count".to_string(), TypeInfo::Primitive(PrimitiveType::I64)),
            (
                "label".to_string(),
                TypeInfo::Primitive(PrimitiveType::String),
            ),
        ];

        let params = vec![ParamInfo {
            name: "msg".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::String),
        }];

        let ctx = ExprContext::new(&params, &locals, &table);
        let str_vars = ctx.string_vars();

        assert_eq!(str_vars.len(), 3);
        assert_eq!(str_vars[0], "name");
        assert_eq!(str_vars[1], "label");
        assert_eq!(str_vars[2], "msg");
    }

    #[test]
    fn test_string_length_direct() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let locals = vec![("s".to_string(), TypeInfo::Primitive(PrimitiveType::String))];

        let mut found = false;
        for seed in 0..100 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            if let Some(expr) = generator.try_generate_string_length(&ctx) {
                assert_eq!(expr, "s.length()");
                found = true;
                break;
            }
        }
        assert!(
            found,
            "Expected try_generate_string_length to succeed at least once"
        );
    }

    #[test]
    fn test_string_length_no_strings() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = ExprConfig::default();
        let mut generator = ExprGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let ctx = ExprContext::new(&[], &[], &table);

        assert!(generator.try_generate_string_length(&ctx).is_none());
    }

    #[test]
    fn test_string_length_in_i64_generation() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let locals = vec![(
            "text".to_string(),
            TypeInfo::Primitive(PrimitiveType::String),
        )];

        let mut found = false;
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
            if expr.contains(".length()") {
                // The .length() call should ultimately be on the "text" variable,
                // possibly via a chained method (e.g. text.to_upper().length()).
                assert!(
                    expr.contains("text"),
                    "Expected .length() to reference 'text', got: {}",
                    expr,
                );
                found = true;
                break;
            }
        }
        assert!(
            found,
            "Expected at least one .length() call in i64 generation across 500 seeds",
        );
    }

    #[test]
    fn test_string_bool_method_direct() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let locals = vec![("s".to_string(), TypeInfo::Primitive(PrimitiveType::String))];

        let valid_methods = ["contains", "starts_with", "ends_with"];
        let mut found = false;
        for seed in 0..100 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            if let Some(expr) = generator.try_generate_string_bool_method(&ctx) {
                let has_valid_method = valid_methods
                    .iter()
                    .any(|m| expr.starts_with(&format!("s.{}(\"", m)));
                assert!(
                    has_valid_method,
                    "Expected 's.<method>(\"...\")' where method is contains/starts_with/ends_with, got: {}",
                    expr,
                );
                assert!(
                    expr.ends_with("\")"),
                    "Expected closing quote-paren, got: {}",
                    expr,
                );
                found = true;
                break;
            }
        }
        assert!(
            found,
            "Expected try_generate_string_bool_method to succeed at least once"
        );
    }

    #[test]
    fn test_string_bool_method_no_strings() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = ExprConfig::default();
        let mut generator = ExprGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let ctx = ExprContext::new(&[], &[], &table);

        assert!(generator.try_generate_string_bool_method(&ctx).is_none());
    }

    #[test]
    fn test_string_bool_method_in_bool_generation() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let locals = vec![(
            "msg".to_string(),
            TypeInfo::Primitive(PrimitiveType::String),
        )];

        let valid_methods = [".contains(", ".starts_with(", ".ends_with("];
        let mut found = false;
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &ctx, 0);
            if valid_methods.iter().any(|m| expr.contains(m)) {
                let has_msg_prefix = valid_methods
                    .iter()
                    .any(|m| expr.contains(&format!("msg{}", m)));
                assert!(
                    has_msg_prefix,
                    "Expected 'msg.<method>(...)', got: {}",
                    expr,
                );
                found = true;
                break;
            }
        }
        assert!(
            found,
            "Expected at least one string bool method call in bool generation across 500 seeds",
        );
    }

    #[test]
    fn test_string_bool_method_variety() {
        // Ensure all three methods (contains, starts_with, ends_with) can be generated
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let locals = vec![("s".to_string(), TypeInfo::Primitive(PrimitiveType::String))];

        let mut seen_contains = false;
        let mut seen_starts_with = false;
        let mut seen_ends_with = false;
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            if let Some(expr) = generator.try_generate_string_bool_method(&ctx) {
                if expr.contains(".contains(") {
                    seen_contains = true;
                }
                if expr.contains(".starts_with(") {
                    seen_starts_with = true;
                }
                if expr.contains(".ends_with(") {
                    seen_ends_with = true;
                }
            }
            if seen_contains && seen_starts_with && seen_ends_with {
                break;
            }
        }
        assert!(
            seen_contains,
            "Expected .contains() to appear across 500 seeds"
        );
        assert!(
            seen_starts_with,
            "Expected .starts_with() to appear across 500 seeds"
        );
        assert!(
            seen_ends_with,
            "Expected .ends_with() to appear across 500 seeds"
        );
    }

    #[test]
    fn test_string_transform_method_direct() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let locals = vec![("s".to_string(), TypeInfo::Primitive(PrimitiveType::String))];

        let valid_methods = [
            ".to_upper()",
            ".to_lower()",
            ".trim()",
            ".replace(",
            ".replace_all(",
            ".substring(",
        ];
        let mut found = false;
        for seed in 0..100 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            if let Some(expr) = generator.try_generate_string_transform_method(&ctx) {
                let has_valid_method = valid_methods.iter().any(|m| expr.contains(m));
                assert!(
                    has_valid_method,
                    "Expected string transform method, got: {}",
                    expr,
                );
                assert!(
                    expr.starts_with("s."),
                    "Expected expression to start with 's.', got: {}",
                    expr,
                );
                found = true;
                break;
            }
        }
        assert!(
            found,
            "Expected try_generate_string_transform_method to succeed at least once"
        );
    }

    #[test]
    fn test_string_transform_method_no_strings() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = ExprConfig::default();
        let mut generator = ExprGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let ctx = ExprContext::new(&[], &[], &table);

        assert!(
            generator
                .try_generate_string_transform_method(&ctx)
                .is_none()
        );
    }

    #[test]
    fn test_string_transform_method_variety() {
        // Ensure all three methods (to_upper, to_lower, trim) can be generated
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let locals = vec![("s".to_string(), TypeInfo::Primitive(PrimitiveType::String))];

        let mut seen_to_upper = false;
        let mut seen_to_lower = false;
        let mut seen_trim = false;
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            if let Some(expr) = generator.try_generate_string_transform_method(&ctx) {
                if expr.contains(".to_upper()") {
                    seen_to_upper = true;
                }
                if expr.contains(".to_lower()") {
                    seen_to_lower = true;
                }
                if expr.contains(".trim()") {
                    seen_trim = true;
                }
            }
            if seen_to_upper && seen_to_lower && seen_trim {
                break;
            }
        }
        assert!(
            seen_to_upper,
            "Expected .to_upper() to appear across 500 seeds"
        );
        assert!(
            seen_to_lower,
            "Expected .to_lower() to appear across 500 seeds"
        );
        assert!(seen_trim, "Expected .trim() to appear across 500 seeds");
    }

    #[test]
    fn test_negated_compound_bool_generation() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let params = vec![
            ParamInfo {
                name: "a".to_string(),
                param_type: TypeInfo::Primitive(PrimitiveType::I64),
            },
            ParamInfo {
                name: "b".to_string(),
                param_type: TypeInfo::Primitive(PrimitiveType::Bool),
            },
        ];

        let mut found_negated_comparison = false;
        let mut found_negated_binary_bool = false;
        for seed in 0..1000 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&params, &[], &table);
            let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &ctx, 0);

            // Negated compound: starts with "(!" and contains comparison or boolean operators
            if expr.starts_with("(!(") {
                if expr.contains("&&") || expr.contains("||") {
                    found_negated_binary_bool = true;
                }
                if expr.contains("==")
                    || expr.contains("!=")
                    || expr.contains(">=")
                    || expr.contains("<=")
                    || expr.contains("> ")
                    || expr.contains("< ")
                {
                    found_negated_comparison = true;
                }
            }
            if found_negated_comparison && found_negated_binary_bool {
                break;
            }
        }
        assert!(
            found_negated_comparison,
            "Expected at least one negated comparison (e.g. !(a > b)) across 1000 seeds"
        );
        assert!(
            found_negated_binary_bool,
            "Expected at least one negated binary bool (e.g. !(a && b)) across 1000 seeds"
        );
    }

    #[test]
    fn test_string_split_direct() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let locals = vec![("s".to_string(), TypeInfo::Primitive(PrimitiveType::String))];

        let valid_delimiters = [",", " ", ":", ";", "-", "::"];
        let mut found = false;
        for seed in 0..100 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            if let Some(expr) = generator.try_generate_string_split(&ctx) {
                assert!(
                    expr.starts_with("s.split(\""),
                    "Expected 's.split(\"...\").collect()', got: {}",
                    expr,
                );
                assert!(
                    expr.ends_with("\").collect()"),
                    "Expected ending with '\").collect()', got: {}",
                    expr,
                );
                // Verify the delimiter is one of the valid ones
                let delim_start = "s.split(\"".len();
                let delim_end = expr.len() - "\").collect()".len();
                let delim = &expr[delim_start..delim_end];
                assert!(
                    valid_delimiters.contains(&delim),
                    "Unexpected delimiter '{}' in expr: {}",
                    delim,
                    expr,
                );
                found = true;
                break;
            }
        }
        assert!(
            found,
            "Expected try_generate_string_split to succeed at least once"
        );
    }

    #[test]
    fn test_string_split_no_strings() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = ExprConfig::default();
        let mut generator = ExprGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let ctx = ExprContext::new(&[], &[], &table);

        assert!(generator.try_generate_string_split(&ctx).is_none());
    }

    #[test]
    fn test_string_split_in_array_generation() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let locals = vec![(
            "text".to_string(),
            TypeInfo::Primitive(PrimitiveType::String),
        )];

        let mut found = false;
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            let expr = generator.generate(
                &TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                &ctx,
                0,
            );
            if expr.contains(".split(") {
                assert!(
                    expr.contains("text.split("),
                    "Expected 'text.split(...)...', got: {}",
                    expr,
                );
                assert!(
                    expr.ends_with(".collect()"),
                    "Expected ending with '.collect()', got: {}",
                    expr,
                );
                found = true;
                break;
            }
        }
        assert!(
            found,
            "Expected at least one .split().collect() call in [string] generation across 500 seeds",
        );
    }

    #[test]
    fn test_string_split_delimiter_variety() {
        // Ensure multiple delimiters can be generated
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let locals = vec![("s".to_string(), TypeInfo::Primitive(PrimitiveType::String))];

        let mut seen_delimiters = std::collections::HashSet::new();
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            if let Some(expr) = generator.try_generate_string_split(&ctx) {
                let delim_start = "s.split(\"".len();
                let delim_end = expr.len() - "\").collect()".len();
                let delim = expr[delim_start..delim_end].to_string();
                seen_delimiters.insert(delim);
            }
            if seen_delimiters.len() >= 3 {
                break;
            }
        }
        assert!(
            seen_delimiters.len() >= 3,
            "Expected at least 3 different delimiters across 500 seeds, got: {:?}",
            seen_delimiters,
        );
    }

    #[test]
    fn test_iter_any_all_direct() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let locals = vec![(
            "arr".to_string(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        )];

        let mut found_any = false;
        let mut found_all = false;
        for seed in 0..200 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            if let Some(expr) = generator.try_generate_iter_any_all(&ctx) {
                assert!(
                    expr.starts_with("arr.iter()."),
                    "Expected 'arr.iter().<method>(...)', got: {}",
                    expr,
                );
                assert!(
                    expr.contains(".any((x) => ") || expr.contains(".all((x) => "),
                    "Expected .any() or .all() call, got: {}",
                    expr,
                );
                if expr.contains(".any(") {
                    found_any = true;
                }
                if expr.contains(".all(") {
                    found_all = true;
                }
                if found_any && found_all {
                    break;
                }
            }
        }
        assert!(
            found_any && found_all,
            "Expected both .any() and .all() across 200 seeds",
        );
    }

    #[test]
    fn test_iter_any_all_no_arrays() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let config = ExprConfig::default();
        let mut generator = ExprGenerator::new(&mut rng, &config);

        let table = SymbolTable::new();
        let locals = vec![("n".to_string(), TypeInfo::Primitive(PrimitiveType::I64))];
        let ctx = ExprContext::new(&[], &locals, &table);

        assert!(generator.try_generate_iter_any_all(&ctx).is_none());
    }

    #[test]
    fn test_iter_any_all_in_bool_generation() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let locals = vec![(
            "nums".to_string(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        )];

        let mut found = false;
        for seed in 0..500 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &ctx, 0);
            if expr.contains(".iter().any(") || expr.contains(".iter().all(") {
                assert!(
                    expr.contains("nums.iter()."),
                    "Expected 'nums.iter().<method>(...)', got: {}",
                    expr,
                );
                found = true;
                break;
            }
        }
        assert!(
            found,
            "Expected at least one .iter().any/all() call in bool generation across 500 seeds",
        );
    }

    #[test]
    fn test_iter_any_all_string_array() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let locals = vec![(
            "words".to_string(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
        )];

        let mut found = false;
        for seed in 0..200 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&[], &locals, &table);
            if let Some(expr) = generator.try_generate_iter_any_all(&ctx) {
                assert!(
                    expr.contains("x.length()"),
                    "String array predicate should use x.length(), got: {}",
                    expr,
                );
                found = true;
                break;
            }
        }
        assert!(
            found,
            "Expected at least one .any/all() on string array across 200 seeds",
        );
    }

    #[test]
    fn test_compound_bool_generation() {
        let config = ExprConfig::default();
        let table = SymbolTable::new();
        let params = vec![
            ParamInfo {
                name: "a".to_string(),
                param_type: TypeInfo::Primitive(PrimitiveType::I64),
            },
            ParamInfo {
                name: "b".to_string(),
                param_type: TypeInfo::Primitive(PrimitiveType::Bool),
            },
        ];

        let mut found_mixed_and_or = false;
        let mut found_parenthesized_group = false;
        for seed in 0..2000 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let ctx = ExprContext::new(&params, &[], &table);
            let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &ctx, 0);

            // Compound bool: contains both && and || in the same expression
            let has_and = expr.contains("&&");
            let has_or = expr.contains("||");
            if has_and && has_or {
                found_mixed_and_or = true;
                // Check for parenthesized sub-groups: pattern like "(X && Y) ||" or "(X || Y) &&"
                if (expr.contains(") ||") || expr.contains(") &&"))
                    && (expr.contains("|| (") || expr.contains("&& ("))
                {
                    found_parenthesized_group = true;
                }
            }
            if found_mixed_and_or && found_parenthesized_group {
                break;
            }
        }
        assert!(
            found_mixed_and_or,
            "Expected at least one expression with both && and || across 2000 seeds"
        );
        assert!(
            found_parenthesized_group,
            "Expected at least one parenthesized compound bool (e.g. (a && b) || (c && d)) across 2000 seeds"
        );
    }
}
