//! Grammar-based expression generation.
//!
//! This module generates type-correct Vole expressions using grammar rules.
//! Expressions are generated with depth limits to prevent infinite recursion.

mod closures;
mod control_flow;
mod methods;

#[cfg(test)]
mod tests;

use rand::Rng;

use crate::symbols::{
    FieldInfo, InterfaceInfo, MethodInfo, ModuleId, ParamInfo, PrimitiveType, SymbolId, SymbolKind,
    SymbolTable, TypeInfo, TypeParam,
};

/// A variable whose type is a constrained type parameter:
/// `(var_name, type_param_name, interface_constraints)`.
pub type ConstrainedTypeParamVar = (String, String, Vec<(ModuleId, SymbolId)>);

/// Parameters for recursive field-path collection in
/// [`ExprGenerator::collect_field_paths`].
pub struct FieldPathSearch<'a> {
    pub table: &'a SymbolTable,
    pub mod_id: ModuleId,
    pub sym_id: SymbolId,
    pub prefix: String,
    pub target: &'a TypeInfo,
    pub candidates: &'a mut Vec<String>,
    pub depth: usize,
}

/// Configuration for expression generation.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
#[serde(default)]
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
        // Default values match the "full" profile so TOML files only specify overrides.
        Self {
            max_depth: 4,
            binary_probability: 0.5,
            when_probability: 0.2,
            match_probability: 0.15,
            if_expr_probability: 0.2,
            lambda_probability: 0.15,
            method_chain_probability: 0.20,
            max_chain_depth: 2,
            unreachable_probability: 0.05,
            max_match_arms: 6,
            inline_expr_arg_probability: 0.12,
            tuple_index_probability: 0.15,
            chained_coalesce_probability: 0.30,
            string_method_probability: 0.15,
            multi_arm_when_probability: 0.35,
            match_guard_probability: 0.15,
            closure_capture_probability: 0.30,
            interface_upcast_probability: 0.30,
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

    /// Get all optional-typed variables whose inner type matches the target.
    ///
    /// Returns `(name, inner_type)` pairs for variables of type `T?`.
    pub fn optional_vars_matching(&self, target: &TypeInfo) -> Vec<(String, TypeInfo)> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            if let TypeInfo::Optional(inner) = ty
                && types_compatible(inner, target)
            {
                vars.push((name.clone(), *inner.clone()));
            }
        }
        for param in self.params {
            if let TypeInfo::Optional(inner) = &param.param_type
                && types_compatible(inner, target)
            {
                vars.push((param.name.clone(), *inner.clone()));
            }
        }
        vars
    }

    /// Get optional variables whose inner type is a class.
    pub fn optional_class_vars(&self) -> Vec<(String, ModuleId, SymbolId)> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            if let TypeInfo::Optional(inner) = ty
                && let TypeInfo::Class(mod_id, sym_id) = inner.as_ref()
            {
                vars.push((name.clone(), *mod_id, *sym_id));
            }
        }
        for param in self.params {
            if let TypeInfo::Optional(inner) = &param.param_type
                && let TypeInfo::Class(mod_id, sym_id) = inner.as_ref()
            {
                vars.push((param.name.clone(), *mod_id, *sym_id));
            }
        }
        vars
    }

    /// Get all tuple-typed variables in scope.
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

    /// Get all union-typed variables in scope.
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

    /// Get all variables in scope with their types.
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
    pub fn class_vars(&self) -> Vec<(String, ModuleId, SymbolId)> {
        let mut vars = Vec::new();
        for (name, ty) in self.locals {
            match ty {
                TypeInfo::Class(mod_id, sym_id) => {
                    vars.push((name.clone(), *mod_id, *sym_id));
                }
                TypeInfo::Interface(mod_id, sym_id) => {
                    // Also include interface-typed vars when looking for class vars
                    // (they are class instances at runtime)
                    vars.push((name.clone(), *mod_id, *sym_id));
                }
                _ => {}
            }
        }
        for param in self.params {
            match &param.param_type {
                TypeInfo::Class(mod_id, sym_id) => {
                    vars.push((param.name.clone(), *mod_id, *sym_id));
                }
                TypeInfo::Interface(mod_id, sym_id) => {
                    vars.push((param.name.clone(), *mod_id, *sym_id));
                }
                _ => {}
            }
        }
        vars
    }

    /// Get all struct-typed variables in scope.
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

    /// Get all variables whose type is a constrained type parameter.
    pub fn constrained_type_param_vars(&self) -> Vec<ConstrainedTypeParamVar> {
        let mut vars = Vec::new();

        // Check all params for TypeParam types, then look up constraints
        for param in self.params {
            if let TypeInfo::TypeParam(tp_name) = &param.param_type {
                // Find this type param in our type_params list
                for tp in self.type_params {
                    if &tp.name == tp_name && !tp.constraints.is_empty() {
                        vars.push((param.name.clone(), tp_name.clone(), tp.constraints.clone()));
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

        if let Some(symbol) = table.get_symbol(mid, sid)
            && let SymbolKind::Interface(ref info) = symbol.kind
        {
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
        if let Some(symbol) = table.get_symbol(mod_id, iface_id)
            && let SymbolKind::Interface(ref iface_info) = symbol.kind
        {
            let iface_methods = get_interface_methods(table, mod_id, iface_id);
            for method in iface_methods {
                if seen_names.insert(method.name.clone()) {
                    methods.push((iface_info.clone(), method));
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
/// Primitive types, non-generic class/struct instances, and optional
/// primitives are capturable. This allows closures to capture these
/// variables and use them in expressions (field access, method calls,
/// null-coalescing), exercising closure-capture codegen interactions.
///
/// NOTE: Optional<Class> is NOT safe to capture — it triggers a segfault
/// during cleanup (see vol-vzqe). Only Optional<Primitive> is allowed.
pub(crate) fn is_capturable_type(ty: &TypeInfo) -> bool {
    match ty {
        TypeInfo::Primitive(_) | TypeInfo::Class(_, _) | TypeInfo::Struct(_, _) => true,
        TypeInfo::Optional(inner) => matches!(inner.as_ref(), TypeInfo::Primitive(_)),
        _ => false,
    }
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
    pub(crate) rng: &'a mut R,
    pub(crate) config: &'a ExprConfig,
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
            && let Some(expr) = self.try_generate_tuple_index_for_type(ty, ctx)
        {
            return expr;
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
            if let SymbolKind::Class(ref class_info) = class_sym.kind
                && class_info.type_params.is_empty()
                && class_info
                    .implements
                    .iter()
                    .any(|&(m, s)| m == iface_mod && s == iface_sym)
            {
                return self.generate_class_construction(iface_mod, class_sym.id, ctx);
            }
        }

        self.literal_for_primitive(PrimitiveType::I64)
    }

    /// Generate arguments for a method call.
    ///
    /// With probability `inline_expr_arg_probability`, each argument may be a
    /// `when`/`if` expression rather than a plain literal or variable reference.
    pub(super) fn generate_method_args(
        &mut self,
        params: &[ParamInfo],
        ctx: &ExprContext,
    ) -> String {
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
                if self.rng.gen_bool(self.config.string_method_probability)
                    && let Some(expr) = self.try_generate_string_bool_method(ctx)
                {
                    return expr;
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

    /// Generate an expression of a primitive type.
    fn generate_primitive(
        &mut self,
        prim: PrimitiveType,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        // ~18% chance to generate a field access if a class-typed local
        // has a field of the target primitive type
        if self.rng.gen_bool(0.18)
            && let Some(access) = self.try_generate_field_access(prim, ctx)
        {
            return access;
        }

        // ~15% chance to generate array indexing: `arrVar[index]`
        // when an array-typed variable with matching element type is in scope
        if self.rng.gen_bool(0.15)
            && let Some(expr) = self.try_generate_array_index(prim, ctx)
        {
            return expr;
        }

        // ~12% chance to generate fixed array indexing: `fixedArrVar[index]`
        // when a fixed-array-typed variable with matching element type is in scope
        if self.rng.gen_bool(0.12)
            && let Some(expr) = self.try_generate_fixed_array_index(prim, ctx)
        {
            return expr;
        }

        // Chance to generate tuple indexing: `tupleVar[index]`
        // when a tuple-typed variable with a matching element type is in scope
        if self.config.tuple_index_probability > 0.0
            && self.rng.gen_bool(self.config.tuple_index_probability)
            && let Some(expr) =
                self.try_generate_tuple_index_for_type(&TypeInfo::Primitive(prim), ctx)
        {
            return expr;
        }

        // ~15% chance to generate null coalescing: `optVar ?? defaultExpr`
        // when an optional-typed variable with matching inner type is in scope
        if self.rng.gen_bool(0.15)
            && let Some(expr) =
                self.try_generate_null_coalesce(&TypeInfo::Primitive(prim), ctx, depth)
        {
            return expr;
        }

        // ~10% chance to generate arr.length() for i64 expressions
        if prim == PrimitiveType::I64
            && self.rng.gen_bool(0.10)
            && let Some(expr) = self.try_generate_array_length(ctx)
        {
            return expr;
        }

        // String method: str.length() for i64 expressions.
        // (No arguments, so vole-fmt never wraps the call across lines.)
        if prim == PrimitiveType::I64
            && self.rng.gen_bool(self.config.string_method_probability)
            && let Some(expr) = self.try_generate_string_length(ctx)
        {
            return expr;
        }

        // ~10% chance to generate arr.iter().count() for i64 expressions
        if prim == PrimitiveType::I64
            && self.rng.gen_bool(0.10)
            && let Some(expr) = self.try_generate_iter_count(ctx)
        {
            return expr;
        }

        // ~8% chance to generate arr.iter().reduce(0, (acc, x) => acc + x) for i64 expressions
        if prim == PrimitiveType::I64
            && self.rng.gen_bool(0.08)
            && let Some(expr) =
                self.try_generate_iter_reduce(&TypeInfo::Primitive(PrimitiveType::I64), ctx)
        {
            return expr;
        }

        // ~10% chance to generate arr.iter().sum() for i64/f64 expressions
        if (prim == PrimitiveType::I64 || prim == PrimitiveType::F64)
            && self.rng.gen_bool(0.10)
            && let Some(expr) = self.try_generate_iter_sum(prim, ctx)
        {
            return expr;
        }

        // ~15% chance to call an interface method on a type-param-typed variable
        // when the method's return type matches our target primitive type.
        if self.rng.gen_bool(0.15)
            && let Some(expr) =
                self.try_generate_type_param_method_call(&TypeInfo::Primitive(prim), ctx)
        {
            return expr;
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
                if self.rng.gen_bool(0.10)
                    && let Some(expr) = self.try_generate_iter_any_all(ctx)
                {
                    return expr;
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
                if self.rng.gen_bool(0.15)
                    && let Some(expr) = self.try_generate_to_string_call(ctx)
                {
                    return expr;
                }
                // String method: to_upper/to_lower/trim/replace/replace_all/substring
                if self.rng.gen_bool(self.config.string_method_probability)
                    && let Some(expr) = self.try_generate_string_transform_method(ctx)
                {
                    return expr;
                }
                // ~12% chance: interpolated string with a method call
                if self.rng.gen_bool(0.12)
                    && let Some(expr) = self.try_generate_method_call_interpolation(ctx)
                {
                    return expr;
                }
                // ~10% chance: arr.iter().reduce("", ...) for string expressions
                if self.rng.gen_bool(0.10)
                    && let Some(expr) = self
                        .try_generate_iter_reduce(&TypeInfo::Primitive(PrimitiveType::String), ctx)
                {
                    return expr;
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

    /// Generate an optional expression.
    fn generate_optional(&mut self, inner: &TypeInfo, ctx: &ExprContext, depth: usize) -> String {
        // ~15% chance to generate arr.iter().first()/last()/nth() for optional expressions
        if self.rng.gen_bool(0.15)
            && let Some(expr) = self.try_generate_iter_first_last_nth(inner, ctx)
        {
            return expr;
        }

        // ~20% chance to generate optional chaining (optVar?.field) when
        // an optional class-typed variable with a field matching inner is in scope.
        // The result of ?. is Optional(field_type).
        if self.rng.gen_bool(0.20)
            && let Some((expr, result_ty)) = self.try_generate_optional_chaining(ctx)
        {
            // result_ty is Optional(field_type); check if field_type matches inner
            if let TypeInfo::Optional(ref chained_inner) = result_ty
                && types_compatible(chained_inner, inner)
            {
                return expr;
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
        if *elem == TypeInfo::Primitive(PrimitiveType::String)
            && self.rng.gen_bool(0.15)
            && let Some(expr) = self.try_generate_string_split(ctx)
        {
            return expr;
        }

        // ~15% chance to generate str.chars().collect() for [i32] arrays
        // (.chars() returns character codepoints as i32)
        if *elem == TypeInfo::Primitive(PrimitiveType::I32)
            && self.rng.gen_bool(0.15)
            && let Some(expr) = self.try_generate_string_chars_collect(ctx)
        {
            return expr;
        }

        // ~15% chance to generate arr.iter().map((x) => expr).collect()
        if self.rng.gen_bool(0.15)
            && let Some(expr) = self.try_generate_iter_map_collect(elem, ctx)
        {
            return expr;
        }

        // ~10% chance to generate arr.iter().filter((x) => pred).collect()
        if self.rng.gen_bool(0.10)
            && let Some(expr) = self.try_generate_iter_filter_collect(elem, ctx)
        {
            return expr;
        }

        // ~8% chance to generate arr.iter().skip(N).take(M).collect()
        if self.rng.gen_bool(0.08)
            && let Some(expr) = self.try_generate_iter_skip_take_collect(elem, ctx)
        {
            return expr;
        }

        // ~8% chance to generate arr.iter().sorted().collect() (i64/i32 only)
        if self.rng.gen_bool(0.08)
            && let Some(expr) = self.try_generate_iter_sorted_collect(elem, ctx)
        {
            return expr;
        }

        // ~8% chance to generate arr1.iter().chain(arr2.iter()).collect() (i64/i32 only)
        if self.rng.gen_bool(0.08)
            && let Some(expr) = self.try_generate_iter_chain_collect(elem, ctx)
        {
            return expr;
        }

        // ~6% chance to generate arr.iter().unique().collect() (i64/i32 only)
        if self.rng.gen_bool(0.06)
            && let Some(expr) = self.try_generate_iter_unique_collect(elem, ctx)
        {
            return expr;
        }

        // ~8% chance to generate arr.iter().flat_map((x) => [...]).collect() (i64/i32 only)
        if self.rng.gen_bool(0.08)
            && let Some(expr) = self.try_generate_iter_flat_map_collect(elem, ctx)
        {
            return expr;
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
        // ~8% chance to generate a boundary value for integer types.
        // This stresses overflow handling, edge cases in arithmetic,
        // and codegen for extreme constant values.
        if matches!(
            prim,
            PrimitiveType::I32
                | PrimitiveType::I64
                | PrimitiveType::I16
                | PrimitiveType::I8
                | PrimitiveType::U8
                | PrimitiveType::U16
                | PrimitiveType::U32
                | PrimitiveType::U64
        ) && self.rng.gen_bool(0.10)
        {
            return self.boundary_literal(prim);
        }
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
                let val: i32 = self.rng.gen_range(-100..100);
                format!("{}_i32", val)
            }
            PrimitiveType::I64 => {
                let val: i64 = self.rng.gen_range(-1000..1000);
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
                let roll = self.rng.gen_range(0..10);
                if roll < 2 {
                    // ~20% chance: string with escape sequences
                    self.string_with_escapes()
                } else if roll < 3 {
                    // ~10% chance: raw string literal @"..."
                    self.raw_string_literal()
                } else {
                    let id = self.rng.gen_range(0..100);
                    format!("\"str{}\"", id)
                }
            }
            PrimitiveType::Nil => "nil".to_string(),
        }
    }

    /// Generate a boundary literal for a signed integer type.
    ///
    /// Returns extreme values (MIN+1, MAX, 0, 1, -1) that stress overflow
    /// handling and edge cases in arithmetic codegen.
    ///
    /// Note: We use MIN+1 instead of MIN because Vole parses `-N` as unary
    /// negation of `N`, and `N = abs(MIN)` overflows the positive range.
    fn boundary_literal(&mut self, prim: PrimitiveType) -> String {
        match prim {
            PrimitiveType::I8 => {
                // i8::MIN (-128) can't be a literal (parser sees unary minus + 128 which overflows i8)
                let vals: &[i8] = &[i8::MIN + 1, i8::MAX, 0, 1, -1, -2];
                let val = vals[self.rng.gen_range(0..vals.len())];
                format!("{}_i8", val)
            }
            PrimitiveType::I16 => {
                let vals: &[i16] = &[i16::MIN + 1, i16::MAX, 0, 1, -1, -2];
                let val = vals[self.rng.gen_range(0..vals.len())];
                format!("{}_i16", val)
            }
            PrimitiveType::I32 => {
                let vals: &[i32] = &[i32::MIN + 1, i32::MAX, 0, 1, -1, -2];
                let val = vals[self.rng.gen_range(0..vals.len())];
                format!("{}_i32", val)
            }
            PrimitiveType::I64 => {
                // i64::MIN can't be a literal (parser sees unary minus + 9223372036854775808 which overflows)
                let vals: &[i64] = &[i64::MIN + 1, i64::MAX, 0, 1, -1, -2];
                let val = vals[self.rng.gen_range(0..vals.len())];
                format!("{}_i64", val)
            }
            PrimitiveType::U8 => {
                let vals: &[u8] = &[0, 1, u8::MAX, u8::MAX - 1];
                let val = vals[self.rng.gen_range(0..vals.len())];
                format!("{}_u8", val)
            }
            PrimitiveType::U16 => {
                let vals: &[u16] = &[0, 1, u16::MAX, u16::MAX - 1];
                let val = vals[self.rng.gen_range(0..vals.len())];
                format!("{}_u16", val)
            }
            PrimitiveType::U32 => {
                // u32::MAX fits in i64 so the parser should handle it
                let vals: &[u32] = &[0, 1, u32::MAX, u32::MAX - 1];
                let val = vals[self.rng.gen_range(0..vals.len())];
                format!("{}_u32", val)
            }
            PrimitiveType::U64 => {
                // u64::MAX overflows i64 so the parser rejects it;
                // use i64::MAX as the safe upper bound for u64 boundary
                let vals: &[u64] = &[0, 1, i64::MAX as u64, 1000];
                let val = vals[self.rng.gen_range(0..vals.len())];
                format!("{}_u64", val)
            }
            _ => self.literal_for_primitive(prim),
        }
    }

    /// Generate a string literal containing escape sequences to stress the
    /// parser and codegen string handling. Produces strings like:
    /// `"hello\nworld"`, `"tab\there"`, `"back\\slash"`, `""` (empty).
    ///
    /// NOTE: We avoid `\{` and `\}` escapes because vole-fmt doesn't re-escape
    /// them after roundtripping, causing `{` to be misinterpreted as
    /// interpolation start.
    fn string_with_escapes(&mut self) -> String {
        let templates = [
            "\"hello\\nworld\"",
            "\"tab\\there\"",
            "\"line1\\r\\nline2\"",
            "\"back\\\\slash\"",
            "\"quote\\\"inside\"",
            "\"multi\\n\\t\\rescapes\"",
            "\"\\n\"",
            "\"\\t\"",
            "\"\"",
            "\"\\n\\n\\n\"",
            "\"a\\tb\\tc\"",
        ];
        templates[self.rng.gen_range(0..templates.len())].to_string()
    }

    /// Generate a raw string literal using `@"..."` syntax.
    /// Raw strings treat backslashes as literal characters.
    fn raw_string_literal(&mut self) -> String {
        let templates = [
            r#"@"C:\Users\name""#,
            r#"@"path\to\file""#,
            r#"@"line1\nline2""#,
            r#"@"hello""#,
            r#"@"raw\tstring""#,
            r#"@"back\\slash""#,
            r#"@"test\r\n""#,
            r#"@"""#,
        ];
        templates[self.rng.gen_range(0..templates.len())].to_string()
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
                let roll = self.rng.gen_range(0..10);
                if roll < 2 {
                    // ~20% chance: string with escape sequences
                    self.string_with_escapes()
                } else if roll < 3 {
                    // ~10% chance: raw string literal @"..."
                    self.raw_string_literal()
                } else {
                    let id = self.rng.gen_range(0..100);
                    format!("\"str{}\"", id)
                }
            }
            PrimitiveType::Nil => "nil".to_string(),
        }
    }
}
