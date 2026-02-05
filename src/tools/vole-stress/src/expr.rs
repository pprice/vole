//! Grammar-based expression generation.
//!
//! This module generates type-correct Vole expressions using grammar rules.
//! Expressions are generated with depth limits to prevent infinite recursion.

use rand::Rng;

use crate::symbols::{
    ModuleId, ParamInfo, PrimitiveType, SymbolId, SymbolKind, SymbolTable, TypeInfo,
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
}

/// Check if two types are compatible for expression generation.
fn types_compatible(actual: &TypeInfo, expected: &TypeInfo) -> bool {
    match (actual, expected) {
        (TypeInfo::Primitive(a), TypeInfo::Primitive(e)) => a == e,
        (TypeInfo::Void, TypeInfo::Void) => true,
        (TypeInfo::Optional(a), TypeInfo::Optional(e)) => types_compatible(a, e),
        (TypeInfo::Array(a), TypeInfo::Array(e)) => types_compatible(a, e),
        (TypeInfo::Tuple(a), TypeInfo::Tuple(e)) => {
            a.len() == e.len()
                && a.iter()
                    .zip(e.iter())
                    .all(|(ai, ei)| types_compatible(ai, ei))
        }
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

        match ty {
            TypeInfo::Primitive(prim) => self.generate_primitive(*prim, ctx, depth),
            TypeInfo::Optional(inner) => self.generate_optional(inner, ctx, depth),
            TypeInfo::Void => "nil".to_string(),
            TypeInfo::Array(elem) => self.generate_array(elem, ctx, depth),
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
            _ => self.generate_simple(ty, ctx),
        }
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

    /// Try to generate a field access expression on a class-typed local.
    ///
    /// Looks for local variables with class type whose fields match the
    /// target primitive type. Returns `Some("local.field")` on success.
    /// Only considers non-generic classes (generic field types are too
    /// complex to resolve).
    fn try_generate_field_access(
        &mut self,
        prim: PrimitiveType,
        ctx: &ExprContext,
    ) -> Option<String> {
        let target = TypeInfo::Primitive(prim);

        // Collect (local_name, field_name) pairs for matching fields
        let mut candidates: Vec<(String, String)> = Vec::new();

        for (name, ty) in ctx.locals {
            if let TypeInfo::Class(mod_id, sym_id) = ty {
                if let Some(sym) = ctx.table.get_symbol(*mod_id, *sym_id) {
                    if let SymbolKind::Class(ref info) = sym.kind {
                        // Skip generic classes
                        if !info.type_params.is_empty() {
                            continue;
                        }
                        for field in &info.fields {
                            if field.field_type == target {
                                candidates.push((name.clone(), field.name.clone()));
                            }
                        }
                    }
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = self.rng.gen_range(0..candidates.len());
        let (local_name, field_name) = &candidates[idx];
        Some(format!("{}.{}", local_name, field_name))
    }

    /// Try to generate a null coalescing expression (`optVar ?? defaultExpr`).
    ///
    /// Looks for optional-typed variables in scope whose inner type matches
    /// the target type. Returns `Some("optVar ?? defaultExpr")` on success.
    /// The result type is the inner type T (not T?).
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
        let (var_name, _inner_ty) = &candidates[idx];

        // Generate a default value of the inner type
        let default_expr = self.generate(target, ctx, depth + 1);

        Some(format!("({} ?? {})", var_name, default_expr))
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

    /// Generate a simple expression (literal or variable reference).
    pub fn generate_simple(&mut self, ty: &TypeInfo, ctx: &ExprContext) -> String {
        // Try to find a matching variable first
        if let Some(var) = ctx.find_matching_var(ty)
            && self.rng.gen_bool(0.6)
        {
            return var;
        }

        // Otherwise generate a literal
        match ty {
            TypeInfo::Primitive(p) => self.literal_for_primitive(*p),
            TypeInfo::Optional(_) => "nil".to_string(),
            TypeInfo::Void => "nil".to_string(),
            TypeInfo::Tuple(elem_types) => {
                // Generate a simple tuple with literal elements
                let elements: Vec<String> = elem_types
                    .iter()
                    .map(|t| self.generate_simple(t, ctx))
                    .collect();
                format!("[{}]", elements.join(", "))
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
            _ => self.literal_for_primitive(PrimitiveType::I64),
        }
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

        // ~15% chance to generate null coalescing: `optVar ?? defaultExpr`
        // when an optional-typed variable with matching inner type is in scope
        if self.rng.gen_bool(0.15) {
            if let Some(expr) =
                self.try_generate_null_coalesce(&TypeInfo::Primitive(prim), ctx, depth)
            {
                return expr;
            }
        }

        let choice = self.rng.gen_range(0..10);

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
                    _ => self.generate_simple(&TypeInfo::Primitive(prim), ctx),
                }
            }
            PrimitiveType::String => {
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
                    _ => self.generate_simple(&TypeInfo::Primitive(prim), ctx),
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
    fn generate_when_expr(&mut self, ty: &TypeInfo, ctx: &ExprContext, depth: usize) -> String {
        let arm_count = self.rng.gen_range(2..=4);
        let mut arms = Vec::new();

        for _ in 0..arm_count - 1 {
            let cond = self.generate(&TypeInfo::Primitive(PrimitiveType::Bool), ctx, depth + 1);
            let value = self.generate(ty, ctx, depth + 1);
            arms.push(format!("{} => {}", cond, value));
        }

        // Default arm with wildcard
        let default_value = self.generate(ty, ctx, depth + 1);
        arms.push(format!("_ => {}", default_value));

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
        let len = self.rng.gen_range(0..=4);
        if len == 0 {
            return "[]".to_string();
        }

        let elements: Vec<String> = (0..len)
            .map(|_| self.generate(elem, ctx, depth + 1))
            .collect();

        format!("[{}]", elements.join(", "))
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

            let interp_expr = self.interp_expr_for_var(name, ty);
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
    /// For numeric types, sometimes wraps in arithmetic (e.g. `param0 + 1_i64`).
    /// For other types, just references the variable directly.
    fn interp_expr_for_var(&mut self, name: &str, ty: &TypeInfo) -> String {
        match ty {
            TypeInfo::Primitive(PrimitiveType::I32) if self.rng.gen_bool(0.3) => {
                let n = self.rng.gen_range(1..10);
                format!("{} + {}_i32", name, n)
            }
            TypeInfo::Primitive(PrimitiveType::I64) if self.rng.gen_bool(0.3) => {
                let n = self.rng.gen_range(1..10);
                format!("{} + {}_i64", name, n)
            }
            _ => name.to_string(),
        }
    }

    /// Generate a literal for a primitive type.
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
    pub fn generate_match_expr(
        &mut self,
        subject_type: &TypeInfo,
        result_type: &TypeInfo,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        let subject = self.generate(subject_type, ctx, depth + 1);
        let arm_count = self.rng.gen_range(2..=4);
        let mut arms = Vec::new();

        // Generate some literal or guarded arms
        for _ in 0..arm_count - 1 {
            let pattern = self.generate_pattern(subject_type);
            let value = self.generate(result_type, ctx, depth + 1);
            arms.push(format!("{} => {}", pattern, value));
        }

        // Always end with wildcard for exhaustiveness
        let default_value = self.generate(result_type, ctx, depth + 1);
        arms.push(format!("_ => {}", default_value));

        format!("match {} {{ {} }}", subject, arms.join(", "))
    }

    /// Generate a match pattern.
    fn generate_pattern(&mut self, ty: &TypeInfo) -> String {
        match ty {
            TypeInfo::Primitive(prim) => {
                match self.rng.gen_range(0..3) {
                    0 => "_".to_string(), // Wildcard
                    1 => {
                        // Literal pattern
                        self.literal_for_primitive(*prim)
                    }
                    _ => {
                        // Guarded wildcard
                        let cond = self.literal_for_primitive(PrimitiveType::Bool);
                        format!("_ if {}", cond)
                    }
                }
            }
            _ => "_".to_string(),
        }
    }

    /// Generate a lambda expression.
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

        let lambda_ctx = ExprContext::new(&lambda_params, &[], ctx.table);

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

        // Check that bitwise NOT does NOT appear in f64 expressions
        for seed in 0..200 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut generator = ExprGenerator::new(&mut rng, &config);
            let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::F64), &ctx, 0);
            assert!(
                !expr.contains('~'),
                "Bitwise NOT should not appear in f64 expressions, got: {}",
                expr,
            );
        }
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
}
