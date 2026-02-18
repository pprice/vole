//! The [`Emit`] abstraction -- recursive engine for rule-based code generation.
//!
//! `Emit` owns the RNG, holds references to the rule registries, and provides
//! sub-generation methods that rules call to recurse into nested statements and
//! expressions. It is the glue between the rule system (trait objects) and the
//! generated Vole source text.

use std::collections::HashMap;

use rand::seq::SliceRandom;
use rand::{Rng, RngCore};

use crate::resolver::ResolvedParams;
use crate::rule::{ExprRule, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, SymbolKind, SymbolTable, TypeInfo};

// ---------------------------------------------------------------------------
// Emit
// ---------------------------------------------------------------------------

/// Recursive generation engine.
///
/// Rules receive `&mut Emit` and call its sub-generation methods to produce
/// nested statements and expressions. `Emit` owns the RNG exclusively --
/// no other struct holds a random source.
pub struct Emit<'a> {
    /// The random number generator (type-erased to avoid generic explosion).
    rng: &'a mut dyn RngCore,
    /// All registered statement rules.
    stmt_rules: &'a [Box<dyn StmtRule>],
    /// All registered expression rules.
    expr_rules: &'a [Box<dyn ExprRule>],
    /// Resolved parameters keyed by rule name.
    resolved_params: &'a ResolvedParams,
    /// Symbol table for looking up class/struct field information when
    /// generating literals for class/struct types.
    table: &'a SymbolTable,
    /// Current indentation level (number of indent units, not spaces).
    indent: usize,
    /// Current expression nesting depth (prevents infinite recursion).
    expr_depth: usize,
    /// Mapping from type parameter names to expressions that produce a value
    /// of that type. Populated when emitting method bodies for generic classes,
    /// so that `literal(TypeParam("T"))` can return e.g. `self.field8` instead
    /// of falling back to an incorrect concrete literal.
    type_param_exprs: HashMap<String, Vec<String>>,
}

/// Number of spaces per indentation level.
const INDENT_WIDTH: usize = 4;

/// Maximum expression nesting depth before falling back to literals.
const MAX_EXPR_DEPTH: usize = 4;

/// An empty [`Params`] bag returned when a rule has no resolved params.
fn empty_params() -> Params {
    Params::from_iter(std::iter::empty())
}

// ---------------------------------------------------------------------------
// Construction
// ---------------------------------------------------------------------------

impl<'a> Emit<'a> {
    /// Create a new `Emit` engine.
    pub fn new(
        rng: &'a mut dyn RngCore,
        stmt_rules: &'a [Box<dyn StmtRule>],
        expr_rules: &'a [Box<dyn ExprRule>],
        resolved_params: &'a ResolvedParams,
        table: &'a SymbolTable,
    ) -> Self {
        Self {
            rng,
            stmt_rules,
            expr_rules,
            resolved_params,
            table,
            indent: 0,
            expr_depth: 0,
            type_param_exprs: HashMap::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

impl Emit<'_> {
    /// Register expressions that produce values of generic type parameters.
    ///
    /// When emitting method bodies for generic classes, this mapping lets
    /// [`literal`](Emit::literal) return e.g. `self.field8` for a type
    /// parameter `T2` instead of falling back to a concrete `i64` literal.
    pub fn set_type_param_exprs(&mut self, map: HashMap<String, Vec<String>>) {
        self.type_param_exprs = map;
    }
}

// ---------------------------------------------------------------------------
// Sub-generation methods
// ---------------------------------------------------------------------------

impl Emit<'_> {
    /// Generate a sub-expression of the expected type.
    ///
    /// Dispatches through the expression rule registry; falls back to a
    /// literal of the expected type if no rule fires.
    pub fn sub_expr(&mut self, ty: &TypeInfo, scope: &Scope) -> String {
        self.dispatch_expr(scope, ty)
    }

    /// Generate a sub-statement.
    ///
    /// Dispatches through the statement rule registry; falls back to a
    /// comment if no rule fires.
    pub fn sub_stmt(&mut self, scope: &mut Scope) -> String {
        self.dispatch_stmt(scope)
    }

    /// Generate a block of `num_stmts` statements with proper indentation.
    ///
    /// Each statement is indented one level deeper than the current level.
    /// Returns the block body (without surrounding braces).
    pub fn block(&mut self, scope: &mut Scope, num_stmts: usize) -> String {
        self.indented(|emit| {
            let mut lines = Vec::with_capacity(num_stmts);
            for _ in 0..num_stmts {
                let stmt = emit.sub_stmt(scope);
                if !stmt.is_empty() {
                    lines.push(format!("{}{}", emit.indent_str(), stmt));
                }
            }
            lines.join("\n")
        })
    }

    /// Generate a random literal of the given type.
    ///
    /// Does not require scope -- purely type-driven.
    pub fn literal(&mut self, ty: &TypeInfo) -> String {
        match ty {
            TypeInfo::Primitive(prim) => self.literal_for_primitive(*prim),
            TypeInfo::Void => "nil".to_string(),
            TypeInfo::Optional(inner) => {
                if self.gen_bool(0.5) {
                    "nil".to_string()
                } else {
                    self.literal(inner)
                }
            }
            TypeInfo::Array(elem) => {
                let v1 = self.literal(elem);
                let v2 = self.literal(elem);
                format!("[{}, {}]", v1, v2)
            }
            TypeInfo::FixedArray(elem, size) => {
                let value = self.literal(elem);
                format!("[{}; {}]", value, size)
            }
            TypeInfo::Tuple(elems) => {
                let parts: Vec<String> = elems.iter().map(|e| self.literal(e)).collect();
                format!("[{}]", parts.join(", "))
            }
            TypeInfo::Class(mod_id, sym_id) | TypeInfo::Struct(mod_id, sym_id) => {
                // Look up the class/struct fields and generate a proper
                // construction expression: `ClassName { f1: v1, f2: v2 }`.
                if let Some(sym) = self.table.get_symbol(*mod_id, *sym_id) {
                    let fields = match &sym.kind {
                        SymbolKind::Class(info) if info.type_params.is_empty() => {
                            Some((sym.name.clone(), info.fields.clone()))
                        }
                        SymbolKind::Struct(info) => Some((sym.name.clone(), info.fields.clone())),
                        _ => None,
                    };
                    if let Some((type_name, fields)) = fields {
                        let field_values: Vec<String> = fields
                            .iter()
                            .map(|f| {
                                let value = self.literal(&f.field_type);
                                format!("{}: {}", f.name, value)
                            })
                            .collect();
                        return format!("{} {{ {} }}", type_name, field_values.join(", "));
                    }
                }
                // Fallback for generic classes or missing symbols.
                self.literal_for_primitive(PrimitiveType::I64)
            }
            TypeInfo::TypeParam(name) => {
                // Look up registered expressions for this type parameter
                // (e.g. `self.field8` when inside a generic class method).
                if let Some(exprs) = self.type_param_exprs.get(name) {
                    if !exprs.is_empty() {
                        let idx = self.rng.gen_range(0..exprs.len());
                        return exprs[idx].clone();
                    }
                }
                // No known expression for this type param; fall back to
                // a default primitive (will be type-incorrect but avoids
                // a panic -- the planner should ensure this path is rare).
                self.literal_for_primitive(PrimitiveType::I64)
            }
            _ => {
                // For types that don't have a natural literal form,
                // fall back to a default primitive.
                self.literal_for_primitive(PrimitiveType::I64)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Literal generation
// ---------------------------------------------------------------------------

impl Emit<'_> {
    /// Generate a non-zero literal for a numeric primitive type.
    ///
    /// Useful for generating safe divisors (avoiding division-by-zero).
    /// Falls back to [`literal`](Emit::literal) for non-numeric types.
    pub fn nonzero_literal(&mut self, prim: PrimitiveType) -> String {
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

    /// Generate a constant-safe literal for a type.
    ///
    /// Only produces values the compiler recognizes as compile-time constants
    /// (non-negative, no unary negation). Used for global variable initialization.
    pub fn constant_literal(&mut self, ty: &TypeInfo) -> String {
        match ty {
            TypeInfo::Primitive(p) => self.constant_literal_for_primitive(*p),
            TypeInfo::Optional(inner) => self.constant_literal(inner),
            TypeInfo::Void => "nil".to_string(),
            TypeInfo::Union(variants) => {
                if let Some(first) = variants.first() {
                    self.constant_literal(first)
                } else {
                    "nil".to_string()
                }
            }
            TypeInfo::Array(elem) => {
                let v1 = self.constant_literal(elem);
                let v2 = self.constant_literal(elem);
                format!("[{}, {}]", v1, v2)
            }
            TypeInfo::Tuple(elems) => {
                let parts: Vec<String> = elems.iter().map(|e| self.constant_literal(e)).collect();
                format!("[{}]", parts.join(", "))
            }
            TypeInfo::FixedArray(elem, size) => {
                let value = self.constant_literal(elem);
                format!("[{}; {}]", value, size)
            }
            _ => "nil".to_string(),
        }
    }

    /// Generate a non-negative literal for a primitive type (constant-safe).
    fn constant_literal_for_primitive(&mut self, prim: PrimitiveType) -> String {
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
            _ => self.literal_for_primitive(prim),
        }
    }

    /// Generate a literal for a primitive type.
    fn literal_for_primitive(&mut self, prim: PrimitiveType) -> String {
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
                let id = self.rng.gen_range(0..100);
                format!("\"str{}\"", id)
            }
            PrimitiveType::Nil => "nil".to_string(),
        }
    }
}

// ---------------------------------------------------------------------------
// RNG convenience methods
// ---------------------------------------------------------------------------

impl Emit<'_> {
    /// Return `true` with probability `prob` (0.0..=1.0).
    pub fn gen_bool(&mut self, prob: f64) -> bool {
        self.rng.gen_bool(prob.clamp(0.0, 1.0))
    }

    /// Generate a random `usize` in `range`.
    pub fn gen_range(&mut self, range: std::ops::Range<usize>) -> usize {
        if range.is_empty() {
            return range.start;
        }
        self.rng.gen_range(range)
    }

    /// Generate a random `usize` in the inclusive range `[min, max]`.
    pub fn random_in(&mut self, min: usize, max: usize) -> usize {
        if min >= max {
            return min;
        }
        self.rng.gen_range(min..=max)
    }

    /// Generate a random `i64` in the given inclusive range.
    pub fn gen_i64_range(&mut self, min: i64, max: i64) -> i64 {
        if min >= max {
            return min;
        }
        self.rng.gen_range(min..=max)
    }

    /// Shuffle a slice in place.
    pub fn shuffle<T>(&mut self, slice: &mut [T]) {
        slice.shuffle(self.rng);
    }

    /// Pick a random primitive type suitable for expressions.
    ///
    /// Delegates to [`PrimitiveType::random_expr_type`], providing access to
    /// the RNG through `Emit`.
    pub fn random_primitive_type(&mut self) -> TypeInfo {
        TypeInfo::Primitive(PrimitiveType::random_expr_type(self.rng))
    }

    /// Pick a random primitive type suitable for expressions (unwrapped).
    ///
    /// Like [`random_primitive_type`](Self::random_primitive_type) but returns
    /// the [`PrimitiveType`] directly instead of wrapping it in `TypeInfo`.
    pub fn random_expr_primitive(&mut self) -> PrimitiveType {
        PrimitiveType::random_expr_type(self.rng)
    }

    /// Pick a random primitive type suitable for array elements.
    ///
    /// Delegates to [`PrimitiveType::random_array_element_type`], which
    /// excludes `i128` (not valid for array elements).
    pub fn random_array_element_type(&mut self) -> PrimitiveType {
        PrimitiveType::random_array_element_type(self.rng)
    }

    /// Pick a random tuple type.
    ///
    /// Delegates to [`TypeInfo::random_tuple_type`].
    pub fn random_tuple_type(&mut self) -> TypeInfo {
        TypeInfo::random_tuple_type(self.rng)
    }

    /// Pick a random fixed-array type.
    ///
    /// Delegates to [`TypeInfo::random_fixed_array_type`].
    pub fn random_fixed_array_type(&mut self) -> TypeInfo {
        TypeInfo::random_fixed_array_type(self.rng)
    }
}

// ---------------------------------------------------------------------------
// Param resolution
// ---------------------------------------------------------------------------

impl Emit<'_> {
    /// Return the resolved params for the named rule.
    ///
    /// Falls back to an empty [`Params`] bag if the rule has no entry in the
    /// resolved params map (this is common during early development when
    /// profile resolution is not yet wired up).
    pub fn params_for(&self, rule_name: &str) -> &Params {
        self.resolved_params.get(rule_name).unwrap_or_else(|| {
            // Leak a static empty Params so we can return a reference.
            // This only happens for rules missing from the profile, which
            // is a startup-time concern (bounded number of rules).
            static EMPTY: std::sync::OnceLock<Params> = std::sync::OnceLock::new();
            EMPTY.get_or_init(empty_params)
        })
    }
}

// ---------------------------------------------------------------------------
// Indentation
// ---------------------------------------------------------------------------

impl Emit<'_> {
    /// Return the current indentation string (spaces).
    pub fn indent_str(&self) -> String {
        " ".repeat(self.indent * INDENT_WIDTH)
    }

    /// Execute `f` at one deeper indentation level, then restore.
    pub fn indented<F, T>(&mut self, f: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        self.indent += 1;
        let result = f(self);
        self.indent -= 1;
        result
    }
}

// ---------------------------------------------------------------------------
// Higher-level generation entry points
// ---------------------------------------------------------------------------

impl Emit<'_> {
    /// Set the indentation level (e.g., to match the emitter's current depth).
    pub fn set_indent(&mut self, indent: usize) {
        self.indent = indent;
    }

    /// Generate a function body: several statements followed by a return.
    ///
    /// Mirrors the old `StmtGenerator::generate_body`: generates `stmt_count`
    /// statements via rule dispatch, then appends a `return <expr>` for
    /// non-void functions.
    pub fn generate_body(
        &mut self,
        return_type: &TypeInfo,
        scope: &mut Scope,
        stmt_count: usize,
    ) -> Vec<String> {
        let mut lines = Vec::new();
        let effective_return_type = return_type.success_type().clone();
        scope.return_type = Some(effective_return_type.clone());

        // Generate statements
        for _ in 0..stmt_count {
            let stmt = self.sub_stmt(scope);
            lines.push(stmt);
        }

        // Generate final return statement for non-void functions
        if !matches!(effective_return_type, TypeInfo::Void) {
            let return_expr = self.sub_expr(&effective_return_type, scope);
            lines.push(format!("return {}", return_expr));
        }

        lines
    }

    /// Generate a generator function body with a while loop and yield.
    ///
    /// Produces:
    /// ```vole
    /// let mut _gi = 0
    /// while _gi < N {
    ///     yield <expr>
    ///     _gi = _gi + 1
    /// }
    /// ```
    pub fn generate_generator_body(&mut self, elem_type: &TypeInfo, scope: &Scope) -> Vec<String> {
        let mut lines = Vec::new();
        let limit = self.random_in(2, 5);

        // Initialize counter
        lines.push("let mut _gi = 0".to_string());

        // For generator yield expressions, use a literal only (compiler bug
        // prevents referencing params inside generators).
        let yield_expr = self.literal(elem_type);

        // Build the while loop with yield
        let indent = " ".repeat((self.indent + 1) * INDENT_WIDTH);
        lines.push(format!("while _gi < {} {{", limit));
        lines.push(format!("{}yield {}", indent, yield_expr));
        lines.push(format!("{}_gi = _gi + 1", indent));
        lines.push("}".to_string());

        lines
    }

    /// Generate a single statement for use in contexts like
    /// `emit_self_returning_body` where individual statements are needed.
    pub fn generate_statement(&mut self, scope: &mut Scope) -> String {
        self.sub_stmt(scope)
    }

    /// Generate a simple return expression for expression-bodied functions.
    ///
    /// Dispatches through the expr rule registry, falling back to a literal.
    pub fn generate_return_expr(&mut self, return_type: &TypeInfo, scope: &Scope) -> String {
        let effective_return_type = return_type.success_type().clone();
        self.sub_expr(&effective_return_type, scope)
    }
}

// ---------------------------------------------------------------------------
// Dispatch (private)
// ---------------------------------------------------------------------------

impl Emit<'_> {
    /// Core statement dispatch loop.
    ///
    /// Shuffles rule order, iterates rules checking probability and
    /// precondition, calls generate. First rule that returns `Some` wins.
    /// Falls back to a comment if nothing fires.
    fn dispatch_stmt(&mut self, scope: &mut Scope) -> String {
        let rule_count = self.stmt_rules.len();
        if rule_count == 0 {
            return "// skip".to_string();
        }

        // Build a shuffled index list.
        let mut indices: Vec<usize> = (0..rule_count).collect();
        indices.shuffle(self.rng);

        // Take a raw pointer to `resolved_params` so we can look up params
        // without holding an immutable borrow on `self` (which would block
        // passing `&mut self` to `generate`).
        //
        // SAFETY: `resolved_params` is an immutable shared reference that
        // outlives this call. We never mutate it through `self`, so the
        // pointer stays valid and the data is never aliased mutably.
        let resolved_ptr: *const ResolvedParams = self.resolved_params;

        for idx in indices {
            let rule = &self.stmt_rules[idx];

            // SAFETY: see `resolved_ptr` comment above.
            let params = unsafe { &*resolved_ptr }
                .get(rule.name())
                .unwrap_or_else(|| {
                    static EMPTY: std::sync::OnceLock<Params> = std::sync::OnceLock::new();
                    EMPTY.get_or_init(empty_params)
                });

            // Check precondition.
            if !rule.precondition(scope, params) {
                continue;
            }

            // Check probability parameter if present.
            if has_probability_param(params) {
                let prob = params.prob("probability");
                if !self.rng.gen_bool(prob.clamp(0.0, 1.0)) {
                    continue;
                }
            }

            // Try to generate.
            //
            // The rule reference borrows `self.stmt_rules` immutably, but
            // `generate` needs `&mut self`. We use a raw pointer to break
            // the overlap. This is safe because `generate` never modifies
            // `stmt_rules` or `resolved_params`.
            let rule_ptr: *const dyn StmtRule = &**rule;
            let params_ptr: *const Params = params;
            let result = unsafe { &*rule_ptr }.generate(scope, self, unsafe { &*params_ptr });

            if let Some(text) = result {
                return text;
            }
        }

        // Fallback: no rule fired.
        "// skip".to_string()
    }

    /// Core expression dispatch loop.
    ///
    /// Shuffles rule order, iterates rules checking probability and
    /// precondition, calls generate. First rule that returns `Some` wins.
    /// Falls back to a literal of the expected type.
    fn dispatch_expr(&mut self, scope: &Scope, expected_type: &TypeInfo) -> String {
        let rule_count = self.expr_rules.len();

        // At max depth, always return a simple literal to prevent infinite
        // recursion through expr rules that call sub_expr.
        if rule_count == 0 || self.expr_depth >= MAX_EXPR_DEPTH {
            return self.literal(expected_type);
        }

        self.expr_depth += 1;

        // Build a shuffled index list.
        let mut indices: Vec<usize> = (0..rule_count).collect();
        indices.shuffle(self.rng);

        // See dispatch_stmt for SAFETY rationale.
        let resolved_ptr: *const ResolvedParams = self.resolved_params;

        for idx in indices {
            let rule = &self.expr_rules[idx];

            let params = unsafe { &*resolved_ptr }
                .get(rule.name())
                .unwrap_or_else(|| {
                    static EMPTY: std::sync::OnceLock<Params> = std::sync::OnceLock::new();
                    EMPTY.get_or_init(empty_params)
                });

            // Check precondition.
            if !rule.precondition(scope, params) {
                continue;
            }

            // Check probability parameter if present.
            if has_probability_param(params) {
                let prob = params.prob("probability");
                if !self.rng.gen_bool(prob.clamp(0.0, 1.0)) {
                    continue;
                }
            }

            // Try to generate (same raw-pointer technique as dispatch_stmt).
            let rule_ptr: *const dyn ExprRule = &**rule;
            let params_ptr: *const Params = params;
            let result =
                unsafe { &*rule_ptr }.generate(scope, self, unsafe { &*params_ptr }, expected_type);

            if let Some(text) = result {
                self.expr_depth -= 1;
                return text;
            }
        }

        self.expr_depth -= 1;
        // Fallback: generate a literal.
        self.literal(expected_type)
    }
}

/// Check whether a [`Params`] bag contains a `"probability"` key.
fn has_probability_param(params: &Params) -> bool {
    params.contains("probability")
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rule::{Param, ParamValue};
    use crate::symbols::SymbolTable;
    use rand::SeedableRng;

    fn test_rng() -> rand::rngs::StdRng {
        rand::rngs::StdRng::seed_from_u64(42)
    }

    fn empty_table() -> SymbolTable {
        SymbolTable::new()
    }

    fn no_params() -> ResolvedParams {
        ResolvedParams::new()
    }

    // -- Construction -------------------------------------------------------

    #[test]
    fn emit_construction() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        assert_eq!(emit.indent, 0);
    }

    // -- RNG convenience ----------------------------------------------------

    #[test]
    fn gen_bool_always_true() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        // prob=1.0 should always be true
        for _ in 0..20 {
            assert!(emit.gen_bool(1.0));
        }
    }

    #[test]
    fn gen_bool_always_false() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        // prob=0.0 should always be false
        for _ in 0..20 {
            assert!(!emit.gen_bool(0.0));
        }
    }

    #[test]
    fn gen_range_single_element() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        // Empty range returns start.
        assert_eq!(emit.gen_range(5..5), 5);
    }

    #[test]
    fn gen_range_in_bounds() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        for _ in 0..50 {
            let val = emit.gen_range(0..10);
            assert!(val < 10);
        }
    }

    #[test]
    fn random_in_bounds() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        for _ in 0..50 {
            let val = emit.random_in(3, 7);
            assert!((3..=7).contains(&val));
        }
    }

    #[test]
    fn random_in_equal_bounds() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        assert_eq!(emit.random_in(5, 5), 5);
    }

    #[test]
    fn shuffle_changes_order_or_preserves_content() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);

        let mut data = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let original = data.clone();
        emit.shuffle(&mut data);
        // Content is preserved.
        let mut sorted = data.clone();
        sorted.sort();
        assert_eq!(sorted, original);
    }

    // -- Indentation --------------------------------------------------------

    #[test]
    fn indent_str_at_zero() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        assert_eq!(emit.indent_str(), "");
    }

    #[test]
    fn indented_increases_and_restores() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        assert_eq!(emit.indent, 0);

        let inner_indent = emit.indented(|e| {
            assert_eq!(e.indent, 1);
            assert_eq!(e.indent_str(), "    ");
            e.indent
        });
        assert_eq!(inner_indent, 1);
        assert_eq!(emit.indent, 0);
    }

    #[test]
    fn nested_indented() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);

        emit.indented(|e| {
            assert_eq!(e.indent_str(), "    ");
            e.indented(|e2| {
                assert_eq!(e2.indent_str(), "        ");
            });
            assert_eq!(e.indent_str(), "    ");
        });
        assert_eq!(emit.indent_str(), "");
    }

    // -- Param resolution ---------------------------------------------------

    #[test]
    fn params_for_missing_rule_returns_empty() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        // Should not panic; returns empty params.
        let _ = emit.params_for("nonexistent_rule");
    }

    #[test]
    fn params_for_existing_rule() {
        let mut rng = test_rng();
        let mut resolved = ResolvedParams::new();
        resolved.insert(
            "my_rule",
            Params::from_iter([("fire_rate", ParamValue::Probability(0.8))]),
        );
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let emit = Emit::new(&mut rng, &stmts, &exprs, &resolved, &table);
        let p = emit.params_for("my_rule");
        assert!((p.prob("fire_rate") - 0.8).abs() < f64::EPSILON);
    }

    // -- Literal generation -------------------------------------------------

    #[test]
    fn literal_i32() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        let lit = emit.literal(&TypeInfo::Primitive(PrimitiveType::I32));
        assert!(lit.ends_with("_i32"), "got: {lit}");
    }

    #[test]
    fn literal_bool() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        let lit = emit.literal(&TypeInfo::Primitive(PrimitiveType::Bool));
        assert!(lit == "true" || lit == "false", "got: {lit}");
    }

    #[test]
    fn literal_string() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        let lit = emit.literal(&TypeInfo::Primitive(PrimitiveType::String));
        assert!(lit.starts_with('"') && lit.ends_with('"'), "got: {lit}");
    }

    #[test]
    fn literal_void() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        assert_eq!(emit.literal(&TypeInfo::Void), "nil");
    }

    #[test]
    fn literal_optional_is_nil_or_inner() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        let ty = TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64)));
        let lit = emit.literal(&ty);
        assert!(lit == "nil" || lit.ends_with("_i64"), "got: {lit}");
    }

    #[test]
    fn literal_array() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        let ty = TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I32)));
        let lit = emit.literal(&ty);
        assert!(lit.starts_with('[') && lit.ends_with(']'), "got: {lit}");
    }

    #[test]
    fn literal_fixed_array() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        let ty = TypeInfo::FixedArray(Box::new(TypeInfo::Primitive(PrimitiveType::Bool)), 3);
        let lit = emit.literal(&ty);
        assert!(lit.contains("; 3]"), "got: {lit}");
    }

    #[test]
    fn literal_tuple() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        let ty = TypeInfo::Tuple(vec![
            TypeInfo::Primitive(PrimitiveType::I32),
            TypeInfo::Primitive(PrimitiveType::Bool),
        ]);
        let lit = emit.literal(&ty);
        assert!(lit.starts_with('[') && lit.ends_with(']'), "got: {lit}");
        assert!(lit.contains(','), "got: {lit}");
    }

    #[test]
    fn literal_fallback_for_unknown_type() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        let ty = TypeInfo::Never;
        let lit = emit.literal(&ty);
        assert!(lit.ends_with("_i64"), "got: {lit}");
    }

    // -- Dispatch fallback ---------------------------------------------------

    #[test]
    fn dispatch_stmt_fallback_when_no_rules() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        let mut scope = Scope::new(&[], &table);
        assert_eq!(emit.sub_stmt(&mut scope), "// skip");
    }

    #[test]
    fn dispatch_expr_fallback_when_no_rules() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        let scope = Scope::new(&[], &table);
        let result = emit.sub_expr(&TypeInfo::Primitive(PrimitiveType::Bool), &scope);
        assert!(result == "true" || result == "false", "got: {result}");
    }

    // -- Dispatch with rules ------------------------------------------------

    /// A test statement rule that always fires and produces "let x = 1".
    struct AlwaysLetRule;

    impl StmtRule for AlwaysLetRule {
        fn name(&self) -> &'static str {
            "always_let"
        }
        fn params(&self) -> Vec<Param> {
            vec![]
        }
        fn generate(
            &self,
            _scope: &mut Scope,
            _emit: &mut Emit,
            _params: &Params,
        ) -> Option<String> {
            Some("let x = 1".to_string())
        }
    }

    /// A test expression rule that fires only for bool and returns "true".
    struct AlwaysTrueRule;

    impl ExprRule for AlwaysTrueRule {
        fn name(&self) -> &'static str {
            "always_true"
        }
        fn params(&self) -> Vec<Param> {
            vec![]
        }
        fn precondition(&self, _scope: &Scope, _params: &Params) -> bool {
            true
        }
        fn generate(
            &self,
            _scope: &Scope,
            _emit: &mut Emit,
            _params: &Params,
            _expected_type: &TypeInfo,
        ) -> Option<String> {
            Some("true".to_string())
        }
    }

    #[test]
    fn dispatch_stmt_fires_registered_rule() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![Box::new(AlwaysLetRule)];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        let mut scope = Scope::new(&[], &table);
        assert_eq!(emit.sub_stmt(&mut scope), "let x = 1");
    }

    #[test]
    fn dispatch_expr_fires_registered_rule() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![Box::new(AlwaysTrueRule)];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        let scope = Scope::new(&[], &table);
        let result = emit.sub_expr(&TypeInfo::Primitive(PrimitiveType::Bool), &scope);
        assert_eq!(result, "true");
    }

    /// A rule that always returns None (fails to generate).
    struct NeverFiresRule;

    impl StmtRule for NeverFiresRule {
        fn name(&self) -> &'static str {
            "never_fires"
        }
        fn params(&self) -> Vec<Param> {
            vec![]
        }
        fn generate(
            &self,
            _scope: &mut Scope,
            _emit: &mut Emit,
            _params: &Params,
        ) -> Option<String> {
            None
        }
    }

    #[test]
    fn dispatch_stmt_falls_back_when_rule_returns_none() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![Box::new(NeverFiresRule)];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        let mut scope = Scope::new(&[], &table);
        assert_eq!(emit.sub_stmt(&mut scope), "// skip");
    }

    /// A rule whose precondition always fails.
    struct GatedStmtRule;

    impl StmtRule for GatedStmtRule {
        fn name(&self) -> &'static str {
            "gated_stmt"
        }
        fn params(&self) -> Vec<Param> {
            vec![]
        }
        fn precondition(&self, _scope: &Scope, _params: &Params) -> bool {
            false
        }
        fn generate(
            &self,
            _scope: &mut Scope,
            _emit: &mut Emit,
            _params: &Params,
        ) -> Option<String> {
            Some("should not appear".to_string())
        }
    }

    #[test]
    fn dispatch_skips_rule_when_precondition_fails() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![Box::new(GatedStmtRule)];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        let mut scope = Scope::new(&[], &table);
        // Gated rule won't fire, so we get fallback.
        assert_eq!(emit.sub_stmt(&mut scope), "// skip");
    }

    // -- Block generation ---------------------------------------------------

    #[test]
    fn block_with_no_rules_produces_skip_comments() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        let mut scope = Scope::new(&[], &table);
        let block = emit.block(&mut scope, 3);
        let lines: Vec<&str> = block.lines().collect();
        assert_eq!(lines.len(), 3);
        for line in &lines {
            assert!(line.contains("// skip"), "line was: {line}");
            // Should be indented one level.
            assert!(line.starts_with("    "), "line was: {line}");
        }
    }

    #[test]
    fn block_with_zero_stmts() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        let mut scope = Scope::new(&[], &table);
        let block = emit.block(&mut scope, 0);
        assert!(block.is_empty());
    }

    #[test]
    fn block_indentation_nests_correctly() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![Box::new(AlwaysLetRule)];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        let mut scope = Scope::new(&[], &table);

        // A block at indent level 0 should have 1 level of indent.
        let block = emit.block(&mut scope, 1);
        assert!(block.starts_with("    "), "got: {block}");
    }

    // -- Dispatch with recursive sub-generation -----------------------------

    /// A statement rule that calls emit.sub_expr to recurse.
    struct RecursiveStmtRule;

    impl StmtRule for RecursiveStmtRule {
        fn name(&self) -> &'static str {
            "recursive_stmt"
        }
        fn params(&self) -> Vec<Param> {
            vec![]
        }
        fn generate(
            &self,
            _scope: &mut Scope,
            emit: &mut Emit,
            _params: &Params,
        ) -> Option<String> {
            let expr = emit.literal(&TypeInfo::Primitive(PrimitiveType::I32));
            Some(format!("let y = {}", expr))
        }
    }

    #[test]
    fn rule_can_call_emit_sub_methods() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![Box::new(RecursiveStmtRule)];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);
        let mut scope = Scope::new(&[], &table);
        let result = emit.sub_stmt(&mut scope);
        assert!(result.starts_with("let y = "), "got: {result}");
        assert!(result.contains("_i32"), "got: {result}");
    }

    // -- All primitive literal types ----------------------------------------

    #[test]
    fn literal_covers_all_primitive_types() {
        let mut rng = test_rng();
        let params = no_params();
        let stmts: Vec<Box<dyn StmtRule>> = vec![];
        let exprs: Vec<Box<dyn ExprRule>> = vec![];
        let table = empty_table();
        let mut emit = Emit::new(&mut rng, &stmts, &exprs, &params, &table);

        let cases = [
            (PrimitiveType::I8, "_i8"),
            (PrimitiveType::I16, "_i16"),
            (PrimitiveType::I32, "_i32"),
            (PrimitiveType::I64, "_i64"),
            (PrimitiveType::I128, "_i128"),
            (PrimitiveType::U8, "_u8"),
            (PrimitiveType::U16, "_u16"),
            (PrimitiveType::U32, "_u32"),
            (PrimitiveType::U64, "_u64"),
            (PrimitiveType::F32, "_f32"),
            (PrimitiveType::F64, "_f64"),
        ];

        for (prim, suffix) in cases {
            let lit = emit.literal(&TypeInfo::Primitive(prim));
            assert!(lit.ends_with(suffix), "{:?} => {lit}", prim);
        }

        // Nil
        let lit = emit.literal(&TypeInfo::Primitive(PrimitiveType::Nil));
        assert_eq!(lit, "nil");
    }
}
