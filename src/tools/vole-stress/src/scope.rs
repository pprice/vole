//! Scope abstraction for vole-stress code generation.
//!
//! `Scope` replaces the raw `StmtContext`/`ExprContext` pair with a single
//! struct that carries all in-scope variable, type, and control-flow context.
//! Statement rules receive `&mut Scope` (may add locals), expression rules
//! receive `&Scope` (read-only).

use rand::Rng;

use crate::symbols::{ModuleId, ParamInfo, Symbol, SymbolId, SymbolTable, TypeInfo, TypeParam};

// ---------------------------------------------------------------------------
// VarSource
// ---------------------------------------------------------------------------

/// Where a variable binding originated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarSource {
    /// A function/method parameter.
    Param,
    /// A local `let` binding.
    Local,
}

// ---------------------------------------------------------------------------
// VarInfo
// ---------------------------------------------------------------------------

/// A variable visible in the current scope.
#[derive(Debug, Clone)]
pub struct VarInfo {
    /// The binding name.
    pub name: String,
    /// The type of the variable.
    pub type_info: TypeInfo,
    /// Whether the variable was declared as mutable.
    pub is_mutable: bool,
    /// Whether the variable came from a parameter or a local binding.
    pub source: VarSource,
}

// ---------------------------------------------------------------------------
// Scope
// ---------------------------------------------------------------------------

/// Tracks all in-scope state needed by statement and expression rules.
///
/// Created once per function body and threaded through generation.
/// Statement rules receive `&mut Scope` (may call [`add_local`](Scope::add_local)),
/// expression rules receive `&Scope`.
#[allow(dead_code)]
pub struct Scope<'a> {
    /// Parameters in scope.
    pub params: &'a [ParamInfo],
    /// Local variables: `(name, type, is_mutable)`.
    pub locals: Vec<(String, TypeInfo, bool)>,
    /// Symbol table for type and symbol lookups.
    pub table: &'a SymbolTable,
    /// The module currently being generated (for class lookups).
    pub module_id: Option<ModuleId>,
    /// Whether we are inside a loop body (break/continue valid).
    pub in_loop: bool,
    /// Whether the innermost loop is a `while` loop.
    pub in_while_loop: bool,
    /// Whether the enclosing function is fallible.
    pub is_fallible: bool,
    /// The error type of the enclosing fallible function, if any.
    pub fallible_error_type: Option<TypeInfo>,
    /// Counter for generating unique local variable names (`local0`, `local1`, ...).
    pub local_counter: usize,
    /// Name of the function being generated (to prevent self-recursion).
    pub current_function_name: Option<String>,
    /// Symbol ID of the free function being generated (ordering guard).
    pub current_function_sym_id: Option<SymbolId>,
    /// Class whose method body is being generated (mutual-recursion guard).
    pub current_class_sym_id: Option<(ModuleId, SymbolId)>,
    /// Variables that must not be modified by compound assignments.
    pub protected_vars: Vec<String>,
    /// Effective return type (success type for fallible functions).
    pub return_type: Option<TypeInfo>,
    /// Type parameters of the current generic function.
    pub type_params: Vec<TypeParam>,
    /// Whether `std:lowlevel` functions are available in this module.
    pub has_lowlevel_import: bool,
    /// Current nesting depth.
    pub depth: usize,
    /// Maximum allowed nesting depth.
    pub max_depth: usize,
}

// ---------------------------------------------------------------------------
// Constructors
// ---------------------------------------------------------------------------

#[allow(dead_code)]
impl<'a> Scope<'a> {
    /// Create a scope with a module context (the common production path).
    pub fn with_module(
        params: &'a [ParamInfo],
        table: &'a SymbolTable,
        module_id: ModuleId,
    ) -> Self {
        Self {
            params,
            locals: Vec::new(),
            table,
            module_id: Some(module_id),
            in_loop: false,
            in_while_loop: false,
            is_fallible: false,
            fallible_error_type: None,
            local_counter: 0,
            current_function_name: None,
            current_function_sym_id: None,
            current_class_sym_id: None,
            protected_vars: Vec::new(),
            return_type: None,
            type_params: Vec::new(),
            has_lowlevel_import: false,
            depth: 0,
            max_depth: 8,
        }
    }

    /// Create a minimal scope for testing (no module context).
    #[cfg(test)]
    pub fn new(params: &'a [ParamInfo], table: &'a SymbolTable) -> Self {
        Self {
            params,
            locals: Vec::new(),
            table,
            module_id: None,
            in_loop: false,
            in_while_loop: false,
            is_fallible: false,
            fallible_error_type: None,
            local_counter: 0,
            current_function_name: None,
            current_function_sym_id: None,
            current_class_sym_id: None,
            protected_vars: Vec::new(),
            return_type: None,
            type_params: Vec::new(),
            has_lowlevel_import: false,
            depth: 0,
            max_depth: 8,
        }
    }
}

// ---------------------------------------------------------------------------
// Variable queries
// ---------------------------------------------------------------------------

#[allow(dead_code)]
impl Scope<'_> {
    /// Pick a random variable whose type matches `ty` exactly.
    ///
    /// Returns `None` when no variable of that type is in scope.
    pub fn pick_var_of_type<R: Rng>(&self, ty: &TypeInfo, rng: &mut R) -> Option<VarInfo> {
        let matches: Vec<VarInfo> = self.vars_of_type(ty);
        if matches.is_empty() {
            return None;
        }
        Some(matches[rng.gen_range(0..matches.len())].clone())
    }

    /// Pick a random variable satisfying `predicate`.
    ///
    /// Returns `None` when no matching variable is in scope.
    pub fn pick_var_matching<R, F>(&self, predicate: F, rng: &mut R) -> Option<VarInfo>
    where
        R: Rng,
        F: Fn(&VarInfo) -> bool,
    {
        let matches: Vec<VarInfo> = self.vars_matching(predicate);
        if matches.is_empty() {
            return None;
        }
        Some(matches[rng.gen_range(0..matches.len())].clone())
    }

    /// Return all variables whose type matches `ty` exactly.
    pub fn vars_of_type(&self, ty: &TypeInfo) -> Vec<VarInfo> {
        self.vars_matching(|v| types_match(&v.type_info, ty))
    }

    /// Return all variables satisfying `predicate`.
    pub fn vars_matching<F: Fn(&VarInfo) -> bool>(&self, predicate: F) -> Vec<VarInfo> {
        let mut out = Vec::new();
        for (name, local_ty, is_mut) in &self.locals {
            let info = VarInfo {
                name: name.clone(),
                type_info: local_ty.clone(),
                is_mutable: *is_mut,
                source: VarSource::Local,
            };
            if predicate(&info) {
                out.push(info);
            }
        }
        for param in self.params {
            let info = VarInfo {
                name: param.name.clone(),
                type_info: param.param_type.clone(),
                is_mutable: false,
                source: VarSource::Param,
            };
            if predicate(&info) {
                out.push(info);
            }
        }
        out
    }

    /// Check whether at least one variable of the given type exists.
    pub fn has_var_of_type(&self, ty: &TypeInfo) -> bool {
        self.locals.iter().any(|(_, t, _)| types_match(t, ty))
            || self.params.iter().any(|p| types_match(&p.param_type, ty))
    }
}

// ---------------------------------------------------------------------------
// Name generation and local registration
// ---------------------------------------------------------------------------

#[allow(dead_code)]
impl Scope<'_> {
    /// Generate a fresh local name (`local0`, `local1`, ...).
    pub fn fresh_name(&mut self) -> String {
        let name = format!("local{}", self.local_counter);
        self.local_counter += 1;
        name
    }

    /// Register a new local variable in this scope.
    pub fn add_local(&mut self, name: String, type_info: TypeInfo, is_mutable: bool) {
        self.locals.push((name, type_info, is_mutable));
    }
}

// ---------------------------------------------------------------------------
// Symbol table delegation
// ---------------------------------------------------------------------------

#[allow(dead_code)]
impl Scope<'_> {
    /// Look up a symbol by module and symbol ID.
    pub fn lookup_symbol(&self, mod_id: ModuleId, sym_id: SymbolId) -> Option<&Symbol> {
        self.table.get_symbol(mod_id, sym_id)
    }
}

// ---------------------------------------------------------------------------
// Context queries
// ---------------------------------------------------------------------------

#[allow(dead_code)]
impl Scope<'_> {
    /// Whether we are generating a method body for a generic class.
    ///
    /// Closures that capture variables inside generic class methods hit a
    /// compiler bug ("Captured variable not found"), so closure-related rules
    /// should return `None` when this is `true`.
    pub fn is_in_generic_class_method(&self) -> bool {
        use crate::symbols::SymbolKind;

        if let Some((cls_mod, cls_sym)) = self.current_class_sym_id
            && let Some(symbol) = self.table.get_symbol(cls_mod, cls_sym)
            && let SymbolKind::Class(info) = &symbol.kind
            && !info.type_params.is_empty()
        {
            return true;
        }
        false
    }

    /// Get all array-typed variables in scope with their element type.
    ///
    /// Returns `(name, element_type)` pairs for variables of type `[T]`.
    pub fn array_vars(&self) -> Vec<(String, TypeInfo)> {
        let mut vars = Vec::new();
        for (name, ty, _) in &self.locals {
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

    /// Get all variables whose type is a constrained type parameter.
    ///
    /// Returns `(var_name, type_param_name, interface_constraints)` triples.
    pub fn constrained_type_param_vars(&self) -> Vec<(String, String, Vec<(ModuleId, SymbolId)>)> {
        let mut vars = Vec::new();
        for param in self.params {
            if let TypeInfo::TypeParam(tp_name) = &param.param_type {
                for tp in &self.type_params {
                    if &tp.name == tp_name && !tp.constraints.is_empty() {
                        vars.push((param.name.clone(), tp_name.clone(), tp.constraints.clone()));
                    }
                }
            }
        }
        vars
    }
}

// ---------------------------------------------------------------------------
// Depth tracking
// ---------------------------------------------------------------------------

#[allow(dead_code)]
impl Scope<'_> {
    /// Whether the current depth still allows further recursion.
    pub fn can_recurse(&self) -> bool {
        self.depth < self.max_depth
    }

    /// The current nesting depth.
    pub fn depth(&self) -> usize {
        self.depth
    }
}

// ---------------------------------------------------------------------------
// Scoped state save/restore
// ---------------------------------------------------------------------------

#[allow(dead_code)]
impl Scope<'_> {
    /// Execute `body` inside a nested scope that saves and restores
    /// local variables and loop/depth state.
    ///
    /// Any locals added inside `body` are removed when it returns.
    /// The `in_loop`, `in_while_loop`, and `depth` fields are also
    /// restored to their prior values.
    pub fn enter_scope<R>(&mut self, body: impl FnOnce(&mut Self) -> R) -> R {
        let saved_locals_len = self.locals.len();
        let saved_in_loop = self.in_loop;
        let saved_in_while_loop = self.in_while_loop;
        let saved_depth = self.depth;
        let saved_protected_len = self.protected_vars.len();

        self.depth += 1;

        let result = body(self);

        self.locals.truncate(saved_locals_len);
        self.in_loop = saved_in_loop;
        self.in_while_loop = saved_in_while_loop;
        self.depth = saved_depth;
        self.protected_vars.truncate(saved_protected_len);

        result
    }
}

// ---------------------------------------------------------------------------
// Private helpers
// ---------------------------------------------------------------------------

/// Structural type equality (same as `stmt::types_match`).
fn types_match(a: &TypeInfo, b: &TypeInfo) -> bool {
    match (a, b) {
        (TypeInfo::Primitive(pa), TypeInfo::Primitive(pb)) => pa == pb,
        (TypeInfo::Void, TypeInfo::Void) => true,
        (TypeInfo::Optional(ia), TypeInfo::Optional(ib)) => types_match(ia, ib),
        (TypeInfo::Array(ea), TypeInfo::Array(eb)) => types_match(ea, eb),
        (TypeInfo::FixedArray(ea, sa), TypeInfo::FixedArray(eb, sb)) => {
            sa == sb && types_match(ea, eb)
        }
        (TypeInfo::Tuple(ea), TypeInfo::Tuple(eb)) => {
            ea.len() == eb.len() && ea.iter().zip(eb.iter()).all(|(a, b)| types_match(a, b))
        }
        (TypeInfo::Class(ma, sa), TypeInfo::Class(mb, sb)) => ma == mb && sa == sb,
        (TypeInfo::Struct(ma, sa), TypeInfo::Struct(mb, sb)) => ma == mb && sa == sb,
        (TypeInfo::Interface(ma, sa), TypeInfo::Interface(mb, sb)) => ma == mb && sa == sb,
        (TypeInfo::Error(ma, sa), TypeInfo::Error(mb, sb)) => ma == mb && sa == sb,
        (TypeInfo::Sentinel(ma, sa), TypeInfo::Sentinel(mb, sb)) => ma == mb && sa == sb,
        (TypeInfo::Union(va), TypeInfo::Union(vb)) => {
            va.len() == vb.len() && va.iter().zip(vb.iter()).all(|(a, b)| types_match(a, b))
        }
        (
            TypeInfo::Fallible {
                success: sa,
                error: ea,
            },
            TypeInfo::Fallible {
                success: sb,
                error: eb,
            },
        ) => types_match(sa, sb) && types_match(ea, eb),
        (TypeInfo::Iterator(ea), TypeInfo::Iterator(eb)) => types_match(ea, eb),
        (TypeInfo::Never, TypeInfo::Never) => true,
        (TypeInfo::TypeParam(a), TypeInfo::TypeParam(b)) => a == b,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbols::PrimitiveType;

    fn empty_table() -> SymbolTable {
        SymbolTable::new()
    }

    // -- Construction -------------------------------------------------------

    #[test]
    fn new_scope_has_no_locals() {
        let table = empty_table();
        let scope = Scope::new(&[], &table);
        assert!(scope.locals.is_empty());
        assert_eq!(scope.depth, 0);
        assert!(!scope.in_loop);
    }

    #[test]
    fn with_module_sets_module_id() {
        let mut table = SymbolTable::new();
        let mod_id = table.add_module("m".into(), "m.vole".into());
        let scope = Scope::with_module(&[], &table, mod_id);
        assert_eq!(scope.module_id, Some(mod_id));
    }

    // -- fresh_name ---------------------------------------------------------

    #[test]
    fn fresh_name_increments() {
        let table = empty_table();
        let mut scope = Scope::new(&[], &table);
        assert_eq!(scope.fresh_name(), "local0");
        assert_eq!(scope.fresh_name(), "local1");
        assert_eq!(scope.fresh_name(), "local2");
    }

    // -- add_local ----------------------------------------------------------

    #[test]
    fn add_local_visible_in_locals() {
        let table = empty_table();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        assert_eq!(scope.locals.len(), 1);
        assert_eq!(scope.locals[0].0, "x");
    }

    // -- has_var_of_type ----------------------------------------------------

    #[test]
    fn has_var_of_type_from_local() {
        let table = empty_table();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("n".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        assert!(scope.has_var_of_type(&TypeInfo::Primitive(PrimitiveType::I64)));
        assert!(!scope.has_var_of_type(&TypeInfo::Primitive(PrimitiveType::Bool)));
    }

    #[test]
    fn has_var_of_type_from_param() {
        let table = empty_table();
        let params = [ParamInfo {
            name: "p".into(),
            param_type: TypeInfo::Primitive(PrimitiveType::String),
        }];
        let scope = Scope::new(&params, &table);
        assert!(scope.has_var_of_type(&TypeInfo::Primitive(PrimitiveType::String)));
        assert!(!scope.has_var_of_type(&TypeInfo::Primitive(PrimitiveType::I32)));
    }

    // -- vars_of_type -------------------------------------------------------

    #[test]
    fn vars_of_type_includes_params_and_locals() {
        let table = empty_table();
        let params = [ParamInfo {
            name: "a".into(),
            param_type: TypeInfo::Primitive(PrimitiveType::I64),
        }];
        let mut scope = Scope::new(&params, &table);
        scope.add_local("b".into(), TypeInfo::Primitive(PrimitiveType::I64), true);
        scope.add_local("c".into(), TypeInfo::Primitive(PrimitiveType::Bool), false);

        let i64_vars = scope.vars_of_type(&TypeInfo::Primitive(PrimitiveType::I64));
        let names: Vec<&str> = i64_vars.iter().map(|v| v.name.as_str()).collect();
        assert_eq!(names, vec!["b", "a"]);
    }

    // -- vars_matching ------------------------------------------------------

    #[test]
    fn vars_matching_filters_by_predicate() {
        let table = empty_table();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), true);
        scope.add_local("y".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mutable = scope.vars_matching(|v| v.is_mutable);
        assert_eq!(mutable.len(), 1);
        assert_eq!(mutable[0].name, "x");
    }

    // -- pick_var_of_type ---------------------------------------------------

    #[test]
    fn pick_var_of_type_returns_some_when_present() {
        let table = empty_table();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("v".into(), TypeInfo::Primitive(PrimitiveType::Bool), false);

        let mut rng = rand::rngs::mock::StepRng::new(0, 1);
        let picked = scope.pick_var_of_type(&TypeInfo::Primitive(PrimitiveType::Bool), &mut rng);
        assert!(picked.is_some());
        assert_eq!(picked.unwrap().name, "v");
    }

    #[test]
    fn pick_var_of_type_returns_none_when_absent() {
        let table = empty_table();
        let scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::mock::StepRng::new(0, 1);
        let picked = scope.pick_var_of_type(&TypeInfo::Primitive(PrimitiveType::I32), &mut rng);
        assert!(picked.is_none());
    }

    // -- pick_var_matching --------------------------------------------------

    #[test]
    fn pick_var_matching_returns_match() {
        let table = empty_table();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("m".into(), TypeInfo::Primitive(PrimitiveType::I64), true);
        scope.add_local("n".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::mock::StepRng::new(0, 1);
        let picked = scope.pick_var_matching(|v| v.is_mutable, &mut rng);
        assert!(picked.is_some());
        assert_eq!(picked.unwrap().name, "m");
    }

    // -- VarInfo source tagging ---------------------------------------------

    #[test]
    fn var_source_distinguishes_param_from_local() {
        let table = empty_table();
        let params = [ParamInfo {
            name: "p".into(),
            param_type: TypeInfo::Primitive(PrimitiveType::I32),
        }];
        let mut scope = Scope::new(&params, &table);
        scope.add_local("l".into(), TypeInfo::Primitive(PrimitiveType::I32), false);

        let all = scope.vars_of_type(&TypeInfo::Primitive(PrimitiveType::I32));
        assert_eq!(all.len(), 2);

        let local_var = all.iter().find(|v| v.name == "l").unwrap();
        assert_eq!(local_var.source, VarSource::Local);

        let param_var = all.iter().find(|v| v.name == "p").unwrap();
        assert_eq!(param_var.source, VarSource::Param);
    }

    // -- lookup_symbol ------------------------------------------------------

    #[test]
    fn lookup_symbol_delegates_to_table() {
        use crate::symbols::{FunctionInfo, SymbolKind};

        let mut table = SymbolTable::new();
        let mod_id = table.add_module("m".into(), "m.vole".into());
        let sym_id = table.get_module_mut(mod_id).unwrap().add_symbol(
            "foo".into(),
            SymbolKind::Function(FunctionInfo {
                type_params: vec![],
                params: vec![],
                return_type: TypeInfo::Void,
            }),
        );

        let scope = Scope::with_module(&[], &table, mod_id);
        let sym = scope.lookup_symbol(mod_id, sym_id).unwrap();
        assert_eq!(sym.name, "foo");
    }

    // -- can_recurse / depth ------------------------------------------------

    #[test]
    fn can_recurse_respects_max_depth() {
        let table = empty_table();
        let mut scope = Scope::new(&[], &table);
        scope.max_depth = 2;
        assert!(scope.can_recurse());

        scope.depth = 1;
        assert!(scope.can_recurse());

        scope.depth = 2;
        assert!(!scope.can_recurse());
    }

    #[test]
    fn depth_returns_current_depth() {
        let table = empty_table();
        let mut scope = Scope::new(&[], &table);
        assert_eq!(scope.depth(), 0);
        scope.depth = 5;
        assert_eq!(scope.depth(), 5);
    }

    // -- enter_scope --------------------------------------------------------

    #[test]
    fn enter_scope_restores_locals() {
        let table = empty_table();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "outer".into(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        scope.enter_scope(|inner| {
            inner.add_local(
                "inner".into(),
                TypeInfo::Primitive(PrimitiveType::Bool),
                false,
            );
            assert_eq!(inner.locals.len(), 2);
        });

        assert_eq!(scope.locals.len(), 1);
        assert_eq!(scope.locals[0].0, "outer");
    }

    #[test]
    fn enter_scope_restores_loop_state() {
        let table = empty_table();
        let mut scope = Scope::new(&[], &table);
        assert!(!scope.in_loop);

        scope.enter_scope(|inner| {
            inner.in_loop = true;
            inner.in_while_loop = true;
            assert!(inner.in_loop);
        });

        assert!(!scope.in_loop);
        assert!(!scope.in_while_loop);
    }

    #[test]
    fn enter_scope_increments_and_restores_depth() {
        let table = empty_table();
        let mut scope = Scope::new(&[], &table);
        assert_eq!(scope.depth, 0);

        scope.enter_scope(|inner| {
            assert_eq!(inner.depth, 1);
            inner.enter_scope(|inner2| {
                assert_eq!(inner2.depth, 2);
            });
            assert_eq!(inner.depth, 1);
        });

        assert_eq!(scope.depth, 0);
    }

    #[test]
    fn enter_scope_restores_protected_vars() {
        let table = empty_table();
        let mut scope = Scope::new(&[], &table);
        scope.protected_vars.push("outer_guard".into());

        scope.enter_scope(|inner| {
            inner.protected_vars.push("inner_guard".into());
            assert_eq!(inner.protected_vars.len(), 2);
        });

        assert_eq!(scope.protected_vars.len(), 1);
        assert_eq!(scope.protected_vars[0], "outer_guard");
    }

    #[test]
    fn enter_scope_returns_body_value() {
        let table = empty_table();
        let mut scope = Scope::new(&[], &table);
        let result = scope.enter_scope(|_| 42);
        assert_eq!(result, 42);
    }

    // -- types_match covers --------------------------------------------------

    #[test]
    fn types_match_optional() {
        let a = TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64)));
        let b = TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64)));
        let c = TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::Bool)));
        assert!(types_match(&a, &b));
        assert!(!types_match(&a, &c));
    }

    #[test]
    fn types_match_array() {
        let a = TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I32)));
        let b = TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I32)));
        let c = TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String)));
        assert!(types_match(&a, &b));
        assert!(!types_match(&a, &c));
    }

    #[test]
    fn types_match_fixed_array() {
        let a = TypeInfo::FixedArray(Box::new(TypeInfo::Primitive(PrimitiveType::I64)), 3);
        let b = TypeInfo::FixedArray(Box::new(TypeInfo::Primitive(PrimitiveType::I64)), 3);
        let c = TypeInfo::FixedArray(Box::new(TypeInfo::Primitive(PrimitiveType::I64)), 4);
        assert!(types_match(&a, &b));
        assert!(!types_match(&a, &c));
    }

    #[test]
    fn types_match_tuple() {
        let a = TypeInfo::Tuple(vec![
            TypeInfo::Primitive(PrimitiveType::I64),
            TypeInfo::Primitive(PrimitiveType::Bool),
        ]);
        let b = TypeInfo::Tuple(vec![
            TypeInfo::Primitive(PrimitiveType::I64),
            TypeInfo::Primitive(PrimitiveType::Bool),
        ]);
        let c = TypeInfo::Tuple(vec![TypeInfo::Primitive(PrimitiveType::I64)]);
        assert!(types_match(&a, &b));
        assert!(!types_match(&a, &c));
    }

    #[test]
    fn types_match_class_and_struct() {
        let m = ModuleId(0);
        let s1 = SymbolId(1);
        let s2 = SymbolId(2);
        assert!(types_match(
            &TypeInfo::Class(m, s1),
            &TypeInfo::Class(m, s1)
        ));
        assert!(!types_match(
            &TypeInfo::Class(m, s1),
            &TypeInfo::Class(m, s2)
        ));
        assert!(types_match(
            &TypeInfo::Struct(m, s1),
            &TypeInfo::Struct(m, s1)
        ));
        assert!(!types_match(
            &TypeInfo::Class(m, s1),
            &TypeInfo::Struct(m, s1)
        ));
    }

    #[test]
    fn types_match_interface_error_sentinel() {
        let m = ModuleId(0);
        let s = SymbolId(0);
        assert!(types_match(
            &TypeInfo::Interface(m, s),
            &TypeInfo::Interface(m, s)
        ));
        assert!(types_match(&TypeInfo::Error(m, s), &TypeInfo::Error(m, s)));
        assert!(types_match(
            &TypeInfo::Sentinel(m, s),
            &TypeInfo::Sentinel(m, s)
        ));
    }

    #[test]
    fn types_match_union() {
        let a = TypeInfo::Union(vec![
            TypeInfo::Primitive(PrimitiveType::I64),
            TypeInfo::Primitive(PrimitiveType::String),
        ]);
        let b = TypeInfo::Union(vec![
            TypeInfo::Primitive(PrimitiveType::I64),
            TypeInfo::Primitive(PrimitiveType::String),
        ]);
        let c = TypeInfo::Union(vec![TypeInfo::Primitive(PrimitiveType::I64)]);
        assert!(types_match(&a, &b));
        assert!(!types_match(&a, &c));
    }

    #[test]
    fn types_match_fallible() {
        let a = TypeInfo::Fallible {
            success: Box::new(TypeInfo::Primitive(PrimitiveType::I64)),
            error: Box::new(TypeInfo::Primitive(PrimitiveType::String)),
        };
        let b = TypeInfo::Fallible {
            success: Box::new(TypeInfo::Primitive(PrimitiveType::I64)),
            error: Box::new(TypeInfo::Primitive(PrimitiveType::String)),
        };
        let c = TypeInfo::Fallible {
            success: Box::new(TypeInfo::Primitive(PrimitiveType::Bool)),
            error: Box::new(TypeInfo::Primitive(PrimitiveType::String)),
        };
        assert!(types_match(&a, &b));
        assert!(!types_match(&a, &c));
    }

    #[test]
    fn types_match_iterator() {
        let a = TypeInfo::Iterator(Box::new(TypeInfo::Primitive(PrimitiveType::I32)));
        let b = TypeInfo::Iterator(Box::new(TypeInfo::Primitive(PrimitiveType::I32)));
        let c = TypeInfo::Iterator(Box::new(TypeInfo::Primitive(PrimitiveType::Bool)));
        assert!(types_match(&a, &b));
        assert!(!types_match(&a, &c));
    }

    #[test]
    fn types_match_never_and_type_param() {
        assert!(types_match(&TypeInfo::Never, &TypeInfo::Never));
        assert!(types_match(
            &TypeInfo::TypeParam("T".into()),
            &TypeInfo::TypeParam("T".into())
        ));
        assert!(!types_match(
            &TypeInfo::TypeParam("T".into()),
            &TypeInfo::TypeParam("U".into())
        ));
    }
}
