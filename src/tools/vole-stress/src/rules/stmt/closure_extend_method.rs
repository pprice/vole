//! Rule: closures capturing structs and calling extend methods.
//!
//! Exercises the interaction between closure captures and extend-method dispatch.
//! Generated output shapes:
//! - `let result = () => var.getter()` + `let val = result()` (closure + invoke)
//! - `let results = arr.iter().map((v: Type) => v.getter()).collect()` (map over struct array)
//! - `let result = () => var.method(prim)` + `let val = result()` (closure capturing struct + primitive)

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{MethodInfo, SymbolId, SymbolKind, TypeInfo};

pub struct ClosureExtendMethod;

impl StmtRule for ClosureExtendMethod {
    fn name(&self) -> &'static str {
        "closure_extend_method"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let _ = scope.module_id?;

        let variant = emit.gen_range(0..3);

        match variant {
            0 => generate_closure_getter(scope, emit),
            1 => generate_map_over_struct_array(scope, emit),
            _ => generate_closure_with_param(scope, emit),
        }
    }
}

/// Variant 1: Closure capturing a struct and calling a getter extend method.
///
/// ```vole
/// let result = () => var.getter_method()
/// let val = result()
/// ```
fn generate_closure_getter(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let candidates = find_struct_with_getter_extend_methods(scope);
    if candidates.is_empty() {
        return None;
    }

    let idx = emit.gen_range(0..candidates.len());
    let (var_name, _struct_type, methods) = &candidates[idx];

    // Pick a getter method (non-void, no extra params)
    let no_param_getters: Vec<&MethodInfo> = methods
        .iter()
        .filter(|m| !matches!(m.return_type, TypeInfo::Void) && m.params.is_empty())
        .collect();

    let method = if !no_param_getters.is_empty() {
        no_param_getters[emit.gen_range(0..no_param_getters.len())]
    } else {
        // Fall back to any non-void method, generate literal args
        let getters: Vec<&MethodInfo> = methods
            .iter()
            .filter(|m| !matches!(m.return_type, TypeInfo::Void))
            .collect();
        if getters.is_empty() {
            return None;
        }
        getters[emit.gen_range(0..getters.len())]
    };

    let args: Vec<String> = method
        .params
        .iter()
        .map(|p| emit.literal(&p.param_type))
        .collect();

    let closure_name = scope.fresh_name();
    let result_name = scope.fresh_name();
    let ret_type = method.return_type.clone();

    // Register the closure variable (function type returning ret_type)
    scope.add_local(
        closure_name.clone(),
        TypeInfo::Function {
            param_types: vec![],
            return_type: Box::new(ret_type.clone()),
        },
        false,
    );
    scope.add_local(result_name.clone(), ret_type, false);

    Some(format!(
        "let {} = () => {}.{}({})\nlet {} = {}()",
        closure_name,
        var_name,
        method.name,
        args.join(", "),
        result_name,
        closure_name,
    ))
}

/// Variant 2: Map over an array of structs, calling a getter extend method.
///
/// ```vole
/// let results = arr.iter().map((v: StructType) => v.getter()).collect()
/// ```
fn generate_map_over_struct_array(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let module_id = scope.module_id?;

    // Find array-of-struct variables where the struct has getter extend methods
    let mut candidates: Vec<(String, String, SymbolId, Vec<MethodInfo>)> = Vec::new();

    for (name, ty, _) in &scope.locals {
        if let TypeInfo::Array(elem) = ty {
            if let TypeInfo::Struct(mod_id, sym_id) = elem.as_ref() {
                if *mod_id == module_id {
                    if let Some(struct_sym) = scope.table.get_symbol(*mod_id, *sym_id) {
                        let struct_name = struct_sym.name.clone();
                        let methods = collect_getter_extend_methods(scope, *mod_id, *sym_id);
                        if !methods.is_empty() {
                            candidates.push((name.clone(), struct_name, *sym_id, methods));
                        }
                    }
                }
            }
        }
    }

    // Also check params
    for param in scope.params {
        if let TypeInfo::Array(elem) = &param.param_type {
            if let TypeInfo::Struct(mod_id, sym_id) = elem.as_ref() {
                if *mod_id == module_id {
                    if let Some(struct_sym) = scope.table.get_symbol(*mod_id, *sym_id) {
                        let struct_name = struct_sym.name.clone();
                        let methods = collect_getter_extend_methods(scope, *mod_id, *sym_id);
                        if !methods.is_empty() {
                            candidates.push((param.name.clone(), struct_name, *sym_id, methods));
                        }
                    }
                }
            }
        }
    }

    if candidates.is_empty() {
        // Fall back to variant 1 if no struct arrays
        return generate_closure_getter(scope, emit);
    }

    let idx = emit.gen_range(0..candidates.len());
    let (arr_name, struct_name, _sym_id, methods) = &candidates[idx];

    // Pick a no-param getter for clean map syntax
    let no_param_getters: Vec<&MethodInfo> =
        methods.iter().filter(|m| m.params.is_empty()).collect();

    let method = if !no_param_getters.is_empty() {
        no_param_getters[emit.gen_range(0..no_param_getters.len())]
    } else {
        &methods[emit.gen_range(0..methods.len())]
    };

    let args: Vec<String> = method
        .params
        .iter()
        .map(|p| emit.literal(&p.param_type))
        .collect();

    let result_name = scope.fresh_name();
    let ret_type = method.return_type.clone();

    scope.add_local(
        result_name.clone(),
        TypeInfo::Array(Box::new(ret_type)),
        false,
    );

    let args_str = if args.is_empty() {
        String::new()
    } else {
        args.join(", ")
    };

    Some(format!(
        "let {} = {}.iter().map((v: {}) => v.{}({})).collect()",
        result_name, arr_name, struct_name, method.name, args_str,
    ))
}

/// Variant 3: Closure capturing a struct + a primitive, calling an extend method
/// that takes an additional parameter.
///
/// ```vole
/// let result = () => var.method(prim_var)
/// let val = result()
/// ```
fn generate_closure_with_param(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let candidates = find_struct_with_getter_extend_methods(scope);
    if candidates.is_empty() {
        return None;
    }

    let idx = emit.gen_range(0..candidates.len());
    let (var_name, _struct_type, methods) = &candidates[idx];

    // Find methods with at least one primitive param
    let methods_with_params: Vec<&MethodInfo> = methods
        .iter()
        .filter(|m| {
            !matches!(m.return_type, TypeInfo::Void)
                && m.params
                    .iter()
                    .any(|p| matches!(p.param_type, TypeInfo::Primitive(_)))
        })
        .collect();

    if methods_with_params.is_empty() {
        // Fall back to variant 1 if no methods with primitive params
        return generate_closure_getter(scope, emit);
    }

    let method = methods_with_params[emit.gen_range(0..methods_with_params.len())];

    // For each param, try to find a matching primitive variable in scope,
    // otherwise fall back to a literal
    let args: Vec<String> = method
        .params
        .iter()
        .map(|p| {
            if let TypeInfo::Primitive(_) = &p.param_type {
                // Try to find a matching variable in scope
                let matching_vars: Vec<String> = scope
                    .vars_matching(|v| v.type_info == p.param_type)
                    .into_iter()
                    .map(|v| v.name)
                    .collect();
                if !matching_vars.is_empty() {
                    matching_vars[emit.gen_range(0..matching_vars.len())].clone()
                } else {
                    emit.literal(&p.param_type)
                }
            } else {
                emit.literal(&p.param_type)
            }
        })
        .collect();

    let closure_name = scope.fresh_name();
    let result_name = scope.fresh_name();
    let ret_type = method.return_type.clone();

    scope.add_local(
        closure_name.clone(),
        TypeInfo::Function {
            param_types: vec![],
            return_type: Box::new(ret_type.clone()),
        },
        false,
    );
    scope.add_local(result_name.clone(), ret_type, false);

    Some(format!(
        "let {} = () => {}.{}({})\nlet {} = {}()",
        closure_name,
        var_name,
        method.name,
        args.join(", "),
        result_name,
        closure_name,
    ))
}

/// Find struct-typed variables in scope that have at least one non-void extend method.
///
/// Returns `(var_name, struct_type, getter_methods)` triples.
fn find_struct_with_getter_extend_methods(
    scope: &Scope,
) -> Vec<(String, TypeInfo, Vec<MethodInfo>)> {
    let module_id = match scope.module_id {
        Some(id) => id,
        None => return Vec::new(),
    };

    let mut candidates = Vec::new();

    // Collect struct-typed variables (locals + params)
    let mut struct_vars: Vec<(String, SymbolId)> = Vec::new();
    for (name, ty, _) in &scope.locals {
        if let TypeInfo::Struct(mod_id, sym_id) = ty {
            if *mod_id == module_id {
                struct_vars.push((name.clone(), *sym_id));
            }
        }
    }
    for param in scope.params {
        if let TypeInfo::Struct(mod_id, sym_id) = &param.param_type {
            if *mod_id == module_id {
                struct_vars.push((param.name.clone(), *sym_id));
            }
        }
    }

    // For each struct var, collect non-void extend methods
    for (var_name, struct_sym_id) in struct_vars {
        let methods = collect_getter_extend_methods(scope, module_id, struct_sym_id);
        if !methods.is_empty() {
            candidates.push((
                var_name,
                TypeInfo::Struct(module_id, struct_sym_id),
                methods,
            ));
        }
    }

    candidates
}

/// Collect non-void extend methods for a given struct from implement blocks.
fn collect_getter_extend_methods(
    scope: &Scope,
    module_id: crate::symbols::ModuleId,
    struct_sym_id: SymbolId,
) -> Vec<MethodInfo> {
    let mut methods = Vec::new();

    if let Some(module) = scope.table.get_module(module_id) {
        for symbol in module.implement_blocks() {
            if let SymbolKind::ImplementBlock(ref info) = symbol.kind {
                // Only standalone extend blocks (no interface) targeting this struct
                if info.interface.is_none()
                    && info.target_type.0 == module_id
                    && info.target_type.1 == struct_sym_id
                {
                    for m in &info.methods {
                        if !matches!(m.return_type, TypeInfo::Void) {
                            methods.push(m.clone());
                        }
                    }
                }
            }
        }
    }

    methods
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::SymbolTable;
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(
            rng,
            EMPTY_STMT,
            EMPTY_EXPR,
            resolved,
            crate::symbols::SymbolTable::empty_ref(),
        )
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(ClosureExtendMethod.name(), "closure_extend_method");
    }

    #[test]
    fn returns_none_without_struct_vars() {
        let mut table = SymbolTable::new();
        let _mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClosureExtendMethod.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn returns_none_without_module() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!ClosureExtendMethod.precondition(&scope, &params));
    }
}
