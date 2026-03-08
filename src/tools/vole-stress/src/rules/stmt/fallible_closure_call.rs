//! Rule: closure calling a fallible function with match-based error handling.
//!
//! Finds fallible functions in the current module and generates closures that
//! call them, matching on the result.  Two variants:
//!
//! **Pattern A -- IIFE (immediately invoked function expression):**
//! ```vole
//! let result = ((x: i64) => {
//!     return match try_compute(x) {
//!         success v => v
//!         error => 0
//!         _ => -1
//!     }
//! })(42)
//! assert(result >= -1)
//! ```
//!
//! **Pattern B -- iterator map with fallible call:**
//! ```vole
//! let mapped = [1, 2, 3].iter().map((x: i64) => {
//!     return match try_compute(x) {
//!         success v => v
//!         error => 0
//!         _ => -1
//!     }
//! }).collect()
//! assert(mapped.length() == 3)
//! ```
//!
//! Both patterns wrap the call in a `when { false => ..., _ => default }` guard
//! to prevent mutual recursion at runtime while still exercising the type
//! checker and codegen paths.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{FunctionInfo, PrimitiveType, SymbolKind, TypeInfo};

pub struct FallibleClosureCall;

impl StmtRule for FallibleClosureCall {
    fn name(&self) -> &'static str {
        "fallible_closure_call"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        !scope.is_in_generic_class_method() && scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let module_id = scope.module_id?;
        let module = scope.table.get_module(module_id)?;

        // Find non-generic fallible functions whose success type is a simple
        // primitive we can work with.  Exclude the current function to avoid
        // self-recursion, and only pick lower-indexed symbols to prevent
        // mutual recursion.
        let current_name = scope.current_function_name.as_deref();
        let current_fn_sym_id = scope.current_function_sym_id;
        let fallible_funcs: Vec<(String, FunctionInfo)> = module
            .functions()
            .filter_map(|sym| {
                if let SymbolKind::Function(ref info) = sym.kind
                    && info.type_params.is_empty()
                    && info.return_type.is_fallible()
                    && current_name != Some(sym.name.as_str())
                {
                    // Only allow lower-indexed symbols to prevent mutual recursion.
                    if let Some(cur_id) = current_fn_sym_id
                        && sym.id.0 >= cur_id.0
                    {
                        return None;
                    }
                    // Only use functions with a primitive success type so the
                    // closure return type stays simple.
                    let success = info.return_type.success_type();
                    if success.is_primitive() {
                        return Some((sym.name.clone(), info.clone()));
                    }
                }
                None
            })
            .collect();

        if fallible_funcs.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..fallible_funcs.len());
        let (func_name, func_info) = fallible_funcs[idx].clone();

        let success_type = func_info.return_type.success_type().clone();
        let default_val = emit.literal(&success_type);
        let default_val2 = emit.literal(&success_type);

        // Generate arguments for the fallible function call
        let args: Vec<String> = func_info
            .params
            .iter()
            .map(|p| emit.literal(&p.param_type))
            .collect();
        let args_str = args.join(", ");

        // Build the match expression inside a when-false guard to prevent
        // mutual recursion at runtime.
        let match_expr = format!(
            "when {{ false => match {}({}) {{ success v => v, error => {}, _ => {} }}, _ => {} }}",
            func_name, args_str, default_val, default_val2, default_val,
        );

        let use_iter = emit.gen_bool(0.4);
        if use_iter {
            emit_iter_pattern(scope, emit, &match_expr, &success_type)
        } else {
            emit_iife_pattern(scope, emit, &match_expr, &success_type, &func_info)
        }
    }
}

/// Pattern A: IIFE -- immediately invoked closure calling a fallible function.
///
/// ```vole
/// let result = ((x: i64) -> i64 => {
///     return <match_expr>
/// })(42)
/// assert(result >= -1)
/// ```
fn emit_iife_pattern(
    scope: &mut Scope,
    emit: &mut Emit,
    match_expr: &str,
    success_type: &TypeInfo,
    func_info: &FunctionInfo,
) -> Option<String> {
    // Use the first param type of the fallible function for the closure param,
    // or fall back to i64 if the function has no params.
    let (param_type, param_type_str, arg_val) = if let Some(p) = func_info.params.first() {
        let ty_str = p.param_type.to_vole_syntax(scope.table);
        let arg = emit.literal(&p.param_type);
        (p.param_type.clone(), ty_str, arg)
    } else {
        let arg = emit.literal(&TypeInfo::Primitive(PrimitiveType::I64));
        (
            TypeInfo::Primitive(PrimitiveType::I64),
            "i64".to_string(),
            arg,
        )
    };

    let _ = param_type; // used for documentation, type determined by func
    let return_type_str = success_type.to_vole_syntax(scope.table);

    let result_name = scope.fresh_name();
    scope.add_local(result_name.clone(), success_type.clone(), false);

    let indent = emit.indent_str();

    Some(format!(
        "let {} = ((_fc_arg: {}) -> {} => {{\n{}    return {}\n{}}})({})",
        result_name, param_type_str, return_type_str, indent, match_expr, indent, arg_val,
    ))
}

/// Pattern B: iterator map -- closure calling fallible function inside `.map()`.
///
/// ```vole
/// let mapped = [1, 2, 3].iter().map((_fc_arg: i64) -> i64 => {
///     return <match_expr>
/// }).collect()
/// assert(mapped.length() == 3)
/// ```
fn emit_iter_pattern(
    scope: &mut Scope,
    emit: &mut Emit,
    match_expr: &str,
    success_type: &TypeInfo,
) -> Option<String> {
    let arr_size = emit.random_in(2, 4);
    let arr_elems: Vec<String> = (0..arr_size)
        .map(|_| format!("{}", emit.random_in(1, 20)))
        .collect();

    let return_type_str = success_type.to_vole_syntax(scope.table);

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Array(Box::new(success_type.clone())),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = [{}].iter().map((_fc_arg: i64) -> {} => {{\n{}    return {}\n{}}}).collect()\n{}assert({}.length() == {})",
        result_name,
        arr_elems.join(", "),
        return_type_str,
        indent,
        match_expr,
        indent,
        indent,
        result_name,
        arr_size,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{ErrorInfo, FieldInfo, FunctionInfo, ParamInfo, SymbolKind, SymbolTable};
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
        assert_eq!(FallibleClosureCall.name(), "fallible_closure_call");
    }

    #[test]
    fn precondition_requires_module() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!FallibleClosureCall.precondition(&scope, &params));
    }

    #[test]
    fn returns_none_without_fallible_functions() {
        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(mod_id);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = FallibleClosureCall.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn returns_none_with_only_non_primitive_success() {
        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        {
            let module = table.get_module_mut(mod_id).unwrap();
            // Add an error type
            module.add_symbol(
                "TestErr".into(),
                SymbolKind::Error(ErrorInfo { fields: vec![] }),
            );
            // Add a fallible function returning a struct (non-primitive success type)
            // -- we can't easily construct a Struct type here, so just use Void which
            // is also non-primitive.
            module.add_symbol(
                "bad_func".into(),
                SymbolKind::Function(FunctionInfo {
                    type_params: vec![],
                    params: vec![],
                    return_type: TypeInfo::Fallible {
                        success: Box::new(TypeInfo::Void),
                        error: Box::new(TypeInfo::Error(mod_id, crate::symbols::SymbolId(0))),
                    },
                }),
            );
        }

        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(mod_id);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = FallibleClosureCall.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    fn make_table_with_fallible_func() -> (SymbolTable, crate::symbols::ModuleId) {
        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test".into(), "test.vole".into());
        {
            let module = table.get_module_mut(mod_id).unwrap();
            // Add an error type
            module.add_symbol(
                "TestErr".into(),
                SymbolKind::Error(ErrorInfo {
                    fields: vec![FieldInfo {
                        name: "msg".into(),
                        field_type: TypeInfo::Primitive(PrimitiveType::String),
                    }],
                }),
            );
            // Add a fallible function with primitive success type
            module.add_symbol(
                "try_compute".into(),
                SymbolKind::Function(FunctionInfo {
                    type_params: vec![],
                    params: vec![ParamInfo {
                        name: "x".into(),
                        param_type: TypeInfo::Primitive(PrimitiveType::I64),
                        has_default: false,
                    }],
                    return_type: TypeInfo::Fallible {
                        success: Box::new(TypeInfo::Primitive(PrimitiveType::I64)),
                        error: Box::new(TypeInfo::Error(mod_id, crate::symbols::SymbolId(0))),
                    },
                }),
            );
        }
        (table, mod_id)
    }

    #[test]
    fn generates_with_fallible_function() {
        let (table, mod_id) = make_table_with_fallible_func();
        let mut scope = Scope::with_module(&[], &table, mod_id);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = FallibleClosureCall.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some(), "expected Some, got None");
        let text = result.unwrap();
        // Should contain the match and closure pattern
        assert!(
            text.contains("try_compute"),
            "expected try_compute in: {text}"
        );
        assert!(text.contains("match"), "expected match in: {text}");
        assert!(text.contains("success"), "expected success in: {text}");
        assert!(
            text.contains("let local"),
            "expected let binding in: {text}"
        );
    }
}
