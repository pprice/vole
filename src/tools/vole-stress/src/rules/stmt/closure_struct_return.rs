//! Rule: closures (lambdas) that return struct instances.
//!
//! Generates closures whose return expression is a struct literal, then
//! immediately invokes them.  This pattern was confirmed to expose a real
//! compiler bug and is generated across many seeds to exercise the fix.
//!
//! **Variant 1 -- simple closure returning struct:**
//! ```vole
//! let make_v0 = (a: i64, b: i64) => StructName { field1: a, field2: b }
//! let result_v1 = make_v0(val1, val2)
//! ```
//!
//! **Variant 2 -- closure with capture returning struct:**
//! ```vole
//! let offset = 42
//! let make_v0 = (n: i64) => StructName { field1: n + offset, field2: n * 2 }
//! let result_v1 = make_v0(val)
//! ```
//! (Only when an i64 variable exists in scope to capture.)

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, StructInfo, SymbolId, SymbolKind, TypeInfo};

pub struct ClosureStructReturn;

/// Find non-generic structs with 2+ i64 fields.
fn find_i64_structs(scope: &Scope, emit: &mut Emit) -> Option<(SymbolId, String, StructInfo)> {
    let module_id = scope.module_id?;
    let module = scope.table.get_module(module_id)?;

    let candidates: Vec<(SymbolId, String, StructInfo)> = module
        .structs()
        .filter_map(|sym| {
            if let SymbolKind::Struct(ref info) = sym.kind {
                if info.fields.len() >= 2
                    && info
                        .fields
                        .iter()
                        .all(|f| matches!(f.field_type, TypeInfo::Primitive(PrimitiveType::I64)))
                {
                    Some((sym.id, sym.name.clone(), info.clone()))
                } else {
                    None
                }
            } else {
                None
            }
        })
        .collect();

    if candidates.is_empty() {
        return None;
    }

    let idx = emit.gen_range(0..candidates.len());
    Some(candidates[idx].clone())
}

/// Variant 1: simple closure returning a struct.
///
/// ```vole
/// let make_NAME = (a: i64, b: i64) => StructName { f1: a, f2: b }
/// let result_NAME = make_NAME(val1, val2)
/// ```
fn gen_simple(
    struct_name: &str,
    struct_info: &StructInfo,
    scope: &mut Scope,
    emit: &mut Emit,
) -> String {
    let make_name = scope.fresh_name();
    let result_name = scope.fresh_name();
    let indent = emit.indent_str();

    // Generate unique param names for the lambda
    let param_names: Vec<String> = struct_info
        .fields
        .iter()
        .map(|_| scope.fresh_name())
        .collect();

    // Build param list: (p0: i64, p1: i64, ...)
    let params_str: String = param_names
        .iter()
        .map(|p| format!("{}: i64", p))
        .collect::<Vec<_>>()
        .join(", ");

    // Build struct literal using param names as field values
    let fields_str: String = struct_info
        .fields
        .iter()
        .zip(param_names.iter())
        .map(|(f, p)| format!("{}: {}", f.name, p))
        .collect::<Vec<_>>()
        .join(", ");

    // Build call arguments: small i64 literals
    let args_str: String = struct_info
        .fields
        .iter()
        .map(|_| format!("{}", emit.gen_i64_range(0, 99)))
        .collect::<Vec<_>>()
        .join(", ");

    format!(
        "let {make} = ({params}) => {sname} {{ {fields} }}\n\
         {indent}let {result} = {make}({args})",
        make = make_name,
        params = params_str,
        sname = struct_name,
        fields = fields_str,
        result = result_name,
        args = args_str,
    )
}

/// Variant 2: closure with capture returning a struct.
///
/// ```vole
/// let offset = 42
/// let make_NAME = (n: i64) => StructName { f1: n + offset, f2: n * 2 }
/// let result_NAME = make_NAME(val)
/// ```
fn gen_with_capture(
    struct_name: &str,
    struct_info: &StructInfo,
    captured_var: &str,
    scope: &mut Scope,
    emit: &mut Emit,
) -> String {
    let make_name = scope.fresh_name();
    let result_name = scope.fresh_name();
    let param_name = scope.fresh_name();
    let indent = emit.indent_str();

    // Build struct fields using expressions that combine the param and capture
    let fields_str: String = struct_info
        .fields
        .iter()
        .enumerate()
        .map(|(i, f)| {
            let expr = if i == 0 {
                format!("{} + {}", param_name, captured_var)
            } else {
                format!("{} * {}", param_name, emit.random_in(2, 5))
            };
            format!("{}: {}", f.name, expr)
        })
        .collect::<Vec<_>>()
        .join(", ");

    let arg = emit.gen_i64_range(1, 50);

    format!(
        "let {make} = ({param}: i64) => {sname} {{ {fields} }}\n\
         {indent}let {result} = {make}({arg})",
        make = make_name,
        param = param_name,
        sname = struct_name,
        fields = fields_str,
        result = result_name,
        arg = arg,
    )
}

impl StmtRule for ClosureStructReturn {
    fn name(&self) -> &'static str {
        "closure_struct_return"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let (_sym_id, struct_name, struct_info) = find_i64_structs(scope, emit)?;

        // Check if we have an i64 variable in scope for capture variant
        let i64_ty = TypeInfo::Primitive(PrimitiveType::I64);
        let i64_vars: Vec<String> = scope
            .vars_of_type(&i64_ty)
            .into_iter()
            .map(|v| v.name)
            .collect();

        let use_capture = !i64_vars.is_empty() && emit.gen_bool(0.5);

        if use_capture {
            let idx = emit.gen_range(0..i64_vars.len());
            let captured = &i64_vars[idx];
            Some(gen_with_capture(
                &struct_name,
                &struct_info,
                captured,
                scope,
                emit,
            ))
        } else {
            Some(gen_simple(&struct_name, &struct_info, scope, emit))
        }
    }
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
        assert_eq!(ClosureStructReturn.name(), "closure_struct_return");
    }

    #[test]
    fn returns_none_without_module() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClosureStructReturn.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn returns_none_without_structs() {
        let mut table = SymbolTable::new();
        let _mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClosureStructReturn.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
