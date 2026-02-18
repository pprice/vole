//! Rule: string iteration let-binding.
//!
//! Generates iterator chains on string variables: `.iter().count()`,
//! `.iter().collect()`, `.iter().filter(...)`, `.iter().any(...)`, `.iter().map(...)`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct StringIterLet;

impl StmtRule for StringIterLet {
    fn name(&self) -> &'static str {
        "string_iter_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.05)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let string_vars: Vec<String> = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::String)))
            .into_iter()
            .map(|v| v.name)
            .chain(
                scope
                    .params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if string_vars.is_empty() {
            return None;
        }

        let str_name = &string_vars[emit.gen_range(0..string_vars.len())];
        let result_name = scope.fresh_name();

        // ~30% chain a string method before iteration
        let method_prefix = if emit.gen_bool(0.30) {
            let methods = [".to_upper()", ".to_lower()", ".trim()"];
            methods[emit.gen_range(0..methods.len())].to_string()
        } else {
            String::new()
        };

        match emit.gen_range(0..5) {
            0 => {
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                Some(format!(
                    "let {} = {}{}.iter().count()",
                    result_name, str_name, method_prefix
                ))
            }
            1 => {
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                    false,
                );
                Some(format!(
                    "let {} = {}{}.iter().collect()",
                    result_name, str_name, method_prefix
                ))
            }
            2 => {
                let filter_chars = [" ", "a", "e", "o"];
                let fc = filter_chars[emit.gen_range(0..filter_chars.len())];
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::I64),
                    false,
                );
                Some(format!(
                    "let {} = {}{}.iter().filter((c) => c != \"{}\").count()",
                    result_name, str_name, method_prefix, fc
                ))
            }
            3 => {
                let check_chars = ["a", "e", " ", "x", "1"];
                let cc = check_chars[emit.gen_range(0..check_chars.len())];
                let method = if emit.gen_bool(0.5) { "any" } else { "all" };
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                    false,
                );
                Some(format!(
                    "let {} = {}{}.iter().{}((c) => c == \"{}\")",
                    result_name, str_name, method_prefix, method, cc
                ))
            }
            _ => {
                let suffixes = ["!", "?", "_", "+"];
                let sf = suffixes[emit.gen_range(0..suffixes.len())];
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                    false,
                );
                Some(format!(
                    "let {} = {}{}.iter().map((c) => c + \"{}\").collect()",
                    result_name, str_name, method_prefix, sf
                ))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{ParamInfo, SymbolTable};
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
        assert_eq!(StringIterLet.name(), "string_iter_let");
    }

    #[test]
    fn generates_string_iter() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "s".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::String),
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringIterLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".iter()"), "got: {text}");
    }
}
