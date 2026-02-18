//! Rule: nth with match on optional result.
//!
//! Generates `let r = arr.iter().nth(0)` followed by a match or when on the result.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct NthLet;

impl StmtRule for NthLet {
    fn name(&self) -> &'static str {
        "nth_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.05)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let mut array_vars: Vec<(String, PrimitiveType)> = Vec::new();

        for var in scope.vars_matching(|v| matches!(v.type_info, TypeInfo::Array(_))) {
            if let TypeInfo::Array(inner) = &var.type_info {
                if let TypeInfo::Primitive(p) = inner.as_ref() {
                    if matches!(
                        p,
                        PrimitiveType::I64
                            | PrimitiveType::I32
                            | PrimitiveType::String
                            | PrimitiveType::Bool
                    ) {
                        array_vars.push((var.name, *p));
                    }
                }
            }
        }

        for param in scope.params.iter() {
            if let TypeInfo::Array(inner) = &param.param_type {
                if let TypeInfo::Primitive(p) = inner.as_ref() {
                    if matches!(
                        p,
                        PrimitiveType::I64
                            | PrimitiveType::I32
                            | PrimitiveType::String
                            | PrimitiveType::Bool
                    ) {
                        array_vars.push((param.name.clone(), *p));
                    }
                }
            }
        }

        if array_vars.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..array_vars.len());
        let (arr_name, elem_prim) = &array_vars[idx];
        let elem_prim = *elem_prim;

        let nth_name = scope.fresh_name();
        let result_name = scope.fresh_name();

        // Optional prefix chain
        let prefix = if emit.gen_bool(0.25)
            && matches!(elem_prim, PrimitiveType::I64 | PrimitiveType::I32)
        {
            match emit.gen_range(0..2) {
                0 => {
                    let n = emit.gen_i64_range(-5, 2);
                    format!(".filter((x) => x > {})", n)
                }
                _ => ".sorted()".to_string(),
            }
        } else {
            String::new()
        };

        let indent = emit.indent_str();
        let inner_indent = format!("{}    ", indent);

        let default_expr = match elem_prim {
            PrimitiveType::I64 => "0".to_string(),
            PrimitiveType::I32 => "0_i32".to_string(),
            PrimitiveType::String => "\"\"".to_string(),
            PrimitiveType::Bool => "false".to_string(),
            _ => "0".to_string(),
        };

        scope.add_local(result_name.clone(), TypeInfo::Primitive(elem_prim), false);

        // ~40% when-is pattern, ~60% match pattern
        if emit.gen_bool(0.40) {
            Some(format!(
                "let {} = {}.iter(){}.nth(0)\n\
                 {}let {} = when {{\n\
                 {}{} is {} => {}\n\
                 {}_ => {}\n\
                 {}}}",
                nth_name,
                arr_name,
                prefix,
                indent,
                result_name,
                inner_indent,
                nth_name,
                elem_prim.as_str(),
                nth_name,
                inner_indent,
                default_expr,
                indent,
            ))
        } else {
            Some(format!(
                "let {} = {}.iter(){}.nth(0)\n\
                 {}let {} = match {} {{\n\
                 {}{} => {}\n\
                 {}nil => {}\n\
                 {}}}",
                nth_name,
                arr_name,
                prefix,
                indent,
                result_name,
                nth_name,
                inner_indent,
                elem_prim.as_str(),
                nth_name,
                inner_indent,
                default_expr,
                indent,
            ))
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
        assert_eq!(NthLet.name(), "nth_let");
    }

    #[test]
    fn generates_nth() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "arr".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = NthLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".nth(0)"), "got: {text}");
    }
}
