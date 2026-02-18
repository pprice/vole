//! Rule: string .length() on literal strings of known lengths.
//!
//! Tests string-length codegen with edge cases: empty string, single char, etc.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct StringLengthEdge;

impl StmtRule for StringLengthEdge {
    fn name(&self) -> &'static str {
        "string_length_edge"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();
        let expr = match emit.gen_range(0..5) {
            0 => "\"\".length()".to_string(),
            1 => "\"a\".length()".to_string(),
            2 => "\"hello\".length()".to_string(),
            3 => "\"hello world\".length()".to_string(),
            _ => {
                let string_vars = collect_string_vars(scope);
                if !string_vars.is_empty() {
                    let var = &string_vars[emit.gen_range(0..string_vars.len())];
                    format!("{}.length()", var)
                } else {
                    "\"test\".length()".to_string()
                }
            }
        };
        scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
        Some(format!("let {} = {}", name, expr))
    }
}

fn collect_string_vars(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if matches!(ty, TypeInfo::Primitive(PrimitiveType::String)) {
            out.push(name.clone());
        }
    }
    for param in scope.params {
        if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::String)) {
            out.push(param.name.clone());
        }
    }
    out
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
        assert_eq!(StringLengthEdge.name(), "string_length_edge");
    }

    #[test]
    fn generates_length_call() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringLengthEdge.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".length()"), "got: {text}");
    }
}
