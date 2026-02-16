//! Rule: method call on a literal value.
//!
//! Tests the compiler's handling of method dispatch on temporaries:
//! ```vole
//! let n = "hello world".length()
//! let s = 42.to_string()
//! let b = "hello".contains("ell")
//! let c = "a,b,c".split(",").count()
//! let t = "  hello  ".trim()
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct LiteralMethod;

impl StmtRule for LiteralMethod {
    fn name(&self) -> &'static str {
        "literal_method"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();

        let variant = emit.gen_range(0..7);
        match variant {
            0 => {
                let lit = match emit.gen_range(0..4) {
                    0 => "\"hello\"",
                    1 => "\"\"",
                    2 => "\"a\"",
                    _ => "\"hello world\"",
                };
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                Some(format!("let {} = {}.length()", name, lit))
            }
            1 => {
                // Only non-negative literals: -50.to_string() parses as -(50.to_string())
                let num = emit.random_in(0, 200);
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!("let {} = {}.to_string()", name, num))
            }
            2 => {
                let (lit, sub) = match emit.gen_range(0..3) {
                    0 => ("\"hello world\"", "\"world\""),
                    1 => ("\"abcdef\"", "\"xyz\""),
                    _ => ("\"test\"", "\"es\""),
                };
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                    false,
                );
                Some(format!("let {} = {}.contains({})", name, lit, sub))
            }
            3 => {
                let (lit, delim) = match emit.gen_range(0..3) {
                    0 => ("\"a,b,c\"", "\",\""),
                    1 => ("\"one-two-three\"", "\"-\""),
                    _ => ("\"x\"", "\",\""),
                };
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                Some(format!("let {} = {}.split({}).count()", name, lit, delim))
            }
            4 => {
                let lit = match emit.gen_range(0..3) {
                    0 => "\"  hello  \"",
                    1 => "\"  \"",
                    _ => "\"no-spaces\"",
                };
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!("let {} = {}.trim()", name, lit))
            }
            5 => {
                let lit = match emit.gen_range(0..3) {
                    0 => "\"HELLO\"",
                    1 => "\"World\"",
                    _ => "\"ABC\"",
                };
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!("let {} = {}.to_lower()", name, lit))
            }
            _ => {
                let lit = match emit.gen_range(0..3) {
                    0 => "\"hello\"",
                    1 => "\"world\"",
                    _ => "\"abc\"",
                };
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!("let {} = {}.to_upper()", name, lit))
            }
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(LiteralMethod.name(), "literal_method");
    }

    #[test]
    fn generates_literal_method() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = LiteralMethod.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let "), "got: {text}");
    }

    #[test]
    fn adds_one_local() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        LiteralMethod.generate(&mut scope, &mut emit, &params);
        assert_eq!(scope.locals.len(), 1);
    }
}
