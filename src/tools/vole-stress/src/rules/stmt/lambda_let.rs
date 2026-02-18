//! Rule: lambda/closure let-binding.
//!
//! Generates a let-binding with a lambda expression:
//! ```vole
//! let f = (x: i64, y: bool) -> string => "hello"
//! ```
//!
//! The lambda has 0-2 parameters of random primitive types and a random
//! primitive return type. The body is a literal of the return type.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct LambdaLet;

impl StmtRule for LambdaLet {
    fn name(&self) -> &'static str {
        "lambda_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.05)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();

        // Pick 0-2 random primitive param types
        let param_count = emit.random_in(0, 2);
        let param_names = ["x", "y", "z"];
        let param_types: Vec<TypeInfo> = (0..param_count)
            .map(|_| emit.random_primitive_type())
            .collect();

        // Pick a random return type
        let return_type = emit.random_primitive_type();

        // Build parameter list
        let params_str: String = param_types
            .iter()
            .enumerate()
            .map(|(i, ty)| {
                let prim = match ty {
                    TypeInfo::Primitive(p) => p.as_str(),
                    _ => "i64",
                };
                format!("{}: {}", param_names[i], prim)
            })
            .collect::<Vec<_>>()
            .join(", ");

        let return_type_str = match &return_type {
            TypeInfo::Primitive(p) => p.as_str(),
            _ => "i64",
        };

        // Generate a literal body of the return type
        let body = emit.literal(&return_type);

        // Lambda variables are not tracked for reuse since their function
        // type doesn't match primitive type expectations in the generator.

        Some(format!(
            "let {} = ({}) -> {} => {}",
            name, params_str, return_type_str, body
        ))
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
        assert_eq!(LambdaLet.name(), "lambda_let");
    }

    #[test]
    fn generates_lambda() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = LambdaLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("let"), "got: {text}");
        assert!(text.contains("=>"), "expected lambda, got: {text}");
        assert!(text.contains("->"), "expected return type, got: {text}");
    }
}
