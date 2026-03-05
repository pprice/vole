//! Rule: `.substring(start, end)` on string variables.
//!
//! Generates `str_var.substring(0, N)` where N is clamped to a safe range.
//! The result type is `string`.
//!
//! **Pattern:**
//! ```vole
//! s.substring(0, 3)
//! ```

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct StringSubstring;

impl ExprRule for StringSubstring {
    fn name(&self) -> &'static str {
        "string_substring"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.has_var_of_type(&TypeInfo::Primitive(PrimitiveType::String))
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        // Only produce string values
        if *expected_type != TypeInfo::Primitive(PrimitiveType::String) {
            return None;
        }

        let string_type = TypeInfo::Primitive(PrimitiveType::String);
        let vars = scope.vars_of_type(&string_type);
        if vars.is_empty() {
            return None;
        }
        let idx = emit.gen_range(0..vars.len());
        let var_name = &vars[idx].name;

        // Generate safe start/end values
        // Use small values to avoid out-of-bounds on short strings
        let start = emit.gen_range(0..3) as i64;
        let end = start + emit.gen_range(1..4) as i64;

        Some(format!("{}.substring({}, {})", var_name, start, end))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ParamValue, StmtRule};
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
        assert_eq!(StringSubstring.name(), "string_substring");
    }

    #[test]
    fn requires_string_in_scope() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!StringSubstring.precondition(&scope, &params));

        let mut scope_with_str = Scope::new(&[], &table);
        scope_with_str.add_local(
            "s".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        assert!(StringSubstring.precondition(&scope_with_str, &params));
    }

    #[test]
    fn generates_substring_call() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "s".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        let string_type = TypeInfo::Primitive(PrimitiveType::String);

        let result = StringSubstring.generate(&scope, &mut emit, &params, &string_type);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".substring("),
            "expected .substring( call, got: {text}"
        );
        assert!(text.starts_with("s."), "expected var name, got: {text}");
    }

    #[test]
    fn returns_none_for_non_string() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "s".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        let i64_type = TypeInfo::Primitive(PrimitiveType::I64);

        let result = StringSubstring.generate(&scope, &mut emit, &params, &i64_type);
        assert!(result.is_none());
    }
}
