//! Rule: string lines count expression.
//!
//! Generates `str_var.lines().count()` when a string-typed variable is in scope
//! and the expected type is `i64`.
//!
//! **Pattern:**
//! ```vole
//! s.lines().count()
//! ```

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct StringLinesCount;

impl ExprRule for StringLinesCount {
    fn name(&self) -> &'static str {
        "string_lines_count"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
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
        if !matches!(expected_type, TypeInfo::Primitive(PrimitiveType::I64)) {
            return None;
        }

        let string_type = TypeInfo::Primitive(PrimitiveType::String);
        let vars = scope.vars_of_type(&string_type);
        if vars.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..vars.len());
        let var_name = &vars[idx].name;

        Some(format!("{}.lines().count()", var_name))
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
        assert_eq!(StringLinesCount.name(), "string_lines_count");
    }

    #[test]
    fn requires_string_in_scope() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!StringLinesCount.precondition(&scope, &params));

        let mut scope_with_str = Scope::new(&[], &table);
        scope_with_str.add_local(
            "s".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        assert!(StringLinesCount.precondition(&scope_with_str, &params));
    }

    #[test]
    fn generates_lines_count_call() {
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

        let result = StringLinesCount.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert_eq!(text, "s.lines().count()");
    }

    #[test]
    fn returns_none_for_non_i64() {
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

        let result = StringLinesCount.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::Bool),
        );
        assert!(result.is_none());
    }
}
