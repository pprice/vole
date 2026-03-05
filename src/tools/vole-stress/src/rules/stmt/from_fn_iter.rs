//! Rule: `from_fn()` iterator calls with mutable variable captures.
//!
//! Generates a mutable counter variable and a `from_fn()` call whose closure
//! captures and mutates the counter, producing an `[i64]` array via `.collect()`.
//!
//! **Countdown variant:**
//! ```vole
//! var count0 = 4
//! let local1 = from_fn(() -> i64? => {
//!     if count0 <= 0 {
//!         return nil
//!     }
//!     let current = count0
//!     count0 = count0 - 1
//!     return current
//! }).collect()
//! ```
//!
//! **Countup variant:**
//! ```vole
//! var count0 = 0
//! let local1 = from_fn(() -> i64? => {
//!     count0 = count0 + 1
//!     if count0 > 3 {
//!         return nil
//!     }
//!     return count0
//! }).collect()
//! ```
//!
//! Stresses closures + mutable captures + optional returns + iterators.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct FromFnIter;

/// The two `from_fn` closure variants.
enum Variant {
    /// Counts down from `start` to 0 (exclusive), producing `[start, start-1, ..., 1]`.
    Countdown { start: usize },
    /// Counts up from 0, returning values 1..=max, producing `[1, 2, ..., max]`.
    Countup { max: usize },
}

impl StmtRule for FromFnIter {
    fn name(&self) -> &'static str {
        "from_fn_iter"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Closures inside generic class methods hit a compiler bug.
        !scope.is_in_generic_class_method()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        if !scope.can_recurse() {
            return None;
        }

        // Pick variant: 0 = countdown, 1 = countup.
        let variant = if emit.gen_bool(0.5) {
            Variant::Countdown {
                start: emit.gen_range(2..7), // 2-6
            }
        } else {
            Variant::Countup {
                max: emit.gen_range(2..6), // 2-5
            }
        };

        let counter_name = scope.fresh_name();
        let result_name = scope.fresh_name();
        let indent = emit.indent_str();

        let code = match &variant {
            Variant::Countdown { start } => {
                format!(
                    "{indent}var {counter} = {start}\n\
                     {indent}let {result} = from_fn(() -> i64? => {{\n\
                     {indent}    if {counter} <= 0 {{\n\
                     {indent}        return nil\n\
                     {indent}    }}\n\
                     {indent}    let current = {counter}\n\
                     {indent}    {counter} = {counter} - 1\n\
                     {indent}    return current\n\
                     {indent}}}).collect()",
                    indent = indent,
                    counter = counter_name,
                    result = result_name,
                    start = start,
                )
            }
            Variant::Countup { max } => {
                format!(
                    "{indent}var {counter} = 0\n\
                     {indent}let {result} = from_fn(() -> i64? => {{\n\
                     {indent}    {counter} = {counter} + 1\n\
                     {indent}    if {counter} > {max} {{\n\
                     {indent}        return nil\n\
                     {indent}    }}\n\
                     {indent}    return {counter}\n\
                     {indent}}}).collect()",
                    indent = indent,
                    counter = counter_name,
                    result = result_name,
                    max = max,
                )
            }
        };

        // Register the result array in scope -- always non-empty for both variants.
        let array_type = TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64)));
        scope.add_local(result_name, array_type, false);

        Some(code)
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
        assert_eq!(FromFnIter.name(), "from_fn_iter");
    }

    #[test]
    fn generates_valid_output() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = FromFnIter.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();

        assert!(
            text.contains("var "),
            "expected var declaration, got: {text}"
        );
        assert!(
            text.contains("from_fn("),
            "expected from_fn call, got: {text}"
        );
        assert!(
            text.contains(".collect()"),
            "expected .collect(), got: {text}"
        );
        assert!(
            text.contains("() -> i64?"),
            "expected closure type annotation, got: {text}"
        );
        assert!(
            text.contains("return nil"),
            "expected nil return, got: {text}"
        );
    }

    #[test]
    fn both_variants_appear() {
        let mut has_countdown = false;
        let mut has_countup = false;

        for seed in 0..200u64 {
            let table = SymbolTable::new();
            let mut scope = Scope::new(&[], &table);

            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            let text = FromFnIter
                .generate(&mut scope, &mut emit, &rule_params)
                .unwrap();

            if text.contains("<= 0") {
                has_countdown = true;
            }
            if text.contains("+ 1") {
                has_countup = true;
            }
        }

        assert!(
            has_countdown,
            "countdown variant never appeared in 200 seeds"
        );
        assert!(has_countup, "countup variant never appeared in 200 seeds");
    }

    #[test]
    fn registers_array_local() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        FromFnIter.generate(&mut scope, &mut emit, &rule_params);

        // The counter name is consumed (local0), result is local1.
        // We should have exactly 1 local registered (the result array).
        assert_eq!(
            scope.locals.len(),
            1,
            "expected exactly 1 registered local (the result array), got: {:?}",
            scope.locals
        );
        assert!(
            matches!(scope.locals[0].1, TypeInfo::Array(_)),
            "expected Array type, got: {:?}",
            scope.locals[0].1
        );
    }
}
