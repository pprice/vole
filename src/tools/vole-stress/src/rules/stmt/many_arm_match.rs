//! Rule: match expression with many arms (20-50) to stress-test match compilation.
//!
//! Generates a match expression on an i64 variable with 20-50 numeric literal
//! arms plus a wildcard default, each mapping to a string literal:
//! ```vole
//! let result = match var {
//!     0 => "zero"
//!     1 => "one"
//!     ...
//!     _ => "default"
//! }
//! assert(result == "zero")
//! ```

use std::collections::HashSet;

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ManyArmMatch;

impl StmtRule for ManyArmMatch {
    fn name(&self) -> &'static str {
        "many_arm_match"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_vars = collect_i64_vars(scope);
        if i64_vars.is_empty() {
            return None;
        }

        let var = i64_vars[emit.gen_range(0..i64_vars.len())].clone();
        let result_name = scope.fresh_name();
        let num_arms = emit.random_in(20, 50);
        let indent = emit.indent_str();

        // Generate unique integer literals for each arm.
        let mut used_values = HashSet::new();
        let mut arm_values: Vec<i64> = Vec::with_capacity(num_arms);
        for _ in 0..num_arms {
            let mut v = emit.gen_i64_range(-100, 200);
            while used_values.contains(&v) {
                v = emit.gen_i64_range(-100, 200);
            }
            used_values.insert(v);
            arm_values.push(v);
        }

        // Pick one arm to use for the assertion.
        let assert_idx = emit.gen_range(0..arm_values.len());
        let assert_val = arm_values[assert_idx];

        // Build the match arms, each mapping an integer to a string.
        let mut arms = Vec::with_capacity(num_arms + 1);
        let mut assert_label = String::new();
        for (i, &v) in arm_values.iter().enumerate() {
            let label = format!("arm{}", i);
            if i == assert_idx {
                assert_label = label.clone();
            }
            arms.push(format!("{}    {} => \"{}\"", indent, v, label));
        }

        // Wildcard default arm.
        arms.push(format!("{}    _ => \"default\"", indent));

        scope.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        Some(format!(
            "let {result} = match {var} {{\n{arms}\n{indent}}}\n\
             {indent}assert({result} == \"{expected}\")",
            result = result_name,
            var = assert_val,
            arms = arms.join("\n"),
            indent = indent,
            expected = assert_label,
        ))
    }
}

fn collect_i64_vars(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)) {
            out.push(name.clone());
        }
    }
    for param in scope.params {
        if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::I64)) {
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

    fn test_params() -> Params {
        Params::from_iter([("probability", ParamValue::Probability(1.0))])
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(ManyArmMatch.name(), "many_arm_match");
    }

    #[test]
    fn returns_none_without_i64_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        assert!(
            ManyArmMatch
                .generate(&mut scope, &mut emit, &test_params())
                .is_none()
        );
    }

    #[test]
    fn generates_many_arms() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = ManyArmMatch.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match "), "got: {text}");
        assert!(text.contains("_ => \"default\""), "got: {text}");
        assert!(text.contains("assert("), "got: {text}");

        // Count the number of => to verify we have many arms (20+ plus wildcard).
        let arrow_count = text.matches(" => ").count();
        assert!(
            arrow_count >= 21,
            "expected at least 21 arms (20 + wildcard), got {arrow_count}"
        );
    }

    #[test]
    fn adds_string_local() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("n".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        ManyArmMatch.generate(&mut scope, &mut emit, &test_params());
        assert_eq!(scope.locals.len(), initial_len + 1);

        // The added local should be a String type.
        let (_, ty, _) = &scope.locals[scope.locals.len() - 1];
        assert!(
            matches!(ty, TypeInfo::Primitive(PrimitiveType::String)),
            "expected String type, got: {ty:?}"
        );
    }

    #[test]
    fn no_duplicate_arm_values() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(99);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let text = ManyArmMatch
            .generate(&mut scope, &mut emit, &test_params())
            .unwrap();

        // Extract all numeric arm values (lines with "=> " but not the wildcard).
        let mut seen = HashSet::new();
        for line in text.lines() {
            let trimmed = line.trim();
            if trimmed.starts_with('_') || !trimmed.contains(" => ") {
                continue;
            }
            let val_str = trimmed.split(" => ").next().unwrap().trim();
            assert!(
                seen.insert(val_str.to_string()),
                "duplicate arm value: {val_str}"
            );
        }
    }
}
