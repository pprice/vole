//! Rule: iterator chains with match expressions inside closures.
//!
//! Generates patterns like:
//! ```vole
//! let result = arr.iter().map((x) => { return match x { 1 => "one" _ => "other" } }).collect()
//! let result = arr.iter().filter((x) => { return match x % 2 { 0 => true _ => false } }).collect()
//! ```
//! This stresses the intersection of iterator dispatch, closure codegen, and
//! pattern matching — three subsystems that each have their own complexity.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct IterMatchClosure;

impl StmtRule for IterMatchClosure {
    fn name(&self) -> &'static str {
        "iter_match_closure"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.can_recurse()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Need an i64 array in scope.
        let i64_arrays: Vec<String> = scope
            .array_vars()
            .into_iter()
            .filter_map(|(name, elem_ty)| {
                if matches!(elem_ty, TypeInfo::Primitive(PrimitiveType::I64)) {
                    Some(name)
                } else {
                    None
                }
            })
            .collect();

        if i64_arrays.is_empty() {
            return None;
        }

        let arr_name = i64_arrays[emit.gen_range(0..i64_arrays.len())].clone();
        let variant = emit.gen_range(0..5);

        match variant {
            0 => gen_map_match_to_string(scope, emit, &arr_name),
            1 => gen_filter_match(scope, emit, &arr_name),
            2 => gen_map_match_to_i64(scope, emit, &arr_name),
            3 => gen_map_match_count(scope, emit, &arr_name),
            _ => gen_filter_map_match(scope, emit, &arr_name),
        }
    }
}

/// `.iter().map((x) => { return match x { ... } }).collect()` → [string]
fn gen_map_match_to_string(scope: &mut Scope, emit: &mut Emit, arr_name: &str) -> Option<String> {
    let arm_count = emit.random_in(2, 4);
    let indent = emit.indent_str();
    let mut arms = String::new();
    let mut used_vals = Vec::new();

    for _ in 0..arm_count {
        let v = emit.gen_range(0..10) as i64;
        if used_vals.contains(&v) {
            continue;
        }
        used_vals.push(v);
        let label = match v % 5 {
            0 => "zero",
            1 => "one",
            2 => "two",
            3 => "three",
            _ => "four",
        };
        arms.push_str(&format!("{indent}        {v} => \"{label}\"\n"));
    }
    arms.push_str(&format!("{indent}        _ => \"other\""));

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
        false,
    );

    Some(format!(
        "let {result_name} = {arr_name}.iter().map((x) => {{\n\
         {indent}    return match x {{\n\
         {arms}\n\
         {indent}    }}\n\
         {indent}}}).collect()"
    ))
}

/// `.iter().filter((x) => { return match x % N { 0 => true _ => false } }).collect()` → [i64]
fn gen_filter_match(scope: &mut Scope, emit: &mut Emit, arr_name: &str) -> Option<String> {
    let divisor = emit.random_in(2, 5);
    let indent = emit.indent_str();

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        false,
    );

    Some(format!(
        "let {result_name} = {arr_name}.iter().filter((x) => {{\n\
         {indent}    return match x % {divisor} {{\n\
         {indent}        0 => true\n\
         {indent}        _ => false\n\
         {indent}    }}\n\
         {indent}}}).collect()"
    ))
}

/// `.iter().map((x) => { return match x { ... } }).collect()` → [i64]
fn gen_map_match_to_i64(scope: &mut Scope, emit: &mut Emit, arr_name: &str) -> Option<String> {
    let arm_count = emit.random_in(2, 3);
    let indent = emit.indent_str();
    let mut arms = String::new();
    let mut used_vals = Vec::new();

    for _ in 0..arm_count {
        let v = emit.gen_range(0..10) as i64;
        if used_vals.contains(&v) {
            continue;
        }
        used_vals.push(v);
        let result = v * 10;
        arms.push_str(&format!("{indent}        {v} => {result}\n"));
    }
    arms.push_str(&format!("{indent}        _ => 0"));

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        false,
    );

    Some(format!(
        "let {result_name} = {arr_name}.iter().map((x) => {{\n\
         {indent}    return match x {{\n\
         {arms}\n\
         {indent}    }}\n\
         {indent}}}).collect()"
    ))
}

/// `.iter().map((x) => { return match x { ... } }).count()` → i64
fn gen_map_match_count(scope: &mut Scope, emit: &mut Emit, arr_name: &str) -> Option<String> {
    let indent = emit.indent_str();

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    Some(format!(
        "let {result_name} = {arr_name}.iter().map((x) => {{\n\
         {indent}    return match x {{\n\
         {indent}        0 => \"zero\"\n\
         {indent}        1 => \"one\"\n\
         {indent}        _ => \"many\"\n\
         {indent}    }}\n\
         {indent}}}).count()"
    ))
}

/// `.iter().filter((x) => match ...).map((x) => match ...).collect()` → [string]
fn gen_filter_map_match(scope: &mut Scope, emit: &mut Emit, arr_name: &str) -> Option<String> {
    let divisor = emit.random_in(2, 4);
    let indent = emit.indent_str();

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
        false,
    );

    Some(format!(
        "let {result_name} = {arr_name}.iter().filter((x) => {{\n\
         {indent}    return match x % {divisor} {{\n\
         {indent}        0 => true\n\
         {indent}        _ => false\n\
         {indent}    }}\n\
         {indent}}}).map((x) => {{\n\
         {indent}    return match x {{\n\
         {indent}        0 => \"zero\"\n\
         {indent}        _ => x.to_string()\n\
         {indent}    }}\n\
         {indent}}}).collect()"
    ))
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

    fn make_scope_with_i64_array(table: &SymbolTable) -> Scope<'_> {
        let mut scope = Scope::new(&[], table);
        scope.add_local(
            "nums".to_string(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );
        scope
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(IterMatchClosure.name(), "iter_match_closure");
    }

    #[test]
    fn no_generation_without_i64_array() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterMatchClosure.generate(&mut scope, &mut emit, &params);
        assert!(result.is_none());
    }

    #[test]
    fn generates_map_match_to_string() {
        let table = SymbolTable::new();
        let mut scope = make_scope_with_i64_array(&table);
        // Seed 10 → variant 0 (map to string)
        let mut rng = rand::rngs::StdRng::seed_from_u64(10);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterMatchClosure.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".iter().map("), "got: {text}");
        assert!(text.contains("match x"), "got: {text}");
        assert!(text.contains(".collect()"), "got: {text}");
    }

    #[test]
    fn generates_filter_match() {
        let table = SymbolTable::new();
        let mut scope = make_scope_with_i64_array(&table);
        // Seed 7 → variant 1 (filter match)
        let mut rng = rand::rngs::StdRng::seed_from_u64(7);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterMatchClosure.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".iter().filter("), "got: {text}");
        assert!(text.contains("match x %"), "got: {text}");
    }

    #[test]
    fn generates_with_various_seeds() {
        let table = SymbolTable::new();
        let resolved = ResolvedParams::new();
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        for seed in [1, 5, 20, 50, 100] {
            let mut scope = make_scope_with_i64_array(&table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut emit = test_emit(&mut rng, &resolved);

            let result = IterMatchClosure.generate(&mut scope, &mut emit, &params);
            assert!(result.is_some(), "seed={seed} failed to generate");
            let text = result.unwrap();
            assert!(
                text.contains("match x"),
                "seed={seed} missing match: {text}"
            );
        }
    }
}
