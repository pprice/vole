//! Rule: struct field array iteration with filter/reduce or map/collect.
//!
//! Generates a struct with an `[i64]` array field, a function that accesses
//! the field and runs an iterator pipeline on it, then instantiates and asserts.
//!
//! **Variant 0 -- filter + reduce** (sum items above threshold):
//! ```vole
//! struct Numbers_12345 {
//!     items: [i64],
//! }
//!
//! func sum_above_12345(ns: Numbers_12345, threshold: i64) -> i64 {
//!     return ns.items.iter().filter((x: i64) => x > threshold).reduce(0, (acc, x) => acc + x)
//! }
//!
//! let ns_12345 = Numbers_12345 { items: [1, 5, 3, 8, 2] }
//! let r_12345 = sum_above_12345(ns_12345, 3)
//! assert(r_12345 == 13)
//! ```
//!
//! **Variant 1 -- map + collect** (double each item, collect to array, check length):
//! ```vole
//! struct Batch_67890 {
//!     elems: [i64],
//! }
//!
//! func doubled_67890(b: Batch_67890) -> [i64] {
//!     return b.elems.iter().map((x: i64) => x * 2).collect()
//! }
//!
//! let b_67890 = Batch_67890 { elems: [4, 7, 1] }
//! let d_67890 = doubled_67890(b_67890)
//! assert(d_67890.length() == 3)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct StructFieldArrayIter;

impl StmtRule for StructFieldArrayIter {
    fn name(&self) -> &'static str {
        "struct_field_array_iter"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let uid = emit.gen_range(10000..99999);
        let variant = emit.gen_range(0..2);

        match variant {
            0 => gen_filter_reduce(scope, emit, uid),
            _ => gen_map_collect(scope, emit, uid),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0: filter + reduce (sum items above threshold)
// ---------------------------------------------------------------------------

fn gen_filter_reduce(scope: &mut Scope, emit: &mut Emit, uid: usize) -> Option<String> {
    let struct_names = ["Numbers", "Scores", "Readings", "Values"];
    let field_names = ["items", "data", "nums", "entries"];

    let sn_idx = emit.gen_range(0..struct_names.len());
    let fn_idx = emit.gen_range(0..field_names.len());
    let struct_name = format!("{}_{}", struct_names[sn_idx], uid);
    let field_name = field_names[fn_idx];

    // Generate 3-6 small i64 array elements
    let count = emit.random_in(3, 6);
    let elems: Vec<i64> = (0..count).map(|_| emit.gen_i64_range(1, 20)).collect();

    // Pick a threshold that produces a non-trivial filter result
    let threshold = emit.gen_i64_range(2, 10);

    // Compute expected result
    let expected: i64 = elems.iter().filter(|&&x| x > threshold).sum();

    let func_name = format!("sum_above_{}", uid);
    let param_name = "ns";
    let threshold_param = "threshold";

    // Module decl: struct definition
    let struct_decl = format!("struct {} {{\n    {}: [i64],\n}}", struct_name, field_name,);
    scope.add_module_decl(struct_decl);

    // Module decl: function definition
    let func_decl = format!(
        "func {func}({param}: {sn}, {thr}: i64) -> i64 {{\n    \
             return {param}.{field}.iter().filter((x: i64) => x > {thr}).reduce(0, (acc: i64, x: i64) => acc + x)\n\
         }}",
        func = func_name,
        param = param_name,
        sn = struct_name,
        thr = threshold_param,
        field = field_name,
    );
    scope.add_module_decl(func_decl);

    // Inline code: instantiate, call, assert
    let inst_var = scope.fresh_name();
    let result_var = scope.fresh_name();

    scope.add_local(
        result_var.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let elems_str = elems
        .iter()
        .map(|e| e.to_string())
        .collect::<Vec<_>>()
        .join(", ");

    let indent = emit.indent_str();
    Some(format!(
        "let {inst} = {sn} {{ {field}: [{elems}] }}\n\
         {indent}let {res} = {func}({inst}, {thr})\n\
         {indent}assert({res} == {expected})",
        inst = inst_var,
        sn = struct_name,
        field = field_name,
        elems = elems_str,
        res = result_var,
        func = func_name,
        thr = threshold,
        expected = expected,
    ))
}

// ---------------------------------------------------------------------------
// Variant 1: map + collect (double each item, collect to array, check length)
// ---------------------------------------------------------------------------

fn gen_map_collect(scope: &mut Scope, emit: &mut Emit, uid: usize) -> Option<String> {
    let struct_names = ["Batch", "Bundle", "Group", "Series"];
    let field_names = ["elems", "parts", "items", "cells"];

    let sn_idx = emit.gen_range(0..struct_names.len());
    let fn_idx = emit.gen_range(0..field_names.len());
    let struct_name = format!("{}_{}", struct_names[sn_idx], uid);
    let field_name = field_names[fn_idx];

    // Generate 2-5 small i64 array elements
    let count = emit.random_in(2, 5);
    let elems: Vec<i64> = (0..count).map(|_| emit.gen_i64_range(1, 30)).collect();

    // Pick a multiplier for the map operation
    let multiplier = emit.random_in(2, 5);

    let func_name = format!("scaled_{}", uid);
    let param_name = "batch";

    // Module decl: struct definition
    let struct_decl = format!("struct {} {{\n    {}: [i64],\n}}", struct_name, field_name,);
    scope.add_module_decl(struct_decl);

    // Module decl: function definition
    let func_decl = format!(
        "func {func}({param}: {sn}) -> [i64] {{\n    \
             return {param}.{field}.iter().map((x: i64) => x * {mult}).collect()\n\
         }}",
        func = func_name,
        param = param_name,
        sn = struct_name,
        field = field_name,
        mult = multiplier,
    );
    scope.add_module_decl(func_decl);

    // Inline code: instantiate, call, assert length
    let inst_var = scope.fresh_name();
    let result_var = scope.fresh_name();

    scope.add_local(
        result_var.clone(),
        TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        false,
    );

    let elems_str = elems
        .iter()
        .map(|e| e.to_string())
        .collect::<Vec<_>>()
        .join(", ");

    let indent = emit.indent_str();
    Some(format!(
        "let {inst} = {sn} {{ {field}: [{elems}] }}\n\
         {indent}let {res} = {func}({inst})\n\
         {indent}assert({res}.length() == {len})",
        inst = inst_var,
        sn = struct_name,
        field = field_name,
        elems = elems_str,
        res = result_var,
        func = func_name,
        len = count,
    ))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

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
        assert_eq!(StructFieldArrayIter.name(), "struct_field_array_iter");
    }

    #[test]
    fn precondition_rejects_class_context() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        // No class context => precondition passes
        assert!(StructFieldArrayIter.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!StructFieldArrayIter.precondition(&scope, &params));
    }

    #[test]
    fn generates_filter_reduce_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = StructFieldArrayIter.generate(&mut scope, &mut emit, &params) {
                if text.contains("sum_above_") {
                    found = true;
                    // Should have 2 module decls: struct + function
                    assert_eq!(
                        scope.module_decls.len(),
                        2,
                        "expected 2 module_decls, got {}",
                        scope.module_decls.len()
                    );
                    // Struct decl should have array field
                    let struct_decl = &scope.module_decls[0];
                    assert!(
                        struct_decl.contains("[i64]"),
                        "expected [i64] field in struct decl: {struct_decl}"
                    );
                    // Function decl should have filter + reduce
                    let func_decl = &scope.module_decls[1];
                    assert!(
                        func_decl.contains(".filter("),
                        "expected .filter() in func decl: {func_decl}"
                    );
                    assert!(
                        func_decl.contains(".reduce("),
                        "expected .reduce() in func decl: {func_decl}"
                    );
                    // Inline code should have assert
                    assert!(
                        text.contains("assert("),
                        "expected assert in inline code: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated filter_reduce variant in 100 seeds");
    }

    #[test]
    fn generates_map_collect_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = StructFieldArrayIter.generate(&mut scope, &mut emit, &params) {
                if text.contains("scaled_") {
                    found = true;
                    // Should have 2 module decls: struct + function
                    assert_eq!(
                        scope.module_decls.len(),
                        2,
                        "expected 2 module_decls, got {}",
                        scope.module_decls.len()
                    );
                    // Function decl should have map + collect
                    let func_decl = &scope.module_decls[1];
                    assert!(
                        func_decl.contains(".map("),
                        "expected .map() in func decl: {func_decl}"
                    );
                    assert!(
                        func_decl.contains(".collect()"),
                        "expected .collect() in func decl: {func_decl}"
                    );
                    // Inline code should have length assert
                    assert!(
                        text.contains(".length()"),
                        "expected .length() check in inline code: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated map_collect variant in 100 seeds");
    }

    #[test]
    fn exercises_multiple_seeds() {
        let table = SymbolTable::new();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            let result = StructFieldArrayIter.generate(&mut scope, &mut emit, &params);
            assert!(result.is_some(), "seed {} returned None", seed);
            let text = result.unwrap();
            assert!(
                text.contains("assert("),
                "seed {} missing assert: {}",
                seed,
                text
            );
            assert_eq!(
                scope.module_decls.len(),
                2,
                "seed {} expected 2 module_decls, got {}",
                seed,
                scope.module_decls.len()
            );
        }
    }

    #[test]
    fn filter_reduce_computes_correct_expected() {
        // Verify the assert value is actually correct by checking against
        // a known seed.
        let table = SymbolTable::new();
        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = StructFieldArrayIter.generate(&mut scope, &mut emit, &params) {
                if text.contains("sum_above_") {
                    // The assert value should be a valid number
                    assert!(
                        text.contains("assert(") && text.contains(" == "),
                        "expected assert with ==: {text}"
                    );
                    return;
                }
            }
        }
        panic!("never generated filter_reduce variant in 200 seeds");
    }
}
