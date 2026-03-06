//! Rule: class with many fields (10-15) to stress instance layout, field
//! offset calculations, and RC handling for multiple string fields.
//!
//! Two variants are chosen at random:
//!
//! **Variant 0 -- all i64 fields (sum all):**
//! ```vole
//! class BigClass_42918 {
//!     f1: i64,
//!     f2: i64,
//!     ...
//!     f12: i64,
//! }
//! let inst = BigClass_42918 { f1: 1, f2: 2, ..., f12: 12 }
//! let total = inst.f1 + inst.f2 + ... + inst.f12
//! ```
//!
//! **Variant 1 -- mixed i64 and string fields (access all):**
//! ```vole
//! class MixedClass_42918 {
//!     n1: i64,
//!     n2: i64,
//!     ...
//!     s1: string,
//!     s2: string,
//!     ...
//! }
//! let inst = MixedClass_42918 { n1: 1, n2: 2, ..., s1: "hello", s2: "world", ... }
//! let num_sum = inst.n1 + inst.n2 + ...
//! let str_result = inst.s1
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct LargeClassInstance;

/// Fixed pool of short string literals for string field values.
const STRING_POOL: &[&str] = &[
    "\"hello\"",
    "\"world\"",
    "\"foo\"",
    "\"bar\"",
    "\"baz\"",
    "\"qux\"",
    "\"abc\"",
    "\"xyz\"",
];

impl StmtRule for LargeClassInstance {
    fn name(&self) -> &'static str {
        "large_class_instance"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Only fire outside class methods -- module-level decls cannot be
        // spliced inside a class body.
        scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..2);
        match variant {
            0 => emit_all_i64(scope, emit),
            _ => emit_mixed(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0: all i64 fields -- sum them all
// ---------------------------------------------------------------------------

fn emit_all_i64(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let num_fields = emit.random_in(10, 15);
    let uid = emit.gen_range(10000..99999);
    let class_name = format!("BigClass_{}", uid);

    // Build field declarations: "f1: i64, f2: i64, ..."
    let field_decls: String = (1..=num_fields)
        .map(|i| format!("    f{}: i64", i))
        .collect::<Vec<_>>()
        .join(",\n");

    let class_decl = format!("class {} {{\n{},\n}}", class_name, field_decls);
    scope.add_module_decl(class_decl);

    // Build construction: "BigClass_NNNNN { f1: 1, f2: 2, ... }"
    let field_values: String = (1..=num_fields)
        .map(|i| {
            let lit = emit.gen_range(1..101) as i64;
            format!("f{}: {}_i64", i, lit)
        })
        .collect::<Vec<_>>()
        .join(", ");

    let inst_name = scope.fresh_name();
    let sum_name = scope.fresh_name();

    // Register inst as i64 (we don't have a class sym id to use for TypeInfo::Class)
    scope.add_local(
        inst_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    // Build sum expression: "inst.f1 + inst.f2 + ... + inst.fN"
    let sum_expr: String = (1..=num_fields)
        .map(|i| format!("{}.f{}", inst_name, i))
        .collect::<Vec<_>>()
        .join(" + ");

    scope.add_local(
        sum_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    Some(format!(
        "let {} = {} {{ {} }}\nlet {} = {}",
        inst_name, class_name, field_values, sum_name, sum_expr,
    ))
}

// ---------------------------------------------------------------------------
// Variant 1: mixed i64 + string fields -- access all
// ---------------------------------------------------------------------------

fn emit_mixed(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let num_i64 = emit.random_in(7, 10);
    let num_str = emit.random_in(3, 5);
    let uid = emit.gen_range(10000..99999);
    let class_name = format!("MixedClass_{}", uid);

    // Build field declarations with i64 fields first, then string fields
    let mut field_decls = Vec::with_capacity(num_i64 + num_str);
    for i in 1..=num_i64 {
        field_decls.push(format!("    n{}: i64", i));
    }
    for i in 1..=num_str {
        field_decls.push(format!("    s{}: string", i));
    }

    let class_decl = format!("class {} {{\n{},\n}}", class_name, field_decls.join(",\n"),);
    scope.add_module_decl(class_decl);

    // Build construction field values
    let mut construction_fields = Vec::with_capacity(num_i64 + num_str);
    for i in 1..=num_i64 {
        let lit = emit.gen_range(1..101) as i64;
        construction_fields.push(format!("n{}: {}_i64", i, lit));
    }
    for i in 1..=num_str {
        let idx = emit.gen_range(0..STRING_POOL.len());
        construction_fields.push(format!("s{}: {}", i, STRING_POOL[idx]));
    }

    let inst_name = scope.fresh_name();

    // Register inst as i64 (best-effort; class sym id is not available)
    scope.add_local(
        inst_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    // Build sum of i64 fields
    let sum_expr: String = (1..=num_i64)
        .map(|i| format!("{}.n{}", inst_name, i))
        .collect::<Vec<_>>()
        .join(" + ");

    let sum_name = scope.fresh_name();
    scope.add_local(
        sum_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    // Bind the first string field for RC access
    let str_name = scope.fresh_name();
    scope.add_local(
        str_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    Some(format!(
        "let {} = {} {{ {} }}\nlet {} = {}\nlet {} = {}.s1",
        inst_name,
        class_name,
        construction_fields.join(", "),
        sum_name,
        sum_expr,
        str_name,
        inst_name,
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
        assert_eq!(LargeClassInstance.name(), "large_class_instance");
    }

    #[test]
    fn precondition_rejects_class_methods() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        // No class sym id => precondition passes
        assert!(LargeClassInstance.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!LargeClassInstance.precondition(&scope, &params));
    }

    #[test]
    fn generates_all_i64_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = LargeClassInstance.generate(&mut scope, &mut emit, &params) {
                if text.contains("BigClass_") {
                    found = true;
                    // Verify module decl was registered
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for BigClass"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("f1: i64"),
                        "expected field f1: i64 in decl: {decl}"
                    );
                    // Should have at least 10 fields
                    let field_count = decl.matches(": i64").count();
                    assert!(
                        field_count >= 10,
                        "expected >= 10 i64 fields, got {}: {}",
                        field_count,
                        decl,
                    );
                    // Result stmt should have a sum expression
                    assert!(
                        text.contains(" + "),
                        "expected sum expression in stmt: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated all-i64 variant in 100 seeds");
    }

    #[test]
    fn generates_mixed_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = LargeClassInstance.generate(&mut scope, &mut emit, &params) {
                if text.contains("MixedClass_") {
                    found = true;
                    // Verify module decl was registered
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for MixedClass"
                    );
                    let decl = &scope.module_decls[0];
                    // Should have i64 fields
                    assert!(
                        decl.contains("n1: i64"),
                        "expected field n1: i64 in decl: {decl}"
                    );
                    // Should have string fields
                    assert!(
                        decl.contains("s1: string"),
                        "expected field s1: string in decl: {decl}"
                    );
                    // Stmt should access string field
                    assert!(
                        text.contains(".s1"),
                        "expected string field access in stmt: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated mixed variant in 100 seeds");
    }

    #[test]
    fn adds_module_decl() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        LargeClassInstance.generate(&mut scope, &mut emit, &params);
        assert_eq!(
            scope.module_decls.len(),
            1,
            "expected exactly one module decl"
        );
    }

    #[test]
    fn adds_locals_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = LargeClassInstance.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        assert!(
            scope.locals.len() >= 2,
            "expected at least 2 locals (inst + result), got {}",
            scope.locals.len(),
        );
    }

    #[test]
    fn field_count_in_range() {
        let table = SymbolTable::new();
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if LargeClassInstance
                .generate(&mut scope, &mut emit, &params)
                .is_some()
            {
                let decl = &scope.module_decls[0];
                // Count all typed field declarations
                let field_count = decl.lines().filter(|l| l.contains(": ")).count();
                assert!(
                    (10..=15).contains(&field_count),
                    "expected 10-15 fields, got {} for seed {}: {}",
                    field_count,
                    seed,
                    decl,
                );
            }
        }
    }

    #[test]
    fn mixed_variant_has_string_fields() {
        let table = SymbolTable::new();
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = LargeClassInstance.generate(&mut scope, &mut emit, &params) {
                if text.contains("MixedClass_") {
                    let decl = &scope.module_decls[0];
                    let str_count = decl.matches(": string").count();
                    assert!(
                        (3..=5).contains(&str_count),
                        "expected 3-5 string fields, got {}: {}",
                        str_count,
                        decl,
                    );
                    let i64_count = decl.matches(": i64").count();
                    assert!(
                        (7..=10).contains(&i64_count),
                        "expected 7-10 i64 fields, got {}: {}",
                        i64_count,
                        decl,
                    );
                }
            }
        }
    }
}
