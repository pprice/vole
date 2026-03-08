//! Rule: struct with many fields (8-12) to stress struct layout, field offset
//! calculations, and copy semantics for value types with many fields.
//!
//! Three variants are chosen at random:
//!
//! **Variant 0 -- all i64 fields (10 fields, sum + assert):**
//! ```vole
//! struct AllI64_local0 {
//!     f0: i64
//!     f1: i64
//!     ...
//!     f9: i64
//! }
//! let local1 = AllI64_local0 { f0: 1, f1: 2, ..., f9: 10 }
//! assert(local1.f0 == 1)
//! assert(local1.f9 == 10)
//! let local2 = local1.f0 + local1.f1 + ... + local1.f9
//! assert(local2 == 55)
//! ```
//!
//! **Variant 1 -- mixed i64 + string fields (8 fields):**
//! ```vole
//! struct Mixed_local0 {
//!     n0: i64
//!     s0: string
//!     n1: i64
//!     s1: string
//!     n2: i64
//!     s2: string
//!     n3: i64
//!     s3: string
//! }
//! let local1 = Mixed_local0 { n0: 5, s0: "a", n1: 10, ... }
//! assert(local1.n0 + local1.n1 + local1.n2 + local1.n3 == 50)
//! assert(local1.s0 + local1.s1 + local1.s2 + local1.s3 == "abcd")
//! ```
//!
//! **Variant 2 -- struct copy (10 i64 fields):**
//! ```vole
//! struct CopyCheck_local0 {
//!     f0: i64
//!     ...
//!     f9: i64
//! }
//! let local1 = CopyCheck_local0 { f0: 1, ..., f9: 10 }
//! let local2 = local1
//! assert(local2.f0 == 1)
//! assert(local2.f9 == 10)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct LargeStructLet;

/// Single-character pool for string field values.
const CHAR_POOL: &[char] = &[
    'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p',
];

impl StmtRule for LargeStructLet {
    fn name(&self) -> &'static str {
        "large_struct_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..3);
        match variant {
            0 => emit_all_i64(scope, emit),
            1 => emit_mixed(scope, emit),
            _ => emit_copy_check(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0: all i64 fields (10 fields) -- assert individual + sum
// ---------------------------------------------------------------------------

fn emit_all_i64(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let num_fields: usize = 10;
    let type_name = scope.fresh_name();
    let struct_label = format!("AllI64_{}", type_name);
    let indent = emit.indent_str();

    // Build struct declaration (newline-separated fields, no commas)
    let field_decls: String = (0..num_fields)
        .map(|i| format!("    f{}: i64", i))
        .collect::<Vec<_>>()
        .join("\n");

    let struct_decl = format!("struct {} {{\n{}\n}}", struct_label, field_decls);
    scope.add_module_decl(struct_decl);

    // Generate random values for each field
    let values: Vec<i64> = (0..num_fields).map(|_| emit.gen_i64_range(1, 20)).collect();

    let expected_sum: i64 = values.iter().sum();

    // Build construction: "AllI64_X { f0: 1, f1: 2, ... }"
    let field_values: String = (0..num_fields)
        .map(|i| format!("f{}: {}", i, values[i]))
        .collect::<Vec<_>>()
        .join(", ");

    let inst_name = scope.fresh_name();
    let sum_name = scope.fresh_name();

    // Assert first and last field
    let assert_first = format!("{}assert({}.f0 == {})", indent, inst_name, values[0]);
    let assert_last = format!(
        "{}assert({}.f{} == {})",
        indent,
        inst_name,
        num_fields - 1,
        values[num_fields - 1]
    );

    // Build sum expression
    let sum_expr: String = (0..num_fields)
        .map(|i| format!("{}.f{}", inst_name, i))
        .collect::<Vec<_>>()
        .join(" + ");

    let assert_sum = format!("{}assert({} == {})", indent, sum_name, expected_sum);

    scope.add_local(
        sum_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    Some(format!(
        "let {} = {} {{ {} }}\n{}\n{}\n{}let {} = {}\n{}",
        inst_name,
        struct_label,
        field_values,
        assert_first,
        assert_last,
        indent,
        sum_name,
        sum_expr,
        assert_sum,
    ))
}

// ---------------------------------------------------------------------------
// Variant 1: mixed i64 + string fields (8 fields, alternating)
// ---------------------------------------------------------------------------

fn emit_mixed(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let num_pairs: usize = 4;
    let type_name = scope.fresh_name();
    let struct_label = format!("Mixed_{}", type_name);
    let indent = emit.indent_str();

    // Build struct declaration: alternating n0: i64, s0: string, ...
    let field_decls: String = (0..num_pairs)
        .flat_map(|i| vec![format!("    n{}: i64", i), format!("    s{}: string", i)])
        .collect::<Vec<_>>()
        .join("\n");

    let struct_decl = format!("struct {} {{\n{}\n}}", struct_label, field_decls);
    scope.add_module_decl(struct_decl);

    // Generate random values
    let int_values: Vec<i64> = (0..num_pairs).map(|_| emit.gen_i64_range(1, 20)).collect();
    let char_values: Vec<char> = (0..num_pairs)
        .map(|_| {
            let idx = emit.gen_range(0..CHAR_POOL.len());
            CHAR_POOL[idx]
        })
        .collect();

    let expected_int_sum: i64 = int_values.iter().sum();
    let expected_str_concat: String = char_values.iter().collect();

    // Build construction field values
    let field_values: String = (0..num_pairs)
        .flat_map(|i| {
            vec![
                format!("n{}: {}", i, int_values[i]),
                format!("s{}: \"{}\"", i, char_values[i]),
            ]
        })
        .collect::<Vec<_>>()
        .join(", ");

    let inst_name = scope.fresh_name();

    // Assert sum of i64 fields
    let int_sum_expr: String = (0..num_pairs)
        .map(|i| format!("{}.n{}", inst_name, i))
        .collect::<Vec<_>>()
        .join(" + ");
    let assert_int_sum = format!("{}assert({} == {})", indent, int_sum_expr, expected_int_sum);

    // Assert concat of string fields
    let str_concat_expr: String = (0..num_pairs)
        .map(|i| format!("{}.s{}", inst_name, i))
        .collect::<Vec<_>>()
        .join(" + ");
    let assert_str_concat = format!(
        "{}assert({} == \"{}\")",
        indent, str_concat_expr, expected_str_concat
    );

    // Register the string concat result as usable local
    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    Some(format!(
        "let {} = {} {{ {} }}\n{}\n{}\n{}let {} = {}",
        inst_name,
        struct_label,
        field_values,
        assert_int_sum,
        assert_str_concat,
        indent,
        result_name,
        str_concat_expr,
    ))
}

// ---------------------------------------------------------------------------
// Variant 2: struct copy (10 i64 fields)
// ---------------------------------------------------------------------------

fn emit_copy_check(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let num_fields: usize = 10;
    let type_name = scope.fresh_name();
    let struct_label = format!("CopyCheck_{}", type_name);
    let indent = emit.indent_str();

    // Build struct declaration (newline-separated fields, no commas)
    let field_decls: String = (0..num_fields)
        .map(|i| format!("    f{}: i64", i))
        .collect::<Vec<_>>()
        .join("\n");

    let struct_decl = format!("struct {} {{\n{}\n}}", struct_label, field_decls);
    scope.add_module_decl(struct_decl);

    // Generate random values
    let values: Vec<i64> = (0..num_fields).map(|_| emit.gen_i64_range(1, 20)).collect();

    // Build construction field values
    let field_values: String = (0..num_fields)
        .map(|i| format!("f{}: {}", i, values[i]))
        .collect::<Vec<_>>()
        .join(", ");

    let inst_name = scope.fresh_name();
    let copy_name = scope.fresh_name();

    // Assert first and last field of the copy
    let assert_first = format!("{}assert({}.f0 == {})", indent, copy_name, values[0]);
    let assert_last = format!(
        "{}assert({}.f{} == {})",
        indent,
        copy_name,
        num_fields - 1,
        values[num_fields - 1]
    );

    // Register the copy result as i64 (sum of first two fields as a usable value)
    let sum_name = scope.fresh_name();
    let sum_val = values[0] + values[1];
    scope.add_local(
        sum_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    Some(format!(
        "let {} = {} {{ {} }}\n{}let {} = {}\n{}\n{}\n{}let {} = {}.f0 + {}.f1",
        inst_name,
        struct_label,
        field_values,
        indent,
        copy_name,
        inst_name,
        assert_first,
        assert_last,
        indent,
        sum_name,
        copy_name,
        copy_name,
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

    fn test_params() -> Params {
        Params::from_iter([("probability", ParamValue::Probability(1.0))])
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(LargeStructLet.name(), "large_struct_let");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!LargeStructLet.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(LargeStructLet.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!LargeStructLet.precondition(&scope, &params));
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

            if let Some(text) = LargeStructLet.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("AllI64_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for AllI64"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("f0: i64"),
                        "expected field f0: i64 in decl: {decl}"
                    );
                    assert!(
                        decl.contains("f9: i64"),
                        "expected field f9: i64 in decl: {decl}"
                    );
                    // Should have exactly 10 fields
                    let field_count = decl.matches(": i64").count();
                    assert_eq!(
                        field_count, 10,
                        "expected 10 i64 fields, got {}: {}",
                        field_count, decl,
                    );
                    // No commas between field declarations
                    assert!(
                        !decl.contains(","),
                        "struct decl should not contain commas: {decl}"
                    );
                    // Should have assert and sum expression
                    assert!(text.contains("assert("), "expected assert in code: {text}");
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

            if let Some(text) = LargeStructLet.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("Mixed_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for Mixed"
                    );
                    let decl = &scope.module_decls[0];
                    // Should have 4 i64 fields and 4 string fields
                    let i64_count = decl.matches(": i64").count();
                    assert_eq!(
                        i64_count, 4,
                        "expected 4 i64 fields, got {}: {}",
                        i64_count, decl,
                    );
                    let str_count = decl.matches(": string").count();
                    assert_eq!(
                        str_count, 4,
                        "expected 4 string fields, got {}: {}",
                        str_count, decl,
                    );
                    // No commas between field declarations
                    assert!(
                        !decl.contains(","),
                        "struct decl should not contain commas: {decl}"
                    );
                    // Should have both numeric and string asserts
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    assert!(text.contains(".n0"), "expected n0 field access: {text}");
                    assert!(text.contains(".s0"), "expected s0 field access: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated mixed variant in 100 seeds");
    }

    #[test]
    fn generates_copy_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = LargeStructLet.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("CopyCheck_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for CopyCheck"
                    );
                    let decl = &scope.module_decls[0];
                    // Should have exactly 10 fields
                    let field_count = decl.matches(": i64").count();
                    assert_eq!(
                        field_count, 10,
                        "expected 10 i64 fields, got {}: {}",
                        field_count, decl,
                    );
                    // No commas between field declarations
                    assert!(
                        !decl.contains(","),
                        "struct decl should not contain commas: {decl}"
                    );
                    // Should have copy and asserts
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    // The text should have two let bindings (original + copy)
                    let let_count = text.matches("let ").count();
                    assert!(
                        let_count >= 3,
                        "expected at least 3 let bindings (inst, copy, sum), got {}: {}",
                        let_count,
                        text,
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated copy variant in 100 seeds");
    }

    #[test]
    fn adds_module_decl() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        LargeStructLet.generate(&mut scope, &mut emit, &test_params());
        assert_eq!(
            scope.module_decls.len(),
            1,
            "expected exactly one module decl"
        );
    }

    #[test]
    fn adds_result_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = LargeStructLet.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        assert!(
            !scope.locals.is_empty(),
            "expected result local added to scope"
        );
        let result_local = scope.locals.last().expect("should add result local");
        // Result type depends on variant but should be either I64 or String.
        assert!(
            result_local.1 == TypeInfo::Primitive(PrimitiveType::I64)
                || result_local.1 == TypeInfo::Primitive(PrimitiveType::String),
            "result must be i64 or string, got: {:?}",
            result_local.1,
        );
    }

    #[test]
    fn struct_decl_has_no_commas() {
        let table = SymbolTable::new();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if LargeStructLet
                .generate(&mut scope, &mut emit, &test_params())
                .is_some()
            {
                let decl = &scope.module_decls[0];
                assert!(
                    !decl.contains(","),
                    "struct field decl must not contain commas (seed {}): {}",
                    seed,
                    decl,
                );
            }
        }
    }
}
