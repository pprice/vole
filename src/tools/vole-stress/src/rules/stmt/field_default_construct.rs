//! Rule: struct with field default values to stress default field layout,
//! construction with omitted fields, and default value codegen.
//!
//! Two variants are chosen at random:
//!
//! **Variant 0 -- struct with all-default i64 fields (omit all, override some):**
//! ```vole
//! struct AllDef_42918 {
//!     f1: i64 = 10,
//!     f2: i64 = 20,
//!     f3: i64 = 30,
//! }
//! let inst0 = AllDef_42918 {}
//! let sum0 = inst0.f1 + inst0.f2 + inst0.f3
//! assert(sum0 == 60)
//! let inst1 = AllDef_42918 { f1: 99 }
//! let check1 = inst1.f1
//! assert(check1 == 99)
//! ```
//!
//! **Variant 1 -- struct with mixed required + default fields:**
//! ```vole
//! struct MixDef_42918 {
//!     r1: i64,
//!     r2: i64,
//!     d1: i64 = 100,
//!     d2: i64 = 200,
//! }
//! let inst = MixDef_42918 { r1: 5, r2: 10 }
//! let sum = inst.r1 + inst.r2 + inst.d1 + inst.d2
//! assert(sum == 315)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct FieldDefaultConstruct;

impl StmtRule for FieldDefaultConstruct {
    fn name(&self) -> &'static str {
        "field_default_construct"
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
            0 => emit_all_defaults(scope, emit),
            _ => emit_mixed_defaults(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0: all-default i64 fields -- construct empty, then override some
// ---------------------------------------------------------------------------

fn emit_all_defaults(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let num_fields = emit.random_in(3, 5);
    let uid = emit.gen_range(10000..99999);
    let struct_name = format!("AllDef_{}", uid);

    // Build field declarations with defaults: "f1: i64 = 10, f2: i64 = 20, ..."
    let mut default_values: Vec<i64> = Vec::with_capacity(num_fields);
    let field_decls: String = (1..=num_fields)
        .map(|i| {
            let default_val = emit.gen_range(1..101) as i64;
            default_values.push(default_val);
            format!("    f{}: i64 = {}_i64", i, default_val)
        })
        .collect::<Vec<_>>()
        .join(",\n");

    let struct_decl = format!("struct {} {{\n{},\n}}", struct_name, field_decls);
    scope.add_module_decl(struct_decl);

    let mut lines = Vec::new();

    // --- First construction: all defaults (empty braces) ---
    let inst0 = scope.fresh_name();
    lines.push(format!("let {} = {} {{}}", inst0, struct_name));

    // Sum all fields and assert the expected total
    let sum_expr: String = (1..=num_fields)
        .map(|i| format!("{}.f{}", inst0, i))
        .collect::<Vec<_>>()
        .join(" + ");
    let expected_sum: i64 = default_values.iter().sum();

    let sum0 = scope.fresh_name();
    scope.add_local(sum0.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
    lines.push(format!("let {} = {}", sum0, sum_expr));
    lines.push(format!("assert({} == {}_i64)", sum0, expected_sum));

    // --- Second construction: override 1-2 fields ---
    let num_overrides = emit.random_in(1, 2).min(num_fields);
    let mut override_fields = Vec::with_capacity(num_overrides);
    let mut override_val = 0i64;
    for i in 1..=num_overrides {
        override_val = emit.gen_range(200..999) as i64;
        override_fields.push(format!("f{}: {}_i64", i, override_val));
    }

    let inst1 = scope.fresh_name();
    lines.push(format!(
        "let {} = {} {{ {} }}",
        inst1,
        struct_name,
        override_fields.join(", "),
    ));

    // Assert the last overridden field has the expected value
    let check1 = scope.fresh_name();
    scope.add_local(
        check1.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );
    lines.push(format!("let {} = {}.f{}", check1, inst1, num_overrides));
    lines.push(format!("assert({} == {}_i64)", check1, override_val));

    Some(lines.join("\n"))
}

// ---------------------------------------------------------------------------
// Variant 1: mixed required + default fields -- provide only required
// ---------------------------------------------------------------------------

fn emit_mixed_defaults(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let num_required = emit.random_in(2, 3);
    let num_defaults = emit.random_in(2, 3);
    let uid = emit.gen_range(10000..99999);
    let struct_name = format!("MixDef_{}", uid);

    // Build field declarations: required fields first, then default fields
    let mut field_decls = Vec::with_capacity(num_required + num_defaults);
    for i in 1..=num_required {
        field_decls.push(format!("    r{}: i64", i));
    }

    let mut default_values: Vec<i64> = Vec::with_capacity(num_defaults);
    for i in 1..=num_defaults {
        let default_val = emit.gen_range(10..201) as i64;
        default_values.push(default_val);
        field_decls.push(format!("    d{}: i64 = {}_i64", i, default_val));
    }

    let struct_decl = format!(
        "struct {} {{\n{},\n}}",
        struct_name,
        field_decls.join(",\n")
    );
    scope.add_module_decl(struct_decl);

    let mut lines = Vec::new();

    // Construct providing only required fields
    let mut required_values: Vec<i64> = Vec::with_capacity(num_required);
    let construction_fields: String = (1..=num_required)
        .map(|i| {
            let val = emit.gen_range(1..101) as i64;
            required_values.push(val);
            format!("r{}: {}_i64", i, val)
        })
        .collect::<Vec<_>>()
        .join(", ");

    let inst = scope.fresh_name();
    lines.push(format!(
        "let {} = {} {{ {} }}",
        inst, struct_name, construction_fields,
    ));

    // Sum all fields (required + default) and assert expected total
    let mut sum_parts = Vec::with_capacity(num_required + num_defaults);
    for i in 1..=num_required {
        sum_parts.push(format!("{}.r{}", inst, i));
    }
    for i in 1..=num_defaults {
        sum_parts.push(format!("{}.d{}", inst, i));
    }
    let sum_expr = sum_parts.join(" + ");

    let expected_sum: i64 =
        required_values.iter().sum::<i64>() + default_values.iter().sum::<i64>();

    let sum_name = scope.fresh_name();
    scope.add_local(
        sum_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );
    lines.push(format!("let {} = {}", sum_name, sum_expr));
    lines.push(format!("assert({} == {}_i64)", sum_name, expected_sum));

    Some(lines.join("\n"))
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
        assert_eq!(FieldDefaultConstruct.name(), "field_default_construct");
    }

    #[test]
    fn precondition_rejects_class_methods() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        // No class sym id => precondition passes
        assert!(FieldDefaultConstruct.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!FieldDefaultConstruct.precondition(&scope, &params));
    }

    #[test]
    fn generates_all_defaults_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = FieldDefaultConstruct.generate(&mut scope, &mut emit, &params) {
                if text.contains("AllDef_") {
                    found = true;
                    // Verify module decl was registered
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for AllDef"
                    );
                    let decl = &scope.module_decls[0];
                    // Should have field defaults
                    assert!(
                        decl.contains("= "),
                        "expected default values in decl: {decl}"
                    );
                    // Should have 3-5 fields
                    let field_count = decl.matches(": i64 =").count();
                    assert!(
                        (3..=5).contains(&field_count),
                        "expected 3-5 default fields, got {}: {}",
                        field_count,
                        decl,
                    );
                    // Result stmt should construct with empty braces
                    assert!(
                        text.contains("{}"),
                        "expected empty-brace construction in stmt: {text}"
                    );
                    // Should have assert statements
                    assert!(text.contains("assert("), "expected assert in stmt: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated all-defaults variant in 100 seeds");
    }

    #[test]
    fn generates_mixed_defaults_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = FieldDefaultConstruct.generate(&mut scope, &mut emit, &params) {
                if text.contains("MixDef_") {
                    found = true;
                    // Verify module decl was registered
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for MixDef"
                    );
                    let decl = &scope.module_decls[0];
                    // Should have required fields (no default)
                    assert!(
                        decl.contains("r1: i64,") || decl.contains("r1: i64\n"),
                        "expected required field r1 in decl: {decl}"
                    );
                    // Should have default fields
                    assert!(
                        decl.contains("d1: i64 ="),
                        "expected default field d1 in decl: {decl}"
                    );
                    // Construction should only have required fields
                    assert!(
                        text.contains("r1:") && !text.contains("d1:"),
                        "expected only required fields in construction: {text}"
                    );
                    // Should have assert statements
                    assert!(text.contains("assert("), "expected assert in stmt: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated mixed-defaults variant in 100 seeds");
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

        FieldDefaultConstruct.generate(&mut scope, &mut emit, &params);
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

        let result = FieldDefaultConstruct.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        assert!(
            scope.locals.len() >= 1,
            "expected at least 1 local (sum result), got {}",
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

            if FieldDefaultConstruct
                .generate(&mut scope, &mut emit, &params)
                .is_some()
            {
                let decl = &scope.module_decls[0];
                // Count all typed field declarations
                let field_count = decl.lines().filter(|l| l.contains(": i64")).count();
                if decl.contains("AllDef_") {
                    assert!(
                        (3..=5).contains(&field_count),
                        "expected 3-5 fields for AllDef, got {} for seed {}: {}",
                        field_count,
                        seed,
                        decl,
                    );
                } else {
                    // MixDef: 2-3 required + 2-3 default = 4-6 total
                    assert!(
                        (4..=6).contains(&field_count),
                        "expected 4-6 fields for MixDef, got {} for seed {}: {}",
                        field_count,
                        seed,
                        decl,
                    );
                }
            }
        }
    }

    #[test]
    fn defaults_after_required_in_mixed_variant() {
        let table = SymbolTable::new();
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(_text) = FieldDefaultConstruct.generate(&mut scope, &mut emit, &params) {
                let decl = &scope.module_decls[0];
                if decl.contains("MixDef_") {
                    // Verify ordering: all required fields before any default field
                    let lines: Vec<&str> = decl.lines().collect();
                    let mut seen_default = false;
                    for line in &lines {
                        if line.contains(": i64 =") {
                            seen_default = true;
                        } else if line.contains(": i64") && !line.contains("=") && seen_default {
                            panic!(
                                "required field after default field in seed {}: {}",
                                seed, decl,
                            );
                        }
                    }
                }
            }
        }
    }
}
