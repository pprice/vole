use super::*;
use crate::symbols::{ClassInfo, FieldInfo};
use rand::SeedableRng;

#[test]
fn test_literal_generation() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let config = ExprConfig::default();
    let mut generator = ExprGenerator::new(&mut rng, &config);

    let i64_lit = generator.literal_for_primitive(PrimitiveType::I64);
    assert!(!i64_lit.is_empty());

    let bool_lit = generator.literal_for_primitive(PrimitiveType::Bool);
    assert!(bool_lit == "true" || bool_lit == "false");

    let str_lit = generator.literal_for_primitive(PrimitiveType::String);
    assert!(str_lit.starts_with('"'));
}

#[test]
fn test_expr_generation() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let config = ExprConfig::default();
    let mut generator = ExprGenerator::new(&mut rng, &config);

    let table = SymbolTable::new();
    let ctx = ExprContext::new(&[], &[], &table);

    let i64_expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
    assert!(!i64_expr.is_empty());

    let bool_expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &ctx, 0);
    assert!(!bool_expr.is_empty());
}

#[test]
fn test_when_expr_generation() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let config = ExprConfig::default();
    let mut generator = ExprGenerator::new(&mut rng, &config);

    let table = SymbolTable::new();
    let ctx = ExprContext::new(&[], &[], &table);

    let when_expr = generator.generate_when_expr(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
    assert!(when_expr.contains("when"));
    assert!(when_expr.contains("=>"));
}

#[test]
fn test_interpolated_string_generation() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(99);
    let config = ExprConfig::default();
    let mut generator = ExprGenerator::new(&mut rng, &config);

    let table = SymbolTable::new();
    let params = vec![
        ParamInfo {
            name: "count".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::I64),
        },
        ParamInfo {
            name: "label".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::String),
        },
    ];
    let ctx = ExprContext::new(&params, &[], &table);

    let interp = generator.generate_interpolated_string(&ctx);
    assert!(interp.starts_with('"'));
    assert!(interp.ends_with('"'));
    // Should contain at least one interpolation brace
    assert!(interp.contains('{'));
    assert!(interp.contains('}'));
}

#[test]
fn test_interpolated_string_no_vars_fallback() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let config = ExprConfig::default();
    let mut generator = ExprGenerator::new(&mut rng, &config);

    let table = SymbolTable::new();
    let ctx = ExprContext::new(&[], &[], &table);

    // With no variables in scope, should fall back to plain string
    let result = generator.generate_interpolated_string(&ctx);
    assert!(result.starts_with('"'));
    assert!(result.ends_with('"'));
    // Should NOT contain interpolation braces (it's a plain "strN" literal)
    assert!(!result.contains('{'));
}

#[test]
fn test_interpolated_string_length_calls() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();

    // Set up an array and a string variable in scope
    let locals = vec![
        (
            "items".to_string(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        ),
        (
            "text".to_string(),
            TypeInfo::Primitive(PrimitiveType::String),
        ),
    ];

    let mut found_array_length = false;
    let mut found_string_length = false;

    // Run across many seeds to exercise the 30% probability branches
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        let result = generator.generate_interpolated_string(&ctx);

        if result.contains("items.length()") {
            found_array_length = true;
        }
        if result.contains("text.length()") {
            found_string_length = true;
        }
        if found_array_length && found_string_length {
            break;
        }
    }

    assert!(
        found_array_length,
        "Expected at least one array .length() call in interpolation across 500 seeds"
    );
    assert!(
        found_string_length,
        "Expected at least one string .length() call in interpolation across 500 seeds"
    );
}

#[test]
fn test_interpolated_string_arithmetic_ops() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();

    let locals = vec![
        ("count".to_string(), TypeInfo::Primitive(PrimitiveType::I64)),
        ("flag".to_string(), TypeInfo::Primitive(PrimitiveType::Bool)),
        ("rate".to_string(), TypeInfo::Primitive(PrimitiveType::F64)),
    ];

    let mut found_sub = false;
    let mut found_mul = false;
    let mut found_bool_neg = false;
    let mut found_f64_arith = false;

    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        let result = generator.generate_interpolated_string(&ctx);

        if result.contains("count -") || result.contains("count *") {
            if result.contains("count -") {
                found_sub = true;
            }
            if result.contains("count *") {
                found_mul = true;
            }
        }
        if result.contains("!flag") {
            found_bool_neg = true;
        }
        if result.contains("rate +") || result.contains("rate -") || result.contains("rate *") {
            found_f64_arith = true;
        }
        if found_sub && found_mul && found_bool_neg && found_f64_arith {
            break;
        }
    }

    assert!(
        found_sub,
        "Expected at least one subtraction in interpolation across 500 seeds"
    );
    assert!(
        found_mul,
        "Expected at least one multiplication in interpolation across 500 seeds"
    );
    assert!(
        found_bool_neg,
        "Expected at least one boolean negation in interpolation across 500 seeds"
    );
    assert!(
        found_f64_arith,
        "Expected at least one f64 arithmetic in interpolation across 500 seeds"
    );
}

#[test]
fn test_interpolated_string_class_field_access() {
    use crate::symbols::StructInfo;

    let config = ExprConfig::default();
    let mut table = SymbolTable::new();

    // Create a module with a class and a struct that have printable fields
    let mod_id = table.add_module("test_mod".to_string(), "test_mod.vole".to_string());
    let module = table.get_module_mut(mod_id).unwrap();

    let class_id = module.add_symbol(
        "MyClass".to_string(),
        SymbolKind::Class(ClassInfo {
            type_params: vec![],
            fields: vec![
                FieldInfo {
                    name: "name".to_string(),
                    field_type: TypeInfo::Primitive(PrimitiveType::String),
                },
                FieldInfo {
                    name: "count".to_string(),
                    field_type: TypeInfo::Primitive(PrimitiveType::I64),
                },
            ],
            methods: vec![],
            implements: vec![],
            static_methods: vec![],
        }),
    );

    let struct_id = module.add_symbol(
        "MyStruct".to_string(),
        SymbolKind::Struct(StructInfo {
            fields: vec![
                FieldInfo {
                    name: "label".to_string(),
                    field_type: TypeInfo::Primitive(PrimitiveType::String),
                },
                FieldInfo {
                    name: "value".to_string(),
                    field_type: TypeInfo::Primitive(PrimitiveType::I32),
                },
            ],
            static_methods: vec![],
        }),
    );

    // Locals: one class instance and one struct instance
    let locals = vec![
        ("obj".to_string(), TypeInfo::Class(mod_id, class_id)),
        ("rec".to_string(), TypeInfo::Struct(mod_id, struct_id)),
    ];

    let mut found_class_field = false;
    let mut found_struct_field = false;

    // Run across many seeds to exercise the 30% probability branch
    for seed in 0..2000 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        let result = generator.generate_interpolated_string(&ctx);

        if result.contains("obj.name") || result.contains("obj.count") {
            found_class_field = true;
        }
        if result.contains("rec.label") || result.contains("rec.value") {
            found_struct_field = true;
        }
        if found_class_field && found_struct_field {
            break;
        }
    }

    assert!(
        found_class_field,
        "Expected at least one class field access in interpolation across 2000 seeds"
    );
    assert!(
        found_struct_field,
        "Expected at least one struct field access in interpolation across 2000 seeds"
    );
}

#[test]
fn test_method_call_interpolation() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();

    // Set up a string and an array variable in scope
    let locals = vec![
        (
            "msg".to_string(),
            TypeInfo::Primitive(PrimitiveType::String),
        ),
        (
            "nums".to_string(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        ),
    ];

    let mut found_string_method = false;
    let mut found_array_length = false;

    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);

        if let Some(result) = generator.try_generate_method_call_interpolation(&ctx) {
            assert!(result.starts_with('"'), "Should be a string: {}", result);
            assert!(result.ends_with('"'), "Should be a string: {}", result);
            assert!(
                result.contains('{'),
                "Should have interpolation: {}",
                result
            );

            if result.contains("msg.to_upper()")
                || result.contains("msg.to_lower()")
                || result.contains("msg.trim()")
                || result.contains("msg.length()")
            {
                found_string_method = true;
            }
            if result.contains("nums.length()") {
                found_array_length = true;
            }
        }
        if found_string_method && found_array_length {
            break;
        }
    }

    assert!(
        found_string_method,
        "Expected at least one string method call interpolation across 500 seeds"
    );
    assert!(
        found_array_length,
        "Expected at least one array .length() interpolation across 500 seeds"
    );
}

#[test]
fn test_method_call_interpolation_no_candidates() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();

    // Only numeric variables - no strings or arrays
    let locals = vec![
        ("x".to_string(), TypeInfo::Primitive(PrimitiveType::I64)),
        ("y".to_string(), TypeInfo::Primitive(PrimitiveType::Bool)),
    ];

    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let mut generator = ExprGenerator::new(&mut rng, &config);
    let ctx = ExprContext::new(&[], &locals, &table);

    assert!(
        generator
            .try_generate_method_call_interpolation(&ctx)
            .is_none()
    );
}

#[test]
fn test_bitwise_generation() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let ctx = ExprContext::new(&[], &[], &table);

    let bitwise_ops = ["&", "|", "^", "<<", ">>"];
    let mut found = std::collections::HashSet::new();

    // Generate many expressions across different seeds to find bitwise ops
    for seed in 0..200 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
        for op in &bitwise_ops {
            if expr.contains(op) {
                found.insert(*op);
            }
        }
    }

    // We should find at least some bitwise ops across 200 seeds
    assert!(
        found.len() >= 3,
        "Expected at least 3 bitwise ops, found: {:?}",
        found,
    );
}

#[test]
fn test_bitwise_shift_rhs_is_small_literal() {
    let config = ExprConfig {
        // Use moderate probabilities so generated bitwise expressions stay
        // simple enough for the rfind-based shift RHS parser below.
        max_depth: 3,
        binary_probability: 0.4,
        when_probability: 0.1,
        match_probability: 0.1,
        if_expr_probability: 0.15,
        lambda_probability: 0.05,
        ..ExprConfig::default()
    };
    let table = SymbolTable::new();
    let ctx = ExprContext::new(&[], &[], &table);

    // Generate many bitwise expressions directly and check shift RHS
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let expr = generator.generate_binary_bitwise(PrimitiveType::I64, &ctx, 2);

        // If it's a shift expression, the RHS should be a small literal
        if expr.contains("<<") || expr.contains(">>") {
            // The expression is like "(LHS << N_i64)" or "(LHS >> N_i64)"
            let shift_op = if expr.contains("<<") { "<<" } else { ">>" };
            if let Some(rhs_start) = expr.rfind(shift_op) {
                let rhs = &expr[rhs_start + shift_op.len()..].trim();
                // RHS should end with "_i64)" and the number should be 0-31
                let rhs = rhs.trim_end_matches(')').trim();
                let num_str = rhs.trim_end_matches("_i64").trim_end_matches("_i32");
                let num: i64 = num_str.parse().expect(&format!(
                    "Failed to parse shift RHS '{}' from expr '{}'",
                    num_str, expr
                ));
                assert!(
                    num >= 0 && num <= 31,
                    "Shift amount {} out of range in expr: {}",
                    num,
                    expr,
                );
            }
        }
    }
}

#[test]
fn test_bitwise_not_generation() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let ctx = ExprContext::new(&[], &[], &table);

    // Check that bitwise NOT appears in i64 expressions
    let mut found_i64 = false;
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
        if expr.contains('~') {
            found_i64 = true;
            break;
        }
    }
    assert!(
        found_i64,
        "Expected at least one bitwise NOT (~) expression for i64 across 500 seeds",
    );

    // Check that bitwise NOT appears in wider integer types (e.g. u8)
    let mut found_u8 = false;
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::U8), &ctx, 0);
        if expr.contains('~') {
            found_u8 = true;
            break;
        }
    }
    assert!(
        found_u8,
        "Expected at least one bitwise NOT (~) expression for u8 across 500 seeds",
    );
}

#[test]
fn test_determinism() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let ctx = ExprContext::new(&[], &[], &table);

    let mut rng1 = rand::rngs::StdRng::seed_from_u64(12345);
    let mut gen1 = ExprGenerator::new(&mut rng1, &config);
    let expr1 = gen1.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);

    let mut rng2 = rand::rngs::StdRng::seed_from_u64(12345);
    let mut gen2 = ExprGenerator::new(&mut rng2, &config);
    let expr2 = gen2.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);

    assert_eq!(expr1, expr2);
}

#[test]
fn test_is_expr_with_union_param() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let params = vec![ParamInfo {
        name: "val".to_string(),
        param_type: TypeInfo::Union(vec![
            TypeInfo::Primitive(PrimitiveType::I32),
            TypeInfo::Primitive(PrimitiveType::String),
        ]),
    }];

    let mut found_is = false;
    for seed in 0..100 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&params, &[], &table);
        if let Some(expr) = generator.generate_is_expr(&ctx) {
            assert!(
                expr.contains("val is "),
                "Expected 'val is ...', got: {}",
                expr
            );
            assert!(
                expr == "(val is i32)" || expr == "(val is string)",
                "Unexpected is expr: {}",
                expr,
            );
            found_is = true;
        }
    }
    assert!(found_is, "Expected to generate at least one is expression");
}

#[test]
fn test_is_expr_no_union_vars() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let config = ExprConfig::default();
    let mut generator = ExprGenerator::new(&mut rng, &config);

    let table = SymbolTable::new();
    let ctx = ExprContext::new(&[], &[], &table);

    // With no union-typed vars, should return None
    assert!(generator.generate_is_expr(&ctx).is_none());
}

#[test]
fn test_is_expr_in_bool_generation() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let params = vec![ParamInfo {
        name: "x".to_string(),
        param_type: TypeInfo::Union(vec![
            TypeInfo::Primitive(PrimitiveType::I64),
            TypeInfo::Primitive(PrimitiveType::Bool),
        ]),
    }];

    let mut found_is = false;
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&params, &[], &table);
        let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &ctx, 0);
        if expr.contains(" is ") {
            found_is = true;
            break;
        }
    }
    assert!(
        found_is,
        "Expected at least one 'is' expression in bool generation across 500 seeds",
    );
}

#[test]
fn test_union_type_expr_generation() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();

    let union_ty = TypeInfo::Union(vec![
        TypeInfo::Primitive(PrimitiveType::I32),
        TypeInfo::Primitive(PrimitiveType::String),
    ]);

    // Should generate valid expressions for union types
    for seed in 0..50 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &[], &table);
        let expr = generator.generate(&union_ty, &ctx, 0);
        assert!(
            !expr.is_empty(),
            "Union type expression should not be empty"
        );
    }
}

#[test]
fn test_null_coalesce_with_optional_var() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let locals = vec![(
        "opt_val".to_string(),
        TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
    )];

    let mut found_coalesce = false;
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
        if expr.contains("??") {
            assert!(
                expr.contains("opt_val"),
                "Null coalesce should reference the optional variable, got: {}",
                expr,
            );
            found_coalesce = true;
            break;
        }
    }
    assert!(
        found_coalesce,
        "Expected at least one null coalescing expression across 500 seeds",
    );
}

#[test]
fn test_null_coalesce_no_optional_vars() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let locals = vec![(
        "plain_val".to_string(),
        TypeInfo::Primitive(PrimitiveType::I64),
    )];

    // With no optional-typed vars, ?? should never appear
    for seed in 0..200 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
        assert!(
            !expr.contains("??"),
            "Should not generate ?? without optional vars, got: {}",
            expr,
        );
    }
}

#[test]
fn test_null_coalesce_type_mismatch_not_generated() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    // Optional<String> should NOT produce ?? when generating i64
    let locals = vec![(
        "opt_str".to_string(),
        TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
    )];

    for seed in 0..200 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
        assert!(
            !expr.contains("??"),
            "Should not generate ?? with mismatched inner type, got: {}",
            expr,
        );
    }
}

#[test]
fn test_null_coalesce_chained_with_multiple_optionals() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    // Multiple optional<i64> variables to enable chained coalescing
    let locals = vec![
        (
            "opt_a".to_string(),
            TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        ),
        (
            "opt_b".to_string(),
            TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        ),
        (
            "opt_c".to_string(),
            TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        ),
    ];

    let mut found_chained = false;
    for seed in 0..2000 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        if let Some(expr) =
            generator.try_generate_null_coalesce(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0)
        {
            // Count the number of ?? operators in the expression
            let coalesce_count = expr.matches("??").count();
            if coalesce_count >= 2 {
                // Chained: e.g. (opt_a ?? opt_b ?? 42_i64)
                found_chained = true;
                break;
            }
        }
    }
    assert!(
        found_chained,
        "Expected at least one chained null coalescing expression (2+ ??) across 2000 seeds",
    );
}

#[test]
fn test_null_coalesce_single_optional_never_chains() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    // Only one optional variable - the top-level pattern should be
    // `(only_opt ?? <default>)` with exactly one leading `??` from
    // our coalesce.  (The default sub-expression may itself contain
    // `??` from recursive generation, so we only check the prefix.)
    let locals = vec![(
        "only_opt".to_string(),
        TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
    )];

    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        if let Some(expr) =
            generator.try_generate_null_coalesce(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0)
        {
            // The expression should start with `(only_opt ?? ` --
            // i.e. only one optional var before the default.
            assert!(
                expr.starts_with("(only_opt ?? "),
                "With one optional var, chain should start with '(only_opt ?? ', got: {}",
                expr,
            );
            // Ensure there's no second optional chained before the default
            // (strip the first `(only_opt ?? ` prefix, the remainder should
            // not start with another `only_opt ??`)
            let rest = &expr["(only_opt ?? ".len()..];
            assert!(
                !rest.starts_with("only_opt ?? "),
                "Should not chain the same optional var twice at top level, got: {}",
                expr,
            );
        }
    }
}

#[test]
fn test_optional_chaining_with_class_optional() {
    let config = ExprConfig::default();
    let mut table = SymbolTable::new();
    let mod_id = table.add_module("test_mod".to_string(), "test_mod.vole".to_string());

    // Create a class with an i64 field
    let sym_id = table.get_module_mut(mod_id).unwrap().add_symbol(
        "Point".to_string(),
        SymbolKind::Class(ClassInfo {
            type_params: vec![],
            fields: vec![FieldInfo {
                name: "x".to_string(),
                field_type: TypeInfo::Primitive(PrimitiveType::I64),
            }],
            methods: vec![],
            implements: vec![],
            static_methods: vec![],
        }),
    );

    // Local variable of type Point?
    let locals = vec![(
        "opt_point".to_string(),
        TypeInfo::Optional(Box::new(TypeInfo::Class(mod_id, sym_id))),
    )];

    let mut found_chaining = false;
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        // Generate Optional<i64> - the result of ?.x on Point?
        let expr = generator.generate(
            &TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            &ctx,
            0,
        );
        if expr.contains("?.") {
            assert!(
                expr.contains("opt_point?.x"),
                "Optional chaining should reference opt_point?.x, got: {}",
                expr,
            );
            found_chaining = true;
            break;
        }
    }
    assert!(
        found_chaining,
        "Expected at least one optional chaining expression across 500 seeds",
    );
}

#[test]
fn test_optional_chaining_no_class_optionals() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    // Only a plain optional, no class-typed optional
    let locals = vec![(
        "opt_num".to_string(),
        TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
    )];

    for seed in 0..200 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        let expr = generator.generate(
            &TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            &ctx,
            0,
        );
        assert!(
            !expr.contains("?."),
            "Should not generate ?. without class-typed optional, got: {}",
            expr,
        );
    }
}

#[test]
fn test_null_coalesce_direct() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let locals = vec![(
        "maybe".to_string(),
        TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::Bool))),
    )];

    let mut found = false;
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        if let Some(expr) =
            generator.try_generate_null_coalesce(&TypeInfo::Primitive(PrimitiveType::Bool), &ctx, 0)
        {
            assert!(
                expr.contains("maybe"),
                "Should reference 'maybe', got: {}",
                expr
            );
            assert!(expr.contains("??"), "Should contain '??', got: {}", expr);
            found = true;
            break;
        }
    }
    assert!(
        found,
        "Expected try_generate_null_coalesce to succeed at least once"
    );
}

#[test]
fn test_optional_chaining_direct() {
    let config = ExprConfig::default();
    let mut table = SymbolTable::new();
    let mod_id = table.add_module("m".to_string(), "m.vole".to_string());
    let sym_id = table.get_module_mut(mod_id).unwrap().add_symbol(
        "Rec".to_string(),
        SymbolKind::Class(ClassInfo {
            type_params: vec![],
            fields: vec![
                FieldInfo {
                    name: "val".to_string(),
                    field_type: TypeInfo::Primitive(PrimitiveType::I32),
                },
                FieldInfo {
                    name: "name".to_string(),
                    field_type: TypeInfo::Primitive(PrimitiveType::String),
                },
            ],
            methods: vec![],
            implements: vec![],
            static_methods: vec![],
        }),
    );

    let locals = vec![(
        "opt_rec".to_string(),
        TypeInfo::Optional(Box::new(TypeInfo::Class(mod_id, sym_id))),
    )];

    let mut found = false;
    for seed in 0..100 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        if let Some((expr, result_ty)) = generator.try_generate_optional_chaining(&ctx) {
            assert!(
                expr.starts_with("opt_rec?."),
                "Should start with 'opt_rec?.', got: {}",
                expr,
            );
            assert!(
                expr == "opt_rec?.val" || expr == "opt_rec?.name",
                "Should reference a field, got: {}",
                expr,
            );
            // Result type should be Optional
            assert!(
                matches!(result_ty, TypeInfo::Optional(_)),
                "Result type should be Optional, got: {:?}",
                result_ty,
            );
            found = true;
            break;
        }
    }
    assert!(
        found,
        "Expected try_generate_optional_chaining to succeed at least once"
    );
}

#[test]
fn test_array_index_with_matching_array_var() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let locals = vec![(
        "nums".to_string(),
        TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
    )];

    let mut found_index = false;
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
        if expr.contains("nums[") {
            // Index should be 0 or 1 with _i64 suffix
            assert!(
                expr.contains("nums[0_i64]") || expr.contains("nums[1_i64]"),
                "Array index should use small constant index (0 or 1), got: {}",
                expr,
            );
            found_index = true;
            break;
        }
    }
    assert!(
        found_index,
        "Expected at least one array index expression across 500 seeds",
    );
}

#[test]
fn test_array_index_no_matching_array_vars() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    // Array of strings should NOT produce array index when generating i64
    let locals = vec![(
        "strs".to_string(),
        TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
    )];

    for seed in 0..200 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
        assert!(
            !expr.contains("strs["),
            "Should not generate array index with mismatched element type, got: {}",
            expr,
        );
    }
}

#[test]
fn test_array_index_direct() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let locals = vec![(
        "arr".to_string(),
        TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I32))),
    )];

    let mut found = false;
    for seed in 0..100 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        if let Some(expr) = generator.try_generate_array_index(PrimitiveType::I32, &ctx) {
            assert!(
                expr.starts_with("arr["),
                "Should start with 'arr[', got: {}",
                expr,
            );
            // Verify index is a small constant with proper suffix
            assert!(
                expr.contains("_i32]"),
                "Index should have _i32 suffix, got: {}",
                expr,
            );
            found = true;
            break;
        }
    }
    assert!(
        found,
        "Expected try_generate_array_index to succeed at least once"
    );
}

#[test]
fn test_array_index_no_arrays_in_scope() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let config = ExprConfig::default();
    let mut generator = ExprGenerator::new(&mut rng, &config);

    let table = SymbolTable::new();
    let ctx = ExprContext::new(&[], &[], &table);

    // With no array-typed vars, should return None
    assert!(
        generator
            .try_generate_array_index(PrimitiveType::I64, &ctx)
            .is_none()
    );
}

#[test]
fn test_array_vars_helper() {
    let table = SymbolTable::new();
    let locals = vec![
        (
            "nums".to_string(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        ),
        ("plain".to_string(), TypeInfo::Primitive(PrimitiveType::I64)),
        (
            "strs".to_string(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
        ),
    ];

    let params = vec![ParamInfo {
        name: "param_arr".to_string(),
        param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::Bool))),
    }];

    let ctx = ExprContext::new(&params, &locals, &table);
    let arr_vars = ctx.array_vars();

    assert_eq!(arr_vars.len(), 3);
    assert_eq!(arr_vars[0].0, "nums");
    assert_eq!(arr_vars[0].1, TypeInfo::Primitive(PrimitiveType::I64));
    assert_eq!(arr_vars[1].0, "strs");
    assert_eq!(arr_vars[1].1, TypeInfo::Primitive(PrimitiveType::String));
    assert_eq!(arr_vars[2].0, "param_arr");
    assert_eq!(arr_vars[2].1, TypeInfo::Primitive(PrimitiveType::Bool));
}

#[test]
fn test_string_vars_helper() {
    let table = SymbolTable::new();
    let locals = vec![
        (
            "name".to_string(),
            TypeInfo::Primitive(PrimitiveType::String),
        ),
        ("count".to_string(), TypeInfo::Primitive(PrimitiveType::I64)),
        (
            "label".to_string(),
            TypeInfo::Primitive(PrimitiveType::String),
        ),
    ];

    let params = vec![ParamInfo {
        name: "msg".to_string(),
        param_type: TypeInfo::Primitive(PrimitiveType::String),
    }];

    let ctx = ExprContext::new(&params, &locals, &table);
    let str_vars = ctx.string_vars();

    assert_eq!(str_vars.len(), 3);
    assert_eq!(str_vars[0], "name");
    assert_eq!(str_vars[1], "label");
    assert_eq!(str_vars[2], "msg");
}

#[test]
fn test_string_length_direct() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let locals = vec![("s".to_string(), TypeInfo::Primitive(PrimitiveType::String))];

    let mut found = false;
    for seed in 0..100 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        if let Some(expr) = generator.try_generate_string_length(&ctx) {
            assert_eq!(expr, "s.length()");
            found = true;
            break;
        }
    }
    assert!(
        found,
        "Expected try_generate_string_length to succeed at least once"
    );
}

#[test]
fn test_string_length_no_strings() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let config = ExprConfig::default();
    let mut generator = ExprGenerator::new(&mut rng, &config);

    let table = SymbolTable::new();
    let ctx = ExprContext::new(&[], &[], &table);

    assert!(generator.try_generate_string_length(&ctx).is_none());
}

#[test]
fn test_string_length_in_i64_generation() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let locals = vec![(
        "text".to_string(),
        TypeInfo::Primitive(PrimitiveType::String),
    )];

    let mut found = false;
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::I64), &ctx, 0);
        if expr.contains(".length()") {
            // The .length() call should ultimately be on the "text" variable,
            // possibly via a chained method (e.g. text.to_upper().length()).
            assert!(
                expr.contains("text"),
                "Expected .length() to reference 'text', got: {}",
                expr,
            );
            found = true;
            break;
        }
    }
    assert!(
        found,
        "Expected at least one .length() call in i64 generation across 500 seeds",
    );
}

#[test]
fn test_string_bool_method_direct() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let locals = vec![("s".to_string(), TypeInfo::Primitive(PrimitiveType::String))];

    let valid_methods = ["contains", "starts_with", "ends_with"];
    let mut found = false;
    for seed in 0..100 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        if let Some(expr) = generator.try_generate_string_bool_method(&ctx) {
            let has_valid_method = valid_methods
                .iter()
                .any(|m| expr.starts_with(&format!("s.{}(\"", m)));
            assert!(
                has_valid_method,
                "Expected 's.<method>(\"...\")' where method is contains/starts_with/ends_with, got: {}",
                expr,
            );
            assert!(
                expr.ends_with("\")"),
                "Expected closing quote-paren, got: {}",
                expr,
            );
            found = true;
            break;
        }
    }
    assert!(
        found,
        "Expected try_generate_string_bool_method to succeed at least once"
    );
}

#[test]
fn test_string_bool_method_no_strings() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let config = ExprConfig::default();
    let mut generator = ExprGenerator::new(&mut rng, &config);

    let table = SymbolTable::new();
    let ctx = ExprContext::new(&[], &[], &table);

    assert!(generator.try_generate_string_bool_method(&ctx).is_none());
}

#[test]
fn test_string_bool_method_in_bool_generation() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let locals = vec![(
        "msg".to_string(),
        TypeInfo::Primitive(PrimitiveType::String),
    )];

    let valid_methods = [".contains(", ".starts_with(", ".ends_with("];
    let mut found = false;
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &ctx, 0);
        if valid_methods.iter().any(|m| expr.contains(m)) {
            let has_msg_prefix = valid_methods
                .iter()
                .any(|m| expr.contains(&format!("msg{}", m)));
            assert!(
                has_msg_prefix,
                "Expected 'msg.<method>(...)', got: {}",
                expr,
            );
            found = true;
            break;
        }
    }
    assert!(
        found,
        "Expected at least one string bool method call in bool generation across 500 seeds",
    );
}

#[test]
fn test_string_bool_method_variety() {
    // Ensure all three methods (contains, starts_with, ends_with) can be generated
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let locals = vec![("s".to_string(), TypeInfo::Primitive(PrimitiveType::String))];

    let mut seen_contains = false;
    let mut seen_starts_with = false;
    let mut seen_ends_with = false;
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        if let Some(expr) = generator.try_generate_string_bool_method(&ctx) {
            if expr.contains(".contains(") {
                seen_contains = true;
            }
            if expr.contains(".starts_with(") {
                seen_starts_with = true;
            }
            if expr.contains(".ends_with(") {
                seen_ends_with = true;
            }
        }
        if seen_contains && seen_starts_with && seen_ends_with {
            break;
        }
    }
    assert!(
        seen_contains,
        "Expected .contains() to appear across 500 seeds"
    );
    assert!(
        seen_starts_with,
        "Expected .starts_with() to appear across 500 seeds"
    );
    assert!(
        seen_ends_with,
        "Expected .ends_with() to appear across 500 seeds"
    );
}

#[test]
fn test_string_transform_method_direct() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let locals = vec![("s".to_string(), TypeInfo::Primitive(PrimitiveType::String))];

    let valid_methods = [
        ".to_upper()",
        ".to_lower()",
        ".trim()",
        ".replace(",
        ".replace_all(",
        ".substring(",
    ];
    let mut found = false;
    for seed in 0..100 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        if let Some(expr) = generator.try_generate_string_transform_method(&ctx) {
            let has_valid_method = valid_methods.iter().any(|m| expr.contains(m));
            assert!(
                has_valid_method,
                "Expected string transform method, got: {}",
                expr,
            );
            assert!(
                expr.starts_with("s."),
                "Expected expression to start with 's.', got: {}",
                expr,
            );
            found = true;
            break;
        }
    }
    assert!(
        found,
        "Expected try_generate_string_transform_method to succeed at least once"
    );
}

#[test]
fn test_string_transform_method_no_strings() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let config = ExprConfig::default();
    let mut generator = ExprGenerator::new(&mut rng, &config);

    let table = SymbolTable::new();
    let ctx = ExprContext::new(&[], &[], &table);

    assert!(
        generator
            .try_generate_string_transform_method(&ctx)
            .is_none()
    );
}

#[test]
fn test_string_transform_method_variety() {
    // Ensure all three methods (to_upper, to_lower, trim) can be generated
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let locals = vec![("s".to_string(), TypeInfo::Primitive(PrimitiveType::String))];

    let mut seen_to_upper = false;
    let mut seen_to_lower = false;
    let mut seen_trim = false;
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        if let Some(expr) = generator.try_generate_string_transform_method(&ctx) {
            if expr.contains(".to_upper()") {
                seen_to_upper = true;
            }
            if expr.contains(".to_lower()") {
                seen_to_lower = true;
            }
            if expr.contains(".trim()") {
                seen_trim = true;
            }
        }
        if seen_to_upper && seen_to_lower && seen_trim {
            break;
        }
    }
    assert!(
        seen_to_upper,
        "Expected .to_upper() to appear across 500 seeds"
    );
    assert!(
        seen_to_lower,
        "Expected .to_lower() to appear across 500 seeds"
    );
    assert!(seen_trim, "Expected .trim() to appear across 500 seeds");
}

#[test]
fn test_negated_compound_bool_generation() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let params = vec![
        ParamInfo {
            name: "a".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::I64),
        },
        ParamInfo {
            name: "b".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::Bool),
        },
    ];

    let mut found_negated_comparison = false;
    let mut found_negated_binary_bool = false;
    for seed in 0..1000 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&params, &[], &table);
        let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &ctx, 0);

        // Negated compound: starts with "(!" and contains comparison or boolean operators
        if expr.starts_with("(!(") {
            if expr.contains("&&") || expr.contains("||") {
                found_negated_binary_bool = true;
            }
            if expr.contains("==")
                || expr.contains("!=")
                || expr.contains(">=")
                || expr.contains("<=")
                || expr.contains("> ")
                || expr.contains("< ")
            {
                found_negated_comparison = true;
            }
        }
        if found_negated_comparison && found_negated_binary_bool {
            break;
        }
    }
    assert!(
        found_negated_comparison,
        "Expected at least one negated comparison (e.g. !(a > b)) across 1000 seeds"
    );
    assert!(
        found_negated_binary_bool,
        "Expected at least one negated binary bool (e.g. !(a && b)) across 1000 seeds"
    );
}

#[test]
fn test_string_split_direct() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let locals = vec![("s".to_string(), TypeInfo::Primitive(PrimitiveType::String))];

    let valid_delimiters = [",", " ", ":", ";", "-", "::"];
    let mut found = false;
    for seed in 0..100 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        if let Some(expr) = generator.try_generate_string_split(&ctx) {
            assert!(
                expr.starts_with("s.split(\""),
                "Expected 's.split(\"...\").collect()', got: {}",
                expr,
            );
            assert!(
                expr.ends_with("\").collect()"),
                "Expected ending with '\").collect()', got: {}",
                expr,
            );
            // Verify the delimiter is one of the valid ones
            let delim_start = "s.split(\"".len();
            let delim_end = expr.len() - "\").collect()".len();
            let delim = &expr[delim_start..delim_end];
            assert!(
                valid_delimiters.contains(&delim),
                "Unexpected delimiter '{}' in expr: {}",
                delim,
                expr,
            );
            found = true;
            break;
        }
    }
    assert!(
        found,
        "Expected try_generate_string_split to succeed at least once"
    );
}

#[test]
fn test_string_split_no_strings() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let config = ExprConfig::default();
    let mut generator = ExprGenerator::new(&mut rng, &config);

    let table = SymbolTable::new();
    let ctx = ExprContext::new(&[], &[], &table);

    assert!(generator.try_generate_string_split(&ctx).is_none());
}

#[test]
fn test_string_split_in_array_generation() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let locals = vec![(
        "text".to_string(),
        TypeInfo::Primitive(PrimitiveType::String),
    )];

    let mut found = false;
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        let expr = generator.generate(
            &TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
            &ctx,
            0,
        );
        if expr.contains(".split(") {
            assert!(
                expr.contains("text.split("),
                "Expected 'text.split(...)...', got: {}",
                expr,
            );
            assert!(
                expr.ends_with(".collect()"),
                "Expected ending with '.collect()', got: {}",
                expr,
            );
            found = true;
            break;
        }
    }
    assert!(
        found,
        "Expected at least one .split().collect() call in [string] generation across 500 seeds",
    );
}

#[test]
fn test_string_split_delimiter_variety() {
    // Ensure multiple delimiters can be generated
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let locals = vec![("s".to_string(), TypeInfo::Primitive(PrimitiveType::String))];

    let mut seen_delimiters = std::collections::HashSet::new();
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        if let Some(expr) = generator.try_generate_string_split(&ctx) {
            let delim_start = "s.split(\"".len();
            let delim_end = expr.len() - "\").collect()".len();
            let delim = expr[delim_start..delim_end].to_string();
            seen_delimiters.insert(delim);
        }
        if seen_delimiters.len() >= 3 {
            break;
        }
    }
    assert!(
        seen_delimiters.len() >= 3,
        "Expected at least 3 different delimiters across 500 seeds, got: {:?}",
        seen_delimiters,
    );
}

#[test]
fn test_iter_any_all_direct() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let locals = vec![(
        "arr".to_string(),
        TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
    )];

    let mut found_any = false;
    let mut found_all = false;
    for seed in 0..200 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        if let Some(expr) = generator.try_generate_iter_any_all(&ctx) {
            assert!(
                expr.starts_with("arr.iter()."),
                "Expected 'arr.iter().<method>(...)', got: {}",
                expr,
            );
            assert!(
                expr.contains(".any((x) => ") || expr.contains(".all((x) => "),
                "Expected .any() or .all() call, got: {}",
                expr,
            );
            if expr.contains(".any(") {
                found_any = true;
            }
            if expr.contains(".all(") {
                found_all = true;
            }
            if found_any && found_all {
                break;
            }
        }
    }
    assert!(
        found_any && found_all,
        "Expected both .any() and .all() across 200 seeds",
    );
}

#[test]
fn test_iter_any_all_no_arrays() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let config = ExprConfig::default();
    let mut generator = ExprGenerator::new(&mut rng, &config);

    let table = SymbolTable::new();
    let locals = vec![("n".to_string(), TypeInfo::Primitive(PrimitiveType::I64))];
    let ctx = ExprContext::new(&[], &locals, &table);

    assert!(generator.try_generate_iter_any_all(&ctx).is_none());
}

#[test]
fn test_iter_any_all_in_bool_generation() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let locals = vec![(
        "nums".to_string(),
        TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
    )];

    let mut found = false;
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &ctx, 0);
        if expr.contains(".iter().any(") || expr.contains(".iter().all(") {
            assert!(
                expr.contains("nums.iter()."),
                "Expected 'nums.iter().<method>(...)', got: {}",
                expr,
            );
            found = true;
            break;
        }
    }
    assert!(
        found,
        "Expected at least one .iter().any/all() call in bool generation across 500 seeds",
    );
}

#[test]
fn test_iter_any_all_string_array() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let locals = vec![(
        "words".to_string(),
        TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
    )];

    let mut found = false;
    for seed in 0..200 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&[], &locals, &table);
        if let Some(expr) = generator.try_generate_iter_any_all(&ctx) {
            assert!(
                expr.contains("x.length()"),
                "String array predicate should use x.length(), got: {}",
                expr,
            );
            found = true;
            break;
        }
    }
    assert!(
        found,
        "Expected at least one .any/all() on string array across 200 seeds",
    );
}

#[test]
fn test_compound_bool_generation() {
    let config = ExprConfig::default();
    let table = SymbolTable::new();
    let params = vec![
        ParamInfo {
            name: "a".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::I64),
        },
        ParamInfo {
            name: "b".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::Bool),
        },
    ];

    let mut found_mixed_and_or = false;
    let mut found_parenthesized_group = false;
    for seed in 0..2000 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = ExprGenerator::new(&mut rng, &config);
        let ctx = ExprContext::new(&params, &[], &table);
        let expr = generator.generate(&TypeInfo::Primitive(PrimitiveType::Bool), &ctx, 0);

        // Compound bool: contains both && and || in the same expression
        let has_and = expr.contains("&&");
        let has_or = expr.contains("||");
        if has_and && has_or {
            found_mixed_and_or = true;
            // Check for parenthesized sub-groups: pattern like "(X && Y) ||" or "(X || Y) &&"
            if (expr.contains(") ||") || expr.contains(") &&"))
                && (expr.contains("|| (") || expr.contains("&& ("))
            {
                found_parenthesized_group = true;
            }
        }
        if found_mixed_and_or && found_parenthesized_group {
            break;
        }
    }
    assert!(
        found_mixed_and_or,
        "Expected at least one expression with both && and || across 2000 seeds"
    );
    assert!(
        found_parenthesized_group,
        "Expected at least one parenthesized compound bool (e.g. (a && b) || (c && d)) across 2000 seeds"
    );
}
