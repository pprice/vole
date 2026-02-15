use super::*;
use rand::SeedableRng;

#[test]
fn test_let_statement() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let config = StmtConfig::default();
    let mut generator = StmtGenerator::new(&mut rng, &config);

    let table = SymbolTable::new();
    let mut ctx = StmtContext::new(&[], &table);

    let stmt = generator.generate_let_statement(&mut ctx);
    assert!(stmt.starts_with("let "));
}

#[test]
fn test_body_generation() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let config = StmtConfig::default();
    let mut generator = StmtGenerator::new(&mut rng, &config);

    let table = SymbolTable::new();
    let mut ctx = StmtContext::new(&[], &table);

    let lines = generator.generate_body(&TypeInfo::Primitive(PrimitiveType::I64), &mut ctx, 0);
    assert!(!lines.is_empty());
    // Should end with return
    assert!(lines.last().unwrap().starts_with("return "));
}

#[test]
fn test_if_statement() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let config = StmtConfig::default();
    let mut generator = StmtGenerator::new(&mut rng, &config);

    let table = SymbolTable::new();
    let mut ctx = StmtContext::new(&[], &table);

    let stmt = generator.generate_if_statement(&mut ctx, 0);
    assert!(stmt.starts_with("if "));
}

#[test]
fn test_for_statement() {
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let config = StmtConfig::default();
    let mut generator = StmtGenerator::new(&mut rng, &config);

    let table = SymbolTable::new();
    let mut ctx = StmtContext::new(&[], &table);

    let stmt = generator.generate_for_statement(&mut ctx, 0);
    assert!(stmt.contains("for "));
    assert!(stmt.contains("in "));
}

#[test]
fn test_for_statement_both_range_syntaxes() {
    let table = SymbolTable::new();
    let config = StmtConfig::default();

    let mut found_exclusive = false;
    let mut found_inclusive = false;
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::new(&[], &table);

        let stmt = generator.generate_for_statement(&mut ctx, 0);
        assert!(stmt.contains("for "), "Should contain 'for': {}", stmt);
        assert!(stmt.contains("in "), "Should contain 'in': {}", stmt);

        if stmt.contains("..=") {
            found_inclusive = true;
        } else if stmt.contains("..") {
            found_exclusive = true;
        }

        if found_exclusive && found_inclusive {
            break;
        }
    }
    assert!(
        found_exclusive,
        "Expected exclusive range syntax (a..b) across 500 seeds",
    );
    assert!(
        found_inclusive,
        "Expected inclusive range syntax (a..=b) across 500 seeds",
    );
}

#[test]
fn test_for_statement_variable_bound() {
    let table = SymbolTable::new();
    let config = StmtConfig::default();

    let mut found_var_bound = false;
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::new(&[], &table);

        // Add an i64 local marked as protected (simulating a while-loop counter)
        // so it can be used as a variable bound in for-loop ranges.
        // Only protected i64 locals are eligible as range bounds since they
        // are guaranteed to hold small values.
        ctx.add_local(
            "n".to_string(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );
        ctx.protected_vars.push("n".to_string());

        let stmt = generator.generate_for_statement(&mut ctx, 0);
        // Check if the range uses the variable name "n" as a bound
        // (either directly or in an expression like (n + 1))
        if stmt.contains("..n")
            || stmt.contains("..=n")
            || stmt.contains("..(n")
            || stmt.contains("..=(n")
        {
            found_var_bound = true;
            break;
        }
    }
    assert!(
        found_var_bound,
        "Expected variable bound in for-loop range across 500 seeds",
    );
}

#[test]
fn test_for_statement_expression_bound() {
    let table = SymbolTable::new();
    let config = StmtConfig::default();

    let mut found_expr_bound = false;
    let mut found_start_expr = false;
    for seed in 0..2000 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::new(&[], &table);

        ctx.add_local(
            "n".to_string(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );
        ctx.protected_vars.push("n".to_string());

        let stmt = generator.generate_for_statement(&mut ctx, 0);
        // Check for arithmetic expression bounds like (n + 1), (n - 1), (n * 2)
        if stmt.contains("(n +") || stmt.contains("(n -") || stmt.contains("(n *") {
            found_expr_bound = true;
        }
        // Check for expression as start bound (before the ..)
        if let Some(in_pos) = stmt.find("in ") {
            let after_in = &stmt[in_pos + 3..];
            if after_in.starts_with('(') || after_in.starts_with('n') {
                found_start_expr = true;
            }
        }

        if found_expr_bound && found_start_expr {
            break;
        }
    }
    assert!(
        found_expr_bound,
        "Expected arithmetic expression bound (e.g., (n + 1)) in for-loop range across 2000 seeds",
    );
    assert!(
        found_start_expr,
        "Expected variable/expression as start bound in for-loop range across 2000 seeds",
    );
}

#[test]
fn test_compound_assignment() {
    let table = SymbolTable::new();
    let compound_ops = ["+=", "-=", "*="];
    let mut found = std::collections::HashSet::new();

    // Generate across many seeds to find compound assignments
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let config = StmtConfig::default();
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::new(&[], &table);

        // Pre-populate with a mutable numeric local so compound assign can fire
        ctx.add_local(
            "x".to_string(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );

        let stmt = generator.generate_statement(&mut ctx, 0);
        for op in &compound_ops {
            if stmt.contains(op) {
                found.insert(*op);
            }
        }
    }

    // We should find at least all three compound operators across 500 seeds
    assert!(
        found.len() >= 3,
        "Expected all 3 compound ops, found: {:?}",
        found,
    );
}

#[test]
fn test_compound_assignment_respects_type() {
    let table = SymbolTable::new();

    for seed in 0..200 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let config = StmtConfig::default();
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::new(&[], &table);

        // Add mutable locals of different numeric types
        ctx.add_local(
            "xi32".to_string(),
            TypeInfo::Primitive(PrimitiveType::I32),
            true,
        );
        ctx.add_local(
            "xf64".to_string(),
            TypeInfo::Primitive(PrimitiveType::F64),
            true,
        );

        let stmt = generator.generate_compound_assignment(&mut ctx);

        // The RHS suffix should match the variable's type
        if stmt.starts_with("xi32") {
            assert!(
                stmt.contains("_i32"),
                "i32 compound assign should have _i32 suffix: {}",
                stmt,
            );
        } else if stmt.starts_with("xf64") {
            assert!(
                stmt.contains("_f64"),
                "f64 compound assign should have _f64 suffix: {}",
                stmt,
            );
        }
    }
}

#[test]
fn test_compound_assignment_not_generated_without_mutable_numeric() {
    let table = SymbolTable::new();
    // Use a config that disables control flow (which can create mutable
    // numeric locals like while-loop counters) to isolate the test
    let config = StmtConfig {
        if_probability: 0.0,
        while_probability: 0.0,
        for_probability: 0.0,
        break_continue_probability: 0.0,
        compound_assign_probability: 0.15,
        ..StmtConfig::default()
    };

    // With no locals at all, compound assignment should never appear
    for seed in 0..100 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::new(&[], &table);

        let stmt = generator.generate_statement(&mut ctx, 0);
        assert!(
            !stmt.contains("+=") && !stmt.contains("-=") && !stmt.contains("*="),
            "Compound assign should not appear without mutable numeric locals: {}",
            stmt,
        );
    }
}

#[test]
fn test_array_let_generation() {
    let table = SymbolTable::new();
    let config = StmtConfig {
        // Disable range/iterator patterns so array lets produce array literals.
        range_iter_probability: 0.0,
        empty_array_iter_probability: 0.0,
        iter_map_filter_probability: 0.0,
        ..StmtConfig::default()
    };

    let mut found_array_let = false;
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::new(&[], &table);

        let stmt = generator.generate_let_statement(&mut ctx);
        let last_local = match ctx.locals.last() {
            Some(l) => l,
            None => continue,
        };
        if matches!(last_local.1, TypeInfo::Array(_)) {
            // Verify it looks like an array literal: let localN = [elem1, elem2, ...]
            assert!(
                stmt.starts_with("let ") && stmt.contains("= ["),
                "Array let should contain '= [', got: {}",
                stmt,
            );
            found_array_let = true;
            break;
        }
    }
    assert!(
        found_array_let,
        "Expected at least one array let statement across 500 seeds",
    );
}

#[test]
fn test_array_let_has_sufficient_elements() {
    let table = SymbolTable::new();
    let config = StmtConfig {
        // Disable range/iterator patterns so array lets produce array literals.
        range_iter_probability: 0.0,
        empty_array_iter_probability: 0.0,
        iter_map_filter_probability: 0.0,
        ..StmtConfig::default()
    };

    // Generate array lets and verify they have 2-4 elements
    for seed in 0..200 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::new(&[], &table);

        let stmt = generator.generate_array_let(&mut ctx);
        assert!(
            stmt.starts_with("let "),
            "Should start with 'let ': {}",
            stmt
        );
        assert!(stmt.contains("= ["), "Should contain '= [': {}", stmt);

        // Count commas to determine element count (N elements = N-1 commas)
        let bracket_start = stmt.find('[').unwrap();
        let bracket_end = stmt.rfind(']').unwrap();
        let inner = &stmt[bracket_start + 1..bracket_end];
        let comma_count = inner.matches(',').count();
        // 2-4 elements means 1-3 commas
        assert!(
            comma_count >= 1 && comma_count <= 3,
            "Expected 2-4 elements (1-3 commas), got {} commas in: {}",
            comma_count,
            stmt,
        );
    }
}

#[test]
fn test_determinism() {
    let config = StmtConfig::default();
    let table = SymbolTable::new();

    let mut rng1 = rand::rngs::StdRng::seed_from_u64(12345);
    let mut gen1 = StmtGenerator::new(&mut rng1, &config);
    let mut ctx1 = StmtContext::new(&[], &table);
    let lines1 = gen1.generate_body(&TypeInfo::Primitive(PrimitiveType::I64), &mut ctx1, 0);

    let mut rng2 = rand::rngs::StdRng::seed_from_u64(12345);
    let mut gen2 = StmtGenerator::new(&mut rng2, &config);
    let mut ctx2 = StmtContext::new(&[], &table);
    let lines2 = gen2.generate_body(&TypeInfo::Primitive(PrimitiveType::I64), &mut ctx2, 0);

    assert_eq!(lines1, lines2);
}

#[test]
fn test_discard_statement_generation() {
    // Set up a symbol table with a module containing a non-generic,
    // non-void-returning function that can be used for discard statements.
    let mut table = SymbolTable::new();
    let module_id = table.add_module("test_mod".to_string(), "test_mod.vole".to_string());

    // Add a function that returns i64 (suitable for discarding)
    {
        let module = table.get_module_mut(module_id).unwrap();
        module.add_symbol(
            "discardable_func".to_string(),
            SymbolKind::Function(FunctionInfo {
                type_params: vec![],
                params: vec![ParamInfo {
                    name: "x".to_string(),
                    param_type: TypeInfo::Primitive(PrimitiveType::I64),
                }],
                return_type: TypeInfo::Primitive(PrimitiveType::I64),
            }),
        );
    }

    // Use a config with high discard probability to trigger the feature
    let config = StmtConfig {
        discard_probability: 0.99, // Very high to ensure it triggers
        if_probability: 0.0,
        while_probability: 0.0,
        for_probability: 0.0,
        break_continue_probability: 0.0,
        compound_assign_probability: 0.0,
        raise_probability: 0.0,
        try_probability: 0.0,
        tuple_probability: 0.0,
        fixed_array_probability: 0.0,
        ..StmtConfig::default()
    };

    let mut found_discard = false;
    for seed in 0..100 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::with_module(&[], &table, module_id);

        let stmt = generator.generate_statement(&mut ctx, 0);

        // Check if this statement contains a discard pattern
        // Discards are wrapped in: if <cond> { _ = func(...) }
        if stmt.contains("_ = discardable_func") {
            found_discard = true;
            // Verify the format: should be wrapped in an if block
            assert!(
                stmt.starts_with("if "),
                "Discard should be wrapped in if: {}",
                stmt
            );
            assert!(
                stmt.contains("_ = discardable_func("),
                "Should contain discard call: {}",
                stmt
            );
            break;
        }
    }
    assert!(
        found_discard,
        "Expected at least one discard statement across 100 seeds"
    );
}

#[test]
fn test_discard_statement_not_generated_without_functions() {
    // Without any functions in the module, discard statements should not be generated
    let mut table = SymbolTable::new();
    let module_id = table.add_module("empty_mod".to_string(), "empty_mod.vole".to_string());

    let config = StmtConfig {
        discard_probability: 0.99,
        if_probability: 0.0,
        while_probability: 0.0,
        for_probability: 0.0,
        ..StmtConfig::default()
    };

    for seed in 0..50 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::with_module(&[], &table, module_id);

        let stmt = generator.generate_statement(&mut ctx, 0);

        // Should not contain discard pattern since there are no functions
        assert!(
            !stmt.contains("_ =") || stmt.contains("_ =>"),
            "Discard should not appear without callable functions: {}",
            stmt
        );
    }
}

#[test]
fn test_early_return_generation() {
    let table = SymbolTable::new();

    // Use a config with high early_return_probability to ensure it triggers
    let config = StmtConfig {
        early_return_probability: 0.99,
        if_probability: 0.0,
        while_probability: 0.0,
        for_probability: 0.0,
        ..StmtConfig::default()
    };

    let mut found_early_return = false;
    for seed in 0..100 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::new(&[], &table);

        let lines = generator.generate_body(&TypeInfo::Primitive(PrimitiveType::I64), &mut ctx, 0);

        // Check if there's an early return (if block containing return before the final return)
        let return_count = lines.iter().filter(|l| l.contains("return ")).count();
        if return_count >= 2 {
            // Should have an "if" block with a return inside it
            let has_if_with_return = lines.iter().any(|l| l.starts_with("if "));
            if has_if_with_return {
                found_early_return = true;
                break;
            }
        }
    }
    assert!(
        found_early_return,
        "Expected at least one early return in if block across 100 seeds"
    );
}

#[test]
fn test_early_return_not_generated_for_void() {
    let table = SymbolTable::new();

    let config = StmtConfig {
        early_return_probability: 0.99,
        if_probability: 0.0,
        while_probability: 0.0,
        for_probability: 0.0,
        ..StmtConfig::default()
    };

    for seed in 0..50 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::new(&[], &table);

        let lines = generator.generate_body(&TypeInfo::Void, &mut ctx, 0);

        // Void functions should not have any return statements
        assert!(
            !lines.iter().any(|l| l.contains("return ")),
            "Void functions should not have return statements: {:?}",
            lines
        );
    }
}

#[test]
fn test_early_return_disabled_when_probability_zero() {
    let table = SymbolTable::new();

    let config = StmtConfig {
        early_return_probability: 0.0,
        if_probability: 0.0,
        while_probability: 0.0,
        for_probability: 0.0,
        nested_loop_probability: 0.0,
        ..StmtConfig::default()
    };

    for seed in 0..100 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::new(&[], &table);

        let lines = generator.generate_body(&TypeInfo::Primitive(PrimitiveType::I64), &mut ctx, 0);

        // Should have exactly one return statement (the final one)
        let return_count = lines.iter().filter(|l| l.contains("return ")).count();
        assert_eq!(
            return_count, 1,
            "With early_return_probability=0.0, should have exactly 1 return: {:?}",
            lines
        );
    }
}

#[test]
fn test_else_if_chain_generation() {
    let table = SymbolTable::new();

    // Use a config with high else_if_probability to ensure it triggers
    let config = StmtConfig {
        if_probability: 0.99,
        else_if_probability: 0.99,
        while_probability: 0.0,
        for_probability: 0.0,
        break_continue_probability: 0.0,
        compound_assign_probability: 0.0,
        ..StmtConfig::default()
    };

    let mut found_else_if = false;
    for seed in 0..200 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::new(&[], &table);

        let stmt = generator.generate_statement(&mut ctx, 0);

        // Check for else-if pattern: "} else if"
        if stmt.contains("} else if ") {
            found_else_if = true;
            // Verify the syntax is correct: should have multiple else-if arms
            // and end with a plain else
            assert!(
                stmt.contains("} else {"),
                "Else-if chain should end with plain else: {}",
                stmt
            );
            break;
        }
    }
    assert!(
        found_else_if,
        "Expected at least one else-if chain across 200 seeds"
    );
}

#[test]
fn test_else_if_chain_not_generated_when_probability_zero() {
    let table = SymbolTable::new();

    let config = StmtConfig {
        if_probability: 0.99,
        else_if_probability: 0.0,
        while_probability: 0.0,
        for_probability: 0.0,
        break_continue_probability: 0.0,
        compound_assign_probability: 0.0,
        ..StmtConfig::default()
    };

    for seed in 0..100 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::new(&[], &table);

        let stmt = generator.generate_statement(&mut ctx, 0);

        // With else_if_probability=0.0, should never see "else if"
        assert!(
            !stmt.contains("else if"),
            "With else_if_probability=0.0, should not have else-if: {}",
            stmt
        );
    }
}

#[test]
fn test_else_if_chain_syntax_correct() {
    let table = SymbolTable::new();

    let config = StmtConfig {
        if_probability: 0.99,
        else_if_probability: 0.99,
        while_probability: 0.0,
        for_probability: 0.0,
        break_continue_probability: 0.0,
        compound_assign_probability: 0.0,
        ..StmtConfig::default()
    };

    // Test multiple seeds to validate syntax
    for seed in 0..100 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::new(&[], &table);

        let stmt = generator.generate_statement(&mut ctx, 0);

        if stmt.contains("else if") {
            // The "else if" must be on the same line as closing brace
            // Valid: "} else if"
            // Invalid: "}\nelse if"
            assert!(
                stmt.contains("} else if "),
                "else-if must follow closing brace on same line: {}",
                stmt
            );
        }
    }
}

#[test]
fn test_match_let_generation() {
    let table = SymbolTable::new();

    let config = StmtConfig {
        match_probability: 0.99,
        if_probability: 0.0,
        while_probability: 0.0,
        for_probability: 0.0,
        break_continue_probability: 0.0,
        compound_assign_probability: 0.0,
        ..StmtConfig::default()
    };

    let mut found_match = false;
    for seed in 0..200 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        // Provide an i64 param as a match scrutinee
        let i64_params = vec![ParamInfo {
            name: "input".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::I64),
        }];
        let mut ctx = StmtContext::new(&i64_params, &table);

        let stmt = generator.generate_let_statement(&mut ctx);

        if stmt.contains("match input") {
            found_match = true;
            // Must have a wildcard arm
            assert!(
                stmt.contains("_ =>"),
                "Match must have wildcard arm: {}",
                stmt
            );
            // Must be a let binding
            assert!(
                stmt.starts_with("let "),
                "Match must be a let binding: {}",
                stmt
            );
            break;
        }
    }
    assert!(
        found_match,
        "Expected at least one match let across 200 seeds"
    );
}

#[test]
fn test_i64_match_not_generated_when_no_i64_in_scope() {
    let table = SymbolTable::new();

    // High i64 match probability, but string match disabled
    let config = StmtConfig {
        match_probability: 0.99,
        string_match_probability: 0.0,
        if_probability: 0.0,
        while_probability: 0.0,
        for_probability: 0.0,
        ..StmtConfig::default()
    };

    // Only string params - no i64 to match on
    let params = vec![ParamInfo {
        name: "text".to_string(),
        param_type: TypeInfo::Primitive(PrimitiveType::String),
    }];

    // With string_match_probability=0.0 and no i64 in scope,
    // the i64 match path should never trigger on a string variable.
    for seed in 0..50 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::new(&params, &table);

        let stmt = generator.generate_let_statement(&mut ctx);
        // Check the first line only - match-let starts with "let localN = match var {"
        let first_line = stmt.lines().next().unwrap_or("");
        assert!(
            !(first_line.contains("= match text")),
            "Should not generate i64 match-let on string var: {}",
            stmt
        );
    }
}

#[test]
fn test_string_match_let_generation() {
    let table = SymbolTable::new();

    let config = StmtConfig {
        string_match_probability: 0.99,
        match_probability: 0.0,
        if_probability: 0.0,
        while_probability: 0.0,
        for_probability: 0.0,
        break_continue_probability: 0.0,
        compound_assign_probability: 0.0,
        reassign_probability: 0.0,
        ..StmtConfig::default()
    };

    // A string param in scope to match on
    let params = vec![ParamInfo {
        name: "msg".to_string(),
        param_type: TypeInfo::Primitive(PrimitiveType::String),
    }];

    let mut found_match = false;
    for seed in 0..200 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::new(&params, &table);

        let stmt = generator.generate_let_statement(&mut ctx);
        if stmt.contains("= match msg {") {
            found_match = true;
            // Verify it has string literal arms
            assert!(
                stmt.contains("\""),
                "String match should have string literal arms: {}",
                stmt
            );
            // Verify wildcard arm
            assert!(
                stmt.contains("_ =>"),
                "String match should have wildcard arm: {}",
                stmt
            );
            // Must be a let binding
            assert!(
                stmt.starts_with("let "),
                "String match must be a let binding: {}",
                stmt
            );
            break;
        }
    }
    assert!(
        found_match,
        "Expected at least one string match let across 200 seeds"
    );
}

#[test]
fn test_class_destructure_generation() {
    use crate::symbols::{ClassInfo, FieldInfo};

    let mut table = SymbolTable::new();
    let mod_id = table.add_module("test_mod".to_string(), "test_mod.vole".to_string());

    // Create a class with two primitive fields
    let sym_id = table.get_module_mut(mod_id).unwrap().add_symbol(
        "Point".to_string(),
        SymbolKind::Class(ClassInfo {
            type_params: vec![],
            fields: vec![
                FieldInfo {
                    name: "x".to_string(),
                    field_type: TypeInfo::Primitive(PrimitiveType::I64),
                },
                FieldInfo {
                    name: "y".to_string(),
                    field_type: TypeInfo::Primitive(PrimitiveType::I64),
                },
            ],
            methods: vec![],
            implements: vec![],
            static_methods: vec![],
        }),
    );

    let config = StmtConfig {
        class_destructure_probability: 0.99,
        // Disable other generation paths so we almost always hit class destructuring
        if_probability: 0.0,
        while_probability: 0.0,
        for_probability: 0.0,
        nested_loop_probability: 0.0,
        ..StmtConfig::default()
    };

    let mut found_destructure = false;
    for seed in 0..500 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::with_module(&[], &table, mod_id);

        // Add a class-typed local so destructuring can fire
        ctx.add_local("point".to_string(), TypeInfo::Class(mod_id, sym_id), false);

        let stmt = generator.generate_statement(&mut ctx, 0);

        // Check if this is a class destructuring statement
        if stmt.starts_with("let {") && stmt.contains("= point") {
            // Should reference field names with renamed bindings
            assert!(
                stmt.contains("x:") || stmt.contains("y:"),
                "Class destructure should reference field names: {}",
                stmt
            );
            found_destructure = true;
            break;
        }
    }
    assert!(
        found_destructure,
        "Expected at least one class destructure across 500 seeds"
    );
}

#[test]
fn test_class_destructure_no_classes_returns_none() {
    let table = SymbolTable::new();

    let config = StmtConfig {
        class_destructure_probability: 0.99,
        ..StmtConfig::default()
    };

    // No class-typed variables in scope: destructuring should never appear
    for seed in 0..50 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::new(&[], &table);

        let result = generator.try_generate_class_destructure(&mut ctx);
        assert!(
            result.is_none(),
            "Should return None without class-typed locals, got: {:?}",
            result
        );
    }
}

#[test]
fn test_class_destructure_skips_generic_classes() {
    use crate::symbols::{ClassInfo, FieldInfo, TypeParam};

    let mut table = SymbolTable::new();
    let mod_id = table.add_module("test_mod".to_string(), "test_mod.vole".to_string());

    // Create a generic class (should be skipped)
    let sym_id = table.get_module_mut(mod_id).unwrap().add_symbol(
        "Box".to_string(),
        SymbolKind::Class(ClassInfo {
            type_params: vec![TypeParam {
                name: "T".to_string(),
                constraints: vec![],
            }],
            fields: vec![FieldInfo {
                name: "value".to_string(),
                field_type: TypeInfo::Primitive(PrimitiveType::I64),
            }],
            methods: vec![],
            implements: vec![],
            static_methods: vec![],
        }),
    );

    let config = StmtConfig {
        class_destructure_probability: 0.99,
        ..StmtConfig::default()
    };

    for seed in 0..50 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::with_module(&[], &table, mod_id);
        ctx.add_local("boxed".to_string(), TypeInfo::Class(mod_id, sym_id), false);

        let result = generator.try_generate_class_destructure(&mut ctx);
        assert!(
            result.is_none(),
            "Should return None for generic class, got: {:?}",
            result
        );
    }
}

#[test]
fn test_iter_first_last_terminal() {
    use rand::SeedableRng;

    let mut table = SymbolTable::new();
    let mod_id = table.add_module("test_mod".to_string(), "test_mod.vole".to_string());

    let config = StmtConfig {
        iter_map_filter_probability: 0.99,
        ..StmtConfig::default()
    };

    let mut found_first = false;
    let mut found_last = false;
    let mut found_optional_type = false;
    let mut found_coalesced = false;

    for seed in 0..2000 {
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut generator = StmtGenerator::new(&mut rng, &config);
        let mut ctx = StmtContext::with_module(&[], &table, mod_id);
        ctx.add_local(
            "nums".to_string(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );

        if let Some(stmt) = generator.try_generate_iter_map_filter_let(&mut ctx) {
            if stmt.contains(".first()") {
                found_first = true;
                // Check that the local was registered with the right type
                let last_local = ctx.locals.last().unwrap();
                if matches!(last_local.1, TypeInfo::Optional(_)) {
                    found_optional_type = true;
                }
            }
            if stmt.contains(".last()") {
                found_last = true;
            }
            if stmt.contains("?? ") {
                found_coalesced = true;
            }
        }
    }

    assert!(
        found_first,
        "Expected at least one .first() terminal across 2000 seeds",
    );
    assert!(
        found_last,
        "Expected at least one .last() terminal across 2000 seeds",
    );
    assert!(
        found_optional_type,
        "Expected at least one .first()/.last() to produce an Optional type",
    );
    assert!(
        found_coalesced,
        "Expected at least one .first()/.last() with ?? coalescing across 2000 seeds",
    );
}
