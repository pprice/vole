//! Rule: module-level function with many parameters (8, 10, or 12) and a call
//! that asserts the result.
//!
//! This stresses calling conventions since parameters beyond the register limit
//! get passed on the stack.
//!
//! Three variants:
//!
//! **Variant 0 -- i64 sum (8 params):**
//! ```vole
//! func sum8_local0(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i64) -> i64 {
//!     return a + b + c + d + e + f + g + h
//! }
//! let local1 = sum8_local0(1, 2, 3, 4, 5, 6, 7, 8)
//! assert(local1 == 36)
//! ```
//!
//! **Variant 1 -- string concat (8 params):**
//! ```vole
//! func concat8_local0(a: string, b: string, c: string, d: string, e: string, f: string, g: string, h: string) -> string {
//!     return a + b + c + d + e + f + g + h
//! }
//! let local1 = concat8_local0("a", "b", "c", "d", "e", "f", "g", "h")
//! assert(local1 == "abcdefgh")
//! ```
//!
//! **Variant 2 -- mixed i64+string (10 params):**
//! ```vole
//! func mixed10_local0(a: i64, b: string, c: i64, d: string, e: i64, f: string, g: i64, h: string, i: i64, j: string) -> string {
//!     return b + d + f + h + j
//! }
//! let local1 = mixed10_local0(1, "x", 2, "y", 3, "z", 4, "w", 5, "v")
//! assert(local1 == "xyzwv")
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ManyParamCall;

/// Parameter names for up to 10 params.
const PARAM_NAMES: &[&str] = &["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"];

impl StmtRule for ManyParamCall {
    fn name(&self) -> &'static str {
        "many_param_call"
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
            0 => emit_i64_sum(scope, emit),
            1 => emit_string_concat(scope, emit),
            _ => emit_mixed(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0 -- i64 sum (8 params)
// ---------------------------------------------------------------------------

fn emit_i64_sum(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_name = scope.fresh_name();
    let fn_label = format!("sum8_{}", fn_name);

    let names = &PARAM_NAMES[..8];

    // Generate 8 random i64 values in 1..=20.
    let values: Vec<i64> = (0..8).map(|_| emit.gen_i64_range(1, 20)).collect();
    let expected: i64 = values.iter().sum();

    // Build parameter signature: "a: i64, b: i64, ..."
    let param_sig: String = names
        .iter()
        .map(|n| format!("{}: i64", n))
        .collect::<Vec<_>>()
        .join(", ");

    // Build body: "return a + b + c + ..."
    let sum_expr: String = names.join(" + ");

    let decl = format!(
        "func {}({}) -> i64 {{\n    return {}\n}}",
        fn_label, param_sig, sum_expr,
    );
    scope.add_module_decl(decl);

    // Build call arguments.
    let call_args: String = values
        .iter()
        .map(|v| format!("{}", v))
        .collect::<Vec<_>>()
        .join(", ");

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}({})\n{}assert({} == {})",
        result_name, fn_label, call_args, indent, result_name, expected,
    ))
}

// ---------------------------------------------------------------------------
// Variant 1 -- string concat (8 params)
// ---------------------------------------------------------------------------

fn emit_string_concat(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_name = scope.fresh_name();
    let fn_label = format!("concat8_{}", fn_name);

    let names = &PARAM_NAMES[..8];

    // Pick 8 random single lowercase chars.
    let chars: Vec<char> = (0..8)
        .map(|_| {
            let c = emit.gen_range(0..26) as u8 + b'a';
            c as char
        })
        .collect();

    let expected: String = chars.iter().collect();

    // Build parameter signature: "a: string, b: string, ..."
    let param_sig: String = names
        .iter()
        .map(|n| format!("{}: string", n))
        .collect::<Vec<_>>()
        .join(", ");

    // Build body: "return a + b + c + ..."
    let concat_expr: String = names.join(" + ");

    let decl = format!(
        "func {}({}) -> string {{\n    return {}\n}}",
        fn_label, param_sig, concat_expr,
    );
    scope.add_module_decl(decl);

    // Build call arguments: "a", "b", ...
    let call_args: String = chars
        .iter()
        .map(|c| format!("\"{}\"", c))
        .collect::<Vec<_>>()
        .join(", ");

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}({})\n{}assert({} == \"{}\")",
        result_name, fn_label, call_args, indent, result_name, expected,
    ))
}

// ---------------------------------------------------------------------------
// Variant 2 -- mixed i64+string (10 params)
// ---------------------------------------------------------------------------

fn emit_mixed(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let fn_name = scope.fresh_name();
    let fn_label = format!("mixed10_{}", fn_name);

    let names = &PARAM_NAMES[..10];

    // Generate 5 random i64 values (1-20) and 5 random single chars.
    let i64_values: Vec<i64> = (0..5).map(|_| emit.gen_i64_range(1, 20)).collect();
    let str_chars: Vec<char> = (0..5)
        .map(|_| {
            let c = emit.gen_range(0..26) as u8 + b'a';
            c as char
        })
        .collect();

    let expected: String = str_chars.iter().collect();

    // Pattern: i64, string, i64, string, ... (alternating, 10 params total)
    // Params: a: i64, b: string, c: i64, d: string, e: i64, f: string, g: i64, h: string, i: i64, j: string
    let param_sig: String = names
        .iter()
        .enumerate()
        .map(|(idx, n)| {
            if idx % 2 == 0 {
                format!("{}: i64", n)
            } else {
                format!("{}: string", n)
            }
        })
        .collect::<Vec<_>>()
        .join(", ");

    // Body: return b + d + f + h + j (the string params only)
    let string_params: Vec<&str> = names
        .iter()
        .enumerate()
        .filter(|(idx, _)| idx % 2 == 1)
        .map(|(_, n)| *n)
        .collect();
    let concat_expr: String = string_params.join(" + ");

    let decl = format!(
        "func {}({}) -> string {{\n    return {}\n}}",
        fn_label, param_sig, concat_expr,
    );
    scope.add_module_decl(decl);

    // Build call arguments: 1, "x", 2, "y", ...
    let call_args: String = (0..10)
        .map(|idx| {
            if idx % 2 == 0 {
                format!("{}", i64_values[idx / 2])
            } else {
                format!("\"{}\"", str_chars[idx / 2])
            }
        })
        .collect::<Vec<_>>()
        .join(", ");

    let result_name = scope.fresh_name();
    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let indent = emit.indent_str();

    Some(format!(
        "let {} = {}({})\n{}assert({} == \"{}\")",
        result_name, fn_label, call_args, indent, result_name, expected,
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
        assert_eq!(ManyParamCall.name(), "many_param_call");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!ManyParamCall.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(ManyParamCall.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!ManyParamCall.precondition(&scope, &params));
    }

    #[test]
    fn generates_i64_sum_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = ManyParamCall.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("sum8_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for i64 sum variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> i64"),
                        "expected i64 return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("a: i64"),
                        "expected param 'a: i64' in decl: {decl}"
                    );
                    assert!(
                        decl.contains("h: i64"),
                        "expected param 'h: i64' in decl: {decl}"
                    );
                    assert!(
                        decl.contains("a + b + c + d + e + f + g + h"),
                        "expected sum expression in decl: {decl}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    // Result should be i64
                    let result_local = scope.locals.last().expect("should add result local");
                    assert_eq!(
                        result_local.1,
                        TypeInfo::Primitive(PrimitiveType::I64),
                        "sum result must be i64"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated i64 sum variant in 100 seeds");
    }

    #[test]
    fn generates_string_concat_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = ManyParamCall.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("concat8_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for string concat variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> string"),
                        "expected string return type in decl: {decl}"
                    );
                    assert!(
                        decl.contains("a: string"),
                        "expected param 'a: string' in decl: {decl}"
                    );
                    assert!(
                        decl.contains("h: string"),
                        "expected param 'h: string' in decl: {decl}"
                    );
                    assert!(
                        decl.contains("a + b + c + d + e + f + g + h"),
                        "expected concat expression in decl: {decl}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    // Result should be string
                    let result_local = scope.locals.last().expect("should add result local");
                    assert_eq!(
                        result_local.1,
                        TypeInfo::Primitive(PrimitiveType::String),
                        "concat result must be string"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated string concat variant in 100 seeds");
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

            if let Some(text) = ManyParamCall.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("mixed10_") {
                    found = true;
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for mixed variant"
                    );
                    let decl = &scope.module_decls[0];
                    assert!(
                        decl.contains("-> string"),
                        "expected string return type in decl: {decl}"
                    );
                    // Check alternating types
                    assert!(
                        decl.contains("a: i64"),
                        "expected param 'a: i64' in decl: {decl}"
                    );
                    assert!(
                        decl.contains("b: string"),
                        "expected param 'b: string' in decl: {decl}"
                    );
                    assert!(
                        decl.contains("j: string"),
                        "expected param 'j: string' in decl: {decl}"
                    );
                    // Body returns concat of string params
                    assert!(
                        decl.contains("b + d + f + h + j"),
                        "expected string concat expression in decl: {decl}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    // Result should be string
                    let result_local = scope.locals.last().expect("should add result local");
                    assert_eq!(
                        result_local.1,
                        TypeInfo::Primitive(PrimitiveType::String),
                        "mixed result must be string"
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

        ManyParamCall.generate(&mut scope, &mut emit, &test_params());
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

        let result = ManyParamCall.generate(&mut scope, &mut emit, &test_params());
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
    fn i64_sum_assert_is_correct() {
        let table = SymbolTable::new();
        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = ManyParamCall.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("sum8_") {
                    // Parse out the call arguments and expected value, verify they match.
                    // Format: "let localN = sum8_localM(a1, a2, ..., a8)\nassert(localN == E)"
                    let lines: Vec<&str> = text.lines().collect();
                    assert_eq!(lines.len(), 2, "expected 2 lines: {text}");

                    // Extract args from call
                    let call_line = lines[0];
                    let open = call_line.find('(').expect("no ( in call");
                    let close = call_line.find(')').expect("no ) in call");
                    let args_str = &call_line[open + 1..close];
                    let args: Vec<i64> = args_str
                        .split(", ")
                        .map(|s| s.trim().parse::<i64>().expect("bad i64 arg"))
                        .collect();
                    assert_eq!(args.len(), 8, "expected 8 args");

                    let actual_sum: i64 = args.iter().sum();

                    // Extract expected from assert
                    let assert_line = lines[1].trim();
                    let eq_pos = assert_line.rfind("== ").expect("no == in assert");
                    let expected_str = &assert_line[eq_pos + 3..assert_line.len() - 1];
                    let expected: i64 = expected_str.parse().expect("bad expected i64");

                    assert_eq!(
                        actual_sum, expected,
                        "sum mismatch for seed {}: args={:?}",
                        seed, args
                    );
                    return; // Found and validated
                }
            }
        }
        panic!("never generated i64 sum variant in 200 seeds");
    }

    #[test]
    fn string_concat_assert_is_correct() {
        let table = SymbolTable::new();
        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = ManyParamCall.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("concat8_") {
                    let lines: Vec<&str> = text.lines().collect();
                    assert_eq!(lines.len(), 2, "expected 2 lines: {text}");

                    // Extract string args from call
                    let call_line = lines[0];
                    let open = call_line.find('(').expect("no ( in call");
                    let close = call_line.rfind(')').expect("no ) in call");
                    let args_str = &call_line[open + 1..close];
                    let args: Vec<&str> = args_str.split(", ").collect();
                    assert_eq!(args.len(), 8, "expected 8 string args");

                    // Strip quotes and concat
                    let actual_concat: String = args.iter().map(|a| a.trim_matches('"')).collect();

                    // Extract expected from assert
                    let assert_line = lines[1].trim();
                    // Format: assert(localN == "expected")
                    let eq_pos = assert_line.rfind("== \"").expect("no == \" in assert");
                    let expected = &assert_line[eq_pos + 4..assert_line.len() - 2];

                    assert_eq!(
                        actual_concat, expected,
                        "concat mismatch for seed {}: args={:?}",
                        seed, args
                    );
                    return;
                }
            }
        }
        panic!("never generated string concat variant in 200 seeds");
    }

    #[test]
    fn mixed_assert_is_correct() {
        let table = SymbolTable::new();
        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) = ManyParamCall.generate(&mut scope, &mut emit, &test_params()) {
                if text.contains("mixed10_") {
                    let lines: Vec<&str> = text.lines().collect();
                    assert_eq!(lines.len(), 2, "expected 2 lines: {text}");

                    // Extract args from call
                    let call_line = lines[0];
                    let open = call_line.find('(').expect("no ( in call");
                    let close = call_line.rfind(')').expect("no ) in call");
                    let args_str = &call_line[open + 1..close];
                    let args: Vec<&str> = args_str.split(", ").collect();
                    assert_eq!(args.len(), 10, "expected 10 args");

                    // Odd-indexed args are strings; concat them.
                    let actual_concat: String = args
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| i % 2 == 1)
                        .map(|(_, a)| a.trim_matches('"'))
                        .collect();

                    // Extract expected from assert
                    let assert_line = lines[1].trim();
                    let eq_pos = assert_line.rfind("== \"").expect("no == \" in assert");
                    let expected = &assert_line[eq_pos + 4..assert_line.len() - 2];

                    assert_eq!(
                        actual_concat, expected,
                        "mixed concat mismatch for seed {}: args={:?}",
                        seed, args
                    );
                    return;
                }
            }
        }
        panic!("never generated mixed variant in 200 seeds");
    }
}
