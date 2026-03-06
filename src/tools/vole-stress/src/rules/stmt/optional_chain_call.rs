//! Rule: optional chaining patterns (`?.` and `??`).
//!
//! Stresses the interaction of optional types with method dispatch and field
//! access by generating functions that take optional parameters and use `?.`
//! for safe access with `??` for default values.
//!
//! **Variant 0 -- optional string method chain:**
//! ```vole
//! func safe_len_42918(s: string?) -> i64 {
//!     return s?.length() ?? 0
//! }
//! let result = safe_len_42918("hello")
//! ```
//! Test via `assert(result == 5)`.
//!
//! **Variant 1 -- optional struct field access:**
//! ```vole
//! struct Info_42918 {
//!     label: string,
//!     count: i64,
//! }
//! func get_count_42918(info: Info_42918?) -> i64 {
//!     return info?.count ?? -1
//! }
//! let result = get_count_42918(Info_42918 { label: "test", count: 42 })
//! ```
//! Test via `assert(result == 42)`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct OptionalChainCall;

impl StmtRule for OptionalChainCall {
    fn name(&self) -> &'static str {
        "optional_chain_call"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..2);
        match variant {
            0 => emit_string_method_variant(scope, emit),
            _ => emit_struct_field_variant(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// String method descriptor
// ---------------------------------------------------------------------------

struct StringMethodDesc {
    /// The method name called after `?.`
    method: &'static str,
    /// Arguments to the method (empty string if none)
    args: &'static str,
    /// The default value after `??`
    default_val: &'static str,
    /// The expected value when called on the test input
    expected: &'static str,
    /// The test input literal
    test_input: &'static str,
    /// The return type of the whole expression
    return_type: TypeInfo,
}

const STRING_METHODS: &[StringMethodDesc] = &[
    StringMethodDesc {
        method: "length",
        args: "",
        default_val: "0",
        expected: "5",
        test_input: "\"hello\"",
        return_type: TypeInfo::Primitive(PrimitiveType::I64),
    },
    StringMethodDesc {
        method: "to_upper",
        args: "",
        default_val: "\"none\"",
        expected: "\"HELLO\"",
        test_input: "\"hello\"",
        return_type: TypeInfo::Primitive(PrimitiveType::String),
    },
    StringMethodDesc {
        method: "trim",
        args: "",
        default_val: "\"none\"",
        expected: "\"hello\"",
        test_input: "\"  hello  \"",
        return_type: TypeInfo::Primitive(PrimitiveType::String),
    },
];

// ---------------------------------------------------------------------------
// Variant 0: optional string method chain
// ---------------------------------------------------------------------------

fn emit_string_method_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let method_idx = emit.gen_range(0..STRING_METHODS.len());
    let desc = &STRING_METHODS[method_idx];

    // Pick a function name prefix
    let prefixes = ["safe_len", "safe_get", "opt_str", "maybe_str", "check_str"];
    let prefix = prefixes[emit.gen_range(0..prefixes.len())];
    let fn_name = format!("{}_{}", prefix, uid);

    // Module decl: function taking string? and returning the result type
    let return_type_str = match &desc.return_type {
        TypeInfo::Primitive(PrimitiveType::I64) => "i64",
        TypeInfo::Primitive(PrimitiveType::String) => "string",
        _ => "i64",
    };

    let func_decl = format!(
        "func {fn_name}(s: string?) -> {ret} {{\n    return s?.{method}({args}) ?? {default}\n}}",
        fn_name = fn_name,
        ret = return_type_str,
        method = desc.method,
        args = desc.args,
        default = desc.default_val,
    );
    scope.add_module_decl(func_decl);

    // Inline code: call the function and assert
    let result_name = scope.fresh_name();
    scope.add_local(result_name.clone(), desc.return_type.clone(), false);

    let indent = emit.indent_str();
    let code = format!(
        "let {rn} = {fn_name}({input})\n{indent}assert({rn} == {expected})",
        rn = result_name,
        fn_name = fn_name,
        input = desc.test_input,
        expected = desc.expected,
        indent = indent,
    );

    Some(code)
}

// ---------------------------------------------------------------------------
// Variant 1: optional struct field access
// ---------------------------------------------------------------------------

/// Struct field descriptor for generation.
struct StructFieldDesc {
    name: &'static str,
    type_info: TypeInfo,
    type_str: &'static str,
    literal: &'static str,
    default_val: &'static str,
}

const I64_FIELD_POOL: &[StructFieldDesc] = &[
    StructFieldDesc {
        name: "count",
        type_info: TypeInfo::Primitive(PrimitiveType::I64),
        type_str: "i64",
        literal: "42",
        default_val: "-1",
    },
    StructFieldDesc {
        name: "score",
        type_info: TypeInfo::Primitive(PrimitiveType::I64),
        type_str: "i64",
        literal: "99",
        default_val: "0",
    },
    StructFieldDesc {
        name: "size",
        type_info: TypeInfo::Primitive(PrimitiveType::I64),
        type_str: "i64",
        literal: "7",
        default_val: "-1",
    },
];

const STRING_FIELD_POOL: &[StructFieldDesc] = &[
    StructFieldDesc {
        name: "label",
        type_info: TypeInfo::Primitive(PrimitiveType::String),
        type_str: "string",
        literal: "\"test\"",
        default_val: "\"none\"",
    },
    StructFieldDesc {
        name: "tag",
        type_info: TypeInfo::Primitive(PrimitiveType::String),
        type_str: "string",
        literal: "\"alpha\"",
        default_val: "\"unknown\"",
    },
    StructFieldDesc {
        name: "title",
        type_info: TypeInfo::Primitive(PrimitiveType::String),
        type_str: "string",
        literal: "\"hello\"",
        default_val: "\"empty\"",
    },
];

fn emit_struct_field_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);

    // Pick 1 i64 field and 1 string field for the struct
    let i64_field = &I64_FIELD_POOL[emit.gen_range(0..I64_FIELD_POOL.len())];
    let str_field = &STRING_FIELD_POOL[emit.gen_range(0..STRING_FIELD_POOL.len())];

    let struct_name = format!("Info_{}", uid);

    // Module decl 1: struct definition
    let struct_decl = format!(
        "struct {sn} {{\n    {sf}: {st},\n    {if_}: {it},\n}}",
        sn = struct_name,
        sf = str_field.name,
        st = str_field.type_str,
        if_ = i64_field.name,
        it = i64_field.type_str,
    );
    scope.add_module_decl(struct_decl);

    // Decide which field to access via ?.
    let access_i64 = emit.gen_bool(0.5);

    let (accessed_field, return_type_str, default_val, expected_val) = if access_i64 {
        (
            i64_field.name,
            i64_field.type_str,
            i64_field.default_val,
            i64_field.literal,
        )
    } else {
        (
            str_field.name,
            str_field.type_str,
            str_field.default_val,
            str_field.literal,
        )
    };

    // Pick a function name prefix
    let prefixes = ["get_field", "read_opt", "safe_read", "maybe_get"];
    let prefix = prefixes[emit.gen_range(0..prefixes.len())];
    let fn_name = format!("{}_{}", prefix, uid);

    // Module decl 2: function taking struct? and returning the field type
    let func_decl = format!(
        "func {fn_name}(item: {sn}?) -> {ret} {{\n    return item?.{field} ?? {default}\n}}",
        fn_name = fn_name,
        sn = struct_name,
        ret = return_type_str,
        field = accessed_field,
        default = default_val,
    );
    scope.add_module_decl(func_decl);

    // Inline code: construct the struct, call the function, assert
    let struct_literal = format!(
        "{sn} {{ {sf}: {sv}, {if_}: {iv} }}",
        sn = struct_name,
        sf = str_field.name,
        sv = str_field.literal,
        if_ = i64_field.name,
        iv = i64_field.literal,
    );

    let result_name = scope.fresh_name();
    let result_type = if access_i64 {
        i64_field.type_info.clone()
    } else {
        str_field.type_info.clone()
    };
    scope.add_local(result_name.clone(), result_type, false);

    let indent = emit.indent_str();
    let code = format!(
        "let {rn} = {fn_name}({sl})\n{indent}assert({rn} == {expected})",
        rn = result_name,
        fn_name = fn_name,
        sl = struct_literal,
        expected = expected_val,
        indent = indent,
    );

    Some(code)
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
        assert_eq!(OptionalChainCall.name(), "optional_chain_call");
    }

    #[test]
    fn precondition_rejects_no_module() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!OptionalChainCall.precondition(&scope, &params));
    }

    #[test]
    fn precondition_rejects_class_methods() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!OptionalChainCall.precondition(&scope, &params));
    }

    #[test]
    fn precondition_accepts_module_level() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(OptionalChainCall.precondition(&scope, &params));
    }

    #[test]
    fn generates_string_method_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = OptionalChainCall.generate(&mut scope, &mut emit, &params) {
                // Check for string method variant (has `string?` in module decl)
                if scope.module_decls.iter().any(|d| d.contains("string?")) {
                    found = true;
                    // Should have 1 module decl: the function
                    assert_eq!(
                        scope.module_decls.len(),
                        1,
                        "expected 1 module_decl for string variant, got {}",
                        scope.module_decls.len()
                    );
                    // Function decl should contain ?. and ??
                    let func_decl = &scope.module_decls[0];
                    assert!(
                        func_decl.contains("?."),
                        "expected ?. in func decl: {func_decl}"
                    );
                    assert!(
                        func_decl.contains("??"),
                        "expected ?? in func decl: {func_decl}"
                    );
                    // Inline code should have assert
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated string method variant in 100 seeds");
    }

    #[test]
    fn generates_struct_field_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = OptionalChainCall.generate(&mut scope, &mut emit, &params) {
                // Check for struct variant (has struct decl)
                if scope
                    .module_decls
                    .iter()
                    .any(|d| d.contains("struct Info_"))
                {
                    found = true;
                    // Should have 2 module decls: struct + function
                    assert_eq!(
                        scope.module_decls.len(),
                        2,
                        "expected 2 module_decls for struct variant, got {}",
                        scope.module_decls.len()
                    );
                    // Struct decl
                    assert!(
                        scope.module_decls[0].contains("struct Info_"),
                        "expected struct decl: {}",
                        scope.module_decls[0]
                    );
                    // Function decl should contain ?. and ??
                    let func_decl = &scope.module_decls[1];
                    assert!(
                        func_decl.contains("?."),
                        "expected ?. in func decl: {func_decl}"
                    );
                    assert!(
                        func_decl.contains("??"),
                        "expected ?? in func decl: {func_decl}"
                    );
                    // Inline code should have struct construction and assert
                    assert!(
                        text.contains("Info_"),
                        "expected struct literal in code: {text}"
                    );
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated struct field variant in 100 seeds");
    }

    #[test]
    fn result_type_matches_method_return() {
        let table = SymbolTable::new();
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(_text) = OptionalChainCall.generate(&mut scope, &mut emit, &params) {
                // Verify result local was registered
                assert!(
                    !scope.locals.is_empty(),
                    "expected at least one local variable"
                );
                let (_, ty, _) = scope.locals.last().unwrap();
                // Result must be i64 or string (not optional)
                assert!(
                    matches!(
                        ty,
                        TypeInfo::Primitive(PrimitiveType::I64)
                            | TypeInfo::Primitive(PrimitiveType::String)
                    ),
                    "result type should be i64 or string, got {:?}",
                    ty
                );
                return;
            }
        }
        panic!("never generated output in 100 seeds");
    }

    #[test]
    fn all_string_methods_reachable() {
        let table = SymbolTable::new();
        let mut seen_length = false;
        let mut seen_to_upper = false;
        let mut seen_trim = false;

        for seed in 0..500 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(_) = OptionalChainCall.generate(&mut scope, &mut emit, &params) {
                for decl in &scope.module_decls {
                    if decl.contains("?.length(") {
                        seen_length = true;
                    }
                    if decl.contains("?.to_upper(") {
                        seen_to_upper = true;
                    }
                    if decl.contains("?.trim(") {
                        seen_trim = true;
                    }
                }
            }
            if seen_length && seen_to_upper && seen_trim {
                break;
            }
        }
        assert!(seen_length, "never generated length() variant");
        assert!(seen_to_upper, "never generated to_upper() variant");
        assert!(seen_trim, "never generated trim() variant");
    }
}
