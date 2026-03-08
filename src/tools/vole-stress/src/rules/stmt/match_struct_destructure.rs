//! Rule: generate match expressions with struct destructuring on optional
//! struct types.
//!
//! Stresses the interaction between optional types, match patterns, and
//! struct field access by generating a module-level struct, a function that
//! takes `StructName?` and uses `match` to destructure or handle `nil`, and
//! call-site assertions for both paths.
//!
//! **Variant 0 -- two i64 fields:**
//! ```vole
//! struct PointN_12345 {
//!     x: i64,
//!     y: i64,
//! }
//!
//! func describe_12345(p: PointN_12345?) -> string {
//!     return match p {
//!         PointN_12345 { x: px, y: py } => "point:{px},{py}"
//!         nil => "none"
//!     }
//! }
//!
//! let r1_12345 = describe_12345(PointN_12345 { x: 10, y: 20 })
//! assert(r1_12345 == "point:10,20")
//! let r2_12345 = describe_12345(nil)
//! assert(r2_12345 == "none")
//! ```
//!
//! **Variant 1 -- three fields (i64, string, i64):**
//! ```vole
//! struct Info_12345 {
//!     id: i64,
//!     label: string,
//!     count: i64,
//! }
//!
//! func show_12345(v: Info_12345?) -> string {
//!     return match v {
//!         Info_12345 { id: a, label: b, count: c } => "{a}:{b}:{c}"
//!         nil => "empty"
//!     }
//! }
//!
//! let r1_12345 = show_12345(Info_12345 { id: 5, label: "hi", count: 3 })
//! assert(r1_12345 == "5:hi:3")
//! let r2_12345 = show_12345(nil)
//! assert(r2_12345 == "empty")
//! ```
//!
//! **Variant 2 -- two fields (string, i64):**
//! ```vole
//! struct NamedVal_12345 {
//!     name: string,
//!     val: i64,
//! }
//!
//! func fmt_12345(v: NamedVal_12345?) -> string {
//!     return match v {
//!         NamedVal_12345 { name: n, val: v } => "{n}={v}"
//!         nil => "nil"
//!     }
//! }
//!
//! let r1_12345 = fmt_12345(NamedVal_12345 { name: "x", val: 7 })
//! assert(r1_12345 == "x=7")
//! let r2_12345 = fmt_12345(nil)
//! assert(r2_12345 == "nil")
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MatchStructDestructure;

impl StmtRule for MatchStructDestructure {
    fn name(&self) -> &'static str {
        "match_struct_destructure"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Module-level functions only (struct decls + func decls at module level).
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..3);
        match variant {
            0 => emit_two_i64_variant(scope, emit),
            1 => emit_three_field_variant(scope, emit),
            _ => emit_string_i64_variant(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0: struct with two i64 fields
// ---------------------------------------------------------------------------

fn emit_two_i64_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let struct_name = format!("PointN_{}", uid);
    let fn_name = format!("describe_{}", uid);

    let x_val = emit.gen_i64_range(1, 50);
    let y_val = emit.gen_i64_range(1, 50);

    // Struct declaration
    let struct_decl = format!(
        concat!("struct {} {{\n", "    x: i64,\n", "    y: i64,\n", "}}"),
        struct_name
    );
    scope.add_module_decl(struct_decl);

    // Function declaration
    let func_decl = format!(
        concat!(
            "func {}(p: {}?) -> string {{\n",
            "    return match p {{\n",
            "        {} {{ x: px, y: py }} => \"point:{{px}},{{py}}\"\n",
            "        nil => \"none\"\n",
            "    }}\n",
            "}}"
        ),
        fn_name, struct_name, struct_name
    );
    scope.add_module_decl(func_decl);

    let indent = emit.indent_str();

    let r1 = format!("r1_{}", uid);
    let r2 = format!("r2_{}", uid);

    scope.add_local(
        r1.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );
    scope.add_local(
        r2.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let expected = format!("point:{},{}", x_val, y_val);

    let code = format!(
        "let {r1} = {fn_name}({struct_name} {{ x: {x_val}, y: {y_val} }})\n\
         {indent}assert({r1} == \"{expected}\")\n\
         {indent}let {r2} = {fn_name}(nil)\n\
         {indent}assert({r2} == \"none\")",
    );

    Some(code)
}

// ---------------------------------------------------------------------------
// Variant 1: struct with three fields (i64, string, i64)
// ---------------------------------------------------------------------------

fn emit_three_field_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let struct_name = format!("Info_{}", uid);
    let fn_name = format!("show_{}", uid);

    let id_val = emit.gen_i64_range(1, 20);
    let labels = ["hi", "ok", "yes", "go", "up"];
    let label_val = labels[emit.gen_range(0..labels.len())];
    let count_val = emit.gen_i64_range(1, 10);

    // Struct declaration
    let struct_decl = format!(
        concat!(
            "struct {} {{\n",
            "    id: i64,\n",
            "    label: string,\n",
            "    count: i64,\n",
            "}}"
        ),
        struct_name
    );
    scope.add_module_decl(struct_decl);

    // Function declaration
    let func_decl = format!(
        concat!(
            "func {}(v: {}?) -> string {{\n",
            "    return match v {{\n",
            "        {} {{ id: a, label: b, count: c }} => \"{{a}}:{{b}}:{{c}}\"\n",
            "        nil => \"empty\"\n",
            "    }}\n",
            "}}"
        ),
        fn_name, struct_name, struct_name
    );
    scope.add_module_decl(func_decl);

    let indent = emit.indent_str();

    let r1 = format!("r1_{}", uid);
    let r2 = format!("r2_{}", uid);

    scope.add_local(
        r1.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );
    scope.add_local(
        r2.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let expected = format!("{}:{}:{}", id_val, label_val, count_val);

    let code = format!(
        "let {r1} = {fn_name}({struct_name} {{ id: {id_val}, label: \"{label_val}\", count: {count_val} }})\n\
         {indent}assert({r1} == \"{expected}\")\n\
         {indent}let {r2} = {fn_name}(nil)\n\
         {indent}assert({r2} == \"empty\")",
    );

    Some(code)
}

// ---------------------------------------------------------------------------
// Variant 2: struct with string + i64 fields
// ---------------------------------------------------------------------------

fn emit_string_i64_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let struct_name = format!("NamedVal_{}", uid);
    let fn_name = format!("fmt_{}", uid);

    let names = ["x", "y", "z", "a", "b"];
    let name_val = names[emit.gen_range(0..names.len())];
    let num_val = emit.gen_i64_range(1, 99);

    // Struct declaration
    let struct_decl = format!(
        concat!(
            "struct {} {{\n",
            "    name: string,\n",
            "    num: i64,\n",
            "}}"
        ),
        struct_name
    );
    scope.add_module_decl(struct_decl);

    // Function declaration
    let func_decl = format!(
        concat!(
            "func {}(v: {}?) -> string {{\n",
            "    return match v {{\n",
            "        {} {{ name: n, num: w }} => \"{{n}}={{w}}\"\n",
            "        nil => \"nil\"\n",
            "    }}\n",
            "}}"
        ),
        fn_name, struct_name, struct_name
    );
    scope.add_module_decl(func_decl);

    let indent = emit.indent_str();

    let r1 = format!("r1_{}", uid);
    let r2 = format!("r2_{}", uid);

    scope.add_local(
        r1.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );
    scope.add_local(
        r2.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        false,
    );

    let expected = format!("{}={}", name_val, num_val);

    let code = format!(
        "let {r1} = {fn_name}({struct_name} {{ name: \"{name_val}\", num: {num_val} }})\n\
         {indent}assert({r1} == \"{expected}\")\n\
         {indent}let {r2} = {fn_name}(nil)\n\
         {indent}assert({r2} == \"nil\")",
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

    fn test_params() -> Params {
        Params::from_iter([("probability", ParamValue::Probability(1.0))])
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(MatchStructDestructure.name(), "match_struct_destructure");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!MatchStructDestructure.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(MatchStructDestructure.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!MatchStructDestructure.precondition(&scope, &params));
    }

    #[test]
    fn generates_two_i64_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) =
                MatchStructDestructure.generate(&mut scope, &mut emit, &test_params())
            {
                if text.contains("describe_") {
                    found = true;
                    // Two module decls: struct + func
                    assert_eq!(
                        scope.module_decls.len(),
                        2,
                        "expected 2 module decls, got {}",
                        scope.module_decls.len()
                    );
                    let struct_decl = &scope.module_decls[0];
                    assert!(
                        struct_decl.contains("struct PointN_"),
                        "expected struct decl: {struct_decl}"
                    );
                    assert!(
                        struct_decl.contains("x: i64"),
                        "expected x field: {struct_decl}"
                    );
                    let func_decl = &scope.module_decls[1];
                    assert!(
                        func_decl.contains("-> string"),
                        "expected string return: {func_decl}"
                    );
                    assert!(
                        func_decl.contains("nil => \"none\""),
                        "expected nil arm: {func_decl}"
                    );
                    // Call-site code
                    assert!(text.contains("point:"), "expected point prefix: {text}");
                    assert!(
                        text.contains("== \"none\""),
                        "expected nil assertion: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated two_i64 variant in 100 seeds");
    }

    #[test]
    fn generates_three_field_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) =
                MatchStructDestructure.generate(&mut scope, &mut emit, &test_params())
            {
                if text.contains("show_") {
                    found = true;
                    assert_eq!(scope.module_decls.len(), 2);
                    let struct_decl = &scope.module_decls[0];
                    assert!(
                        struct_decl.contains("struct Info_"),
                        "expected Info struct: {struct_decl}"
                    );
                    assert!(
                        struct_decl.contains("label: string"),
                        "expected string field: {struct_decl}"
                    );
                    let func_decl = &scope.module_decls[1];
                    assert!(
                        func_decl.contains("nil => \"empty\""),
                        "expected nil arm: {func_decl}"
                    );
                    assert!(
                        text.contains("== \"empty\""),
                        "expected empty assertion: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated three_field variant in 100 seeds");
    }

    #[test]
    fn generates_string_i64_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) =
                MatchStructDestructure.generate(&mut scope, &mut emit, &test_params())
            {
                if text.contains("fmt_") {
                    found = true;
                    assert_eq!(scope.module_decls.len(), 2);
                    let struct_decl = &scope.module_decls[0];
                    assert!(
                        struct_decl.contains("struct NamedVal_"),
                        "expected NamedVal struct: {struct_decl}"
                    );
                    assert!(
                        struct_decl.contains("name: string"),
                        "expected name field: {struct_decl}"
                    );
                    let func_decl = &scope.module_decls[1];
                    assert!(
                        func_decl.contains("nil => \"nil\""),
                        "expected nil arm: {func_decl}"
                    );
                    assert!(text.contains("="), "expected = in output: {text}");
                    assert!(
                        text.contains("== \"nil\""),
                        "expected nil assertion: {text}"
                    );
                    break;
                }
            }
        }
        assert!(found, "never generated string_i64 variant in 100 seeds");
    }

    #[test]
    fn always_adds_two_string_locals() {
        let table = SymbolTable::new();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if MatchStructDestructure
                .generate(&mut scope, &mut emit, &test_params())
                .is_some()
            {
                assert_eq!(
                    scope.locals.len(),
                    2,
                    "expected 2 locals, got {}",
                    scope.locals.len()
                );
                for (name, ty, _) in &scope.locals {
                    assert_eq!(
                        *ty,
                        TypeInfo::Primitive(PrimitiveType::String),
                        "expected string type for local '{}', got {:?}",
                        name,
                        ty
                    );
                }
                return;
            }
        }
        panic!("never generated any variant in 50 seeds");
    }

    #[test]
    fn always_adds_two_module_decls() {
        let table = SymbolTable::new();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if MatchStructDestructure
                .generate(&mut scope, &mut emit, &test_params())
                .is_some()
            {
                assert_eq!(
                    scope.module_decls.len(),
                    2,
                    "expected 2 module decls (struct + func), got {}",
                    scope.module_decls.len()
                );
                return;
            }
        }
        panic!("never generated any variant in 50 seeds");
    }

    #[test]
    fn exercises_all_three_variants() {
        let table = SymbolTable::new();
        let mut saw_two_i64 = false;
        let mut saw_three_field = false;
        let mut saw_string_i64 = false;

        for seed in 0..300 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            if let Some(text) =
                MatchStructDestructure.generate(&mut scope, &mut emit, &test_params())
            {
                if text.contains("describe_") {
                    saw_two_i64 = true;
                }
                if text.contains("show_") {
                    saw_three_field = true;
                }
                if text.contains("fmt_") {
                    saw_string_i64 = true;
                }
            }

            if saw_two_i64 && saw_three_field && saw_string_i64 {
                break;
            }
        }

        assert!(saw_two_i64, "never generated two_i64 variant in 300 seeds");
        assert!(
            saw_three_field,
            "never generated three_field variant in 300 seeds"
        );
        assert!(
            saw_string_i64,
            "never generated string_i64 variant in 300 seeds"
        );
    }

    #[test]
    fn result_names_use_uid() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(7);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        if let Some(text) = MatchStructDestructure.generate(&mut scope, &mut emit, &test_params()) {
            assert!(
                text.contains("r1_") && text.contains("r2_"),
                "expected uid-based result names in code: {text}"
            );
        }
    }
}
