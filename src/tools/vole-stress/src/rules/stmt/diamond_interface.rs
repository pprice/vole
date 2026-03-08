//! Rule: diamond interface inheritance patterns.
//!
//! Generates a diamond inheritance pattern where a class implements two
//! interfaces that both extend a common base interface. This stresses vtable
//! generation, interface dispatch, and the resolution of inherited interface
//! methods across the diamond.
//!
//! **Variant 0 -- i64 diamond:**
//! ```vole
//! interface BaseLocal0 {
//!     func get_id() -> i64
//! }
//!
//! interface LeftLocal0 extends BaseLocal0 {
//!     func left_val() -> i64
//! }
//!
//! interface RightLocal0 extends BaseLocal0 {
//!     func right_val() -> i64
//! }
//!
//! class DiamondLocal0 {
//!     field1: i64
//!     field2: i64
//! }
//!
//! extend DiamondLocal0 with LeftLocal0 {
//!     func get_id() -> i64 {
//!         return self.field1
//!     }
//!     func left_val() -> i64 {
//!         return self.field1
//!     }
//! }
//!
//! extend DiamondLocal0 with RightLocal0 {
//!     func right_val() -> i64 {
//!         return self.field2
//!     }
//! }
//!
//! func use_base_local0(b: BaseLocal0) -> i64 {
//!     return b.get_id()
//! }
//! func use_left_local0(l: LeftLocal0) -> i64 {
//!     return l.left_val()
//! }
//! func use_right_local0(r: RightLocal0) -> i64 {
//!     return r.right_val()
//! }
//!
//! let local1 = DiamondLocal0 { field1: 10, field2: 20 }
//! assert(use_base_local0(local1) == 10)
//! assert(use_left_local0(local1) == 10)
//! assert(use_right_local0(local1) == 20)
//! ```
//!
//! **Variant 1 -- string diamond:**
//! ```vole
//! interface BaseLocal0 {
//!     func label() -> string
//! }
//!
//! interface LeftLocal0 extends BaseLocal0 {
//!     func left_str() -> string
//! }
//!
//! interface RightLocal0 extends BaseLocal0 {
//!     func right_str() -> string
//! }
//!
//! class DiamondLocal0 {
//!     tag: string
//!     num: i64
//! }
//!
//! extend DiamondLocal0 with LeftLocal0 {
//!     func label() -> string {
//!         return self.tag
//!     }
//!     func left_str() -> string {
//!         return self.tag
//!     }
//! }
//!
//! extend DiamondLocal0 with RightLocal0 {
//!     func right_str() -> string {
//!         return "{self.num}"
//!     }
//! }
//!
//! func use_base_local0(b: BaseLocal0) -> string { ... }
//! func use_left_local0(l: LeftLocal0) -> string { ... }
//! func use_right_local0(r: RightLocal0) -> string { ... }
//!
//! let local1 = DiamondLocal0 { tag: "hello", num: 42 }
//! assert(use_base_local0(local1) == "hello")
//! assert(use_left_local0(local1) == "hello")
//! assert(use_right_local0(local1) == "42")
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;

pub struct DiamondInterface;

impl StmtRule for DiamondInterface {
    fn name(&self) -> &'static str {
        "diamond_interface"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.01)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let _module_id = scope.module_id?;

        let variant = emit.gen_range(0..2);
        match variant {
            0 => emit_i64_diamond(scope, emit),
            _ => emit_string_diamond(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0 -- i64 diamond
// ---------------------------------------------------------------------------

fn emit_i64_diamond(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let base = scope.fresh_name();
    let cap = capitalize(&base);

    let base_iface = format!("Base{}", cap);
    let left_iface = format!("Left{}", cap);
    let right_iface = format!("Right{}", cap);
    let class_name = format!("Diamond{}", cap);
    let use_base_fn = format!("use_base_{}", base);
    let use_left_fn = format!("use_left_{}", base);
    let use_right_fn = format!("use_right_{}", base);

    let field1_val = emit.gen_i64_range(1, 50);
    let field2_val = emit.gen_i64_range(1, 50);

    // --- Module decl 1: base interface ---
    let base_decl = format!("interface {} {{\n    func get_id() -> i64\n}}", base_iface,);
    scope.add_module_decl(base_decl);

    // --- Module decl 2: left interface extends base ---
    let left_decl = format!(
        "interface {} extends {} {{\n    func left_val() -> i64\n}}",
        left_iface, base_iface,
    );
    scope.add_module_decl(left_decl);

    // --- Module decl 3: right interface extends base ---
    let right_decl = format!(
        "interface {} extends {} {{\n    func right_val() -> i64\n}}",
        right_iface, base_iface,
    );
    scope.add_module_decl(right_decl);

    // --- Module decl 4: class ---
    let class_decl = format!(
        "class {} {{\n    field1: i64\n    field2: i64\n}}",
        class_name,
    );
    scope.add_module_decl(class_decl);

    // --- Module decl 5: extend class with Left (implements get_id + left_val) ---
    let extend_left = format!(
        "extend {} with {} {{\n    \
            func get_id() -> i64 {{\n        \
                return self.field1\n    \
            }}\n    \
            func left_val() -> i64 {{\n        \
                return self.field1\n    \
            }}\n\
        }}",
        class_name, left_iface,
    );
    scope.add_module_decl(extend_left);

    // --- Module decl 6: extend class with Right (implements right_val) ---
    let extend_right = format!(
        "extend {} with {} {{\n    \
            func right_val() -> i64 {{\n        \
                return self.field2\n    \
            }}\n\
        }}",
        class_name, right_iface,
    );
    scope.add_module_decl(extend_right);

    // --- Module decl 7: use_base helper ---
    let use_base_decl = format!(
        "func {}(b: {}) -> i64 {{\n    return b.get_id()\n}}",
        use_base_fn, base_iface,
    );
    scope.add_module_decl(use_base_decl);

    // --- Module decl 8: use_left helper ---
    let use_left_decl = format!(
        "func {}(l: {}) -> i64 {{\n    return l.left_val()\n}}",
        use_left_fn, left_iface,
    );
    scope.add_module_decl(use_left_decl);

    // --- Module decl 9: use_right helper ---
    let use_right_decl = format!(
        "func {}(r: {}) -> i64 {{\n    return r.right_val()\n}}",
        use_right_fn, right_iface,
    );
    scope.add_module_decl(use_right_decl);

    // --- Inline code ---
    // Do NOT add the class instance to scope (same pattern as generic_struct_let).
    let inst = scope.fresh_name();
    let indent = emit.indent_str();

    Some(format!(
        "let {inst} = {cls} {{ field1: {f1}, field2: {f2} }}\n\
         {indent}assert({use_base}({inst}) == {f1})\n\
         {indent}assert({use_left}({inst}) == {f1})\n\
         {indent}assert({use_right}({inst}) == {f2})",
        inst = inst,
        cls = class_name,
        f1 = field1_val,
        f2 = field2_val,
        use_base = use_base_fn,
        use_left = use_left_fn,
        use_right = use_right_fn,
        indent = indent,
    ))
}

// ---------------------------------------------------------------------------
// Variant 1 -- string diamond
// ---------------------------------------------------------------------------

fn emit_string_diamond(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let base = scope.fresh_name();
    let cap = capitalize(&base);

    let base_iface = format!("Base{}", cap);
    let left_iface = format!("Left{}", cap);
    let right_iface = format!("Right{}", cap);
    let class_name = format!("Diamond{}", cap);
    let use_base_fn = format!("use_base_{}", base);
    let use_left_fn = format!("use_left_{}", base);
    let use_right_fn = format!("use_right_{}", base);

    let str_vals = ["hello", "world", "test", "item", "data"];
    let str_idx = emit.gen_range(0..str_vals.len());
    let str_val = str_vals[str_idx];
    let num_val = emit.gen_i64_range(1, 99);

    // --- Module decl 1: base interface ---
    let base_decl = format!(
        "interface {} {{\n    func label() -> string\n}}",
        base_iface,
    );
    scope.add_module_decl(base_decl);

    // --- Module decl 2: left interface extends base ---
    let left_decl = format!(
        "interface {} extends {} {{\n    func left_str() -> string\n}}",
        left_iface, base_iface,
    );
    scope.add_module_decl(left_decl);

    // --- Module decl 3: right interface extends base ---
    let right_decl = format!(
        "interface {} extends {} {{\n    func right_str() -> string\n}}",
        right_iface, base_iface,
    );
    scope.add_module_decl(right_decl);

    // --- Module decl 4: class ---
    let class_decl = format!("class {} {{\n    tag: string\n    num: i64\n}}", class_name,);
    scope.add_module_decl(class_decl);

    // --- Module decl 5: extend class with Left (implements label + left_str) ---
    let extend_left = format!(
        "extend {} with {} {{\n    \
            func label() -> string {{\n        \
                return self.tag\n    \
            }}\n    \
            func left_str() -> string {{\n        \
                return self.tag\n    \
            }}\n\
        }}",
        class_name, left_iface,
    );
    scope.add_module_decl(extend_left);

    // --- Module decl 6: extend class with Right (implements right_str) ---
    let extend_right = format!(
        "extend {} with {} {{\n    \
            func right_str() -> string {{\n        \
                return \"{{self.num}}\"\n    \
            }}\n\
        }}",
        class_name, right_iface,
    );
    scope.add_module_decl(extend_right);

    // --- Module decl 7: use_base helper ---
    let use_base_decl = format!(
        "func {}(b: {}) -> string {{\n    return b.label()\n}}",
        use_base_fn, base_iface,
    );
    scope.add_module_decl(use_base_decl);

    // --- Module decl 8: use_left helper ---
    let use_left_decl = format!(
        "func {}(l: {}) -> string {{\n    return l.left_str()\n}}",
        use_left_fn, left_iface,
    );
    scope.add_module_decl(use_left_decl);

    // --- Module decl 9: use_right helper ---
    let use_right_decl = format!(
        "func {}(r: {}) -> string {{\n    return r.right_str()\n}}",
        use_right_fn, right_iface,
    );
    scope.add_module_decl(use_right_decl);

    // --- Inline code ---
    // Do NOT add the class instance to scope (same pattern as generic_struct_let).
    let inst = scope.fresh_name();
    let indent = emit.indent_str();

    Some(format!(
        "let {inst} = {cls} {{ tag: \"{str_val}\", num: {num} }}\n\
         {indent}assert({use_base}({inst}) == \"{str_val}\")\n\
         {indent}assert({use_left}({inst}) == \"{str_val}\")\n\
         {indent}assert({use_right}({inst}) == \"{num}\")",
        inst = inst,
        cls = class_name,
        str_val = str_val,
        num = num_val,
        use_base = use_base_fn,
        use_left = use_left_fn,
        use_right = use_right_fn,
        indent = indent,
    ))
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Capitalize the first character of a string (e.g. "local0" -> "Local0").
fn capitalize(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
    }
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
        assert_eq!(DiamondInterface.name(), "diamond_interface");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!DiamondInterface.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(crate::symbols::ModuleId(0));
        assert!(DiamondInterface.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!DiamondInterface.precondition(&scope, &params));
    }

    #[test]
    fn generates_diamond_across_seeds() {
        let table = SymbolTable::new();
        let mut found_i64 = false;
        let mut found_string = false;

        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let text = DiamondInterface
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            // Every seed should produce 9 module decls:
            // base iface, left iface, right iface, class,
            // extend left, extend right,
            // use_base fn, use_left fn, use_right fn
            assert_eq!(
                scope.module_decls.len(),
                9,
                "seed {seed}: expected 9 module_decls, got {}",
                scope.module_decls.len(),
            );

            // Decl 0: base interface
            assert!(
                scope.module_decls[0].contains("interface"),
                "seed {seed}: expected base interface: {}",
                scope.module_decls[0],
            );

            // Decl 1: left extends base
            assert!(
                scope.module_decls[1].contains("extends"),
                "seed {seed}: expected left extends: {}",
                scope.module_decls[1],
            );

            // Decl 2: right extends base
            assert!(
                scope.module_decls[2].contains("extends"),
                "seed {seed}: expected right extends: {}",
                scope.module_decls[2],
            );

            // Decl 3: class
            assert!(
                scope.module_decls[3].contains("class"),
                "seed {seed}: expected class: {}",
                scope.module_decls[3],
            );

            // Decl 4: extend with left
            assert!(
                scope.module_decls[4].contains("extend") && scope.module_decls[4].contains("with"),
                "seed {seed}: expected extend-with left: {}",
                scope.module_decls[4],
            );

            // Decl 5: extend with right
            assert!(
                scope.module_decls[5].contains("extend") && scope.module_decls[5].contains("with"),
                "seed {seed}: expected extend-with right: {}",
                scope.module_decls[5],
            );

            // Inline code should have asserts
            assert!(
                text.contains("assert("),
                "seed {seed}: expected assert in code: {text}",
            );

            // Interface methods should have implicit self (no self param)
            assert!(
                !scope.module_decls[0].contains("self"),
                "seed {seed}: base interface should have implicit self: {}",
                scope.module_decls[0],
            );

            // Check variant type
            if text.contains("field1:") && text.contains("field2:") {
                found_i64 = true;
            }
            if text.contains("tag:") && text.contains("num:") {
                found_string = true;
            }

            if found_i64 && found_string {
                break;
            }
        }

        assert!(
            found_i64,
            "never generated i64 diamond variant in 100 seeds"
        );
        assert!(
            found_string,
            "never generated string diamond variant in 100 seeds"
        );
    }
}
