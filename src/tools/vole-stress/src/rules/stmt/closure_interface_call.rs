//! Rule: closures capturing class instances and calling interface methods.
//!
//! Exercises RC types (class instances) + closure captures + interface dispatch
//! together. Generates an interface, a class, an extend block implementing the
//! interface method, a function returning a closure that captures the class
//! instance and calls the interface method, and test assertions.
//!
//! **Variant 0 -- closure calls method returning i64 (sum of fields):**
//! ```vole
//! interface Summable_12345 {
//!     func total() -> i64
//! }
//!
//! class Pair_12345 {
//!     a: i64
//!     b: i64
//! }
//!
//! extend Pair_12345 with Summable_12345 {
//!     func total(self: Pair_12345) -> i64 {
//!         return self.a + self.b
//!     }
//! }
//!
//! func make_total_getter_12345(p: Pair_12345) -> () -> i64 {
//!     return () => p.total()
//! }
//!
//! let inst = Pair_12345 { a: 10, b: 20 }
//! let getter = make_total_getter_12345(inst)
//! assert(getter() == 30)
//! ```
//!
//! **Variant 1 -- closure calls method returning string (interpolation):**
//! ```vole
//! interface Showable_12345 {
//!     func show() -> string
//! }
//!
//! class Point_12345 {
//!     x: i64
//!     y: i64
//! }
//!
//! extend Point_12345 with Showable_12345 {
//!     func show(self: Point_12345) -> string {
//!         return "{self.x},{self.y}"
//!     }
//! }
//!
//! func make_shower_12345(p: Point_12345) -> () -> string {
//!     return () => p.show()
//! }
//!
//! let inst = Point_12345 { x: 5, y: 9 }
//! let shower = make_shower_12345(inst)
//! assert(shower() == "5,9")
//! ```
//!
//! **Variant 2 -- two closures, one calls method, one uses field + method:**
//! ```vole
//! interface Combinable_12345 {
//!     func combine() -> i64
//! }
//!
//! class Triple_12345 {
//!     a: i64
//!     b: i64
//!     c: i64
//! }
//!
//! extend Triple_12345 with Combinable_12345 {
//!     func combine(self: Triple_12345) -> i64 {
//!         return self.a + self.b + self.c
//!     }
//! }
//!
//! func make_combine_getter_12345(t: Triple_12345) -> () -> i64 {
//!     return () => t.combine()
//! }
//!
//! func make_offset_getter_12345(t: Triple_12345, offset: i64) -> () -> i64 {
//!     return () => t.combine() + offset
//! }
//!
//! let inst = Triple_12345 { a: 3, b: 4, c: 5 }
//! let getter1 = make_combine_getter_12345(inst)
//! let getter2 = make_offset_getter_12345(inst, 100)
//! assert(getter1() == 12)
//! assert(getter2() == 112)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;

pub struct ClosureInterfaceCall;

impl StmtRule for ClosureInterfaceCall {
    fn name(&self) -> &'static str {
        "closure_interface_call"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let _module_id = scope.module_id?;

        let variant = emit.gen_range(0..3);
        match variant {
            0 => emit_i64_sum_variant(scope, emit),
            1 => emit_string_show_variant(scope, emit),
            _ => emit_two_closures_variant(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0 -- closure captures class, calls method returning i64 (sum)
// ---------------------------------------------------------------------------

fn emit_i64_sum_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);

    // Pick names
    let iface_prefixes = ["Summable", "Totalable", "Addable", "Countable"];
    let iface_prefix = iface_prefixes[emit.gen_range(0..iface_prefixes.len())];
    let iface_name = format!("{}_{}", iface_prefix, uid);

    let method_names = ["total", "sum_all", "tally", "count_up"];
    let method = method_names[emit.gen_range(0..method_names.len())];

    let class_prefixes = ["Pair", "Duo", "Coord", "Cell"];
    let class_prefix = class_prefixes[emit.gen_range(0..class_prefixes.len())];
    let class_name = format!("{}_{}", class_prefix, uid);

    let func_prefixes = ["make_total_getter", "build_sum_fn", "create_tally_fn"];
    let func_prefix = func_prefixes[emit.gen_range(0..func_prefixes.len())];
    let func_name = format!("{}_{}", func_prefix, uid);

    // Pick 2 field names
    let field_sets: &[&[&str]] = &[&["a", "b"], &["x", "y"], &["left", "right"]];
    let fields = field_sets[emit.gen_range(0..field_sets.len())];

    // Pick field values
    let f0_val = emit.gen_i64_range(1, 30);
    let f1_val = emit.gen_i64_range(1, 30);
    let expected = f0_val + f1_val;

    // --- Module decl 1: interface ---
    let iface_decl = format!(
        "interface {} {{\n    func {}() -> i64\n}}",
        iface_name, method,
    );
    scope.add_module_decl(iface_decl);

    // --- Module decl 2: class ---
    let class_decl = format!(
        "class {} {{\n    {}: i64\n    {}: i64\n}}",
        class_name, fields[0], fields[1],
    );
    scope.add_module_decl(class_decl);

    // --- Module decl 3: extend with interface ---
    let sum_expr = format!("self.{} + self.{}", fields[0], fields[1]);
    let extend_decl = format!(
        "extend {} with {} {{\n    func {}(self: {}) -> i64 {{\n        return {}\n    }}\n}}",
        class_name, iface_name, method, class_name, sum_expr,
    );
    scope.add_module_decl(extend_decl);

    // --- Module decl 4: function returning closure ---
    let param_name_choices = ["p", "obj", "item", "inst"];
    let param_name = param_name_choices[emit.gen_range(0..param_name_choices.len())];
    let func_decl = format!(
        "func {}({}: {}) -> () -> i64 {{\n    return () => {}.{}()\n}}",
        func_name, param_name, class_name, param_name, method,
    );
    scope.add_module_decl(func_decl);

    // --- Inline code: instantiate, get closure, assert ---
    let inst_var = scope.fresh_name();
    let closure_var = scope.fresh_name();
    let field_values = format!("{}: {}, {}: {}", fields[0], f0_val, fields[1], f1_val);
    let indent = emit.indent_str();

    Some(format!(
        "let {inst} = {cls} {{ {fvals} }}\n\
         {indent}let {closure} = {func}({inst})\n\
         {indent}assert({closure}() == {expected})",
        inst = inst_var,
        cls = class_name,
        fvals = field_values,
        closure = closure_var,
        func = func_name,
        expected = expected,
        indent = indent,
    ))
}

// ---------------------------------------------------------------------------
// Variant 1 -- closure captures class, calls method returning string
// ---------------------------------------------------------------------------

fn emit_string_show_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);

    // Pick names
    let iface_prefixes = ["Showable", "Displayable", "Printable", "Renderable"];
    let iface_prefix = iface_prefixes[emit.gen_range(0..iface_prefixes.len())];
    let iface_name = format!("{}_{}", iface_prefix, uid);

    let method_names = ["show", "display", "render", "stringify"];
    let method = method_names[emit.gen_range(0..method_names.len())];

    let class_prefixes = ["Point", "Loc", "Spot", "Marker"];
    let class_prefix = class_prefixes[emit.gen_range(0..class_prefixes.len())];
    let class_name = format!("{}_{}", class_prefix, uid);

    let func_prefixes = ["make_shower", "build_display_fn", "create_renderer"];
    let func_prefix = func_prefixes[emit.gen_range(0..func_prefixes.len())];
    let func_name = format!("{}_{}", func_prefix, uid);

    // Pick 2 field names
    let field_sets: &[&[&str]] = &[&["x", "y"], &["row", "col"], &["lat", "lon"]];
    let fields = field_sets[emit.gen_range(0..field_sets.len())];

    // Pick field values
    let f0_val = emit.gen_i64_range(1, 50);
    let f1_val = emit.gen_i64_range(1, 50);

    // Build expected string and method body
    let sep_chars = [",", ":", "/"];
    let sep = sep_chars[emit.gen_range(0..sep_chars.len())];
    let expected_str = format!("{}{}{}", f0_val, sep, f1_val);

    // --- Module decl 1: interface ---
    let iface_decl = format!(
        "interface {} {{\n    func {}() -> string\n}}",
        iface_name, method,
    );
    scope.add_module_decl(iface_decl);

    // --- Module decl 2: class ---
    let class_decl = format!(
        "class {} {{\n    {}: i64\n    {}: i64\n}}",
        class_name, fields[0], fields[1],
    );
    scope.add_module_decl(class_decl);

    // --- Module decl 3: extend with interface ---
    let interp_body = format!(
        "return \"{{self.{}}}{}{{self.{}}}\"",
        fields[0], sep, fields[1],
    );
    let extend_decl = format!(
        "extend {} with {} {{\n    func {}(self: {}) -> string {{\n        {}\n    }}\n}}",
        class_name, iface_name, method, class_name, interp_body,
    );
    scope.add_module_decl(extend_decl);

    // --- Module decl 4: function returning closure ---
    let param_name_choices = ["p", "obj", "item", "inst"];
    let param_name = param_name_choices[emit.gen_range(0..param_name_choices.len())];
    let func_decl = format!(
        "func {}({}: {}) -> () -> string {{\n    return () => {}.{}()\n}}",
        func_name, param_name, class_name, param_name, method,
    );
    scope.add_module_decl(func_decl);

    // --- Inline code: instantiate, get closure, assert ---
    let inst_var = scope.fresh_name();
    let closure_var = scope.fresh_name();
    let field_values = format!("{}: {}, {}: {}", fields[0], f0_val, fields[1], f1_val);
    let indent = emit.indent_str();

    Some(format!(
        "let {inst} = {cls} {{ {fvals} }}\n\
         {indent}let {closure} = {func}({inst})\n\
         {indent}assert({closure}() == \"{expected}\")",
        inst = inst_var,
        cls = class_name,
        fvals = field_values,
        closure = closure_var,
        func = func_name,
        expected = expected_str,
        indent = indent,
    ))
}

// ---------------------------------------------------------------------------
// Variant 2 -- two closures: one calls method directly, one adds offset
// ---------------------------------------------------------------------------

fn emit_two_closures_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);

    // Pick names
    let iface_prefixes = ["Combinable", "Mergeable", "Reducible", "Foldable"];
    let iface_prefix = iface_prefixes[emit.gen_range(0..iface_prefixes.len())];
    let iface_name = format!("{}_{}", iface_prefix, uid);

    let method_names = ["combine", "merge", "reduce", "fold_up"];
    let method = method_names[emit.gen_range(0..method_names.len())];

    let class_prefixes = ["Triple", "Trio", "Triad", "Triplet"];
    let class_prefix = class_prefixes[emit.gen_range(0..class_prefixes.len())];
    let class_name = format!("{}_{}", class_prefix, uid);

    let func_a_prefixes = ["make_combine_getter", "build_merge_fn", "create_fold_fn"];
    let func_a_prefix = func_a_prefixes[emit.gen_range(0..func_a_prefixes.len())];
    let func_a_name = format!("{}_{}", func_a_prefix, uid);

    let func_b_prefixes = [
        "make_offset_getter",
        "build_adjusted_fn",
        "create_shifted_fn",
    ];
    let func_b_prefix = func_b_prefixes[emit.gen_range(0..func_b_prefixes.len())];
    let func_b_name = format!("{}_{}", func_b_prefix, uid);

    // Pick 3 field names
    let field_sets: &[&[&str]] = &[&["a", "b", "c"], &["p", "q", "r"], &["u", "v", "w"]];
    let fields = field_sets[emit.gen_range(0..field_sets.len())];

    // Pick field values
    let f0_val = emit.gen_i64_range(1, 20);
    let f1_val = emit.gen_i64_range(1, 20);
    let f2_val = emit.gen_i64_range(1, 20);
    let combined = f0_val + f1_val + f2_val;

    // Offset for second closure
    let offset = emit.gen_i64_range(10, 200);
    let expected_offset = combined + offset;

    // --- Module decl 1: interface ---
    let iface_decl = format!(
        "interface {} {{\n    func {}() -> i64\n}}",
        iface_name, method,
    );
    scope.add_module_decl(iface_decl);

    // --- Module decl 2: class ---
    let class_decl = format!(
        "class {} {{\n    {}: i64\n    {}: i64\n    {}: i64\n}}",
        class_name, fields[0], fields[1], fields[2],
    );
    scope.add_module_decl(class_decl);

    // --- Module decl 3: extend with interface ---
    let sum_expr = format!(
        "self.{} + self.{} + self.{}",
        fields[0], fields[1], fields[2]
    );
    let extend_decl = format!(
        "extend {} with {} {{\n    func {}(self: {}) -> i64 {{\n        return {}\n    }}\n}}",
        class_name, iface_name, method, class_name, sum_expr,
    );
    scope.add_module_decl(extend_decl);

    // --- Module decl 4: function A returning closure (direct method call) ---
    let param_a_choices = ["t", "obj", "item"];
    let param_a = param_a_choices[emit.gen_range(0..param_a_choices.len())];
    let func_a_decl = format!(
        "func {}({}: {}) -> () -> i64 {{\n    return () => {}.{}()\n}}",
        func_a_name, param_a, class_name, param_a, method,
    );
    scope.add_module_decl(func_a_decl);

    // --- Module decl 5: function B returning closure (method + offset) ---
    let param_b_choices = ["t", "obj", "item"];
    let param_b = param_b_choices[emit.gen_range(0..param_b_choices.len())];
    let func_b_decl = format!(
        "func {}({}: {}, offset: i64) -> () -> i64 {{\n    return () => {}.{}() + offset\n}}",
        func_b_name, param_b, class_name, param_b, method,
    );
    scope.add_module_decl(func_b_decl);

    // --- Inline code: instantiate, get closures, assert ---
    let inst_var = scope.fresh_name();
    let closure_a_var = scope.fresh_name();
    let closure_b_var = scope.fresh_name();
    let field_values = format!(
        "{}: {}, {}: {}, {}: {}",
        fields[0], f0_val, fields[1], f1_val, fields[2], f2_val,
    );
    let indent = emit.indent_str();

    Some(format!(
        "let {inst} = {cls} {{ {fvals} }}\n\
         {indent}let {ca} = {fa}({inst})\n\
         {indent}let {cb} = {fb}({inst}, {offset})\n\
         {indent}assert({ca}() == {expected_a})\n\
         {indent}assert({cb}() == {expected_b})",
        inst = inst_var,
        cls = class_name,
        fvals = field_values,
        ca = closure_a_var,
        fa = func_a_name,
        cb = closure_b_var,
        fb = func_b_name,
        offset = offset,
        expected_a = combined,
        expected_b = expected_offset,
        indent = indent,
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
    use crate::symbols::{ModuleId, SymbolId, SymbolTable};
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
        assert_eq!(ClosureInterfaceCall.name(), "closure_interface_call");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!ClosureInterfaceCall.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(ModuleId(0));
        assert!(ClosureInterfaceCall.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id = Some((ModuleId(0), SymbolId(0)));
        assert!(!ClosureInterfaceCall.precondition(&scope, &params));
    }

    #[test]
    fn returns_none_without_module() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = test_params();

        let result = ClosureInterfaceCall.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn generates_module_decls_variant_0() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(ModuleId(0));

        // Use a seed that produces variant 0
        // variant = gen_range(0..3), we need variant == 0
        // We'll try multiple seeds to find one that hits variant 0
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let text = ClosureInterfaceCall
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            // Variant 0 has 4 module decls, variant 2 has 5
            if scope.module_decls.len() == 4 {
                // Check: interface, class, extend, function
                assert!(
                    scope.module_decls[0].contains("interface"),
                    "expected interface decl: {}",
                    scope.module_decls[0],
                );
                assert!(
                    scope.module_decls[0].contains("-> i64")
                        || scope.module_decls[0].contains("-> string"),
                    "expected return type in interface: {}",
                    scope.module_decls[0],
                );
                assert!(
                    scope.module_decls[1].contains("class"),
                    "expected class decl: {}",
                    scope.module_decls[1],
                );
                assert!(
                    scope.module_decls[2].contains("extend")
                        && scope.module_decls[2].contains("with"),
                    "expected extend-with decl: {}",
                    scope.module_decls[2],
                );
                assert!(
                    scope.module_decls[3].contains("func") && scope.module_decls[3].contains("=> "),
                    "expected closure-returning func: {}",
                    scope.module_decls[3],
                );
                assert!(text.contains("assert("), "expected assert in code: {text}",);
                found = true;
                break;
            }
        }
        assert!(found, "never generated a 4-decl variant in 100 seeds");
    }

    #[test]
    fn extend_blocks_have_explicit_self() {
        let table = SymbolTable::new();
        for seed in 0..30 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            ClosureInterfaceCall
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            // The extend block (decl 2) should have explicit self parameter
            let extend = &scope.module_decls[2];
            assert!(
                extend.contains("(self:"),
                "seed {seed}: expected explicit self param in extend: {extend}",
            );
        }
    }

    #[test]
    fn interfaces_have_implicit_self() {
        let table = SymbolTable::new();
        for seed in 0..30 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            ClosureInterfaceCall
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            // Interface declarations (decl 0) should NOT have self parameter
            let iface = &scope.module_decls[0];
            assert!(
                !iface.contains("self"),
                "seed {seed}: interface should have implicit self (no self param): {iface}",
            );
        }
    }

    #[test]
    fn does_not_add_locals_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = ClosureInterfaceCall.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        assert!(
            scope.locals.is_empty(),
            "should not add locals to scope for closure/interface-typed values",
        );
    }

    #[test]
    fn uses_class_not_struct() {
        let table = SymbolTable::new();
        for seed in 0..30 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            ClosureInterfaceCall
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            // Decl 1 should be a class, not a struct
            assert!(
                scope.module_decls[1].starts_with("class"),
                "seed {seed}: expected class decl, got: {}",
                scope.module_decls[1],
            );
        }
    }

    #[test]
    fn generates_all_three_variants() {
        let table = SymbolTable::new();
        let mut found_i64 = false;
        let mut found_string = false;
        let mut found_two_closures = false;

        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let text = ClosureInterfaceCall
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            if scope.module_decls.len() == 5 {
                // Variant 2: two closures (5 decls)
                found_two_closures = true;
            } else if scope.module_decls.len() == 4 {
                if scope.module_decls[0].contains("-> string") {
                    found_string = true;
                } else if scope.module_decls[0].contains("-> i64") {
                    found_i64 = true;
                }
            }

            // All variants should have asserts
            assert!(
                text.contains("assert("),
                "seed {seed}: expected asserts in code: {text}",
            );

            if found_i64 && found_string && found_two_closures {
                break;
            }
        }

        assert!(found_i64, "never generated i64 sum variant in 200 seeds");
        assert!(
            found_string,
            "never generated string show variant in 200 seeds"
        );
        assert!(
            found_two_closures,
            "never generated two-closures variant in 200 seeds"
        );
    }

    #[test]
    fn closure_returning_func_captures_parameter() {
        let table = SymbolTable::new();
        for seed in 0..30 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            ClosureInterfaceCall
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            // The function decl (decl 3) should return a closure type
            let func_decl = &scope.module_decls[3];
            assert!(
                func_decl.contains("-> ()"),
                "seed {seed}: func should return closure type: {func_decl}",
            );
            // And should contain a lambda expression
            assert!(
                func_decl.contains("=> "),
                "seed {seed}: func should contain lambda: {func_decl}",
            );
        }
    }

    #[test]
    fn deterministic_across_seeds() {
        let table = SymbolTable::new();
        for seed in 0..20 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let text = ClosureInterfaceCall
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            // Every seed should produce at least 4 module decls
            assert!(
                scope.module_decls.len() >= 4,
                "seed {seed}: expected >= 4 module_decls, got {}",
                scope.module_decls.len(),
            );

            // Inline code should reference the class name from decl 1
            let class_name = scope.module_decls[1]
                .split_whitespace()
                .nth(1)
                .expect("class name");
            assert!(
                text.contains(class_name),
                "seed {seed}: expected class name '{class_name}' in code: {text}",
            );
        }
    }
}
