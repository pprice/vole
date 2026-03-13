//! Rule: struct implementing multiple interfaces via separate extend blocks.
//!
//! Stresses multiple vtable generation, interface dispatch, and the extend
//! block resolution path with split declarations by generating a fresh struct,
//! two interfaces, two extend blocks (one per interface), and two dispatcher
//! functions that accept interface-typed parameters.
//!
//! ```vole
//! struct Data_12345 {
//!     x: i64,
//!     y: i64,
//! }
//!
//! interface Showable_12345 {
//!     func show() -> string
//! }
//!
//! interface Summable_12345 {
//!     func total() -> i64
//! }
//!
//! extend Data_12345 with Showable_12345 {
//!     func show() -> string {
//!         return "({self.x}, {self.y})"
//!     }
//! }
//!
//! extend Data_12345 with Summable_12345 {
//!     func total() -> i64 {
//!         return self.x + self.y
//!     }
//! }
//!
//! func show_it_12345(d: Showable_12345) -> string {
//!     return d.show()
//! }
//!
//! func sum_it_12345(s: Summable_12345) -> i64 {
//!     return s.total()
//! }
//!
//! let inst = Data_12345 { x: 5, y: 10 }
//! let shown = show_it_12345(inst)
//! let total = sum_it_12345(inst)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MultiInterfaceExtend;

/// Pick a struct name prefix.
fn pick_struct_prefix(emit: &mut Emit) -> &'static str {
    let prefixes = ["Data", "Record", "Entry", "Item", "Node"];
    let idx = emit.gen_range(0..prefixes.len());
    prefixes[idx]
}

/// Pick field names for the struct (2 or 3 i64 fields).
fn pick_fields(emit: &mut Emit) -> Vec<&'static str> {
    let field_sets: &[&[&str]] = &[
        &["x", "y"],
        &["a", "b"],
        &["x", "y", "z"],
        &["a", "b", "c"],
        &["width", "height"],
        &["lo", "hi", "mid"],
    ];
    let idx = emit.gen_range(0..field_sets.len());
    field_sets[idx].to_vec()
}

/// Pick interface A name prefix (the "show"-like interface).
fn pick_iface_a_prefix(emit: &mut Emit) -> (&'static str, &'static str) {
    let options: &[(&str, &str)] = &[
        ("Showable", "show"),
        ("Displayable", "display"),
        ("Printable", "render"),
        ("Describable", "describe"),
    ];
    let idx = emit.gen_range(0..options.len());
    options[idx]
}

/// Pick interface B name prefix (the "sum"-like interface).
fn pick_iface_b_prefix(emit: &mut Emit) -> (&'static str, &'static str) {
    let options: &[(&str, &str)] = &[
        ("Summable", "total"),
        ("Measurable", "measure"),
        ("Computable", "compute"),
        ("Scorable", "score"),
    ];
    let idx = emit.gen_range(0..options.len());
    options[idx]
}

/// Pick a dispatcher function name prefix for the string interface.
fn pick_dispatch_a_prefix(emit: &mut Emit) -> &'static str {
    let prefixes = ["show_it", "display_it", "render_it", "describe_it"];
    let idx = emit.gen_range(0..prefixes.len());
    prefixes[idx]
}

/// Pick a dispatcher function name prefix for the i64 interface.
fn pick_dispatch_b_prefix(emit: &mut Emit) -> &'static str {
    let prefixes = ["sum_it", "measure_it", "compute_it", "score_it"];
    let idx = emit.gen_range(0..prefixes.len());
    prefixes[idx]
}

/// Build a string-returning method body from struct fields.
fn build_string_body(struct_name: &str, fields: &[&str], emit: &mut Emit) -> String {
    let variant = emit.gen_range(0..3);
    match variant {
        0 => {
            // Interpolation: "({self.x}, {self.y})"
            let parts: Vec<String> = fields.iter().map(|f| format!("{{self.{f}}}")).collect();
            format!("return \"({})\"", parts.join(", "),)
        }
        1 => {
            // Concatenation: "{struct_name}:" + self.x.to_string() + "," + self.y.to_string()
            let mut expr = format!("\"{struct_name}:\"");
            for (i, f) in fields.iter().enumerate() {
                if i > 0 {
                    expr.push_str(" + \",\"");
                }
                expr.push_str(&format!(" + self.{f}.to_string()"));
            }
            format!("return {expr}")
        }
        _ => {
            // Simple interpolation: "{self.x}-{self.y}"
            let parts: Vec<String> = fields.iter().map(|f| format!("{{self.{f}}}")).collect();
            format!("return \"{}\"", parts.join("-"))
        }
    }
}

/// Build an i64-returning method body from struct fields.
fn build_i64_body(fields: &[&str], emit: &mut Emit) -> String {
    let ops = ["+", "*"];
    let op = ops[emit.gen_range(0..ops.len())];

    if fields.len() == 2 {
        format!("return self.{} {} self.{}", fields[0], op, fields[1])
    } else {
        // 3 fields: chain ops
        let op2 = ops[emit.gen_range(0..ops.len())];
        format!(
            "return self.{} {} self.{} {} self.{}",
            fields[0], op, fields[1], op2, fields[2]
        )
    }
}

impl StmtRule for MultiInterfaceExtend {
    fn name(&self) -> &'static str {
        "multi_interface_extend"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Must be at module level (not inside a class method) and have a module
        scope.module_id.is_some() && scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Need a module to add declarations to
        let _module_id = scope.module_id?;

        let uid = emit.gen_range(10000..99999);

        // Pick names
        let struct_prefix = pick_struct_prefix(emit);
        let struct_name = format!("{}_{}", struct_prefix, uid);
        let fields = pick_fields(emit);

        let (iface_a_name_prefix, method_a) = pick_iface_a_prefix(emit);
        let iface_a_name = format!("{}_{}", iface_a_name_prefix, uid);

        let (iface_b_name_prefix, method_b) = pick_iface_b_prefix(emit);
        let iface_b_name = format!("{}_{}", iface_b_name_prefix, uid);

        let dispatch_a_prefix = pick_dispatch_a_prefix(emit);
        let dispatch_a_name = format!("{}_{}", dispatch_a_prefix, uid);

        let dispatch_b_prefix = pick_dispatch_b_prefix(emit);
        let dispatch_b_name = format!("{}_{}", dispatch_b_prefix, uid);

        // --- Module decl 1: struct ---
        let field_decls: Vec<String> = fields.iter().map(|f| format!("    {}: i64,", f)).collect();
        let struct_decl = format!("struct {} {{\n{}\n}}", struct_name, field_decls.join("\n"),);
        scope.add_module_decl(struct_decl);

        // --- Module decl 2: interface A (string-returning) ---
        let iface_a_decl = format!(
            "interface {} {{\n    func {}() -> string\n}}",
            iface_a_name, method_a,
        );
        scope.add_module_decl(iface_a_decl);

        // --- Module decl 3: interface B (i64-returning) ---
        let iface_b_decl = format!(
            "interface {} {{\n    func {}() -> i64\n}}",
            iface_b_name, method_b,
        );
        scope.add_module_decl(iface_b_decl);

        // --- Module decl 4: extend struct with interface A ---
        let string_body = build_string_body(&struct_name, &fields, emit);
        let extend_a_decl = format!(
            "extend {} with {} {{\n    func {}() -> string {{\n        {}\n    }}\n}}",
            struct_name, iface_a_name, method_a, string_body,
        );
        scope.add_module_decl(extend_a_decl);

        // --- Module decl 5: extend struct with interface B ---
        let i64_body = build_i64_body(&fields, emit);
        let extend_b_decl = format!(
            "extend {} with {} {{\n    func {}() -> i64 {{\n        {}\n    }}\n}}",
            struct_name, iface_b_name, method_b, i64_body,
        );
        scope.add_module_decl(extend_b_decl);

        // --- Module decl 6: dispatcher function A (interface-typed param -> string) ---
        let dispatch_a_decl = format!(
            "func {}(d: {}) -> string {{\n    return d.{}()\n}}",
            dispatch_a_name, iface_a_name, method_a,
        );
        scope.add_module_decl(dispatch_a_decl);

        // --- Module decl 7: dispatcher function B (interface-typed param -> i64) ---
        let dispatch_b_decl = format!(
            "func {}(s: {}) -> i64 {{\n    return s.{}()\n}}",
            dispatch_b_name, iface_b_name, method_b,
        );
        scope.add_module_decl(dispatch_b_decl);

        // --- Inline code: instantiate and call both dispatchers ---
        let inst_var = scope.fresh_name();
        let field_values: Vec<String> = fields
            .iter()
            .map(|f| {
                let v = emit.gen_i64_range(1, 50);
                format!("{}: {}", f, v)
            })
            .collect();
        let struct_literal = format!("{} {{ {} }}", struct_name, field_values.join(", "));

        let shown_var = scope.fresh_name();
        scope.add_local(
            shown_var.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let total_var = scope.fresh_name();
        scope.add_local(
            total_var.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        let indent = emit.indent_str();
        let code = format!(
            "let {inst} = {lit}\n\
             {indent}let {shown} = {da}({inst})\n\
             {indent}let {total} = {db}({inst})",
            inst = inst_var,
            lit = struct_literal,
            shown = shown_var,
            da = dispatch_a_name,
            total = total_var,
            db = dispatch_b_name,
            indent = indent,
        );

        Some(code)
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

    fn make_table_with_module() -> SymbolTable {
        let mut table = SymbolTable::new();
        let _mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        table
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(MultiInterfaceExtend.name(), "multi_interface_extend");
    }

    #[test]
    fn precondition_rejects_class_methods() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        // No module => precondition fails
        assert!(!MultiInterfaceExtend.precondition(&scope, &params));
        // With module_id
        scope.module_id = Some(ModuleId(0));
        assert!(MultiInterfaceExtend.precondition(&scope, &params));
        // Inside a class method => precondition fails
        scope.current_class_sym_id = Some((ModuleId(0), SymbolId(0)));
        assert!(!MultiInterfaceExtend.precondition(&scope, &params));
    }

    #[test]
    fn returns_none_without_module() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = MultiInterfaceExtend.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn generates_seven_module_decls() {
        let table = make_table_with_module();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let text = MultiInterfaceExtend
            .generate(&mut scope, &mut emit, &params)
            .expect("should generate code");

        // 7 module decls: struct, 2 interfaces, 2 extend blocks, 2 dispatchers
        assert_eq!(
            scope.module_decls.len(),
            7,
            "expected 7 module_decls, got {}:\n{:#?}",
            scope.module_decls.len(),
            scope.module_decls,
        );

        // Decl 0: struct
        assert!(
            scope.module_decls[0].contains("struct"),
            "expected struct decl: {}",
            scope.module_decls[0]
        );
        assert!(
            scope.module_decls[0].contains("i64"),
            "expected i64 fields: {}",
            scope.module_decls[0]
        );

        // Decl 1: interface A
        assert!(
            scope.module_decls[1].contains("interface"),
            "expected interface A decl: {}",
            scope.module_decls[1]
        );
        assert!(
            scope.module_decls[1].contains("-> string"),
            "expected string return in interface A: {}",
            scope.module_decls[1]
        );

        // Decl 2: interface B
        assert!(
            scope.module_decls[2].contains("interface"),
            "expected interface B decl: {}",
            scope.module_decls[2]
        );
        assert!(
            scope.module_decls[2].contains("-> i64"),
            "expected i64 return in interface B: {}",
            scope.module_decls[2]
        );

        // Decl 3: extend with interface A
        assert!(
            scope.module_decls[3].contains("extend") && scope.module_decls[3].contains("with"),
            "expected extend-with decl A: {}",
            scope.module_decls[3]
        );
        assert!(
            scope.module_decls[3].contains("-> string"),
            "expected string return in extend A: {}",
            scope.module_decls[3]
        );

        // Decl 4: extend with interface B
        assert!(
            scope.module_decls[4].contains("extend") && scope.module_decls[4].contains("with"),
            "expected extend-with decl B: {}",
            scope.module_decls[4]
        );
        assert!(
            scope.module_decls[4].contains("-> i64"),
            "expected i64 return in extend B: {}",
            scope.module_decls[4]
        );

        // Decl 5: dispatcher function A
        assert!(
            scope.module_decls[5].contains("func") && scope.module_decls[5].contains("-> string"),
            "expected dispatcher A: {}",
            scope.module_decls[5]
        );

        // Decl 6: dispatcher function B
        assert!(
            scope.module_decls[6].contains("func") && scope.module_decls[6].contains("-> i64"),
            "expected dispatcher B: {}",
            scope.module_decls[6]
        );

        // Inline code should instantiate and call both dispatchers
        assert!(
            text.contains("let "),
            "expected let bindings in code: {text}"
        );
    }

    #[test]
    fn extend_blocks_have_implicit_self() {
        let table = make_table_with_module();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(99);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        MultiInterfaceExtend
            .generate(&mut scope, &mut emit, &params)
            .expect("should generate code");

        // Both extend blocks (decls 3 and 4) should NOT have explicit self parameter
        let extend_a = &scope.module_decls[3];
        assert!(
            !extend_a.contains("(self:"),
            "expected implicit self (no self param) in extend A: {extend_a}"
        );

        let extend_b = &scope.module_decls[4];
        assert!(
            !extend_b.contains("(self:"),
            "expected implicit self (no self param) in extend B: {extend_b}"
        );
    }

    #[test]
    fn interfaces_have_implicit_self() {
        let table = make_table_with_module();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(77);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        MultiInterfaceExtend
            .generate(&mut scope, &mut emit, &params)
            .expect("should generate code");

        // Interface declarations (decls 1 and 2) should NOT have self parameter
        let iface_a = &scope.module_decls[1];
        assert!(
            !iface_a.contains("self"),
            "interface A should have implicit self (no self param): {iface_a}"
        );

        let iface_b = &scope.module_decls[2];
        assert!(
            !iface_b.contains("self"),
            "interface B should have implicit self (no self param): {iface_b}"
        );
    }

    #[test]
    fn adds_two_locals() {
        let table = make_table_with_module();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(55);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        MultiInterfaceExtend
            .generate(&mut scope, &mut emit, &params)
            .expect("should generate code");

        // Should add two result locals: one string, one i64
        assert!(
            scope.locals.len() >= 2,
            "expected at least 2 locals, got {}",
            scope.locals.len()
        );

        let types: Vec<&TypeInfo> = scope.locals.iter().map(|(_, ty, _)| ty).collect();
        assert!(
            types.contains(&&TypeInfo::Primitive(PrimitiveType::String)),
            "expected a string local"
        );
        assert!(
            types.contains(&&TypeInfo::Primitive(PrimitiveType::I64)),
            "expected an i64 local"
        );
    }

    #[test]
    fn dispatchers_use_interface_typed_params() {
        let table = make_table_with_module();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(33);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        MultiInterfaceExtend
            .generate(&mut scope, &mut emit, &params)
            .expect("should generate code");

        // Dispatcher A (decl 5) should reference interface A name in its parameter
        let dispatcher_a = &scope.module_decls[5];
        // The interface name from decl 1 should appear in dispatcher A's param type
        let iface_a_name = scope.module_decls[1]
            .split_whitespace()
            .nth(1)
            .expect("interface name");
        assert!(
            dispatcher_a.contains(iface_a_name),
            "dispatcher A should reference interface A name '{}': {}",
            iface_a_name,
            dispatcher_a
        );

        // Dispatcher B (decl 6) should reference interface B name in its parameter
        let dispatcher_b = &scope.module_decls[6];
        let iface_b_name = scope.module_decls[2]
            .split_whitespace()
            .nth(1)
            .expect("interface name");
        assert!(
            dispatcher_b.contains(iface_b_name),
            "dispatcher B should reference interface B name '{}': {}",
            iface_b_name,
            dispatcher_b
        );
    }

    #[test]
    fn deterministic_across_seeds() {
        let table = make_table_with_module();
        for seed in 0..20 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            let text = MultiInterfaceExtend
                .generate(&mut scope, &mut emit, &params)
                .expect("should generate code");

            // Every seed should produce 7 module decls
            assert_eq!(
                scope.module_decls.len(),
                7,
                "seed {seed}: expected 7 module_decls, got {}",
                scope.module_decls.len()
            );

            // Inline code should reference the struct name from decl 0
            let struct_name = scope.module_decls[0]
                .split_whitespace()
                .nth(1)
                .expect("struct name");
            assert!(
                text.contains(struct_name),
                "seed {seed}: expected struct name '{struct_name}' in code: {text}"
            );
        }
    }
}
