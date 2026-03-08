//! Rule: classes with multiple extend blocks implementing different interfaces.
//!
//! Exercises vtable generation, interface dispatch, and method resolution by
//! generating a class that implements two different interfaces via separate
//! `extend ClassName with InterfaceName` blocks, along with dispatcher
//! functions that accept the interface type and call its method.
//!
//! **Variant 0 -- sum + label:**
//! ```vole
//! interface Labelable_12345 {
//!     func label() -> string
//! }
//!
//! interface Totalable_12345 {
//!     func total() -> i64
//! }
//!
//! class Box_12345 {
//!     width: i64
//!     height: i64
//!     depth: i64
//! }
//!
//! extend Box_12345 with Labelable_12345 {
//!     func label(self: Box_12345) -> string {
//!         return "{self.width}x{self.height}x{self.depth}"
//!     }
//! }
//!
//! extend Box_12345 with Totalable_12345 {
//!     func total(self: Box_12345) -> i64 {
//!         return self.width + self.height + self.depth
//!     }
//! }
//!
//! func get_label_12345(obj: Labelable_12345) -> string {
//!     return obj.label()
//! }
//!
//! func get_total_12345(obj: Totalable_12345) -> i64 {
//!     return obj.total()
//! }
//!
//! let inst = Box_12345 { width: 3, height: 4, depth: 5 }
//! assert(get_label_12345(inst) == "3x4x5")
//! assert(get_total_12345(inst) == 12)
//! ```
//!
//! **Variant 1 -- product + describe:**
//! ```vole
//! interface Describable_12345 {
//!     func describe() -> string
//! }
//!
//! interface Productable_12345 {
//!     func product() -> i64
//! }
//!
//! class Pair_12345 {
//!     a: i64
//!     b: i64
//! }
//!
//! extend Pair_12345 with Describable_12345 {
//!     func describe(self: Pair_12345) -> string {
//!         return "pair(" + self.a.to_string() + "," + self.b.to_string() + ")"
//!     }
//! }
//!
//! extend Pair_12345 with Productable_12345 {
//!     func product(self: Pair_12345) -> i64 {
//!         return self.a * self.b
//!     }
//! }
//!
//! func describe_it_12345(d: Describable_12345) -> string {
//!     return d.describe()
//! }
//!
//! func product_it_12345(p: Productable_12345) -> i64 {
//!     return p.product()
//! }
//!
//! let inst = Pair_12345 { a: 6, b: 7 }
//! assert(describe_it_12345(inst) == "pair(6,7)")
//! assert(product_it_12345(inst) == 42)
//! ```
//!
//! **Variant 2 -- max + format:**
//! ```vole
//! interface Formattable_12345 {
//!     func format() -> string
//! }
//!
//! interface Maxable_12345 {
//!     func max_val() -> i64
//! }
//!
//! class Triple_12345 {
//!     p: i64
//!     q: i64
//!     r: i64
//! }
//!
//! extend Triple_12345 with Formattable_12345 {
//!     func format(self: Triple_12345) -> string {
//!         return "{self.p}/{self.q}/{self.r}"
//!     }
//! }
//!
//! extend Triple_12345 with Maxable_12345 {
//!     func max_val(self: Triple_12345) -> i64 {
//!         let result = self.p
//!         if self.q > result {
//!             result = self.q
//!         }
//!         if self.r > result {
//!             result = self.r
//!         }
//!         return result
//!     }
//! }
//!
//! func format_it_12345(f: Formattable_12345) -> string {
//!     return f.format()
//! }
//!
//! func max_it_12345(m: Maxable_12345) -> i64 {
//!     return m.max_val()
//! }
//!
//! let inst = Triple_12345 { p: 10, q: 30, r: 20 }
//! assert(format_it_12345(inst) == "10/30/20")
//! assert(max_it_12345(inst) == 30)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;

pub struct MultiExtendInterface;

impl StmtRule for MultiExtendInterface {
    fn name(&self) -> &'static str {
        "multi_extend_interface"
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
            0 => emit_sum_label_variant(scope, emit),
            1 => emit_product_describe_variant(scope, emit),
            _ => emit_max_format_variant(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0 -- sum + label (3 i64 fields, addition-based total)
// ---------------------------------------------------------------------------

fn emit_sum_label_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);

    // Pick names
    let class_prefixes = ["Box", "Dims", "Volume", "Bounds"];
    let class_prefix = class_prefixes[emit.gen_range(0..class_prefixes.len())];
    let class_name = format!("{}_{}", class_prefix, uid);

    let iface_a_prefixes = ["Labelable", "Taggable", "Nameable"];
    let iface_a_prefix = iface_a_prefixes[emit.gen_range(0..iface_a_prefixes.len())];
    let iface_a_name = format!("{}_{}", iface_a_prefix, uid);

    let method_a_names = ["label", "tag", "name_it"];
    let method_a = method_a_names[emit.gen_range(0..method_a_names.len())];

    let iface_b_prefixes = ["Totalable", "Summable", "Addable"];
    let iface_b_prefix = iface_b_prefixes[emit.gen_range(0..iface_b_prefixes.len())];
    let iface_b_name = format!("{}_{}", iface_b_prefix, uid);

    let method_b_names = ["total", "sum_all", "add_up"];
    let method_b = method_b_names[emit.gen_range(0..method_b_names.len())];

    let dispatch_a_prefixes = ["get_label", "fetch_tag", "read_name"];
    let dispatch_a_name = format!(
        "{}_{}",
        dispatch_a_prefixes[emit.gen_range(0..dispatch_a_prefixes.len())],
        uid,
    );

    let dispatch_b_prefixes = ["get_total", "fetch_sum", "read_total"];
    let dispatch_b_name = format!(
        "{}_{}",
        dispatch_b_prefixes[emit.gen_range(0..dispatch_b_prefixes.len())],
        uid,
    );

    // Pick 3 field names
    let field_sets: &[&[&str]] = &[
        &["width", "height", "depth"],
        &["x", "y", "z"],
        &["lo", "mid", "hi"],
    ];
    let fields = field_sets[emit.gen_range(0..field_sets.len())];

    // Pick field values
    let f0_val = emit.gen_i64_range(1, 30);
    let f1_val = emit.gen_i64_range(1, 30);
    let f2_val = emit.gen_i64_range(1, 30);
    let expected_total = f0_val + f1_val + f2_val;

    // Expected label string: "{f0_val}x{f1_val}x{f2_val}" or similar
    let sep_chars = ["x", "-", "/"];
    let sep = sep_chars[emit.gen_range(0..sep_chars.len())];
    let expected_label = format!("{}{}{}{}{}", f0_val, sep, f1_val, sep, f2_val);

    // --- Module decl 1: interface A (string-returning) ---
    let iface_a_decl = format!(
        "interface {} {{\n    func {}() -> string\n}}",
        iface_a_name, method_a,
    );
    scope.add_module_decl(iface_a_decl);

    // --- Module decl 2: interface B (i64-returning) ---
    let iface_b_decl = format!(
        "interface {} {{\n    func {}() -> i64\n}}",
        iface_b_name, method_b,
    );
    scope.add_module_decl(iface_b_decl);

    // --- Module decl 3: class ---
    let class_decl = format!(
        "class {} {{\n    {}: i64\n    {}: i64\n    {}: i64\n}}",
        class_name, fields[0], fields[1], fields[2],
    );
    scope.add_module_decl(class_decl);

    // --- Module decl 4: extend with interface A (string method) ---
    let label_parts: Vec<String> = fields.iter().map(|f| format!("{{self.{f}}}")).collect();
    let label_body = format!("return \"{}\"", label_parts.join(sep));

    let extend_a_decl = format!(
        "extend {} with {} {{\n    func {}(self: {}) -> string {{\n        {}\n    }}\n}}",
        class_name, iface_a_name, method_a, class_name, label_body,
    );
    scope.add_module_decl(extend_a_decl);

    // --- Module decl 5: extend with interface B (i64 method) ---
    let sum_expr: Vec<String> = fields.iter().map(|f| format!("self.{f}")).collect();
    let i64_body = format!("return {}", sum_expr.join(" + "));

    let extend_b_decl = format!(
        "extend {} with {} {{\n    func {}(self: {}) -> i64 {{\n        {}\n    }}\n}}",
        class_name, iface_b_name, method_b, class_name, i64_body,
    );
    scope.add_module_decl(extend_b_decl);

    // --- Module decl 6: dispatcher function A ---
    let dispatch_a_decl = format!(
        "func {}(obj: {}) -> string {{\n    return obj.{}()\n}}",
        dispatch_a_name, iface_a_name, method_a,
    );
    scope.add_module_decl(dispatch_a_decl);

    // --- Module decl 7: dispatcher function B ---
    let dispatch_b_decl = format!(
        "func {}(obj: {}) -> i64 {{\n    return obj.{}()\n}}",
        dispatch_b_name, iface_b_name, method_b,
    );
    scope.add_module_decl(dispatch_b_decl);

    // --- Inline code: instantiate, dispatch, assert ---
    let inst_var = scope.fresh_name();
    let field_values = format!(
        "{}: {}, {}: {}, {}: {}",
        fields[0], f0_val, fields[1], f1_val, fields[2], f2_val,
    );
    let indent = emit.indent_str();

    Some(format!(
        "let {inst} = {cls} {{ {fvals} }}\n\
         {indent}assert({da}({inst}) == \"{expected_label}\")\n\
         {indent}assert({db}({inst}) == {expected_total})",
        inst = inst_var,
        cls = class_name,
        fvals = field_values,
        da = dispatch_a_name,
        expected_label = expected_label,
        db = dispatch_b_name,
        expected_total = expected_total,
        indent = indent,
    ))
}

// ---------------------------------------------------------------------------
// Variant 1 -- product + describe (2 i64 fields, multiplication-based product)
// ---------------------------------------------------------------------------

fn emit_product_describe_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);

    // Pick names
    let class_prefixes = ["Pair", "Duo", "Coord", "Cell"];
    let class_prefix = class_prefixes[emit.gen_range(0..class_prefixes.len())];
    let class_name = format!("{}_{}", class_prefix, uid);

    let iface_a_name = format!("Describable_{}", uid);
    let method_a = "describe";

    let iface_b_prefixes = ["Productable", "Multipliable", "Combinable"];
    let iface_b_prefix = iface_b_prefixes[emit.gen_range(0..iface_b_prefixes.len())];
    let iface_b_name = format!("{}_{}", iface_b_prefix, uid);

    let method_b_names = ["product", "multiply", "combine"];
    let method_b = method_b_names[emit.gen_range(0..method_b_names.len())];

    let dispatch_a_name = format!("describe_it_{}", uid);
    let dispatch_b_name = format!("product_it_{}", uid);

    // Pick 2 field names
    let field_sets: &[&[&str]] = &[&["a", "b"], &["left", "right"], &["first", "second"]];
    let fields = field_sets[emit.gen_range(0..field_sets.len())];

    // Pick field values
    let f0_val = emit.gen_i64_range(2, 20);
    let f1_val = emit.gen_i64_range(2, 20);
    let expected_product = f0_val * f1_val;

    // Build expected describe string: "pair(6,7)" style
    let desc_prefix_names = ["pair", "duo", "coord", "cell"];
    let desc_prefix = desc_prefix_names[emit.gen_range(0..desc_prefix_names.len())];
    let expected_describe = format!("{}({},{})", desc_prefix, f0_val, f1_val);

    // --- Module decl 1: interface A (string-returning) ---
    let iface_a_decl = format!(
        "interface {} {{\n    func {}() -> string\n}}",
        iface_a_name, method_a,
    );
    scope.add_module_decl(iface_a_decl);

    // --- Module decl 2: interface B (i64-returning) ---
    let iface_b_decl = format!(
        "interface {} {{\n    func {}() -> i64\n}}",
        iface_b_name, method_b,
    );
    scope.add_module_decl(iface_b_decl);

    // --- Module decl 3: class ---
    let class_decl = format!(
        "class {} {{\n    {}: i64\n    {}: i64\n}}",
        class_name, fields[0], fields[1],
    );
    scope.add_module_decl(class_decl);

    // --- Module decl 4: extend with interface A (describe method) ---
    let describe_body = format!(
        "return \"{prefix}(\" + self.{f0}.to_string() + \",\" + self.{f1}.to_string() + \")\"",
        prefix = desc_prefix,
        f0 = fields[0],
        f1 = fields[1],
    );
    let extend_a_decl = format!(
        "extend {} with {} {{\n    func {}(self: {}) -> string {{\n        {}\n    }}\n}}",
        class_name, iface_a_name, method_a, class_name, describe_body,
    );
    scope.add_module_decl(extend_a_decl);

    // --- Module decl 5: extend with interface B (product method) ---
    let product_body = format!("return self.{} * self.{}", fields[0], fields[1]);
    let extend_b_decl = format!(
        "extend {} with {} {{\n    func {}(self: {}) -> i64 {{\n        {}\n    }}\n}}",
        class_name, iface_b_name, method_b, class_name, product_body,
    );
    scope.add_module_decl(extend_b_decl);

    // --- Module decl 6: dispatcher function A ---
    let dispatch_a_decl = format!(
        "func {}(d: {}) -> string {{\n    return d.{}()\n}}",
        dispatch_a_name, iface_a_name, method_a,
    );
    scope.add_module_decl(dispatch_a_decl);

    // --- Module decl 7: dispatcher function B ---
    let dispatch_b_decl = format!(
        "func {}(p: {}) -> i64 {{\n    return p.{}()\n}}",
        dispatch_b_name, iface_b_name, method_b,
    );
    scope.add_module_decl(dispatch_b_decl);

    // --- Inline code: instantiate, dispatch, assert ---
    let inst_var = scope.fresh_name();
    let field_values = format!("{}: {}, {}: {}", fields[0], f0_val, fields[1], f1_val,);
    let indent = emit.indent_str();

    Some(format!(
        "let {inst} = {cls} {{ {fvals} }}\n\
         {indent}assert({da}({inst}) == \"{expected_describe}\")\n\
         {indent}assert({db}({inst}) == {expected_product})",
        inst = inst_var,
        cls = class_name,
        fvals = field_values,
        da = dispatch_a_name,
        expected_describe = expected_describe,
        db = dispatch_b_name,
        expected_product = expected_product,
        indent = indent,
    ))
}

// ---------------------------------------------------------------------------
// Variant 2 -- max + format (3 i64 fields, max-based computation)
// ---------------------------------------------------------------------------

fn emit_max_format_variant(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);

    // Pick names
    let class_prefixes = ["Triple", "Trio", "Triad", "Triplet"];
    let class_prefix = class_prefixes[emit.gen_range(0..class_prefixes.len())];
    let class_name = format!("{}_{}", class_prefix, uid);

    let iface_a_prefixes = ["Formattable", "Renderable", "Stringable"];
    let iface_a_prefix = iface_a_prefixes[emit.gen_range(0..iface_a_prefixes.len())];
    let iface_a_name = format!("{}_{}", iface_a_prefix, uid);

    let method_a_names = ["fmt", "render", "stringify"];
    let method_a = method_a_names[emit.gen_range(0..method_a_names.len())];

    let iface_b_name = format!("Maxable_{}", uid);
    let method_b = "max_val";

    let dispatch_a_name = format!("format_it_{}", uid);
    let dispatch_b_name = format!("max_it_{}", uid);

    // Pick 3 field names
    let field_sets: &[&[&str]] = &[&["p", "q", "r"], &["u", "v", "w"], &["m", "n", "o"]];
    let fields = field_sets[emit.gen_range(0..field_sets.len())];

    // Pick field values -- make sure they are distinct so max is unambiguous
    let mut vals = [
        emit.gen_i64_range(1, 30),
        emit.gen_i64_range(1, 30),
        emit.gen_i64_range(1, 30),
    ];
    // Ensure distinct values
    vals[1] = vals[0] + emit.gen_i64_range(1, 10);
    vals[2] = vals[1] + emit.gen_i64_range(1, 10);
    // Shuffle via a simple swap based on rng
    let swap_variant = emit.gen_range(0..6);
    match swap_variant {
        1 => vals.swap(0, 1),
        2 => vals.swap(0, 2),
        3 => vals.swap(1, 2),
        4 => {
            vals.swap(0, 1);
            vals.swap(1, 2);
        }
        5 => {
            vals.swap(0, 2);
            vals.swap(1, 2);
        }
        _ => {} // keep original order
    }

    let expected_max = *vals.iter().max().unwrap();

    // Build expected format string: "p/q/r" style
    let sep_chars = ["/", "-", ":"];
    let sep = sep_chars[emit.gen_range(0..sep_chars.len())];
    let expected_format = format!("{}{}{}{}{}", vals[0], sep, vals[1], sep, vals[2]);

    // --- Module decl 1: interface A (string-returning) ---
    let iface_a_decl = format!(
        "interface {} {{\n    func {}() -> string\n}}",
        iface_a_name, method_a,
    );
    scope.add_module_decl(iface_a_decl);

    // --- Module decl 2: interface B (i64-returning) ---
    let iface_b_decl = format!(
        "interface {} {{\n    func {}() -> i64\n}}",
        iface_b_name, method_b,
    );
    scope.add_module_decl(iface_b_decl);

    // --- Module decl 3: class ---
    let class_decl = format!(
        "class {} {{\n    {}: i64\n    {}: i64\n    {}: i64\n}}",
        class_name, fields[0], fields[1], fields[2],
    );
    scope.add_module_decl(class_decl);

    // --- Module decl 4: extend with interface A (format method) ---
    let format_parts: Vec<String> = fields.iter().map(|f| format!("{{self.{f}}}")).collect();
    let format_body = format!("return \"{}\"", format_parts.join(sep));

    let extend_a_decl = format!(
        "extend {} with {} {{\n    func {}(self: {}) -> string {{\n        {}\n    }}\n}}",
        class_name, iface_a_name, method_a, class_name, format_body,
    );
    scope.add_module_decl(extend_a_decl);

    // --- Module decl 5: extend with interface B (max_val method) ---
    // Use a simple if-chain to find the max of 3 values
    let max_body = format!(
        "let result = self.{f0}\n\
         \x20       if self.{f1} > result {{\n\
         \x20           result = self.{f1}\n\
         \x20       }}\n\
         \x20       if self.{f2} > result {{\n\
         \x20           result = self.{f2}\n\
         \x20       }}\n\
         \x20       return result",
        f0 = fields[0],
        f1 = fields[1],
        f2 = fields[2],
    );
    let extend_b_decl = format!(
        "extend {} with {} {{\n    func {}(self: {}) -> i64 {{\n        {}\n    }}\n}}",
        class_name, iface_b_name, method_b, class_name, max_body,
    );
    scope.add_module_decl(extend_b_decl);

    // --- Module decl 6: dispatcher function A ---
    let dispatch_a_decl = format!(
        "func {}(f: {}) -> string {{\n    return f.{}()\n}}",
        dispatch_a_name, iface_a_name, method_a,
    );
    scope.add_module_decl(dispatch_a_decl);

    // --- Module decl 7: dispatcher function B ---
    let dispatch_b_decl = format!(
        "func {}(m: {}) -> i64 {{\n    return m.{}()\n}}",
        dispatch_b_name, iface_b_name, method_b,
    );
    scope.add_module_decl(dispatch_b_decl);

    // --- Inline code: instantiate, dispatch, assert ---
    let inst_var = scope.fresh_name();
    let field_values = format!(
        "{}: {}, {}: {}, {}: {}",
        fields[0], vals[0], fields[1], vals[1], fields[2], vals[2],
    );
    let indent = emit.indent_str();

    Some(format!(
        "let {inst} = {cls} {{ {fvals} }}\n\
         {indent}assert({da}({inst}) == \"{expected_format}\")\n\
         {indent}assert({db}({inst}) == {expected_max})",
        inst = inst_var,
        cls = class_name,
        fvals = field_values,
        da = dispatch_a_name,
        expected_format = expected_format,
        db = dispatch_b_name,
        expected_max = expected_max,
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
        assert_eq!(MultiExtendInterface.name(), "multi_extend_interface");
    }

    #[test]
    fn precondition_requires_module_and_no_class() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = test_params();

        // No module => precondition fails
        assert!(!MultiExtendInterface.precondition(&scope, &params));

        // With module_id
        scope.module_id = Some(ModuleId(0));
        assert!(MultiExtendInterface.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id = Some((ModuleId(0), SymbolId(0)));
        assert!(!MultiExtendInterface.precondition(&scope, &params));
    }

    #[test]
    fn returns_none_without_module() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = test_params();

        let result = MultiExtendInterface.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn generates_seven_module_decls() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let text = MultiExtendInterface
            .generate(&mut scope, &mut emit, &test_params())
            .expect("should generate code");

        // 7 module decls: 2 interfaces, class, 2 extend blocks, 2 dispatchers
        assert_eq!(
            scope.module_decls.len(),
            7,
            "expected 7 module_decls, got {}:\n{:#?}",
            scope.module_decls.len(),
            scope.module_decls,
        );

        // Decl 0: interface A
        assert!(
            scope.module_decls[0].contains("interface"),
            "expected interface A decl: {}",
            scope.module_decls[0],
        );
        assert!(
            scope.module_decls[0].contains("-> string"),
            "expected string return in interface A: {}",
            scope.module_decls[0],
        );

        // Decl 1: interface B
        assert!(
            scope.module_decls[1].contains("interface"),
            "expected interface B decl: {}",
            scope.module_decls[1],
        );
        assert!(
            scope.module_decls[1].contains("-> i64"),
            "expected i64 return in interface B: {}",
            scope.module_decls[1],
        );

        // Decl 2: class
        assert!(
            scope.module_decls[2].contains("class"),
            "expected class decl: {}",
            scope.module_decls[2],
        );

        // Decl 3: extend with interface A
        assert!(
            scope.module_decls[3].contains("extend") && scope.module_decls[3].contains("with"),
            "expected extend-with decl A: {}",
            scope.module_decls[3],
        );
        assert!(
            scope.module_decls[3].contains("-> string"),
            "expected string return in extend A: {}",
            scope.module_decls[3],
        );

        // Decl 4: extend with interface B
        assert!(
            scope.module_decls[4].contains("extend") && scope.module_decls[4].contains("with"),
            "expected extend-with decl B: {}",
            scope.module_decls[4],
        );
        assert!(
            scope.module_decls[4].contains("-> i64"),
            "expected i64 return in extend B: {}",
            scope.module_decls[4],
        );

        // Decl 5: dispatcher function A
        assert!(
            scope.module_decls[5].contains("func") && scope.module_decls[5].contains("-> string"),
            "expected dispatcher A: {}",
            scope.module_decls[5],
        );

        // Decl 6: dispatcher function B
        assert!(
            scope.module_decls[6].contains("func") && scope.module_decls[6].contains("-> i64"),
            "expected dispatcher B: {}",
            scope.module_decls[6],
        );

        // Inline code should have asserts
        assert!(text.contains("assert("), "expected assert in code: {text}",);
    }

    #[test]
    fn extend_blocks_have_explicit_self() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(99);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        MultiExtendInterface
            .generate(&mut scope, &mut emit, &test_params())
            .expect("should generate code");

        // Both extend blocks (decls 3 and 4) should have explicit self parameter
        let extend_a = &scope.module_decls[3];
        assert!(
            extend_a.contains("(self:"),
            "expected explicit self param in extend A: {extend_a}",
        );

        let extend_b = &scope.module_decls[4];
        assert!(
            extend_b.contains("(self:"),
            "expected explicit self param in extend B: {extend_b}",
        );
    }

    #[test]
    fn interfaces_have_implicit_self() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(77);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        MultiExtendInterface
            .generate(&mut scope, &mut emit, &test_params())
            .expect("should generate code");

        // Interface declarations (decls 0 and 1) should NOT have self parameter
        let iface_a = &scope.module_decls[0];
        assert!(
            !iface_a.contains("self"),
            "interface A should have implicit self (no self param): {iface_a}",
        );

        let iface_b = &scope.module_decls[1];
        assert!(
            !iface_b.contains("self"),
            "interface B should have implicit self (no self param): {iface_b}",
        );
    }

    #[test]
    fn does_not_add_locals_to_scope() {
        // Interface types are complex -- do not add result variables to scope.
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = MultiExtendInterface.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        assert!(
            scope.locals.is_empty(),
            "should not add locals to scope for interface-typed values",
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

            MultiExtendInterface
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            // Decl 2 should be a class, not a struct
            assert!(
                scope.module_decls[2].starts_with("class"),
                "seed {seed}: expected class decl, got: {}",
                scope.module_decls[2],
            );
        }
    }

    #[test]
    fn dispatchers_use_interface_typed_params() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(33);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        MultiExtendInterface
            .generate(&mut scope, &mut emit, &test_params())
            .expect("should generate code");

        // Dispatcher A (decl 5) should reference interface A name from decl 0
        let dispatcher_a = &scope.module_decls[5];
        let iface_a_name = scope.module_decls[0]
            .split_whitespace()
            .nth(1)
            .expect("interface name");
        assert!(
            dispatcher_a.contains(iface_a_name),
            "dispatcher A should reference interface A name '{}': {}",
            iface_a_name,
            dispatcher_a,
        );

        // Dispatcher B (decl 6) should reference interface B name from decl 1
        let dispatcher_b = &scope.module_decls[6];
        let iface_b_name = scope.module_decls[1]
            .split_whitespace()
            .nth(1)
            .expect("interface name");
        assert!(
            dispatcher_b.contains(iface_b_name),
            "dispatcher B should reference interface B name '{}': {}",
            iface_b_name,
            dispatcher_b,
        );
    }

    #[test]
    fn generates_all_three_variants() {
        let table = SymbolTable::new();
        let mut found_sum = false;
        let mut found_product = false;
        let mut found_max = false;

        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let text = MultiExtendInterface
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            // Variant 0 uses 3 fields and sum (addition-based total)
            let class_decl = &scope.module_decls[2];
            let extend_b = &scope.module_decls[4];
            if extend_b.contains(" + self.") {
                found_sum = true;
            }
            // Variant 1 uses 2 fields and product (multiplication-based)
            if extend_b.contains(" * self.") {
                found_product = true;
            }
            // Variant 2 uses max logic with if statements
            if extend_b.contains("let result =") && extend_b.contains("> result") {
                found_max = true;
            }

            // All variants should have asserts
            assert!(
                text.contains("assert("),
                "seed {seed}: expected asserts in code: {text}",
            );

            // All class decls should use "class" keyword
            assert!(
                class_decl.starts_with("class"),
                "seed {seed}: expected class keyword: {}",
                class_decl,
            );

            if found_sum && found_product && found_max {
                break;
            }
        }

        assert!(found_sum, "never generated sum variant in 200 seeds");
        assert!(
            found_product,
            "never generated product variant in 200 seeds"
        );
        assert!(found_max, "never generated max variant in 200 seeds");
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

            let text = MultiExtendInterface
                .generate(&mut scope, &mut emit, &test_params())
                .expect("should generate code");

            // Every seed should produce 7 module decls
            assert_eq!(
                scope.module_decls.len(),
                7,
                "seed {seed}: expected 7 module_decls, got {}",
                scope.module_decls.len(),
            );

            // Inline code should reference the class name from decl 2
            let class_name = scope.module_decls[2]
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
