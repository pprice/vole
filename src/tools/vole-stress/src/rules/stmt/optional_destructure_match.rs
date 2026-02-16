//! Rule: optional destructure match let-binding.
//!
//! Finds a non-generic class or struct with at least one primitive field,
//! creates an optional variable, and generates a match expression with
//! destructuring:
//! ```vole
//! let varN: ClassName? = ClassName { field1: val1, field2: val2 }
//! let resultN = match varN {
//!     ClassName { field1: a, field2: b } => a + b
//!     nil => 0_i64
//! }
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{FieldInfo, PrimitiveType, SymbolKind, TypeInfo};

pub struct OptionalDestructureMatch;

impl StmtRule for OptionalDestructureMatch {
    fn name(&self) -> &'static str {
        "optional_destructure_match"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.04)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let module_id = scope.module_id?;
        let module = scope.table.get_module(module_id)?;

        let candidates = collect_candidates(module, module_id);
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let candidate = &candidates[idx];
        let sym_id = candidate.sym_id;
        let type_name = candidate.type_name.clone();
        let fields = candidate.fields.clone();
        let is_class = candidate.is_class;

        // Determine the optional type
        let base_type = if is_class {
            TypeInfo::Class(module_id, sym_id)
        } else {
            TypeInfo::Struct(module_id, sym_id)
        };
        let optional_type = TypeInfo::Optional(Box::new(base_type));

        let opt_var_name = scope.fresh_name();

        // 50% assign nil, 50% assign constructed instance
        let init_value = if emit.gen_bool(0.5) {
            "nil".to_string()
        } else {
            let field_values: Vec<String> = fields
                .iter()
                .map(|f| {
                    let value = emit.literal(&f.field_type);
                    format!("{}: {}", f.name, value)
                })
                .collect();
            format!("{} {{ {} }}", type_name, field_values.join(", "))
        };

        let let_stmt = format!("let {}: {}? = {}", opt_var_name, type_name, init_value);
        scope.add_local(opt_var_name.clone(), optional_type, false);

        // Collect primitive fields for the destructure arm body
        let primitive_fields: Vec<&FieldInfo> = fields
            .iter()
            .filter(|f| f.field_type.is_primitive())
            .collect();
        if primitive_fields.is_empty() {
            return None;
        }

        // Build destructure bindings
        let bindings = build_bindings(scope, &fields);

        // Build the arm body expression (result type is i64)
        let arm_body = build_arm_body(emit, &bindings);

        // Generate the nil arm default value
        let nil_values = ["-1_i64", "0_i64", "42_i64"];
        let nil_value = nil_values[emit.gen_range(0..nil_values.len())];

        let result_name = scope.fresh_name();
        let indent = emit.indented(|e| e.indent_str());
        let close_indent = emit.indent_str();

        let pattern_parts: Vec<String> = bindings
            .iter()
            .map(|b| format!("{}: {}", b.field_name, b.binding_name))
            .collect();

        let match_stmt = format!(
            "let {} = match {} {{\n{}{} {{ {} }} => {}\n{}nil => {}\n{}}}",
            result_name,
            opt_var_name,
            indent,
            type_name,
            pattern_parts.join(", "),
            arm_body,
            indent,
            nil_value,
            close_indent,
        );

        scope.add_local(result_name, TypeInfo::Primitive(PrimitiveType::I64), false);

        Some(format!("{}\n{}", let_stmt, match_stmt))
    }
}

struct Candidate {
    sym_id: crate::symbols::SymbolId,
    type_name: String,
    fields: Vec<FieldInfo>,
    is_class: bool,
}

fn collect_candidates(
    module: &crate::symbols::ModuleSymbols,
    _module_id: crate::symbols::ModuleId,
) -> Vec<Candidate> {
    let mut all = Vec::new();

    // Non-generic classes with at least one primitive field
    for sym in module.classes() {
        if let SymbolKind::Class(ref info) = sym.kind
            && info.type_params.is_empty()
            && info.fields.iter().any(|f| f.field_type.is_primitive())
        {
            all.push(Candidate {
                sym_id: sym.id,
                type_name: sym.name.clone(),
                fields: info.fields.clone(),
                is_class: true,
            });
        }
    }

    // Structs with at least one primitive field
    for sym in module.structs() {
        if let SymbolKind::Struct(ref info) = sym.kind
            && info.fields.iter().any(|f| f.field_type.is_primitive())
        {
            all.push(Candidate {
                sym_id: sym.id,
                type_name: sym.name.clone(),
                fields: info.fields.clone(),
                is_class: false,
            });
        }
    }

    all
}

struct Binding {
    field_name: String,
    binding_name: String,
    field_type: TypeInfo,
}

fn build_bindings(scope: &mut Scope, fields: &[FieldInfo]) -> Vec<Binding> {
    fields
        .iter()
        .map(|f| {
            let binding = scope.fresh_name();
            Binding {
                field_name: f.name.clone(),
                binding_name: binding,
                field_type: f.field_type.clone(),
            }
        })
        .collect()
}

fn build_arm_body(emit: &mut Emit, bindings: &[Binding]) -> String {
    // Find i64/i32 compatible bindings for arithmetic
    let i64_compat: Vec<&Binding> = bindings
        .iter()
        .filter(|b| {
            matches!(
                b.field_type,
                TypeInfo::Primitive(PrimitiveType::I64) | TypeInfo::Primitive(PrimitiveType::I32)
            )
        })
        .collect();

    let string_bindings: Vec<&Binding> = bindings
        .iter()
        .filter(|b| matches!(b.field_type, TypeInfo::Primitive(PrimitiveType::String)))
        .collect();

    let bool_bindings: Vec<&Binding> = bindings
        .iter()
        .filter(|b| matches!(b.field_type, TypeInfo::Primitive(PrimitiveType::Bool)))
        .collect();

    if !i64_compat.is_empty() {
        let ops = [" + ", " * ", " - "];
        let op = ops[emit.gen_range(0..ops.len())];
        let parts: Vec<&str> = i64_compat
            .iter()
            .take(3)
            .map(|b| b.binding_name.as_str())
            .collect();
        let expr = parts.join(op);
        let has_i32 = i64_compat
            .iter()
            .any(|b| matches!(b.field_type, TypeInfo::Primitive(PrimitiveType::I32)));
        if has_i32 {
            format!("{} + 0_i64", expr)
        } else {
            expr
        }
    } else if !string_bindings.is_empty() {
        format!("{}.length()", string_bindings[0].binding_name)
    } else if !bool_bindings.is_empty() {
        format!(
            "when {{ {} => 1_i64, _ => 0_i64 }}",
            bool_bindings[0].binding_name
        )
    } else {
        "1_i64".to_string()
    }
}

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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(
            OptionalDestructureMatch.name(),
            "optional_destructure_match"
        );
    }

    #[test]
    fn returns_none_without_types() {
        let mut table = SymbolTable::new();
        let _mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = OptionalDestructureMatch.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
