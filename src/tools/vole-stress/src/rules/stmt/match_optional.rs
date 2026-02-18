//! Rule: optional destructure match.
//!
//! Creates an optional variable (`ClassName?` or `StructName?`), assigns
//! either a constructed instance or `nil`, then matches with destructuring:
//! ```vole
//! let varN: ClassName? = ClassName { field1: val1, field2: val2 }
//! let resultN = match varN {
//!     ClassName { field1: a, field2: b } => a + b
//!     nil => 0
//! }
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{FieldInfo, PrimitiveType, SymbolKind, TypeInfo};

pub struct MatchOptional;

impl StmtRule for MatchOptional {
    fn name(&self) -> &'static str {
        "match_optional"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.12)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let module_id = scope.module_id?;
        let module = scope.table.get_module(module_id)?;

        // Collect non-generic classes with at least one primitive field
        let mut all_candidates: Vec<CandidateType> = Vec::new();

        for sym in module.classes() {
            if let SymbolKind::Class(ref info) = sym.kind {
                if info.type_params.is_empty()
                    && info.fields.iter().any(|f| f.field_type.is_primitive())
                {
                    all_candidates.push(CandidateType {
                        sym_id: sym.id,
                        name: sym.name.clone(),
                        fields: info.fields.clone(),
                        is_class: true,
                    });
                }
            }
        }

        for sym in module.structs() {
            if let SymbolKind::Struct(ref info) = sym.kind {
                if info.fields.iter().any(|f| f.field_type.is_primitive()) {
                    all_candidates.push(CandidateType {
                        sym_id: sym.id,
                        name: sym.name.clone(),
                        fields: info.fields.clone(),
                        is_class: false,
                    });
                }
            }
        }

        if all_candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..all_candidates.len());
        let candidate = &all_candidates[idx];

        let base_type = if candidate.is_class {
            TypeInfo::Class(module_id, candidate.sym_id)
        } else {
            TypeInfo::Struct(module_id, candidate.sym_id)
        };
        let optional_type = TypeInfo::Optional(Box::new(base_type));

        let opt_var_name = scope.fresh_name();

        // Randomly (50%) assign nil or a constructed instance
        let assign_nil = emit.gen_bool(0.5);
        let init_value = if assign_nil {
            "nil".to_string()
        } else {
            let field_values = generate_field_values(&candidate.fields, emit);
            format!("{} {{ {} }}", candidate.name, field_values)
        };

        let let_stmt = format!("let {}: {}? = {}", opt_var_name, candidate.name, init_value);
        scope.add_local(opt_var_name.clone(), optional_type, false);

        // Build destructure pattern and arm body
        let (pattern_parts, arm_body) = build_destructure(scope, &candidate.fields)?;

        // Generate the nil arm default value
        let nil_values = ["-1_i64", "0_i64", "42_i64"];
        let nil_value = nil_values[emit.gen_range(0..nil_values.len())];

        let result_name = scope.fresh_name();
        let indent = emit.indent_str();

        let match_stmt = format!(
            "let {} = match {} {{\n\
             {}    {} {{ {} }} => {}\n\
             {}    nil => {}\n\
             {}}}",
            result_name,
            opt_var_name,
            indent,
            candidate.name,
            pattern_parts.join(", "),
            arm_body,
            indent,
            nil_value,
            indent,
        );

        scope.add_local(result_name, TypeInfo::Primitive(PrimitiveType::I64), false);

        Some(format!("{}\n{}{}", let_stmt, indent, match_stmt))
    }
}

struct CandidateType {
    sym_id: crate::symbols::SymbolId,
    name: String,
    fields: Vec<FieldInfo>,
    is_class: bool,
}

fn generate_field_values(fields: &[FieldInfo], emit: &mut Emit) -> String {
    fields
        .iter()
        .map(|f| {
            let value = emit.literal(&f.field_type);
            format!("{}: {}", f.name, value)
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// Build destructure pattern parts and the arm body expression.
///
/// Returns `(pattern_parts, arm_body)` or `None` if no primitive fields.
fn build_destructure(scope: &mut Scope, fields: &[FieldInfo]) -> Option<(Vec<String>, String)> {
    let primitive_fields: Vec<&FieldInfo> = fields
        .iter()
        .filter(|f| f.field_type.is_primitive())
        .collect();

    if primitive_fields.is_empty() {
        return None;
    }

    let mut pattern_parts = Vec::new();
    let mut binding_names = Vec::new();
    let mut binding_types = Vec::new();

    for field in fields {
        let binding = scope.fresh_name();
        pattern_parts.push(format!("{}: {}", field.name, binding));
        binding_names.push(binding);
        binding_types.push(field.field_type.clone());
    }

    let arm_body = build_arm_body(&binding_names, &binding_types);

    Some((pattern_parts, arm_body))
}

/// Build the arm body expression from destructured bindings.
fn build_arm_body(binding_names: &[String], binding_types: &[TypeInfo]) -> String {
    // Filter numeric bindings to only i64/i32 (both widen to i64 implicitly)
    let i64_compatible: Vec<(&String, &TypeInfo)> = binding_names
        .iter()
        .zip(binding_types.iter())
        .filter(|(_, ty)| {
            matches!(
                ty,
                TypeInfo::Primitive(PrimitiveType::I64 | PrimitiveType::I32)
            )
        })
        .collect();

    let string_bindings: Vec<&String> = binding_names
        .iter()
        .zip(binding_types.iter())
        .filter(|(_, ty)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
        .map(|(name, _)| name)
        .collect();

    let bool_bindings: Vec<&String> = binding_names
        .iter()
        .zip(binding_types.iter())
        .filter(|(_, ty)| matches!(ty, TypeInfo::Primitive(PrimitiveType::Bool)))
        .map(|(name, _)| name)
        .collect();

    if !i64_compatible.is_empty() {
        let parts: Vec<&str> = i64_compatible
            .iter()
            .take(3)
            .map(|(name, _)| name.as_str())
            .collect();
        let expr = parts.join(" + ");
        let has_i32 = i64_compatible
            .iter()
            .any(|(_, ty)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I32)));
        if has_i32 {
            format!("{} + 0_i64", expr)
        } else {
            expr
        }
    } else if !string_bindings.is_empty() {
        format!("{}.length()", string_bindings[0])
    } else if !bool_bindings.is_empty() {
        format!("when {{ {} => 1_i64, _ => 0_i64 }}", bool_bindings[0])
    } else {
        "1_i64".to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{ClassInfo, SymbolKind, SymbolTable};
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
        assert_eq!(MatchOptional.name(), "match_optional");
    }

    #[test]
    fn returns_none_without_module() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            MatchOptional
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn returns_none_without_classes() {
        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test".into(), "test.vole".into());
        let mut scope = Scope::with_module(&[], &table, mod_id);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            MatchOptional
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_with_class_having_primitive_field() {
        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test".into(), "test.vole".into());
        let module = table.get_module_mut(mod_id).unwrap();
        module.add_symbol(
            "Point".into(),
            SymbolKind::Class(ClassInfo {
                type_params: vec![],
                fields: vec![
                    FieldInfo {
                        name: "x".into(),
                        field_type: TypeInfo::Primitive(PrimitiveType::I64),
                    },
                    FieldInfo {
                        name: "y".into(),
                        field_type: TypeInfo::Primitive(PrimitiveType::I64),
                    },
                ],
                methods: vec![],
                implements: vec![],
                static_methods: vec![],
            }),
        );

        let mut scope = Scope::with_module(&[], &table, mod_id);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = MatchOptional.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("Point?"), "got: {text}");
        assert!(text.contains("match "), "got: {text}");
        assert!(text.contains("nil =>"), "got: {text}");
    }
}
