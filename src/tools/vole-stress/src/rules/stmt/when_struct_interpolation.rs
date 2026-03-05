//! Rule: when expression with struct field access and string interpolation.
//!
//! Generates a `when` expression that uses struct field access in conditions
//! and string interpolation with struct fields in arm bodies:
//! ```vole
//! let result = when {
//!     s.count > 10 => "{s.label}_high"
//!     s.count > 0 => "{s.label}_mid"
//!     _ => "{s.label}_low"
//! }
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, SymbolKind, TypeInfo};

pub struct WhenStructInterpolation;

impl StmtRule for WhenStructInterpolation {
    fn name(&self) -> &'static str {
        "when_struct_interpolation"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let candidates = find_struct_with_string_and_i64(scope);
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, str_field, i64_field) = &candidates[idx];
        let var_name = var_name.clone();
        let str_field = str_field.clone();
        let i64_field = i64_field.clone();

        // Generate 2-3 conditional arms + wildcard
        let arm_count = if emit.gen_bool(0.5) { 3 } else { 2 };

        let comparisons = [">", "<", "==", ">="];
        let suffixes = ["_high", "_mid", "_low", "_zero", "_pos", "_neg"];

        let indent = emit.indented(|e| e.indent_str());
        let mut arms = Vec::new();

        for i in 0..arm_count {
            let cmp = comparisons[emit.gen_range(0..comparisons.len())];
            let threshold = emit.gen_i64_range(-10, 100);
            let suffix = suffixes[emit.gen_range(0..suffixes.len())];

            // Avoid reusing the same suffix in different arms
            let _ = i;
            arms.push(format!(
                "{}{}.{} {} {} => \"{{{}.{}}}{}\"",
                indent, var_name, i64_field, cmp, threshold, var_name, str_field, suffix
            ));
        }

        // Wildcard arm (required for exhaustiveness)
        let wildcard_suffix = suffixes[emit.gen_range(0..suffixes.len())];
        arms.push(format!(
            "{}_ => \"{{{}.{}}}{}\"",
            indent, var_name, str_field, wildcard_suffix
        ));

        let close_indent = emit.indent_str();
        let result_name = scope.fresh_name();

        scope.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        Some(format!(
            "let {} = when {{\n{}\n{}}}",
            result_name,
            arms.join("\n"),
            close_indent,
        ))
    }
}

/// Find struct-typed variables in scope that have both a string field and an i64 field.
///
/// Returns `(var_name, string_field_name, i64_field_name)` triples.
fn find_struct_with_string_and_i64(scope: &Scope) -> Vec<(String, String, String)> {
    let mut candidates = Vec::new();

    for (name, ty, _) in &scope.locals {
        if let TypeInfo::Struct(mod_id, sym_id) = ty
            && let Some(sym) = scope.table.get_symbol(*mod_id, *sym_id)
            && let SymbolKind::Struct(ref info) = sym.kind
        {
            let str_fields: Vec<&str> = info
                .fields
                .iter()
                .filter(|f| matches!(f.field_type, TypeInfo::Primitive(PrimitiveType::String)))
                .map(|f| f.name.as_str())
                .collect();

            let i64_fields: Vec<&str> = info
                .fields
                .iter()
                .filter(|f| matches!(f.field_type, TypeInfo::Primitive(PrimitiveType::I64)))
                .map(|f| f.name.as_str())
                .collect();

            if !str_fields.is_empty() && !i64_fields.is_empty() {
                // Use first matching field of each type
                candidates.push((
                    name.clone(),
                    str_fields[0].to_string(),
                    i64_fields[0].to_string(),
                ));
            }
        }
    }

    candidates
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{FieldInfo, ModuleId, StructInfo, SymbolKind, SymbolTable};
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

    fn make_table_with_struct() -> (SymbolTable, ModuleId) {
        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let module = table.get_module_mut(mod_id).unwrap();
        module.add_symbol(
            "Item".into(),
            SymbolKind::Struct(StructInfo {
                fields: vec![
                    FieldInfo {
                        name: "label".into(),
                        field_type: TypeInfo::Primitive(PrimitiveType::String),
                    },
                    FieldInfo {
                        name: "count".into(),
                        field_type: TypeInfo::Primitive(PrimitiveType::I64),
                    },
                ],
                static_methods: vec![],
            }),
        );
        (table, mod_id)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(WhenStructInterpolation.name(), "when_struct_interpolation");
    }

    #[test]
    fn returns_none_without_structs() {
        let mut table = SymbolTable::new();
        let _mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(ModuleId(0));

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WhenStructInterpolation.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn generates_with_struct_having_string_and_i64() {
        let (table, mod_id) = make_table_with_struct();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(mod_id);

        // Add a struct-typed local
        let sym_id = table
            .get_module(mod_id)
            .unwrap()
            .symbols()
            .find(|s| s.name == "Item")
            .unwrap()
            .id;
        scope.add_local("item".into(), TypeInfo::Struct(mod_id, sym_id), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WhenStructInterpolation.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some(), "expected Some, got None");
        let text = result.unwrap();
        assert!(text.contains("when {"), "missing 'when {{': {text}");
        assert!(
            text.contains("item.count"),
            "missing struct i64 field access: {text}"
        );
        assert!(
            text.contains("{item.label}"),
            "missing interpolation: {text}"
        );
        assert!(text.contains("_ =>"), "missing wildcard arm: {text}");
    }

    #[test]
    fn generates_multiple_seeds_without_panic() {
        let (table, mod_id) = make_table_with_struct();

        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(mod_id);

            let sym_id = table
                .get_module(mod_id)
                .unwrap()
                .symbols()
                .find(|s| s.name == "Item")
                .unwrap()
                .id;
            scope.add_local("item".into(), TypeInfo::Struct(mod_id, sym_id), false);

            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            let result = WhenStructInterpolation.generate(&mut scope, &mut emit, &rule_params);
            assert!(result.is_some(), "seed {seed} returned None");
        }
    }
}
