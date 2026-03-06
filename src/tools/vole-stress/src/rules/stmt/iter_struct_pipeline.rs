//! Rule: iterator pipeline operations on arrays of structs.
//!
//! Generates iterator pipelines (`.iter().map()`, `.iter().filter()`) that
//! operate on arrays of struct instances, stressing the interaction between
//! iterator machinery and struct field access inside closures.
//!
//! Variant 0 -- map struct field to value + sum/count:
//! ```vole
//! let items = [S { a: 1, b: 2 }, S { a: 3, b: 4 }]
//! let result = items.iter().map((x: S) => x.a).sum()
//! ```
//!
//! Variant 1 -- filter by field predicate + count:
//! ```vole
//! let items = [S { a: 1, b: 2 }, S { a: 3, b: 4 }]
//! let result = items.iter().filter((x: S) => x.a > 10).count()
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, StructInfo, SymbolId, SymbolKind, TypeInfo};

pub struct IterStructPipeline;

/// Find structs with 2+ fields that are ALL i64.
fn find_i64_only_structs(scope: &Scope, emit: &mut Emit) -> Option<(SymbolId, String, StructInfo)> {
    let module_id = scope.module_id?;
    let module = scope.table.get_module(module_id)?;

    let candidates: Vec<(SymbolId, String, StructInfo)> = module
        .structs()
        .filter_map(|sym| {
            if let SymbolKind::Struct(ref info) = sym.kind {
                if info.fields.len() >= 2
                    && info
                        .fields
                        .iter()
                        .all(|f| matches!(f.field_type, TypeInfo::Primitive(PrimitiveType::I64)))
                {
                    Some((sym.id, sym.name.clone(), info.clone()))
                } else {
                    None
                }
            } else {
                None
            }
        })
        .collect();

    if candidates.is_empty() {
        return None;
    }

    let idx = emit.gen_range(0..candidates.len());
    Some(candidates[idx].clone())
}

/// Generate a struct literal with small i64 values.
fn gen_struct_literal(
    struct_name: &str,
    struct_info: &StructInfo,
    scope: &Scope,
    emit: &mut Emit,
) -> String {
    let i64_ty = TypeInfo::Primitive(PrimitiveType::I64);
    let i64_vars: Vec<String> = scope
        .vars_of_type(&i64_ty)
        .into_iter()
        .map(|v| v.name)
        .collect();

    let fields: Vec<String> = struct_info
        .fields
        .iter()
        .map(|f| {
            let value = if !i64_vars.is_empty() && emit.gen_bool(0.3) {
                let idx = emit.gen_range(0..i64_vars.len());
                i64_vars[idx].clone()
            } else {
                format!("{}", emit.gen_i64_range(0, 99))
            };
            format!("{}: {}", f.name, value)
        })
        .collect();

    format!("{} {{ {} }}", struct_name, fields.join(", "))
}

/// Variant 0: map a struct field to i64, then sum or count.
fn gen_map_sum(
    struct_name: &str,
    struct_info: &StructInfo,
    scope: &mut Scope,
    emit: &mut Emit,
) -> String {
    let items_name = scope.fresh_name();
    let result_name = scope.fresh_name();

    let lit0 = gen_struct_literal(struct_name, struct_info, scope, emit);
    let lit1 = gen_struct_literal(struct_name, struct_info, scope, emit);
    let lit2 = gen_struct_literal(struct_name, struct_info, scope, emit);

    let f_idx = emit.gen_range(0..struct_info.fields.len());
    let field_name = &struct_info.fields[f_idx].name;

    // Pick a lambda parameter name that isn't `val` (reserved word)
    let param = "item";

    // Either plain field access or field * constant
    let map_expr = if emit.gen_bool(0.5) {
        format!("{}.{}", param, field_name)
    } else {
        let factor = emit.gen_i64_range(2, 5);
        format!("{}.{} * {}", param, field_name, factor)
    };

    // Terminal: sum or count
    let terminal = if emit.gen_bool(0.7) { "sum" } else { "count" };

    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    format!(
        "let {items} = [{s0}, {s1}, {s2}]\n\
         let {result} = {items}.iter().map(({param}: {sn}) => {map_expr}).{terminal}()",
        items = items_name,
        s0 = lit0,
        s1 = lit1,
        s2 = lit2,
        result = result_name,
        param = param,
        sn = struct_name,
        map_expr = map_expr,
        terminal = terminal,
    )
}

/// Variant 1: filter structs by field predicate, then count.
fn gen_filter_count(
    struct_name: &str,
    struct_info: &StructInfo,
    scope: &mut Scope,
    emit: &mut Emit,
) -> String {
    let items_name = scope.fresh_name();
    let result_name = scope.fresh_name();

    let lit0 = gen_struct_literal(struct_name, struct_info, scope, emit);
    let lit1 = gen_struct_literal(struct_name, struct_info, scope, emit);

    let f_idx = emit.gen_range(0..struct_info.fields.len());
    let field_name = &struct_info.fields[f_idx].name;

    let param = "item";
    let threshold = emit.gen_i64_range(0, 50);

    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    format!(
        "let {items} = [{s0}, {s1}]\n\
         let {result} = {items}.iter().filter(({param}: {sn}) => {param}.{field} > {threshold}).count()",
        items = items_name,
        s0 = lit0,
        s1 = lit1,
        result = result_name,
        param = param,
        sn = struct_name,
        field = field_name,
        threshold = threshold,
    )
}

impl StmtRule for IterStructPipeline {
    fn name(&self) -> &'static str {
        "iter_struct_pipeline"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let (_sym_id, struct_name, struct_info) = find_i64_only_structs(scope, emit)?;

        let variant = emit.gen_range(0..2);

        let code = match variant {
            0 => gen_map_sum(&struct_name, &struct_info, scope, emit),
            _ => gen_filter_count(&struct_name, &struct_info, scope, emit),
        };

        Some(code)
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
        assert_eq!(IterStructPipeline.name(), "iter_struct_pipeline");
    }

    #[test]
    fn returns_none_without_module() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterStructPipeline.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn returns_none_without_structs() {
        let mut table = SymbolTable::new();
        let _mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterStructPipeline.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
