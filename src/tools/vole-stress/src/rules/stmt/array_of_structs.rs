//! Rule: create arrays of struct instances and access/iterate them.
//!
//! Generates three variants that stress RC ownership for struct fields
//! stored in arrays:
//!
//! 1. Array literal with field access:
//!    ```vole
//!    let items = [S { a: 1, b: 2 }, S { a: 3, b: 4 }]
//!    let result = items[0].a + items[1].b
//!    ```
//!
//! 2. Push structs to array in loop:
//!    ```vole
//!    var items: [S] = []
//!    items.push(S { a: 1, b: 2 })
//!    items.push(S { a: 3, b: 4 })
//!    let first = items[0].a
//!    ```
//!
//! 3. Iterate array of structs and accumulate (only i64-field structs):
//!    ```vole
//!    let items = [S { a: 1, b: 2 }, S { a: 3, b: 4 }]
//!    var acc = 0
//!    for item in items {
//!        acc = acc + item.a + item.b
//!    }
//!    ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, StructInfo, SymbolId, SymbolKind, TypeInfo};

pub struct ArrayOfStructs;

/// Find structs with 2+ fields that are ALL i64.
fn find_i64_only_structs(scope: &Scope, emit: &mut Emit) -> Option<(SymbolId, String, StructInfo)> {
    let module_id = scope.module_id?;
    let module = scope.table.get_module(module_id)?;

    let candidates: Vec<(SymbolId, String, StructInfo)> = module
        .structs()
        .filter_map(|sym| {
            if let SymbolKind::Struct(ref info) = sym.kind {
                // Need 2+ fields, ALL i64
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

/// Generate a struct literal with small i64 values or existing scope vars.
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

/// Variant 1: Array literal of structs with field access.
fn gen_array_literal_access(
    struct_name: &str,
    struct_info: &StructInfo,
    scope: &mut Scope,
    emit: &mut Emit,
) -> String {
    let items_name = scope.fresh_name();
    let result_name = scope.fresh_name();

    let lit0 = gen_struct_literal(struct_name, struct_info, scope, emit);
    let lit1 = gen_struct_literal(struct_name, struct_info, scope, emit);

    let field_count = struct_info.fields.len();
    let f0_idx = emit.gen_range(0..field_count);
    let f1_idx = emit.gen_range(0..field_count);
    let f0_name = &struct_info.fields[f0_idx].name;
    let f1_name = &struct_info.fields[f1_idx].name;

    format!(
        "let {items} = [{s0}, {s1}]\nlet {result} = {items}[0].{f0} + {items}[1].{f1}",
        items = items_name,
        s0 = lit0,
        s1 = lit1,
        result = result_name,
        f0 = f0_name,
        f1 = f1_name,
    )
}

/// Variant 2: Push structs to array then access a field.
fn gen_push_access(
    struct_name: &str,
    struct_info: &StructInfo,
    scope: &mut Scope,
    emit: &mut Emit,
) -> String {
    let items_name = scope.fresh_name();
    let field_name = scope.fresh_name();

    let lit0 = gen_struct_literal(struct_name, struct_info, scope, emit);
    let lit1 = gen_struct_literal(struct_name, struct_info, scope, emit);

    let f_idx = emit.gen_range(0..struct_info.fields.len());
    let f_name = &struct_info.fields[f_idx].name;

    format!(
        "var {items}: [{sn}] = []\n{items}.push({s0})\n{items}.push({s1})\nlet {field} = {items}[0].{f}",
        items = items_name,
        sn = struct_name,
        s0 = lit0,
        s1 = lit1,
        field = field_name,
        f = f_name,
    )
}

/// Variant 3: Iterate array of structs and accumulate field values.
fn gen_iterate_accumulate(
    struct_name: &str,
    struct_info: &StructInfo,
    scope: &mut Scope,
    emit: &mut Emit,
) -> String {
    let items_name = scope.fresh_name();
    let acc_name = scope.fresh_name();
    let iter_name = scope.fresh_name();

    let lit0 = gen_struct_literal(struct_name, struct_info, scope, emit);
    let lit1 = gen_struct_literal(struct_name, struct_info, scope, emit);

    // Build accumulation expression from fields: item.f1 + item.f2 + ...
    let field_accesses: Vec<String> = struct_info
        .fields
        .iter()
        .map(|f| format!("{}.{}", iter_name, f.name))
        .collect();
    let acc_expr = field_accesses.join(" + ");

    format!(
        "let {items} = [{s0}, {s1}]\nvar {acc} = 0\nfor {iter} in {items} {{\n    {acc} = {acc} + {acc_expr}\n}}",
        items = items_name,
        s0 = lit0,
        s1 = lit1,
        acc = acc_name,
        iter = iter_name,
        acc_expr = acc_expr,
    )
}

impl StmtRule for ArrayOfStructs {
    fn name(&self) -> &'static str {
        "array_of_structs"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let (_sym_id, struct_name, struct_info) = find_i64_only_structs(scope, emit)?;

        // Pick variant: 0 = literal+access, 1 = push+access, 2 = iterate+accumulate
        let variant = emit.gen_range(0..3);

        let code = match variant {
            0 => gen_array_literal_access(&struct_name, &struct_info, scope, emit),
            1 => gen_push_access(&struct_name, &struct_info, scope, emit),
            _ => gen_iterate_accumulate(&struct_name, &struct_info, scope, emit),
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
        assert_eq!(ArrayOfStructs.name(), "array_of_structs");
    }

    #[test]
    fn returns_none_without_module() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        // module_id is None

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ArrayOfStructs.generate(&mut scope, &mut emit, &rule_params);
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

        let result = ArrayOfStructs.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
