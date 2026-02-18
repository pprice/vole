//! Rule: closure invocation with class/struct instance arguments.
//!
//! Combines closures with RC types to stress-test reference counting.
//! Generates patterns like:
//!   `let inst = MyClass { field1: 42, field2: "hello" }`
//!   `let f = (x: MyClass) -> i64 => x.field1 + 1`
//!   `let result = f(inst)`

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{ClassInfo, FieldInfo, PrimitiveType, SymbolId, SymbolKind, TypeInfo};

pub struct ClosureClassCall;

/// Primitive types we consider valid for field access in the lambda body.
fn is_usable_primitive(ty: &TypeInfo) -> Option<PrimitiveType> {
    if let TypeInfo::Primitive(p) = ty {
        match p {
            PrimitiveType::I64
            | PrimitiveType::I32
            | PrimitiveType::String
            | PrimitiveType::Bool
            | PrimitiveType::F64 => Some(*p),
            _ => None,
        }
    } else {
        None
    }
}

impl StmtRule for ClosureClassCall {
    fn name(&self) -> &'static str {
        "closure_class_call"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.04)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        if scope.is_in_generic_class_method() {
            return false;
        }
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        if scope.is_in_generic_class_method() {
            return None;
        }
        let module_id = scope.module_id?;
        let module = scope.table.get_module(module_id)?;

        // Collect non-generic classes that have at least one primitive-typed field
        // we can use.
        let candidates: Vec<(SymbolId, String, ClassInfo, Vec<(String, PrimitiveType)>)> = module
            .classes()
            .filter_map(|sym| {
                if let SymbolKind::Class(ref info) = sym.kind
                    && info.type_params.is_empty()
                {
                    let usable_fields: Vec<(String, PrimitiveType)> = info
                        .fields
                        .iter()
                        .filter_map(|f| {
                            is_usable_primitive(&f.field_type).map(|p| (f.name.clone(), p))
                        })
                        .collect();
                    if usable_fields.is_empty() {
                        None
                    } else {
                        Some((sym.id, sym.name.clone(), info.clone(), usable_fields))
                    }
                } else {
                    None
                }
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        // Pick a random candidate class
        let idx = emit.gen_range(0..candidates.len());
        let (sym_id, class_name, class_info, usable_fields) = &candidates[idx];
        let sym_id = *sym_id;
        let class_name = class_name.clone();
        let class_info = class_info.clone();
        let usable_fields = usable_fields.clone();

        // Pick one usable field for the lambda body
        let field_idx = emit.gen_range(0..usable_fields.len());
        let (chosen_field_name, chosen_prim) = &usable_fields[field_idx];
        let chosen_field_name = chosen_field_name.clone();
        let chosen_prim = *chosen_prim;

        // Determine the return type of the lambda and the body expression
        let (return_prim, body_expr) = match chosen_prim {
            PrimitiveType::I64 => (PrimitiveType::I64, format!("x.{} + 1", chosen_field_name)),
            PrimitiveType::I32 => (
                PrimitiveType::I32,
                format!("x.{} + 1_i32", chosen_field_name),
            ),
            PrimitiveType::String => (PrimitiveType::String, format!("x.{}", chosen_field_name)),
            PrimitiveType::Bool => (PrimitiveType::Bool, format!("x.{}", chosen_field_name)),
            PrimitiveType::F64 => (PrimitiveType::F64, format!("x.{}", chosen_field_name)),
            _ => unreachable!("is_usable_primitive filters to only the above"),
        };

        // Generate the class type annotation using the symbol table
        let class_ty = TypeInfo::Class(module_id, sym_id);
        let class_type_str = class_ty.to_vole_syntax(scope.table);
        let return_type_str = PrimitiveType::as_str(&return_prim);

        // Generate field values for the instance construction
        let field_values = generate_field_values(&class_info.fields, emit);

        // Generate fresh names for: instance, lambda, result
        let inst_name = scope.fresh_name();
        let lambda_name = scope.fresh_name();
        let result_name = scope.fresh_name();

        // Register the instance variable
        scope.add_local(inst_name.clone(), class_ty.clone(), false);

        // Register the result variable with the return primitive type
        scope.add_local(result_name.clone(), TypeInfo::Primitive(return_prim), false);

        // Build the three-statement sequence:
        //   let inst = ClassName { field1: val1, field2: val2 }
        //   let f = (x: ClassName) -> RetType => body
        //   let result = f(inst)
        Some(format!(
            "let {} = {} {{ {} }}\n    let {} = (x: {}) -> {} => {}\n    let {} = {}({})",
            inst_name,
            class_name,
            field_values,
            lambda_name,
            class_type_str,
            return_type_str,
            body_expr,
            result_name,
            lambda_name,
            inst_name,
        ))
    }
}

/// Generate field value literals for class construction.
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
        assert_eq!(ClosureClassCall.name(), "closure_class_call");
    }

    #[test]
    fn returns_none_without_classes() {
        let mut table = SymbolTable::new();
        let _mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClosureClassCall.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
