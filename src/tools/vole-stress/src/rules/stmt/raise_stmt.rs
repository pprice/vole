//! Rule: conditional raise statement in fallible function body.
//!
//! Generates `if <cond> { raise ErrorType { fields } }` when the current
//! function is fallible and the error type can be resolved from the symbol
//! table.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, SymbolKind, TypeInfo};

pub struct RaiseStmt;

impl StmtRule for RaiseStmt {
    fn name(&self) -> &'static str {
        "raise_stmt"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.is_fallible && scope.fallible_error_type.is_some() && scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let error_type = scope.fallible_error_type.as_ref()?;

        let (error_name, error_fields) = match error_type {
            TypeInfo::Error(mod_id, sym_id) => {
                let symbol = scope.table.get_symbol(*mod_id, *sym_id)?;
                if let SymbolKind::Error(ref info) = symbol.kind {
                    (symbol.name.clone(), info.fields.clone())
                } else {
                    return None;
                }
            }
            _ => return None,
        };

        // Generate a simple bool condition so the raise doesn't always trigger
        let cond = emit.literal(&TypeInfo::Primitive(PrimitiveType::Bool));

        // Generate field values for the error construction
        let field_values = if error_fields.is_empty() {
            String::new()
        } else {
            let values: Vec<String> = error_fields
                .iter()
                .map(|f| {
                    let val = emit.literal(&f.field_type);
                    format!("{}: {}", f.name, val)
                })
                .collect();
            format!(" {}", values.join(", "))
        };

        let indent = emit.indent_str();
        let inner_indent = format!("{}    ", indent);

        Some(format!(
            "if {} {{\n{}raise {} {{{}}}\n{}}}",
            cond, inner_indent, error_name, field_values, indent,
        ))
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
        assert_eq!(RaiseStmt.name(), "raise_stmt");
    }

    #[test]
    fn precondition_requires_fallible() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!RaiseStmt.precondition(&scope, &params));
    }

    #[test]
    fn returns_none_without_error_type() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.is_fallible = true;
        // No fallible_error_type set

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = RaiseStmt.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
