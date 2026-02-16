//! Rule: interface value expression.
//!
//! Constructs a concrete class implementing an interface type.
//! Finds a non-generic class in the same module that implements
//! the requested interface and constructs it.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::SymbolKind;

pub struct InterfaceValue;

impl ExprRule for InterfaceValue {
    fn name(&self) -> &'static str {
        "interface_value"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.15)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        let (iface_mod, iface_sym) = match expected_type {
            TypeInfo::Interface(m, s) => (*m, *s),
            _ => return None,
        };

        let module = scope.table.get_module(iface_mod)?;

        // Find a non-generic class implementing this interface
        for class_sym in module.classes() {
            if let SymbolKind::Class(ref class_info) = class_sym.kind
                && class_info.type_params.is_empty()
                && class_info
                    .implements
                    .iter()
                    .any(|&(m, s)| m == iface_mod && s == iface_sym)
            {
                let class_name = class_sym.name.clone();
                let fields = class_info.fields.clone();

                let field_values: Vec<String> = fields
                    .iter()
                    .map(|f| {
                        let value = emit.sub_expr(&f.field_type, scope);
                        format!("{}: {}", f.name, value)
                    })
                    .collect();

                return Some(format!("{} {{ {} }}", class_name, field_values.join(", ")));
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ParamValue, StmtRule};
    use crate::symbols::{PrimitiveType, SymbolTable};
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(InterfaceValue.name(), "interface_value");
    }

    #[test]
    fn returns_none_for_non_interface() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = InterfaceValue.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }
}
