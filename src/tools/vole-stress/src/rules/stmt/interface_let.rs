//! Rule: interface-typed local via upcast from a class instance.
//!
//! Finds a non-generic interface with methods in the current module that has
//! at least one implementing class. Constructs the class and assigns it to a
//! local with the interface type annotation:
//!   `let local5: IFace1 = MyClass { field1: 42_i64 }`

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{ClassInfo, SymbolId, SymbolKind, TypeInfo};

pub struct InterfaceLet;

impl StmtRule for InterfaceLet {
    fn name(&self) -> &'static str {
        "interface_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.05)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let module_id = scope.module_id?;
        let (iface_sym_id, iface_name, class_info) = find_implementor_pair(scope, emit, module_id)?;

        let name = scope.fresh_name();

        // Generate field values for the class construction
        let fields: Vec<String> = class_info
            .fields
            .iter()
            .map(|f| {
                let value = emit.literal(&f.field_type);
                format!("{}: {}", f.name, value)
            })
            .collect();
        let expr = format!("{} {{ {} }}", class_info.name, fields.join(", "));

        // Register as interface-typed
        scope.add_local(
            name.clone(),
            TypeInfo::Interface(module_id, iface_sym_id),
            false,
        );

        Some(format!("let {}: {} = {}", name, iface_name, expr))
    }
}

/// Result of finding an interface/class pair.
struct ImplementorClassInfo {
    name: String,
    fields: Vec<crate::symbols::FieldInfo>,
}

/// Find a (interface, implementing class) pair in a module.
fn find_implementor_pair(
    scope: &Scope,
    emit: &mut Emit,
    module_id: crate::symbols::ModuleId,
) -> Option<(SymbolId, String, ImplementorClassInfo)> {
    let module = scope.table.get_module(module_id)?;

    let mut candidates: Vec<(SymbolId, String, ImplementorClassInfo)> = Vec::new();

    for iface_sym in module.interfaces() {
        let _iface_info = match &iface_sym.kind {
            SymbolKind::Interface(info)
                if info.type_params.is_empty() && !info.methods.is_empty() =>
            {
                info
            }
            _ => continue,
        };

        for class_sym in module.classes() {
            if let SymbolKind::Class(ref class_info) = class_sym.kind
                && class_info.type_params.is_empty()
                && class_info
                    .implements
                    .iter()
                    .any(|&(m, s)| m == module_id && s == iface_sym.id)
            {
                candidates.push((
                    iface_sym.id,
                    iface_sym.name.clone(),
                    ImplementorClassInfo {
                        name: class_sym.name.clone(),
                        fields: class_info.fields.clone(),
                    },
                ));
            }
        }
    }

    if candidates.is_empty() {
        return None;
    }

    let idx = emit.gen_range(0..candidates.len());
    Some(candidates.swap_remove(idx))
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
        assert_eq!(InterfaceLet.name(), "interface_let");
    }

    #[test]
    fn returns_none_without_interfaces() {
        let mut table = SymbolTable::new();
        let _mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = InterfaceLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}
