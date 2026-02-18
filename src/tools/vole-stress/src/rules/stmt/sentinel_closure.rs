//! Rule: closure that captures a sentinel union variable.
//!
//! Creates a `PrimType | Sentinel` union local, then a closure `(x: i64) -> i64`
//! that captures the union variable and uses a `when` expression inside.
//! The closure is immediately invoked with a literal argument.
//!
//! ```vole
//! let local0: i64 | Sent1 = Sent1
//! let local1 = ((x: i64) -> i64 => when { local0 is Sent1 => x + 1, _ => x })(10)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct SentinelClosure;

impl StmtRule for SentinelClosure {
    fn name(&self) -> &'static str {
        "sentinel_closure"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.10)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let module_id = scope.module_id?;
        let module = scope.table.get_module(module_id)?;

        let sentinels: Vec<_> = module.sentinels().collect();
        if sentinels.is_empty() {
            return None;
        }

        let sentinel_idx = emit.gen_range(0..sentinels.len());
        let sentinel_name = sentinels[sentinel_idx].name.clone();
        let sentinel_sym_id = sentinels[sentinel_idx].id;

        // Create the union variable: i64 | Sentinel
        let union_var = scope.fresh_name();
        let assign_sentinel = emit.gen_bool(0.5);
        let init_value = if assign_sentinel {
            sentinel_name.clone()
        } else {
            let n = emit.random_in(0, 200) as i64 - 100; // range -100..=100
            format!("{}_i64", n)
        };

        let union_stmt = format!(
            "let {}: i64 | {} = {}",
            union_var, sentinel_name, init_value
        );
        scope.add_local(
            union_var.clone(),
            TypeInfo::Union(vec![
                TypeInfo::Primitive(PrimitiveType::I64),
                TypeInfo::Sentinel(module_id, sentinel_sym_id),
            ]),
            false,
        );

        // Create a closure that captures the union variable
        let result_var = scope.fresh_name();
        let sentinel_val = emit.random_in(1, 100);
        let arg_val = emit.random_in(1, 50);

        let closure_expr = format!(
            "((x: i64) -> i64 => when {{ {} is {} => x + {}_i64, _ => x }})({})",
            union_var, sentinel_name, sentinel_val, arg_val
        );

        let result_stmt = format!("let {} = {}", result_var, closure_expr);
        scope.add_local(result_var, TypeInfo::Primitive(PrimitiveType::I64), false);

        let indent = emit.indent_str();
        Some(format!("{}\n{}{}", union_stmt, indent, result_stmt))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{SymbolKind, SymbolTable};
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
        assert_eq!(SentinelClosure.name(), "sentinel_closure");
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
            SentinelClosure
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn returns_none_without_sentinels() {
        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test".into(), "test.vole".into());
        let mut scope = Scope::with_module(&[], &table, mod_id);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            SentinelClosure
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_with_sentinel_in_module() {
        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test".into(), "test.vole".into());
        let module = table.get_module_mut(mod_id).unwrap();
        module.add_symbol("Empty".into(), SymbolKind::Sentinel);

        let mut scope = Scope::with_module(&[], &table, mod_id);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = SentinelClosure.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("i64 | Empty"), "got: {text}");
        assert!(text.contains("is Empty"), "got: {text}");
        assert!(text.contains("when"), "got: {text}");
    }

    #[test]
    fn adds_two_locals() {
        let mut table = SymbolTable::new();
        let mod_id = table.add_module("test".into(), "test.vole".into());
        let module = table.get_module_mut(mod_id).unwrap();
        module.add_symbol("Done".into(), SymbolKind::Sentinel);

        let mut scope = Scope::with_module(&[], &table, mod_id);
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        SentinelClosure.generate(&mut scope, &mut emit, &params);
        // Should add union var + result = 2 new locals
        assert_eq!(scope.locals.len(), initial_len + 2);
    }
}
