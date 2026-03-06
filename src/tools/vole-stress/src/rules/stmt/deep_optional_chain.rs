//! Rule: deep optional chaining over nested struct types.
//!
//! Generates 2-3 nested struct types with optional fields and exercises `?.`
//! optional chaining with `?? default` fallback at varying depths and nil
//! combinations.
//!
//! **Variant 0 -- full chain (all non-nil):**
//! ```vole
//! struct Inner_42918 { value: i64 }
//! struct Outer_42918 { inner: Inner_42918? }
//! let inst = Outer_42918 { inner: Inner_42918 { value: 42 } }
//! let result = inst.inner?.value ?? -1
//! assert(result == 42)
//! ```
//!
//! **Variant 1 -- nil at middle level:**
//! ```vole
//! struct Inner_42918 { value: i64 }
//! struct Outer_42918 { inner: Inner_42918? }
//! let inst = Outer_42918 { inner: nil }
//! let result = inst.inner?.value ?? -1
//! assert(result == -1)
//! ```
//!
//! **Variant 2 -- three-deep chain:**
//! ```vole
//! struct Deep_42918 { data: i64 }
//! struct Mid_42918 { deep: Deep_42918? }
//! struct Top_42918 { mid: Mid_42918? }
//! let inst = Top_42918 { mid: Mid_42918 { deep: Deep_42918 { data: 99 } } }
//! let result = inst.mid?.deep?.data ?? 0
//! assert(result == 99)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct DeepOptionalChain;

impl StmtRule for DeepOptionalChain {
    fn name(&self) -> &'static str {
        "deep_optional_chain"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Can't declare structs inside class methods.
        scope.current_class_sym_id.is_none()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..3);
        match variant {
            0 => emit_full_chain(scope, emit),
            1 => emit_nil_middle(scope, emit),
            _ => emit_three_deep(scope, emit),
        }
    }
}

// ---------------------------------------------------------------------------
// Variant 0: two-level chain, all non-nil
// ---------------------------------------------------------------------------

fn emit_full_chain(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let inner_val = emit.gen_range(1..200) as i64;
    let default_val = -(emit.gen_range(1..100) as i64);

    let inner_name = format!("Inner_{}", uid);
    let outer_name = format!("Outer_{}", uid);

    // struct Inner_X { value: i64 }
    let inner_decl = format!("struct {} {{\n    value: i64,\n}}", inner_name);
    scope.add_module_decl(inner_decl);

    // struct Outer_X { inner: Inner_X? }
    let outer_decl = format!("struct {} {{\n    inner: {}?,\n}}", outer_name, inner_name);
    scope.add_module_decl(outer_decl);

    let mut lines = Vec::new();

    // let inst = Outer_X { inner: Inner_X { value: N } }
    let inst = scope.fresh_name();
    lines.push(format!(
        "let {} = {} {{ inner: {} {{ value: {}_i64 }} }}",
        inst, outer_name, inner_name, inner_val,
    ));

    // let result = inst.inner?.value ?? default
    let result = scope.fresh_name();
    scope.add_local(
        result.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );
    lines.push(format!(
        "let {} = {}.inner?.value ?? {}_i64",
        result, inst, default_val,
    ));

    // assert(result == inner_val)
    lines.push(format!("assert({} == {}_i64)", result, inner_val));

    Some(lines.join("\n"))
}

// ---------------------------------------------------------------------------
// Variant 1: two-level chain, nil at inner field
// ---------------------------------------------------------------------------

fn emit_nil_middle(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let default_val = -(emit.gen_range(1..100) as i64);

    let inner_name = format!("InnerN_{}", uid);
    let outer_name = format!("OuterN_{}", uid);

    // struct InnerN_X { value: i64 }
    let inner_decl = format!("struct {} {{\n    value: i64,\n}}", inner_name);
    scope.add_module_decl(inner_decl);

    // struct OuterN_X { inner: InnerN_X? }
    let outer_decl = format!("struct {} {{\n    inner: {}?,\n}}", outer_name, inner_name,);
    scope.add_module_decl(outer_decl);

    let mut lines = Vec::new();

    // let inst = OuterN_X { inner: nil }
    let inst = scope.fresh_name();
    lines.push(format!("let {} = {} {{ inner: nil }}", inst, outer_name,));

    // let result = inst.inner?.value ?? default
    let result = scope.fresh_name();
    scope.add_local(
        result.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );
    lines.push(format!(
        "let {} = {}.inner?.value ?? {}_i64",
        result, inst, default_val,
    ));

    // assert(result == default_val)  -- inner is nil so fallback fires
    lines.push(format!("assert({} == {}_i64)", result, default_val));

    Some(lines.join("\n"))
}

// ---------------------------------------------------------------------------
// Variant 2: three-level chain, all non-nil
// ---------------------------------------------------------------------------

fn emit_three_deep(scope: &mut Scope, emit: &mut Emit) -> Option<String> {
    let uid = emit.gen_range(10000..99999);
    let data_val = emit.gen_range(1..500) as i64;
    let default_val = emit.gen_range(0..10) as i64;

    let deep_name = format!("Deep_{}", uid);
    let mid_name = format!("Mid_{}", uid);
    let top_name = format!("Top_{}", uid);

    // struct Deep_X { data: i64 }
    let deep_decl = format!("struct {} {{\n    data: i64,\n}}", deep_name);
    scope.add_module_decl(deep_decl);

    // struct Mid_X { deep: Deep_X? }
    let mid_decl = format!("struct {} {{\n    deep: {}?,\n}}", mid_name, deep_name,);
    scope.add_module_decl(mid_decl);

    // struct Top_X { mid: Mid_X? }
    let top_decl = format!("struct {} {{\n    mid: {}?,\n}}", top_name, mid_name,);
    scope.add_module_decl(top_decl);

    let mut lines = Vec::new();

    // let inst = Top_X { mid: Mid_X { deep: Deep_X { data: N } } }
    let inst = scope.fresh_name();
    lines.push(format!(
        "let {} = {} {{ mid: {} {{ deep: {} {{ data: {}_i64 }} }} }}",
        inst, top_name, mid_name, deep_name, data_val,
    ));

    // let result = inst.mid?.deep?.data ?? default
    let result = scope.fresh_name();
    scope.add_local(
        result.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );
    lines.push(format!(
        "let {} = {}.mid?.deep?.data ?? {}_i64",
        result, inst, default_val,
    ));

    // assert(result == data_val)
    lines.push(format!("assert({} == {}_i64)", result, data_val));

    Some(lines.join("\n"))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

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
        assert_eq!(DeepOptionalChain.name(), "deep_optional_chain");
    }

    #[test]
    fn precondition_rejects_class_methods() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        // No class sym id => precondition passes
        assert!(DeepOptionalChain.precondition(&scope, &params));

        // Inside a class method => precondition fails
        scope.current_class_sym_id =
            Some((crate::symbols::ModuleId(0), crate::symbols::SymbolId(0)));
        assert!(!DeepOptionalChain.precondition(&scope, &params));
    }

    #[test]
    fn generates_full_chain_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = DeepOptionalChain.generate(&mut scope, &mut emit, &params) {
                if scope
                    .module_decls
                    .iter()
                    .any(|d| d.contains("struct Inner_"))
                {
                    found = true;
                    // Should have 2 module decls: Inner + Outer
                    assert_eq!(
                        scope.module_decls.len(),
                        2,
                        "expected 2 module_decls for full chain variant"
                    );
                    // Inner struct has a value field
                    assert!(
                        scope.module_decls[0].contains("value: i64"),
                        "expected value field in Inner: {}",
                        scope.module_decls[0]
                    );
                    // Outer struct has optional inner field
                    assert!(
                        scope.module_decls[1].contains("inner: Inner_"),
                        "expected inner field in Outer: {}",
                        scope.module_decls[1]
                    );
                    assert!(
                        scope.module_decls[1].contains("?"),
                        "expected optional type in Outer: {}",
                        scope.module_decls[1]
                    );
                    // Code uses ?. and ??
                    assert!(text.contains("?.value"), "expected ?.value in code: {text}");
                    assert!(text.contains("??"), "expected ?? fallback in code: {text}");
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated full chain variant in 100 seeds");
    }

    #[test]
    fn generates_nil_middle_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = DeepOptionalChain.generate(&mut scope, &mut emit, &params) {
                if scope
                    .module_decls
                    .iter()
                    .any(|d| d.contains("struct InnerN_"))
                {
                    found = true;
                    // Should have 2 module decls: InnerN + OuterN
                    assert_eq!(
                        scope.module_decls.len(),
                        2,
                        "expected 2 module_decls for nil-middle variant"
                    );
                    // Construction uses nil
                    assert!(
                        text.contains("inner: nil"),
                        "expected nil construction in code: {text}"
                    );
                    // Code uses ?. and ??
                    assert!(text.contains("?.value"), "expected ?.value in code: {text}");
                    assert!(text.contains("??"), "expected ?? fallback in code: {text}");
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated nil-middle variant in 100 seeds");
    }

    #[test]
    fn generates_three_deep_variant() {
        let table = SymbolTable::new();
        let mut found = false;
        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = DeepOptionalChain.generate(&mut scope, &mut emit, &params) {
                if scope
                    .module_decls
                    .iter()
                    .any(|d| d.contains("struct Deep_"))
                {
                    found = true;
                    // Should have 3 module decls: Deep + Mid + Top
                    assert_eq!(
                        scope.module_decls.len(),
                        3,
                        "expected 3 module_decls for three-deep variant"
                    );
                    // Deep struct has data field
                    assert!(
                        scope.module_decls[0].contains("data: i64"),
                        "expected data field in Deep: {}",
                        scope.module_decls[0]
                    );
                    // Mid struct has optional deep field
                    assert!(
                        scope.module_decls[1].contains("deep: Deep_"),
                        "expected deep field in Mid: {}",
                        scope.module_decls[1]
                    );
                    // Top struct has optional mid field
                    assert!(
                        scope.module_decls[2].contains("mid: Mid_"),
                        "expected mid field in Top: {}",
                        scope.module_decls[2]
                    );
                    // Code uses double ?. chain
                    assert!(
                        text.contains("?.deep?.data"),
                        "expected ?.deep?.data in code: {text}"
                    );
                    assert!(text.contains("??"), "expected ?? fallback in code: {text}");
                    assert!(text.contains("assert("), "expected assert in code: {text}");
                    break;
                }
            }
        }
        assert!(found, "never generated three-deep variant in 100 seeds");
    }

    #[test]
    fn adds_module_decls() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        DeepOptionalChain.generate(&mut scope, &mut emit, &params);
        assert!(
            scope.module_decls.len() >= 2,
            "expected at least 2 module_decls, got {}",
            scope.module_decls.len(),
        );
    }

    #[test]
    fn adds_result_local_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = DeepOptionalChain.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        assert!(
            scope.locals.len() >= 1,
            "expected at least 1 local (result binding), got {}",
            scope.locals.len(),
        );
        // The registered local should be i64 (the result of ?? default)
        let (_, ty, _) = scope.locals.last().unwrap();
        assert!(
            matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)),
            "result type should be i64, got {:?}",
            ty,
        );
    }

    #[test]
    fn all_variants_reachable() {
        let table = SymbolTable::new();
        let mut seen_full = false;
        let mut seen_nil = false;
        let mut seen_deep = false;

        for seed in 0..200 {
            let mut scope = Scope::new(&[], &table);
            scope.module_id = Some(crate::symbols::ModuleId(0));
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(_) = DeepOptionalChain.generate(&mut scope, &mut emit, &params) {
                if scope
                    .module_decls
                    .iter()
                    .any(|d| d.contains("struct Inner_"))
                {
                    seen_full = true;
                }
                if scope
                    .module_decls
                    .iter()
                    .any(|d| d.contains("struct InnerN_"))
                {
                    seen_nil = true;
                }
                if scope
                    .module_decls
                    .iter()
                    .any(|d| d.contains("struct Deep_"))
                {
                    seen_deep = true;
                }
            }
            if seen_full && seen_nil && seen_deep {
                break;
            }
        }
        assert!(seen_full, "never generated full-chain variant");
        assert!(seen_nil, "never generated nil-middle variant");
        assert!(seen_deep, "never generated three-deep variant");
    }
}
