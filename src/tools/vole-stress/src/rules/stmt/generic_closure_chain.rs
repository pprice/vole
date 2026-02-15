//! Rule: generic closure + interface dispatch in an iterator chain.
//!
//! Requires all three in scope:
//! 1. An array-typed variable with i64 or i32 elements
//! 2. A function-typed parameter `(ElemType) -> ElemType`
//! 3. A constrained type-param variable with interface methods
//!
//! Generates an iterator chain using the closure in `.map(transform)` and the
//! interface method in `.filter((n: T) => n > criterion.method())`.
//!
//! ```vole
//! let local5 = items.iter()
//!     .map(transform)
//!     .filter((n: i64) => n > criterion.threshold())
//!     .collect()
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{ModuleId, ParamInfo, PrimitiveType, SymbolId, TypeInfo};

pub struct GenericClosureChain;

impl StmtRule for GenericClosureChain {
    fn name(&self) -> &'static str {
        "generic_closure_chain"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.15)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Step 1: Find array variables with i64 or i32 elements
        let prim_arrays = find_prim_arrays(scope);
        if prim_arrays.is_empty() {
            return None;
        }

        // Step 2: Find function-typed params (PrimType) -> PrimType
        let fn_params = find_fn_params(scope);
        if fn_params.is_empty() {
            return None;
        }

        // Step 3: Find constrained type param variables with interface methods
        let constrained_vars = scope.constrained_type_param_vars();
        if constrained_vars.is_empty() {
            return None;
        }

        let iface_candidates = collect_iface_candidates(scope, &constrained_vars);
        if iface_candidates.is_empty() {
            return None;
        }

        // Pick an array variable
        let arr_idx = emit.gen_range(0..prim_arrays.len());
        let (arr_name, elem_prim) = prim_arrays[arr_idx].clone();

        // Pick a matching function-typed param
        let matching: Vec<&(String, PrimitiveType)> = fn_params
            .iter()
            .filter(|(_, pt)| *pt == elem_prim)
            .collect();
        if matching.is_empty() {
            return None;
        }
        let fn_idx = emit.gen_range(0..matching.len());
        let fn_name = matching[fn_idx].0.clone();

        // Pick an interface method candidate
        let iface_idx = emit.gen_range(0..iface_candidates.len());
        let candidate = iface_candidates[iface_idx].clone();

        let method_call = build_method_call(&candidate, scope, emit);

        let elem_type_name = prim_type_name(elem_prim);
        let filter_info = build_filter(
            &method_call,
            &candidate.return_type,
            elem_prim,
            elem_type_name,
        );
        let (chain, result_type) =
            pick_chain_pattern(&fn_name, &filter_info.predicate, elem_prim, emit);

        let name = scope.fresh_name();
        scope.add_local(name.clone(), result_type, false);

        let chain_stmt = format!("let {} = {}.iter(){}", name, arr_name, chain);

        if filter_info.needs_discard {
            let discard_name = scope.fresh_name();
            scope.add_local(discard_name.clone(), candidate.return_type.clone(), false);
            let discard = format!("let {} = {}", discard_name, method_call);
            let indent = emit.indent_str();
            Some(format!("{}\n{}{}", discard, indent, chain_stmt))
        } else {
            Some(chain_stmt)
        }
    }
}

// ---------------------------------------------------------------------------
// Data types
// ---------------------------------------------------------------------------

/// An interface method candidate with all info needed for code generation.
#[derive(Clone)]
struct IfaceCandidate {
    var_name: String,
    method_name: String,
    method_params: Vec<ParamInfo>,
    return_type: TypeInfo,
}

/// Filter predicate info.
struct FilterInfo {
    predicate: String,
    needs_discard: bool,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Find array-typed variables with i64 or i32 elements.
fn find_prim_arrays(scope: &Scope) -> Vec<(String, PrimitiveType)> {
    scope
        .array_vars()
        .into_iter()
        .filter_map(|(name, elem_ty)| {
            if let TypeInfo::Primitive(prim) = elem_ty {
                if matches!(prim, PrimitiveType::I64 | PrimitiveType::I32) {
                    return Some((name, prim));
                }
            }
            None
        })
        .collect()
}

/// Find function-typed params that are `(PrimType) -> PrimType`.
fn find_fn_params(scope: &Scope) -> Vec<(String, PrimitiveType)> {
    scope
        .params
        .iter()
        .filter_map(|p| {
            if let TypeInfo::Function {
                param_types,
                return_type,
            } = &p.param_type
                && param_types.len() == 1
                && let (TypeInfo::Primitive(pt), TypeInfo::Primitive(rt)) =
                    (&param_types[0], return_type.as_ref())
                && pt == rt
                && matches!(pt, PrimitiveType::I64 | PrimitiveType::I32)
            {
                Some((p.name.clone(), *pt))
            } else {
                None
            }
        })
        .collect()
}

/// Collect interface method candidates from constrained type-param variables.
fn collect_iface_candidates(
    scope: &Scope,
    constrained_vars: &[(String, String, Vec<(ModuleId, SymbolId)>)],
) -> Vec<IfaceCandidate> {
    let mut candidates = Vec::new();
    for (var_name, _tp_name, constraints) in constrained_vars {
        let methods = crate::expr::get_type_param_constraint_methods(scope.table, constraints);
        for (_iface_info, method) in methods {
            candidates.push(IfaceCandidate {
                var_name: var_name.clone(),
                method_name: method.name.clone(),
                method_params: method.params.clone(),
                return_type: method.return_type.clone(),
            });
        }
    }
    candidates
}

/// Build the method call string, generating arguments via `emit.sub_expr`.
fn build_method_call(candidate: &IfaceCandidate, scope: &Scope, emit: &mut Emit) -> String {
    let args = if candidate.method_params.is_empty() {
        String::new()
    } else {
        candidate
            .method_params
            .iter()
            .map(|p| emit.sub_expr(&p.param_type, scope))
            .collect::<Vec<_>>()
            .join(", ")
    };
    format!("{}.{}({})", candidate.var_name, candidate.method_name, args)
}

/// Build the filter predicate based on the method return type.
fn build_filter(
    method_call: &str,
    return_type: &TypeInfo,
    elem_prim: PrimitiveType,
    elem_type_name: &str,
) -> FilterInfo {
    let returns_matching = matches!(
        return_type,
        TypeInfo::Primitive(p) if *p == elem_prim
    );
    let returns_bool = matches!(return_type, TypeInfo::Primitive(PrimitiveType::Bool));
    let needs_discard = !returns_matching && !returns_bool;

    let predicate = if returns_matching {
        format!("(n: {}) => n > {}", elem_type_name, method_call)
    } else if returns_bool {
        format!("(n: {}) => {} || n > 0", elem_type_name, method_call)
    } else {
        format!("(n: {}) => n > 0", elem_type_name)
    };

    FilterInfo {
        predicate,
        needs_discard,
    }
}

/// Pick one of 6 chain patterns and return `(chain_suffix, result_type)`.
fn pick_chain_pattern(
    fn_name: &str,
    filter_pred: &str,
    elem_prim: PrimitiveType,
    emit: &mut Emit,
) -> (String, TypeInfo) {
    let arr_type = TypeInfo::Array(Box::new(TypeInfo::Primitive(elem_prim)));

    match emit.gen_range(0..6) {
        0 => (
            format!(".map({}).filter({}).collect()", fn_name, filter_pred),
            arr_type,
        ),
        1 => (
            format!(".filter({}).map({}).collect()", filter_pred, fn_name),
            arr_type,
        ),
        2 => (
            format!(".map({}).filter({}).count()", fn_name, filter_pred),
            TypeInfo::Primitive(PrimitiveType::I64),
        ),
        3 => (format!(".filter({}).collect()", filter_pred), arr_type),
        4 => (
            format!(".map({}).filter({}).sum()", fn_name, filter_pred),
            TypeInfo::Primitive(elem_prim),
        ),
        _ => {
            let take_n = emit.random_in(1, 3);
            (
                format!(
                    ".map({}).filter({}).take({}).collect()",
                    fn_name, filter_pred, take_n
                ),
                arr_type,
            )
        }
    }
}

fn prim_type_name(prim: PrimitiveType) -> &'static str {
    match prim {
        PrimitiveType::I64 => "i64",
        PrimitiveType::I32 => "i32",
        _ => "i64",
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
        assert_eq!(GenericClosureChain.name(), "generic_closure_chain");
    }

    #[test]
    fn returns_none_without_array() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            GenericClosureChain
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn returns_none_without_fn_param() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "arr".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            GenericClosureChain
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }
}
