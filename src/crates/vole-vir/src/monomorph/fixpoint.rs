// fixpoint.rs
//
// Monomorphization fixpoint loop for VIR.
//
// Scans monomorphized VIR functions for `CallTarget::GenericCall` nodes.
// Each generic call creates a new monomorphization instance (function_id +
// concrete type_args).  The loop runs until no new instances are discovered.

use rustc_hash::{FxHashMap, FxHashSet};
use vole_identity::{FunctionId, VirTypeId};

use crate::calls::CallTarget;
use crate::expr::{VirExpr, VirMetaKind, VirStringPart};
use crate::func::{VirBody, VirFunction};
use crate::program::VirProgram;
use crate::refs::VirRef;
use crate::stmt::VirStmt;

use super::rederive::rederive_decisions;
use super::rewrite::{RewriteCtx, rewrite_function};
use super::substitute::{TypeSubstitution, substitute_types};

/// A monomorphization instance: a generic function + concrete type args.
///
/// Used as a deduplication key so that the same generic function called
/// with the same type arguments produces exactly one monomorphized copy.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MonomorphInstance {
    /// Which generic function to monomorphize.
    pub function_id: FunctionId,
    /// Concrete type arguments for this instantiation.
    pub type_args: Vec<VirTypeId>,
}

/// Result of monomorphization: concrete functions and an instance-to-index
/// mapping for resolving `GenericCall` targets.
pub struct MonomorphResult {
    /// All newly monomorphized concrete functions.
    pub functions: Vec<VirFunction>,
    /// Maps each `MonomorphInstance` to its index within `functions`.
    ///
    /// After the caller appends `functions` to `VirProgram.functions` at
    /// some base offset, it must add that offset to each value to get the
    /// absolute index.
    pub instance_map: FxHashMap<MonomorphInstance, usize>,
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Monomorphize all generic functions reachable from the program's concrete
/// functions, resolving nested generic calls to a fixpoint.
///
/// Algorithm:
/// 1. Collect all `GenericCall` sites from the program's concrete functions.
/// 2. For each unseen instance, look up the generic template, build a
///    substitution map, and produce a concrete function via substitute +
///    rewrite + rederive.
/// 3. Scan newly created functions for further `GenericCall` sites.
/// 4. Repeat until no new instances are discovered.
///
/// Returns the newly created concrete functions.  The caller is responsible
/// for adding them to `VirProgram.functions`.
pub fn monomorphize(program: &mut VirProgram) -> MonomorphResult {
    monomorphize_with_seeds(program, Vec::new())
}

/// Monomorphize with external seeds in addition to scanning concrete functions.
///
/// External seeds are `MonomorphInstance`s injected by the caller (e.g.,
/// derived from the sema monomorph cache) so that VIR monomorphization
/// can produce concrete functions for instances that sema has discovered.
/// The fixpoint loop processes both seeds and `GenericCall` sites found
/// in concrete functions, transitively discovering further instances.
pub fn monomorphize_with_seeds(
    program: &mut VirProgram,
    seeds: Vec<MonomorphInstance>,
) -> MonomorphResult {
    let mut worklist: Vec<MonomorphInstance> = Vec::new();
    let mut seen: FxHashSet<MonomorphInstance> = FxHashSet::default();
    let mut result_functions: Vec<VirFunction> = Vec::new();
    let mut instance_map: FxHashMap<MonomorphInstance, usize> = FxHashMap::default();

    // Seed the worklist from all existing concrete functions.
    for func in &program.functions {
        collect_generic_calls_from_function(func, &mut worklist);
    }

    // Inject external seeds (from sema monomorph cache).
    worklist.extend(seeds);

    while let Some(instance) = worklist.pop() {
        if seen.contains(&instance) {
            continue;
        }
        seen.insert(instance.clone());

        let concrete = monomorphize_one(&instance, program);
        let Some(concrete) = concrete else {
            continue;
        };

        // Scan the newly created function for nested generic calls.
        collect_generic_calls_from_function(&concrete, &mut worklist);
        let idx = result_functions.len();
        instance_map.insert(instance, idx);
        result_functions.push(concrete);
    }

    MonomorphResult {
        functions: result_functions,
        instance_map,
    }
}

// ---------------------------------------------------------------------------
// Single instance monomorphization
// ---------------------------------------------------------------------------

/// Monomorphize a single instance: look up the template, substitute, rewrite,
/// and rederive.
///
/// Returns `None` if the generic template cannot be found (the function_id
/// may refer to a function in a module not yet lowered to VIR).
fn monomorphize_one(instance: &MonomorphInstance, program: &mut VirProgram) -> Option<VirFunction> {
    // Find the generic template.  We need to search generic_functions by
    // FunctionId since GenericCall carries a FunctionId.
    let template = find_generic_template(program, instance.function_id)?;

    // Build substitution map: type_params[i] -> type_args[i].
    let substitution = build_substitution(&template, &instance.type_args);

    // Clone the type table so we can use the original as source and the
    // clone as target.  This is necessary because substitute_types needs
    // &source and &mut target to be separate.
    let mut target_table = program.type_table.clone();
    let type_map = substitute_types(&program.type_table, &mut target_table, &substitution);

    let ctx = RewriteCtx::new(type_map);
    let mut concrete = rewrite_function(&template, &ctx);

    rederive_decisions(&mut concrete, &target_table);

    // Clear type_params on the concrete function (it's no longer generic).
    concrete.type_params = Vec::new();

    // Generate a mangled name for the monomorphized instance.
    concrete.name = format!(
        "{}<{}>",
        template.name,
        instance
            .type_args
            .iter()
            .map(|t| format!("{t:?}"))
            .collect::<Vec<_>>()
            .join(", ")
    );

    // Merge the target table back into the program.
    program.type_table = target_table;

    Some(concrete)
}

/// Find a generic function template by its `FunctionId`.
fn find_generic_template(program: &VirProgram, function_id: FunctionId) -> Option<VirFunction> {
    program
        .generic_functions
        .iter()
        .find(|f| f.id == function_id)
        .cloned()
}

/// Build a type substitution map from a generic template's type_params
/// and the concrete type_args from a `GenericCall`.
fn build_substitution(template: &VirFunction, type_args: &[VirTypeId]) -> TypeSubstitution {
    let mut subs = FxHashMap::default();
    for (param_name, &concrete_ty) in template.type_params.iter().zip(type_args) {
        subs.insert(*param_name, concrete_ty);
    }
    subs
}

// ---------------------------------------------------------------------------
// Generic call collection
// ---------------------------------------------------------------------------

/// Collect all `GenericCall` sites from a single function into the worklist.
fn collect_generic_calls_from_function(func: &VirFunction, worklist: &mut Vec<MonomorphInstance>) {
    collect_from_body(&func.body, worklist);
}

fn collect_from_body(body: &VirBody, out: &mut Vec<MonomorphInstance>) {
    for stmt in &body.stmts {
        collect_from_stmt(stmt, out);
    }
    if let Some(ref trailing) = body.trailing {
        collect_from_expr(trailing, out);
    }
}

fn collect_from_ref(r: &VirRef, out: &mut Vec<MonomorphInstance>) {
    collect_from_expr(r, out);
}

fn collect_from_stmt(stmt: &VirStmt, out: &mut Vec<MonomorphInstance>) {
    match stmt {
        VirStmt::Let { value, .. } => collect_from_ref(value, out),
        VirStmt::LetTuple { value, .. } => collect_from_ref(value, out),
        VirStmt::Assign { target, value } => {
            collect_from_assign_target(target, out);
            collect_from_ref(value, out);
        }
        VirStmt::Expr { value } => collect_from_ref(value, out),
        VirStmt::While { cond, body } => {
            collect_from_ref(cond, out);
            collect_from_body(body, out);
        }
        VirStmt::For(vir_for) => {
            collect_from_ref(&vir_for.iterable, out);
            collect_from_body(&vir_for.body, out);
        }
        VirStmt::Return { value } => {
            if let Some(v) = value {
                collect_from_ref(v, out);
            }
        }
        VirStmt::Break | VirStmt::Continue | VirStmt::Noop => {}
        VirStmt::Raise { fields, .. } => {
            for (_, val) in fields {
                collect_from_ref(val, out);
            }
        }
        VirStmt::RcInc { value } | VirStmt::RcDec { value } => {
            collect_from_ref(value, out);
        }
    }
}

fn collect_from_assign_target(
    target: &crate::stmt::AssignTarget,
    out: &mut Vec<MonomorphInstance>,
) {
    use crate::stmt::AssignTarget;
    match target {
        AssignTarget::Local(_) => {}
        AssignTarget::Field { object, .. } => collect_from_ref(object, out),
        AssignTarget::Index { array, index } => {
            collect_from_ref(array, out);
            collect_from_ref(index, out);
        }
    }
}

/// Walk a VIR expression tree, collecting `GenericCall` instances.
///
/// Delegates to category-specific helpers to stay under the line limit.
fn collect_from_expr(expr: &VirExpr, out: &mut Vec<MonomorphInstance>) {
    match expr {
        // Calls, literals, operators, strings, fields, RC, coercion
        VirExpr::Call { .. }
        | VirExpr::Range { .. }
        | VirExpr::ArrayLiteral { .. }
        | VirExpr::RepeatLiteral { .. }
        | VirExpr::StructLiteral { .. }
        | VirExpr::ClassInstance { .. }
        | VirExpr::BinaryOp { .. }
        | VirExpr::UnaryOp { .. }
        | VirExpr::StringConcat { .. }
        | VirExpr::InterpolatedString { .. }
        | VirExpr::MethodCall { .. }
        | VirExpr::FieldLoad { .. }
        | VirExpr::FieldStore { .. }
        | VirExpr::Index { .. }
        | VirExpr::IndexStore { .. }
        | VirExpr::RcInc { .. }
        | VirExpr::RcDec { .. }
        | VirExpr::RcMove { .. }
        | VirExpr::Coerce { .. } => collect_from_expr_data(expr, out),

        // Control flow, type ops, reflection, variables, lambda,
        // optional, try, yield
        VirExpr::If { .. }
        | VirExpr::Match { .. }
        | VirExpr::Block { .. }
        | VirExpr::IsCheck { .. }
        | VirExpr::AsCast { .. }
        | VirExpr::MetaAccess { .. }
        | VirExpr::LocalLoad { .. }
        | VirExpr::LocalStore { .. }
        | VirExpr::Lambda { .. }
        | VirExpr::NullCoalesce { .. }
        | VirExpr::OptionalChain { .. }
        | VirExpr::OptionalMethodCall { .. }
        | VirExpr::Try { .. }
        | VirExpr::Yield { .. } => collect_from_expr_control(expr, out),

        // Leaf nodes
        VirExpr::IntLiteral { .. }
        | VirExpr::WideLiteral { .. }
        | VirExpr::FloatLiteral { .. }
        | VirExpr::BoolLiteral(_)
        | VirExpr::StringLiteral(_)
        | VirExpr::NilLiteral
        | VirExpr::Unreachable { .. }
        | VirExpr::Import { .. }
        | VirExpr::TypeLiteral => {}
    }
}

/// Collect from data-oriented expressions: calls, literals, operators,
/// strings, fields, RC, coercion.
fn collect_from_expr_data(expr: &VirExpr, out: &mut Vec<MonomorphInstance>) {
    match expr {
        VirExpr::Call { target, args, .. } => {
            if let CallTarget::GenericCall {
                function_id,
                type_args,
            } = target
            {
                out.push(MonomorphInstance {
                    function_id: *function_id,
                    type_args: type_args.clone(),
                });
            }
            for arg in args {
                collect_from_ref(arg, out);
            }
        }
        VirExpr::Range { start, end, .. } => {
            collect_from_ref(start, out);
            collect_from_ref(end, out);
        }
        VirExpr::ArrayLiteral { elements, .. } => {
            for elem in elements {
                collect_from_ref(elem, out);
            }
        }
        VirExpr::RepeatLiteral { element, .. } => collect_from_ref(element, out),
        VirExpr::StructLiteral { fields, .. } | VirExpr::ClassInstance { fields, .. } => {
            for (_, val) in fields {
                collect_from_ref(val, out);
            }
        }
        VirExpr::BinaryOp { lhs, rhs, .. } => {
            collect_from_ref(lhs, out);
            collect_from_ref(rhs, out);
        }
        VirExpr::UnaryOp { operand, .. } => collect_from_ref(operand, out),
        VirExpr::StringConcat { parts } => {
            for part in parts {
                collect_from_ref(part, out);
            }
        }
        VirExpr::InterpolatedString { parts } => {
            for part in parts {
                if let VirStringPart::Expr { value, .. } = part {
                    collect_from_ref(value, out);
                }
            }
        }
        VirExpr::MethodCall { receiver, args, .. } => {
            collect_from_ref(receiver, out);
            for arg in args {
                collect_from_ref(arg, out);
            }
        }
        VirExpr::FieldLoad { object, .. } => collect_from_ref(object, out),
        VirExpr::FieldStore { object, value, .. } => {
            collect_from_ref(object, out);
            collect_from_ref(value, out);
        }
        VirExpr::Index { object, index, .. } => {
            collect_from_ref(object, out);
            collect_from_ref(index, out);
        }
        VirExpr::IndexStore {
            object,
            index,
            value,
            ..
        } => {
            collect_from_ref(object, out);
            collect_from_ref(index, out);
            collect_from_ref(value, out);
        }
        VirExpr::RcInc { value } | VirExpr::RcDec { value } | VirExpr::RcMove { value } => {
            collect_from_ref(value, out)
        }
        VirExpr::Coerce { value, .. } => collect_from_ref(value, out),
        _ => unreachable!("collect_from_expr_data called with wrong variant"),
    }
}

/// Collect from control flow, type ops, reflection, variables, lambda,
/// optional, try, and yield expressions.
fn collect_from_expr_control(expr: &VirExpr, out: &mut Vec<MonomorphInstance>) {
    match expr {
        VirExpr::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            collect_from_ref(cond, out);
            collect_from_body(then_body, out);
            if let Some(eb) = else_body {
                collect_from_body(eb, out);
            }
        }
        VirExpr::Match {
            scrutinee, arms, ..
        } => {
            collect_from_ref(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_from_ref(guard, out);
                }
                collect_from_body(&arm.body, out);
                collect_from_pattern(&arm.pattern, out);
            }
        }
        VirExpr::Block {
            stmts, trailing, ..
        } => {
            for stmt in stmts {
                collect_from_stmt(stmt, out);
            }
            if let Some(t) = trailing {
                collect_from_ref(t, out);
            }
        }
        VirExpr::IsCheck { value, .. } | VirExpr::AsCast { value, .. } => {
            collect_from_ref(value, out)
        }
        VirExpr::MetaAccess { kind, .. } => match kind {
            VirMetaKind::Static { object, .. } => {
                if let Some(obj) = object {
                    collect_from_ref(obj, out);
                }
            }
            VirMetaKind::Dynamic { value } | VirMetaKind::TypeParam { value, .. } => {
                collect_from_ref(value, out)
            }
        },
        VirExpr::LocalLoad { .. } => {}
        VirExpr::LocalStore { value, .. } => collect_from_ref(value, out),
        VirExpr::Lambda { body, .. } => collect_from_body(body, out),
        VirExpr::NullCoalesce { value, default, .. } => {
            collect_from_ref(value, out);
            collect_from_ref(default, out);
        }
        VirExpr::OptionalChain { object, .. } => collect_from_ref(object, out),
        VirExpr::OptionalMethodCall {
            object,
            method_args,
            ..
        } => {
            collect_from_ref(object, out);
            for arg in method_args {
                collect_from_ref(arg, out);
            }
        }
        VirExpr::Try { value, .. } | VirExpr::Yield { value } => collect_from_ref(value, out),
        _ => unreachable!("collect_from_expr_control called with wrong variant"),
    }
}

fn collect_from_pattern(pat: &crate::expr::VirPattern, out: &mut Vec<MonomorphInstance>) {
    use crate::expr::VirPattern;
    match pat {
        VirPattern::Wildcard
        | VirPattern::Binding { .. }
        | VirPattern::Val { .. }
        | VirPattern::Error { .. } => {}
        VirPattern::TypeCheck { .. } => {}
        VirPattern::Literal { value, .. } => collect_from_ref(value, out),
        VirPattern::Success { inner, .. } => {
            if let Some(p) = inner {
                collect_from_pattern(p, out);
            }
        }
        VirPattern::Tuple { bindings } => {
            for b in bindings {
                collect_from_pattern(&b.pattern, out);
            }
        }
        VirPattern::Record { fields, .. } => {
            let _ = fields; // Field patterns are simple bindings.
        }
    }
}

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::func::VirBody;
    use crate::type_table::VirTypeTable;
    use crate::types::VirType;
    use vole_identity::{FunctionId, NameId, Symbol, VirTypeId};

    fn name(n: u32) -> NameId {
        NameId::new_for_test(n)
    }

    fn type_id(n: u32) -> VirTypeId {
        VirTypeId::from_raw(n)
    }

    fn sym(n: u32) -> Symbol {
        Symbol::new_for_test(n)
    }

    /// Build a generic function template: fn identity<T>(x: T) -> T { x }
    fn build_identity_template(
        func_id: FunctionId,
        t_name: NameId,
        param_vir_ty: VirTypeId,
    ) -> VirFunction {
        VirFunction {
            id: func_id,
            name: "identity".to_string(),
            params: vec![(sym(1), type_id(10), param_vir_ty)],
            return_type: type_id(10),
            vir_return_type: param_vir_ty,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::LocalLoad {
                    name: sym(1),
                    ty: type_id(10),
                    vir_ty: param_vir_ty,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: vec![t_name],
        }
    }

    /// Build a concrete function that calls a generic function.
    fn build_caller(
        generic_func_id: FunctionId,
        call_type_args: Vec<VirTypeId>,
        result_vir_ty: VirTypeId,
    ) -> VirFunction {
        VirFunction {
            id: FunctionId::new(100),
            name: "caller".to_string(),
            params: vec![],
            return_type: type_id(20),
            vir_return_type: result_vir_ty,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::Call {
                    target: CallTarget::GenericCall {
                        function_id: generic_func_id,
                        type_args: call_type_args,
                    },
                    args: vec![Box::new(VirExpr::IntLiteral {
                        value: 42,
                        ty: type_id(10),
                        vir_ty: VirTypeId::I64,
                    })],
                    ty: type_id(20),
                    vir_ty: result_vir_ty,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        }
    }

    fn build_minimal_program(
        functions: Vec<VirFunction>,
        generic_functions: Vec<VirFunction>,
    ) -> VirProgram {
        let mut generic_map = FxHashMap::default();
        for (i, gf) in generic_functions.iter().enumerate() {
            generic_map.insert(NameId::new_for_test(gf.id.index()), i);
        }
        let mut function_map = FxHashMap::default();
        for (i, f) in functions.iter().enumerate() {
            function_map.insert(f.id, i);
        }
        VirProgram {
            type_table: VirTypeTable::new(),
            functions,
            monomorph_map: FxHashMap::default(),
            function_map,
            method_map: FxHashMap::default(),
            generic_functions,
            generic_map,
            tests: Vec::new(),
            global_inits: FxHashMap::default(),
            module_global_inits: FxHashMap::default(),
            vir_monomorph_base: usize::MAX,
        }
    }

    #[test]
    fn collect_no_generic_calls() {
        let func = VirFunction {
            id: FunctionId::new(1),
            name: "no_calls".to_string(),
            params: vec![],
            return_type: type_id(10),
            vir_return_type: VirTypeId::I64,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::IntLiteral {
                    value: 42,
                    ty: type_id(10),
                    vir_ty: VirTypeId::I64,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let mut calls = Vec::new();
        collect_generic_calls_from_function(&func, &mut calls);
        assert!(calls.is_empty());
    }

    #[test]
    fn collect_single_generic_call() {
        let func = build_caller(FunctionId::new(42), vec![VirTypeId::I64], VirTypeId::I64);
        let mut calls = Vec::new();
        collect_generic_calls_from_function(&func, &mut calls);

        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].function_id, FunctionId::new(42));
        assert_eq!(calls[0].type_args, vec![VirTypeId::I64]);
    }

    #[test]
    fn collect_generic_calls_in_nested_if() {
        let func = VirFunction {
            id: FunctionId::new(1),
            name: "nested".to_string(),
            params: vec![],
            return_type: type_id(10),
            vir_return_type: VirTypeId::I64,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::If {
                    cond: Box::new(VirExpr::BoolLiteral(true)),
                    then_body: VirBody {
                        stmts: vec![],
                        trailing: Some(Box::new(VirExpr::Call {
                            target: CallTarget::GenericCall {
                                function_id: FunctionId::new(10),
                                type_args: vec![VirTypeId::I64],
                            },
                            args: vec![],
                            ty: type_id(10),
                            vir_ty: VirTypeId::I64,
                        })),
                    },
                    else_body: Some(VirBody {
                        stmts: vec![],
                        trailing: Some(Box::new(VirExpr::Call {
                            target: CallTarget::GenericCall {
                                function_id: FunctionId::new(20),
                                type_args: vec![VirTypeId::STRING],
                            },
                            args: vec![],
                            ty: type_id(10),
                            vir_ty: VirTypeId::STRING,
                        })),
                    }),
                    ty: type_id(10),
                    vir_ty: VirTypeId::I64,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let mut calls = Vec::new();
        collect_generic_calls_from_function(&func, &mut calls);

        assert_eq!(calls.len(), 2);
        assert_eq!(calls[0].function_id, FunctionId::new(10));
        assert_eq!(calls[1].function_id, FunctionId::new(20));
    }

    #[test]
    fn collect_generic_calls_in_lambda() {
        let func = VirFunction {
            id: FunctionId::new(1),
            name: "with_lambda".to_string(),
            params: vec![],
            return_type: type_id(10),
            vir_return_type: VirTypeId::VOID,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::Lambda {
                    params: vec![sym(1)],
                    body: VirBody {
                        stmts: vec![],
                        trailing: Some(Box::new(VirExpr::Call {
                            target: CallTarget::GenericCall {
                                function_id: FunctionId::new(77),
                                type_args: vec![VirTypeId::F64],
                            },
                            args: vec![],
                            ty: type_id(10),
                            vir_ty: VirTypeId::F64,
                        })),
                    },
                    captures: vec![],
                    ty: type_id(20),
                    vir_ty: VirTypeId::VOID,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let mut calls = Vec::new();
        collect_generic_calls_from_function(&func, &mut calls);

        assert_eq!(calls.len(), 1);
        assert_eq!(calls[0].function_id, FunctionId::new(77));
        assert_eq!(calls[0].type_args, vec![VirTypeId::F64]);
    }

    #[test]
    fn build_substitution_single_param() {
        let t_name = name(100);
        let template = VirFunction {
            id: FunctionId::new(1),
            name: "f".to_string(),
            params: vec![],
            return_type: type_id(10),
            vir_return_type: VirTypeId::VOID,
            body: VirBody {
                stmts: vec![],
                trailing: None,
            },
            mangled_name_id: None,
            method_id: None,
            type_params: vec![t_name],
        };

        let subs = build_substitution(&template, &[VirTypeId::I64]);
        assert_eq!(subs.len(), 1);
        assert_eq!(subs[&t_name], VirTypeId::I64);
    }

    #[test]
    fn build_substitution_multiple_params() {
        let t_name = name(100);
        let u_name = name(200);
        let template = VirFunction {
            id: FunctionId::new(1),
            name: "f".to_string(),
            params: vec![],
            return_type: type_id(10),
            vir_return_type: VirTypeId::VOID,
            body: VirBody {
                stmts: vec![],
                trailing: None,
            },
            mangled_name_id: None,
            method_id: None,
            type_params: vec![t_name, u_name],
        };

        let subs = build_substitution(&template, &[VirTypeId::I64, VirTypeId::STRING]);
        assert_eq!(subs.len(), 2);
        assert_eq!(subs[&t_name], VirTypeId::I64);
        assert_eq!(subs[&u_name], VirTypeId::STRING);
    }

    #[test]
    fn monomorphize_one_simple_identity() {
        let t_name = name(100);
        let generic_id = FunctionId::new(1);

        // Build a type table with the Param type.
        let mut type_table = VirTypeTable::new();
        let param_vir_ty = type_table.intern(VirType::Param { name: t_name }, None);

        let template = build_identity_template(generic_id, t_name, param_vir_ty);

        let mut program = build_minimal_program(vec![], vec![template]);
        program.type_table = type_table;

        let instance = MonomorphInstance {
            function_id: generic_id,
            type_args: vec![VirTypeId::I64],
        };

        let result = monomorphize_one(&instance, &mut program);
        assert!(result.is_some());

        let concrete = result.unwrap();
        // type_params should be cleared.
        assert!(concrete.type_params.is_empty());
        // The VIR return type should be I64.
        assert_eq!(concrete.vir_return_type, VirTypeId::I64);
        // The param's vir_ty should be I64.
        assert_eq!(concrete.params[0].2, VirTypeId::I64);
    }

    #[test]
    fn monomorphize_one_missing_template_returns_none() {
        let mut program = build_minimal_program(vec![], vec![]);

        let instance = MonomorphInstance {
            function_id: FunctionId::new(999),
            type_args: vec![VirTypeId::I64],
        };

        assert!(monomorphize_one(&instance, &mut program).is_none());
    }

    #[test]
    fn deduplication_same_instance_not_processed_twice() {
        let t_name = name(100);
        let generic_id = FunctionId::new(1);

        let mut type_table = VirTypeTable::new();
        let param_vir_ty = type_table.intern(VirType::Param { name: t_name }, None);

        let template = build_identity_template(generic_id, t_name, param_vir_ty);

        // Two callers calling the same generic with the same type args.
        let caller1 = build_caller(generic_id, vec![VirTypeId::I64], VirTypeId::I64);
        let caller2 = VirFunction {
            id: FunctionId::new(101),
            name: "caller2".to_string(),
            ..build_caller(generic_id, vec![VirTypeId::I64], VirTypeId::I64)
        };

        let mut program = build_minimal_program(vec![caller1, caller2], vec![template]);
        program.type_table = type_table;

        let result = monomorphize(&mut program);
        // Should produce exactly 1 monomorphized function, not 2.
        assert_eq!(result.functions.len(), 1);
    }

    #[test]
    fn different_type_args_produce_separate_instances() {
        let t_name = name(100);
        let generic_id = FunctionId::new(1);

        let mut type_table = VirTypeTable::new();
        let param_vir_ty = type_table.intern(VirType::Param { name: t_name }, None);

        let template = build_identity_template(generic_id, t_name, param_vir_ty);

        // Two callers with different type args.
        let caller1 = build_caller(generic_id, vec![VirTypeId::I64], VirTypeId::I64);
        let caller2 = VirFunction {
            id: FunctionId::new(101),
            name: "caller2".to_string(),
            ..build_caller(generic_id, vec![VirTypeId::STRING], VirTypeId::STRING)
        };

        let mut program = build_minimal_program(vec![caller1, caller2], vec![template]);
        program.type_table = type_table;

        let result = monomorphize(&mut program);
        // Should produce 2 monomorphized functions.
        assert_eq!(result.functions.len(), 2);
    }

    #[test]
    fn nested_generic_calls_reach_fixpoint() {
        let t_name = name(100);
        let inner_id = FunctionId::new(1);
        let outer_id = FunctionId::new(2);

        let mut type_table = VirTypeTable::new();
        let param_vir_ty = type_table.intern(VirType::Param { name: t_name }, None);

        // Inner generic: fn inner<T>(x: T) -> T { x }
        let inner_template = build_identity_template(inner_id, t_name, param_vir_ty);

        // Outer generic: fn outer<T>(x: T) -> T { inner<T>(x) }
        // This calls inner with the same type param -- after outer is
        // monomorphized with T=I64, the inner call becomes inner<I64>.
        let outer_template = VirFunction {
            id: outer_id,
            name: "outer".to_string(),
            params: vec![(sym(1), type_id(10), param_vir_ty)],
            return_type: type_id(10),
            vir_return_type: param_vir_ty,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::Call {
                    target: CallTarget::GenericCall {
                        function_id: inner_id,
                        type_args: vec![param_vir_ty],
                    },
                    args: vec![Box::new(VirExpr::LocalLoad {
                        name: sym(1),
                        ty: type_id(10),
                        vir_ty: param_vir_ty,
                    })],
                    ty: type_id(10),
                    vir_ty: param_vir_ty,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: vec![t_name],
        };

        // Concrete caller: calls outer<I64>.
        let caller = build_caller(outer_id, vec![VirTypeId::I64], VirTypeId::I64);

        let mut program = build_minimal_program(vec![caller], vec![inner_template, outer_template]);
        program.type_table = type_table;

        let result = monomorphize(&mut program);

        // Should produce 2 monomorphized functions:
        // outer<...> and identity<...> (discovered from outer's body).
        assert_eq!(result.functions.len(), 2);

        // Verify that identity<I64> (the inner monomorph) has concrete types.
        let inner_mono = result
            .functions
            .iter()
            .find(|f| f.name.starts_with("identity"))
            .expect("should find identity monomorph");
        assert_eq!(inner_mono.vir_return_type, VirTypeId::I64);
        assert!(inner_mono.type_params.is_empty());
    }

    #[test]
    fn fixpoint_terminates_with_no_generic_calls() {
        let func = VirFunction {
            id: FunctionId::new(1),
            name: "concrete".to_string(),
            params: vec![],
            return_type: type_id(10),
            vir_return_type: VirTypeId::I64,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::IntLiteral {
                    value: 42,
                    ty: type_id(10),
                    vir_ty: VirTypeId::I64,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let mut program = build_minimal_program(vec![func], vec![]);
        let result = monomorphize(&mut program);
        assert!(result.functions.is_empty());
    }
}
