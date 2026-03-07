// resolve.rs
//
// Post-monomorphization pass: resolve `CallTarget::GenericCall` and
// `CallTarget::Unresolved` (with monomorph keys) in concrete functions
// to `CallTarget::VirDirect` using the instance map built during
// monomorphization.

use rustc_hash::FxHashMap;

use crate::calls::CallTarget;
use crate::entity_metadata::VirEntityMetadata;
use crate::expr::{VirExpr, VirMetaKind, VirStringPart};
use crate::func::{VirBody, VirFunction};
use crate::refs::VirRef;
use crate::stmt::VirStmt;

use super::fixpoint::MonomorphInstance;

/// Mapping from `MonomorphInstance` to absolute index in `VirProgram.functions`.
pub type InstanceIndex = FxHashMap<MonomorphInstance, usize>;

/// Context for resolving call targets after monomorphization.
///
/// Wraps the `InstanceIndex` plus optional entity metadata for resolving
/// `Unresolved` calls whose `monomorph_key` identifies the generic function
/// by `NameId` rather than `FunctionId`.
struct ResolveCtx<'a> {
    /// Instance index: maps `(FunctionId, type_args)` to function index.
    /// Used for `GenericCall` resolution and for `Unresolved` resolution.
    index: &'a InstanceIndex,
    /// Entity metadata for `NameId -> FunctionId` resolution.
    /// `None` when only `GenericCall` resolution is needed.
    entity_metadata: Option<&'a VirEntityMetadata>,
}

/// Resolve all `CallTarget::GenericCall` in the given functions to
/// `CallTarget::VirDirect` using the instance index.
///
/// Any `GenericCall` whose `(function_id, type_args)` is found in the index
/// is rewritten to `VirDirect { function_index }`.  Unresolved calls (e.g.,
/// for templates not yet in VIR) are left as `GenericCall` -- codegen will
/// never see them because those functions are generic templates, not concrete
/// functions compiled by codegen.
pub fn resolve_generic_calls(functions: &mut [VirFunction], index: &InstanceIndex) {
    let ctx = ResolveCtx {
        index,
        entity_metadata: None,
    };
    for func in functions.iter_mut() {
        resolve_in_body(&mut func.body, &ctx);
    }
}

/// Resolve both `GenericCall` and `Unresolved` (with monomorph key) call
/// targets to `VirDirect`.
///
/// For `Unresolved` calls with monomorph keys, converts the key's
/// `func_name: NameId` to `FunctionId` via entity metadata, then looks up
/// `MonomorphInstance` in the instance index.  Only resolves calls whose
/// targets were produced by VIR monomorphization (present in the instance
/// index).  Functions monomorphized by the sema fallback path are not in
/// the instance index and remain `Unresolved` for codegen to handle.
pub fn resolve_all_calls(
    functions: &mut [VirFunction],
    index: &InstanceIndex,
    entity_metadata: &VirEntityMetadata,
) {
    let ctx = ResolveCtx {
        index,
        entity_metadata: Some(entity_metadata),
    };
    for func in functions.iter_mut() {
        resolve_in_body(&mut func.body, &ctx);
    }
}

fn resolve_in_body(body: &mut VirBody, ctx: &ResolveCtx<'_>) {
    for stmt in &mut body.stmts {
        resolve_in_stmt(stmt, ctx);
    }
    if let Some(ref mut trailing) = body.trailing {
        resolve_in_ref(trailing, ctx);
    }
}

fn resolve_in_ref(r: &mut VirRef, ctx: &ResolveCtx<'_>) {
    resolve_in_expr(r, ctx);
}

fn resolve_in_stmt(stmt: &mut VirStmt, ctx: &ResolveCtx<'_>) {
    match stmt {
        VirStmt::Let { value, .. } => resolve_in_ref(value, ctx),
        VirStmt::LetTuple { value, .. } => resolve_in_ref(value, ctx),
        VirStmt::Assign { target, value } => {
            resolve_in_assign_target(target, ctx);
            resolve_in_ref(value, ctx);
        }
        VirStmt::Expr { value } => resolve_in_ref(value, ctx),
        VirStmt::While { cond, body } => {
            resolve_in_ref(cond, ctx);
            resolve_in_body(body, ctx);
        }
        VirStmt::For(vir_for) => {
            resolve_in_ref(&mut vir_for.iterable, ctx);
            resolve_in_body(&mut vir_for.body, ctx);
        }
        VirStmt::Return { value, .. } => {
            if let Some(v) = value {
                resolve_in_ref(v, ctx);
            }
        }
        VirStmt::Break | VirStmt::Continue | VirStmt::Noop => {}
        VirStmt::Raise { fields, .. } => {
            for (_, val) in fields {
                resolve_in_ref(val, ctx);
            }
        }
        VirStmt::RcInc { value, .. } | VirStmt::RcDec { value, .. } => {
            resolve_in_ref(value, ctx);
        }
    }
}

fn resolve_in_assign_target(target: &mut crate::stmt::AssignTarget, ctx: &ResolveCtx<'_>) {
    use crate::stmt::AssignTarget;
    match target {
        AssignTarget::Local(_) => {}
        AssignTarget::Field { object, .. } => resolve_in_ref(object, ctx),
        AssignTarget::Index { array, index } => {
            resolve_in_ref(array, ctx);
            resolve_in_ref(index, ctx);
        }
    }
}

/// Walk a VIR expression tree, resolving call targets in place.
///
/// Delegates to category-specific helpers to stay under the line limit.
fn resolve_in_expr(expr: &mut VirExpr, ctx: &ResolveCtx<'_>) {
    match expr {
        // Calls, data, operators, strings, fields, RC, coercion
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
        | VirExpr::Coerce { .. } => resolve_in_expr_data(expr, ctx),

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
        | VirExpr::Yield { .. } => resolve_in_expr_control(expr, ctx),

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

/// Resolve in data-oriented expressions: calls, literals, operators,
/// strings, fields, RC, coercion.
fn resolve_in_expr_data(expr: &mut VirExpr, ctx: &ResolveCtx<'_>) {
    match expr {
        VirExpr::Call { target, args, .. } => {
            resolve_call_target(target, ctx);
            for arg in args {
                resolve_in_ref(arg, ctx);
            }
        }
        VirExpr::Range { start, end, .. } => {
            resolve_in_ref(start, ctx);
            resolve_in_ref(end, ctx);
        }
        VirExpr::ArrayLiteral { elements, .. } => {
            for elem in elements {
                resolve_in_ref(elem, ctx);
            }
        }
        VirExpr::RepeatLiteral { element, .. } => resolve_in_ref(element, ctx),
        VirExpr::StructLiteral { fields, .. } | VirExpr::ClassInstance { fields, .. } => {
            for (_, val) in fields {
                resolve_in_ref(val, ctx);
            }
        }
        VirExpr::BinaryOp { lhs, rhs, .. } => {
            resolve_in_ref(lhs, ctx);
            resolve_in_ref(rhs, ctx);
        }
        VirExpr::UnaryOp { operand, .. } => resolve_in_ref(operand, ctx),
        VirExpr::StringConcat { parts } => {
            for part in parts {
                resolve_in_ref(part, ctx);
            }
        }
        VirExpr::InterpolatedString { parts } => {
            for part in parts {
                if let VirStringPart::Expr { value, .. } = part {
                    resolve_in_ref(value, ctx);
                }
            }
        }
        VirExpr::MethodCall { receiver, args, .. } => {
            resolve_in_ref(receiver, ctx);
            for arg in args {
                resolve_in_ref(arg, ctx);
            }
        }
        VirExpr::FieldLoad { object, .. } => resolve_in_ref(object, ctx),
        VirExpr::FieldStore { object, value, .. } => {
            resolve_in_ref(object, ctx);
            resolve_in_ref(value, ctx);
        }
        VirExpr::Index {
            object, index: idx, ..
        } => {
            resolve_in_ref(object, ctx);
            resolve_in_ref(idx, ctx);
        }
        VirExpr::IndexStore {
            object,
            index: idx,
            value,
            ..
        } => {
            resolve_in_ref(object, ctx);
            resolve_in_ref(idx, ctx);
            resolve_in_ref(value, ctx);
        }
        VirExpr::RcInc { value, .. } | VirExpr::RcDec { value, .. } | VirExpr::RcMove { value } => {
            resolve_in_ref(value, ctx)
        }
        VirExpr::Coerce { value, .. } => resolve_in_ref(value, ctx),
        _ => {}
    }
}

/// Resolve in control flow, type ops, reflection, variables, lambda,
/// optional, try, and yield expressions.
fn resolve_in_expr_control(expr: &mut VirExpr, ctx: &ResolveCtx<'_>) {
    match expr {
        VirExpr::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            resolve_in_ref(cond, ctx);
            resolve_in_body(then_body, ctx);
            if let Some(eb) = else_body {
                resolve_in_body(eb, ctx);
            }
        }
        VirExpr::Match {
            scrutinee, arms, ..
        } => {
            resolve_in_ref(scrutinee, ctx);
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    resolve_in_ref(guard, ctx);
                }
                resolve_in_body(&mut arm.body, ctx);
                resolve_in_pattern(&mut arm.pattern, ctx);
            }
        }
        VirExpr::Block {
            stmts, trailing, ..
        } => {
            for stmt in stmts {
                resolve_in_stmt(stmt, ctx);
            }
            if let Some(t) = trailing {
                resolve_in_ref(t, ctx);
            }
        }
        VirExpr::IsCheck { value, .. } | VirExpr::AsCast { value, .. } => {
            resolve_in_ref(value, ctx);
        }
        VirExpr::MetaAccess { kind, .. } => match kind {
            VirMetaKind::Static { object, .. } => {
                if let Some(obj) = object {
                    resolve_in_ref(obj, ctx);
                }
            }
            VirMetaKind::Dynamic { value } | VirMetaKind::TypeParam { value, .. } => {
                resolve_in_ref(value, ctx);
            }
        },
        VirExpr::LocalLoad { .. } => {}
        VirExpr::LocalStore { value, .. } => resolve_in_ref(value, ctx),
        VirExpr::Lambda { body, .. } => resolve_in_body(body, ctx),
        VirExpr::NullCoalesce { value, default, .. } => {
            resolve_in_ref(value, ctx);
            resolve_in_ref(default, ctx);
        }
        VirExpr::OptionalChain { object, .. } => resolve_in_ref(object, ctx),
        VirExpr::OptionalMethodCall {
            object,
            method_args,
            ..
        } => {
            resolve_in_ref(object, ctx);
            for arg in method_args {
                resolve_in_ref(arg, ctx);
            }
        }
        VirExpr::Try { value, .. } | VirExpr::Yield { value } => {
            resolve_in_ref(value, ctx);
        }
        _ => {}
    }
}

fn resolve_in_pattern(pat: &mut crate::expr::VirPattern, ctx: &ResolveCtx<'_>) {
    use crate::expr::VirPattern;
    match pat {
        VirPattern::Wildcard
        | VirPattern::Binding { .. }
        | VirPattern::Val { .. }
        | VirPattern::Error { .. }
        | VirPattern::TypeCheck { .. } => {}
        VirPattern::Literal { value, .. } => resolve_in_ref(value, ctx),
        VirPattern::Success { inner, .. } => {
            if let Some(p) = inner {
                resolve_in_pattern(p, ctx);
            }
        }
        VirPattern::Tuple { bindings } => {
            for b in bindings {
                resolve_in_pattern(&mut b.pattern, ctx);
            }
        }
        VirPattern::Record { .. } => {}
    }
}

/// Resolve a single `CallTarget` in place.
///
/// Handles two cases:
/// 1. `GenericCall { function_id, type_args }` -- looks up `(function_id, type_args)`
///    in the instance index and replaces with `VirDirect` if found.
/// 2. `Unresolved { monomorph_key: Some(...) }` -- converts `func_name -> FunctionId`
///    via entity metadata, then looks up `MonomorphInstance` in the instance index.
///    Only resolves when the target is a VIR-monomorphized function (in the index).
///    Functions monomorphized by the sema fallback path are not in the instance
///    index and remain `Unresolved` for codegen to handle via `call_dispatch()`.
fn resolve_call_target(target: &mut CallTarget, ctx: &ResolveCtx<'_>) {
    match target {
        CallTarget::GenericCall {
            function_id,
            type_args,
        } => {
            let instance = MonomorphInstance {
                function_id: *function_id,
                type_args: type_args.clone(),
            };
            if let Some(&func_idx) = ctx.index.get(&instance) {
                *target = CallTarget::VirDirect {
                    function_index: func_idx,
                };
            }
        }
        CallTarget::Unresolved {
            monomorph_key: Some(key),
            ..
        } => {
            if let Some(entity_metadata) = ctx.entity_metadata
                && let Some(function_id) = entity_metadata.function_by_name(key.func_name)
            {
                let instance = MonomorphInstance {
                    function_id,
                    type_args: key.type_keys.clone(),
                };
                if let Some(&func_idx) = ctx.index.get(&instance) {
                    *target = CallTarget::VirDirect {
                        function_index: func_idx,
                    };
                }
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::calls::CallTarget;
    use crate::expr::VirExpr;
    use crate::func::{VirBody, VirFunction};
    use vole_identity::{FunctionId, MonomorphKey, NameId, NodeId, Symbol, VirTypeId};

    fn type_id(n: u32) -> VirTypeId {
        VirTypeId::from_raw(n)
    }

    fn sym(n: u32) -> Symbol {
        Symbol::new_for_test(n)
    }

    fn name(n: u32) -> NameId {
        NameId::new_for_test(n)
    }

    #[test]
    fn resolve_generic_call_to_vir_direct() {
        let generic_id = FunctionId::new(42);
        let mut func = VirFunction {
            id: FunctionId::new(1),
            name: "caller".to_string(),
            params: vec![],
            return_type: type_id(10),
            vir_return_type: VirTypeId::I64,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::Call {
                    target: CallTarget::GenericCall {
                        function_id: generic_id,
                        type_args: vec![VirTypeId::I64],
                    },
                    args: vec![],
                    ty: type_id(10),
                    vir_ty: VirTypeId::I64,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let mut index = InstanceIndex::default();
        index.insert(
            MonomorphInstance {
                function_id: generic_id,
                type_args: vec![VirTypeId::I64],
            },
            7,
        );

        resolve_generic_calls(std::slice::from_mut(&mut func), &index);

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::Call { target, .. } => match target {
                CallTarget::VirDirect { function_index } => {
                    assert_eq!(*function_index, 7);
                }
                other => panic!("expected VirDirect, got {other:?}"),
            },
            other => panic!("expected Call, got {other:?}"),
        }
    }

    #[test]
    fn unresolved_generic_call_left_as_is() {
        let generic_id = FunctionId::new(42);
        let mut func = VirFunction {
            id: FunctionId::new(1),
            name: "caller".to_string(),
            params: vec![],
            return_type: type_id(10),
            vir_return_type: VirTypeId::I64,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::Call {
                    target: CallTarget::GenericCall {
                        function_id: generic_id,
                        type_args: vec![VirTypeId::STRING],
                    },
                    args: vec![],
                    ty: type_id(10),
                    vir_ty: VirTypeId::I64,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        // Empty index -- no instances registered.
        let index = InstanceIndex::default();
        resolve_generic_calls(std::slice::from_mut(&mut func), &index);

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::Call { target, .. } => {
                assert!(
                    matches!(target, CallTarget::GenericCall { .. }),
                    "expected GenericCall to remain, got {target:?}"
                );
            }
            other => panic!("expected Call, got {other:?}"),
        }
    }

    #[test]
    fn resolve_nested_in_if_body() {
        let generic_id = FunctionId::new(10);
        let mut func = VirFunction {
            id: FunctionId::new(1),
            name: "nested".to_string(),
            params: vec![],
            return_type: type_id(10),
            vir_return_type: VirTypeId::I64,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::If {
                    cond: Box::new(VirExpr::BoolLiteral(true)),
                    then_body: VirBody {
                        stmts: vec![],
                        trailing: Some(Box::new(VirExpr::Call {
                            target: CallTarget::GenericCall {
                                function_id: generic_id,
                                type_args: vec![VirTypeId::I64],
                            },
                            args: vec![],
                            ty: type_id(10),
                            vir_ty: VirTypeId::I64,
                        })),
                    },
                    else_body: None,
                    ty: type_id(10),
                    vir_ty: VirTypeId::I64,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let mut index = InstanceIndex::default();
        index.insert(
            MonomorphInstance {
                function_id: generic_id,
                type_args: vec![VirTypeId::I64],
            },
            99,
        );

        resolve_generic_calls(std::slice::from_mut(&mut func), &index);

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::If { then_body, .. } => {
                let inner = then_body.trailing.as_ref().unwrap();
                match inner.as_ref() {
                    VirExpr::Call { target, .. } => match target {
                        CallTarget::VirDirect { function_index } => {
                            assert_eq!(*function_index, 99);
                        }
                        other => panic!("expected VirDirect, got {other:?}"),
                    },
                    other => panic!("expected Call, got {other:?}"),
                }
            }
            other => panic!("expected If, got {other:?}"),
        }
    }

    #[test]
    fn resolve_in_lambda_body() {
        let generic_id = FunctionId::new(77);
        let mut func = VirFunction {
            id: FunctionId::new(1),
            name: "with_lambda".to_string(),
            params: vec![],
            return_type: type_id(10),
            vir_return_type: VirTypeId::VOID,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::Lambda {
                    params: vec![sym(1)],
                    body: VirBody {
                        stmts: vec![],
                        trailing: Some(Box::new(VirExpr::Call {
                            target: CallTarget::GenericCall {
                                function_id: generic_id,
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

        let mut index = InstanceIndex::default();
        index.insert(
            MonomorphInstance {
                function_id: generic_id,
                type_args: vec![VirTypeId::F64],
            },
            42,
        );

        resolve_generic_calls(std::slice::from_mut(&mut func), &index);

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::Lambda { body, .. } => {
                let inner = body.trailing.as_ref().unwrap();
                match inner.as_ref() {
                    VirExpr::Call { target, .. } => match target {
                        CallTarget::VirDirect { function_index } => {
                            assert_eq!(*function_index, 42);
                        }
                        other => panic!("expected VirDirect, got {other:?}"),
                    },
                    other => panic!("expected Call, got {other:?}"),
                }
            }
            other => panic!("expected Lambda, got {other:?}"),
        }
    }

    #[test]
    fn resolve_unresolved_with_monomorph_key_to_vir_direct() {
        let generic_id = FunctionId::new(42);
        let func_name_id = name(100);

        let mut func = VirFunction {
            id: FunctionId::new(1),
            name: "caller".to_string(),
            params: vec![],
            return_type: type_id(10),
            vir_return_type: VirTypeId::I64,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::Call {
                    target: CallTarget::Unresolved {
                        callee_sym: sym(1),
                        call_node_id: NodeId::new_for_test(1),
                        line: 1,
                        resolved_call_args: None,
                        lambda_defaults: None,
                        monomorph_key: Some(MonomorphKey::new(func_name_id, vec![VirTypeId::I64])),
                    },
                    args: vec![],
                    ty: type_id(10),
                    vir_ty: VirTypeId::I64,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let mut index = InstanceIndex::default();
        index.insert(
            MonomorphInstance {
                function_id: generic_id,
                type_args: vec![VirTypeId::I64],
            },
            5,
        );

        // Build entity metadata with the func_name -> function_id mapping.
        let mut entity_metadata = VirEntityMetadata::new();
        entity_metadata.insert_function_by_name(func_name_id, generic_id);

        resolve_all_calls(std::slice::from_mut(&mut func), &index, &entity_metadata);

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::Call { target, .. } => match target {
                CallTarget::VirDirect { function_index } => {
                    assert_eq!(*function_index, 5);
                }
                other => panic!("expected VirDirect, got {other:?}"),
            },
            other => panic!("expected Call, got {other:?}"),
        }
    }

    #[test]
    fn unresolved_without_monomorph_key_left_as_is() {
        let mut func = VirFunction {
            id: FunctionId::new(1),
            name: "caller".to_string(),
            params: vec![],
            return_type: type_id(10),
            vir_return_type: VirTypeId::I64,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::Call {
                    target: CallTarget::Unresolved {
                        callee_sym: sym(1),
                        call_node_id: NodeId::new_for_test(1),
                        line: 1,
                        resolved_call_args: None,
                        lambda_defaults: None,
                        monomorph_key: None,
                    },
                    args: vec![],
                    ty: type_id(10),
                    vir_ty: VirTypeId::I64,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        let index = InstanceIndex::default();
        let entity_metadata = VirEntityMetadata::new();
        resolve_all_calls(std::slice::from_mut(&mut func), &index, &entity_metadata);

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::Call { target, .. } => {
                assert!(
                    matches!(target, CallTarget::Unresolved { .. }),
                    "expected Unresolved to remain, got {target:?}"
                );
            }
            other => panic!("expected Call, got {other:?}"),
        }
    }

    #[test]
    fn unresolved_with_unknown_func_name_left_as_is() {
        let func_name_id = name(999);

        let mut func = VirFunction {
            id: FunctionId::new(1),
            name: "caller".to_string(),
            params: vec![],
            return_type: type_id(10),
            vir_return_type: VirTypeId::I64,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::Call {
                    target: CallTarget::Unresolved {
                        callee_sym: sym(1),
                        call_node_id: NodeId::new_for_test(1),
                        line: 1,
                        resolved_call_args: None,
                        lambda_defaults: None,
                        monomorph_key: Some(MonomorphKey::new(func_name_id, vec![VirTypeId::I64])),
                    },
                    args: vec![],
                    ty: type_id(10),
                    vir_ty: VirTypeId::I64,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        // Entity metadata has no function for name 999.
        let index = InstanceIndex::default();
        let entity_metadata = VirEntityMetadata::new();
        resolve_all_calls(std::slice::from_mut(&mut func), &index, &entity_metadata);

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::Call { target, .. } => {
                assert!(
                    matches!(target, CallTarget::Unresolved { .. }),
                    "expected Unresolved to remain, got {target:?}"
                );
            }
            other => panic!("expected Call, got {other:?}"),
        }
    }
}
