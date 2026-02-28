// resolve.rs
//
// Post-monomorphization pass: resolve all remaining `CallTarget::GenericCall`
// in concrete functions to `CallTarget::VirDirect` using the instance map
// built during monomorphization.

use rustc_hash::FxHashMap;

use crate::calls::CallTarget;
use crate::expr::{VirExpr, VirMetaKind, VirStringPart};
use crate::func::{VirBody, VirFunction};
use crate::refs::VirRef;
use crate::stmt::VirStmt;

use super::fixpoint::MonomorphInstance;

/// Mapping from `MonomorphInstance` to absolute index in `VirProgram.functions`.
pub type InstanceIndex = FxHashMap<MonomorphInstance, usize>;

/// Resolve all `CallTarget::GenericCall` in the given functions to
/// `CallTarget::VirDirect` using the instance index.
///
/// Any `GenericCall` whose `(function_id, type_args)` is found in the index
/// is rewritten to `VirDirect { function_index }`.  Unresolved calls (e.g.,
/// for templates not yet in VIR) are left as `GenericCall` — codegen will
/// never see them because those functions are generic templates, not concrete
/// functions compiled by codegen.
pub fn resolve_generic_calls(functions: &mut [VirFunction], index: &InstanceIndex) {
    for func in functions.iter_mut() {
        resolve_in_body(&mut func.body, index);
    }
}

fn resolve_in_body(body: &mut VirBody, index: &InstanceIndex) {
    for stmt in &mut body.stmts {
        resolve_in_stmt(stmt, index);
    }
    if let Some(ref mut trailing) = body.trailing {
        resolve_in_ref(trailing, index);
    }
}

fn resolve_in_ref(r: &mut VirRef, index: &InstanceIndex) {
    resolve_in_expr(r, index);
}

fn resolve_in_stmt(stmt: &mut VirStmt, index: &InstanceIndex) {
    match stmt {
        VirStmt::Let { value, .. } => resolve_in_ref(value, index),
        VirStmt::LetTuple { value, .. } => resolve_in_ref(value, index),
        VirStmt::Assign { target, value } => {
            resolve_in_assign_target(target, index);
            resolve_in_ref(value, index);
        }
        VirStmt::Expr { value } => resolve_in_ref(value, index),
        VirStmt::While { cond, body } => {
            resolve_in_ref(cond, index);
            resolve_in_body(body, index);
        }
        VirStmt::For(vir_for) => {
            resolve_in_ref(&mut vir_for.iterable, index);
            resolve_in_body(&mut vir_for.body, index);
        }
        VirStmt::Return { value, .. } => {
            if let Some(v) = value {
                resolve_in_ref(v, index);
            }
        }
        VirStmt::Break | VirStmt::Continue | VirStmt::Noop => {}
        VirStmt::Raise { fields, .. } => {
            for (_, val) in fields {
                resolve_in_ref(val, index);
            }
        }
        VirStmt::RcInc { value } | VirStmt::RcDec { value } => {
            resolve_in_ref(value, index);
        }
    }
}

fn resolve_in_assign_target(target: &mut crate::stmt::AssignTarget, index: &InstanceIndex) {
    use crate::stmt::AssignTarget;
    match target {
        AssignTarget::Local(_) => {}
        AssignTarget::Field { object, .. } => resolve_in_ref(object, index),
        AssignTarget::Index { array, index: idx } => {
            resolve_in_ref(array, index);
            resolve_in_ref(idx, index);
        }
    }
}

/// Walk a VIR expression tree, resolving `GenericCall` targets in place.
///
/// Delegates to category-specific helpers to stay under the line limit.
fn resolve_in_expr(expr: &mut VirExpr, index: &InstanceIndex) {
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
        | VirExpr::Coerce { .. } => resolve_in_expr_data(expr, index),

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
        | VirExpr::Yield { .. } => resolve_in_expr_control(expr, index),

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
fn resolve_in_expr_data(expr: &mut VirExpr, index: &InstanceIndex) {
    match expr {
        VirExpr::Call { target, args, .. } => {
            resolve_call_target(target, index);
            for arg in args {
                resolve_in_ref(arg, index);
            }
        }
        VirExpr::Range { start, end, .. } => {
            resolve_in_ref(start, index);
            resolve_in_ref(end, index);
        }
        VirExpr::ArrayLiteral { elements, .. } => {
            for elem in elements {
                resolve_in_ref(elem, index);
            }
        }
        VirExpr::RepeatLiteral { element, .. } => resolve_in_ref(element, index),
        VirExpr::StructLiteral { fields, .. } | VirExpr::ClassInstance { fields, .. } => {
            for (_, val) in fields {
                resolve_in_ref(val, index);
            }
        }
        VirExpr::BinaryOp { lhs, rhs, .. } => {
            resolve_in_ref(lhs, index);
            resolve_in_ref(rhs, index);
        }
        VirExpr::UnaryOp { operand, .. } => resolve_in_ref(operand, index),
        VirExpr::StringConcat { parts } => {
            for part in parts {
                resolve_in_ref(part, index);
            }
        }
        VirExpr::InterpolatedString { parts } => {
            for part in parts {
                if let VirStringPart::Expr { value, .. } = part {
                    resolve_in_ref(value, index);
                }
            }
        }
        VirExpr::MethodCall { receiver, args, .. } => {
            resolve_in_ref(receiver, index);
            for arg in args {
                resolve_in_ref(arg, index);
            }
        }
        VirExpr::FieldLoad { object, .. } => resolve_in_ref(object, index),
        VirExpr::FieldStore { object, value, .. } => {
            resolve_in_ref(object, index);
            resolve_in_ref(value, index);
        }
        VirExpr::Index {
            object, index: idx, ..
        } => {
            resolve_in_ref(object, index);
            resolve_in_ref(idx, index);
        }
        VirExpr::IndexStore {
            object,
            index: idx,
            value,
            ..
        } => {
            resolve_in_ref(object, index);
            resolve_in_ref(idx, index);
            resolve_in_ref(value, index);
        }
        VirExpr::RcInc { value } | VirExpr::RcDec { value } | VirExpr::RcMove { value } => {
            resolve_in_ref(value, index)
        }
        VirExpr::Coerce { value, .. } => resolve_in_ref(value, index),
        _ => {}
    }
}

/// Resolve in control flow, type ops, reflection, variables, lambda,
/// optional, try, and yield expressions.
fn resolve_in_expr_control(expr: &mut VirExpr, index: &InstanceIndex) {
    match expr {
        VirExpr::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            resolve_in_ref(cond, index);
            resolve_in_body(then_body, index);
            if let Some(eb) = else_body {
                resolve_in_body(eb, index);
            }
        }
        VirExpr::Match {
            scrutinee, arms, ..
        } => {
            resolve_in_ref(scrutinee, index);
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    resolve_in_ref(guard, index);
                }
                resolve_in_body(&mut arm.body, index);
                resolve_in_pattern(&mut arm.pattern, index);
            }
        }
        VirExpr::Block {
            stmts, trailing, ..
        } => {
            for stmt in stmts {
                resolve_in_stmt(stmt, index);
            }
            if let Some(t) = trailing {
                resolve_in_ref(t, index);
            }
        }
        VirExpr::IsCheck { value, .. } | VirExpr::AsCast { value, .. } => {
            resolve_in_ref(value, index);
        }
        VirExpr::MetaAccess { kind, .. } => match kind {
            VirMetaKind::Static { object, .. } => {
                if let Some(obj) = object {
                    resolve_in_ref(obj, index);
                }
            }
            VirMetaKind::Dynamic { value } | VirMetaKind::TypeParam { value, .. } => {
                resolve_in_ref(value, index);
            }
        },
        VirExpr::LocalLoad { .. } => {}
        VirExpr::LocalStore { value, .. } => resolve_in_ref(value, index),
        VirExpr::Lambda { body, .. } => resolve_in_body(body, index),
        VirExpr::NullCoalesce { value, default, .. } => {
            resolve_in_ref(value, index);
            resolve_in_ref(default, index);
        }
        VirExpr::OptionalChain { object, .. } => resolve_in_ref(object, index),
        VirExpr::OptionalMethodCall {
            object,
            method_args,
            ..
        } => {
            resolve_in_ref(object, index);
            for arg in method_args {
                resolve_in_ref(arg, index);
            }
        }
        VirExpr::Try { value, .. } | VirExpr::Yield { value } => {
            resolve_in_ref(value, index);
        }
        _ => {}
    }
}

fn resolve_in_pattern(pat: &mut crate::expr::VirPattern, index: &InstanceIndex) {
    use crate::expr::VirPattern;
    match pat {
        VirPattern::Wildcard
        | VirPattern::Binding { .. }
        | VirPattern::Val { .. }
        | VirPattern::Error { .. }
        | VirPattern::TypeCheck { .. } => {}
        VirPattern::Literal { value, .. } => resolve_in_ref(value, index),
        VirPattern::Success { inner, .. } => {
            if let Some(p) = inner {
                resolve_in_pattern(p, index);
            }
        }
        VirPattern::Tuple { bindings } => {
            for b in bindings {
                resolve_in_pattern(&mut b.pattern, index);
            }
        }
        VirPattern::Record { .. } => {}
    }
}

/// Resolve a single `CallTarget`: if it's a `GenericCall` whose instance
/// is in the index, replace it with `VirDirect`.
fn resolve_call_target(target: &mut CallTarget, index: &InstanceIndex) {
    let CallTarget::GenericCall {
        function_id,
        type_args,
    } = target
    else {
        return;
    };

    let instance = MonomorphInstance {
        function_id: *function_id,
        type_args: type_args.clone(),
    };

    if let Some(&func_idx) = index.get(&instance) {
        *target = CallTarget::VirDirect {
            function_index: func_idx,
        };
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
    use vole_identity::{FunctionId, Symbol, VirTypeId};

    fn type_id(n: u32) -> VirTypeId {
        VirTypeId::from_raw(n)
    }

    fn sym(n: u32) -> Symbol {
        Symbol::new_for_test(n)
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

        // Empty index — no instances registered.
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
}
