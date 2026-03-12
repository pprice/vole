// rederive.rs
//
// Decision re-derivation for monomorphized VIR functions.
//
// After type substitution and tree rewriting, VirTypeId fields are concrete
// but some embedded decision values (IsCheckResult, StringConversion,
// VirIterKind, VirMetaKind) may still carry generic/placeholder values.
// This pass walks the VIR tree and re-derives those decisions from the
// now-concrete types.

use std::cell::RefCell;

use rustc_hash::{FxHashMap, FxHashSet};
use vole_identity::{
    Interner, ModuleId, NameTable, StringConversion, Symbol, UnionStorageKind, VirTypeId,
};

use crate::calls::CallTarget;
use crate::entity_metadata::VirEntityMetadata;
use crate::expr::{
    FieldCoercionHint, FieldStorage, IsCheckResult, VirExpr, VirMetaKind, VirPattern, VirStringPart,
};
use crate::func::{ReturnAbi, VirBody, VirFunction};
use crate::implement_dispatch::VirImplementDispatch;
use crate::intrinsics::IntrinsicKey;
use crate::refs::VirRef;
use crate::stmt::{LetStorageHint, ReturnConvention, VirDestructurePattern, VirIterKind, VirStmt};
use crate::type_table::VirTypeTable;
use crate::types::{VirPrimitiveKind, VirType};

// ---------------------------------------------------------------------------
// Call target reclassification context
// ---------------------------------------------------------------------------

/// Context for re-classifying `CallTarget::Unresolved` during rederive.
///
/// After monomorphization, some calls that were `Unresolved` in generic
/// templates can be classified with concrete type information.  This context
/// provides the name resolution and entity lookup needed for reclassification.
///
/// Constructed by `monomorphize_one` which has access to `VirProgram`.
pub struct RederiveCallCtx<'a> {
    /// String interner for resolving `Symbol` to `&str`.
    pub interner: &'a Interner,
    /// Name table for resolving `(ModuleId, Symbol)` to `NameId`.
    pub name_table: &'a NameTable,
    /// Module ID of the generic template's declaring module.
    pub module_id: ModuleId,
    /// Implement-dispatch metadata for external function lookup.
    pub implement_dispatch: &'a VirImplementDispatch,
    /// Function parameter names and VIR types from the monomorphized function.
    /// Used to detect closure variable calls (callee matches a function-typed param).
    pub params: Vec<(Symbol, VirTypeId)>,
    /// Local variables with function types, accumulated during rederive walk.
    /// Used to detect closure variable calls for let-bound lambdas.
    /// Interior mutability allows population during the immutable walk.
    pub local_vars: RefCell<FxHashMap<Symbol, VirTypeId>>,
    /// Captured variables with function types, populated when entering a Lambda body.
    /// Used to detect captured closure variable calls.
    /// Save/restore pattern mirrors VIR lowering's capture scope management.
    pub captures: RefCell<FxHashMap<Symbol, VirTypeId>>,
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Walk a monomorphized VirFunction and re-derive decisions from concrete types.
///
/// After type substitution (vol-kj2e) and tree rewriting (vol-uo2t), all
/// VirTypeId fields are concrete.  However, some decision enums still carry
/// placeholder/generic values that were computed when the function was
/// polymorphic.  This pass updates:
///
/// 1. **IsCheckResult**: `CheckUnknown` with concrete types -> `AlwaysTrue`,
///    `AlwaysFalse`, or `CheckTag(tag)` when the scrutinee is a union.
/// 2. **StringConversion**: `Generic` -> concrete conversion based on VirType.
/// 3. **VirIterKind**: `Generic` -> concrete iteration kind based on the
///    iterable's VirType.
/// 4. **VirMetaKind**: `TypeParam` -> left as-is (requires EntityRegistry;
///    see vol-b4d0).
/// 5. **FieldStorage**: `ByName` -> `Direct`/`Heap` when the object type
///    is now a concrete struct or class.
pub fn rederive_decisions(
    func: &mut VirFunction,
    table: &VirTypeTable,
    entities: &VirEntityMetadata,
) {
    rederive_decisions_inner(func, table, entities, None);
}

/// Walk a monomorphized VirFunction and re-derive decisions, including
/// call target reclassification when a `RederiveCallCtx` is provided.
pub fn rederive_decisions_with_calls(
    func: &mut VirFunction,
    table: &VirTypeTable,
    entities: &VirEntityMetadata,
    call_ctx: &RederiveCallCtx<'_>,
) {
    rederive_decisions_inner(func, table, entities, Some(call_ctx));
}

/// Re-rederive call targets on VIR-monomorphized functions and test bodies.
///
/// The early VIR monomorph pass runs with a temporary empty interner, which
/// prevents `rederive_call_target` from resolving Unresolved calls.  This
/// function re-runs call reclassification on monomorphized functions
/// (those at indices `>= vir_monomorph_base`) and all test bodies using the
/// program's real interner and name_table.
///
/// For generic calls with monomorph keys, rederive converts them to
/// `GenericCall` so the subsequent `resolve_test_calls` pass can convert
/// them to `VirDirect`.
///
/// Should be called after the program's interner and name_table have been
/// populated (i.e., after `lower_vir_program` returns and the CLI sets them).
pub fn rederive_monomorphized_calls(program: &mut crate::program::VirProgram) {
    let base = program.vir_monomorph_base;
    if base == usize::MAX || base >= program.functions.len() {
        return;
    }

    // Temporarily take the functions vec to avoid borrow-checker conflicts
    // between &mut func and shared refs to other program fields.
    let mut functions = std::mem::take(&mut program.functions);

    for func in &mut functions[base..] {
        let module_id = program
            .entity_metadata
            .get_function_def(func.id)
            .map(|def| def.module)
            .unwrap_or(program.module_id);
        let call_ctx = RederiveCallCtx {
            interner: &program.interner,
            name_table: &program.name_table,
            module_id,
            implement_dispatch: &program.implement_dispatch,
            params: func.params.iter().map(|&(s, _, v)| (s, v)).collect(),
            local_vars: RefCell::new(FxHashMap::default()),
            captures: RefCell::new(FxHashMap::default()),
        };
        rederive_decisions_with_calls(
            func,
            &program.type_table,
            &program.entity_metadata,
            &call_ctx,
        );
    }

    program.functions = functions;

    // Also rederive call targets in test bodies.  Test VIR bodies can contain
    // Unresolved calls (e.g. test-scoped calls to generic functions) that
    // were not processed by the monomorph rederive above.
    rederive_test_calls(program);
}

/// Re-derive call targets in VIR test bodies.
///
/// Test bodies are stored separately from `program.functions` and were not
/// previously covered by `rederive_monomorphized_calls`.  This function
/// walks each test body with a call-reclassification context so that
/// `CallTarget::Unresolved` is resolved before codegen.
fn rederive_test_calls(program: &mut crate::program::VirProgram) {
    if program.tests.is_empty() {
        return;
    }

    let mut tests = std::mem::take(&mut program.tests);

    for test in &mut tests {
        let call_ctx = RederiveCallCtx {
            interner: &program.interner,
            name_table: &program.name_table,
            module_id: program.module_id,
            implement_dispatch: &program.implement_dispatch,
            params: Vec::new(),
            local_vars: RefCell::new(FxHashMap::default()),
            captures: RefCell::new(FxHashMap::default()),
        };
        rederive_body(
            &mut test.body,
            &program.type_table,
            VirTypeId::VOID,
            &program.entity_metadata,
            Some(&call_ctx),
        );
    }

    program.tests = tests;
}

fn rederive_decisions_inner(
    func: &mut VirFunction,
    table: &VirTypeTable,
    entities: &VirEntityMetadata,
    call_ctx: Option<&RederiveCallCtx<'_>>,
) {
    // Recompute return ABI from now-concrete return type.
    func.return_abi = ReturnAbi::classify(func.vir_return_type, table);

    let ret_ty = func.vir_return_type;
    rederive_body(&mut func.body, table, ret_ty, entities, call_ctx);
}

// ---------------------------------------------------------------------------
// Body / statement / expression walkers
// ---------------------------------------------------------------------------

fn rederive_body(
    body: &mut VirBody,
    table: &VirTypeTable,
    ret_ty: VirTypeId,
    entities: &VirEntityMetadata,
    call_ctx: Option<&RederiveCallCtx<'_>>,
) {
    for stmt in &mut body.stmts {
        rederive_stmt(stmt, table, ret_ty, entities, call_ctx);
    }
    if let Some(ref mut trailing) = body.trailing {
        rederive_ref(trailing, table, ret_ty, entities, call_ctx);
    }
}

fn rederive_ref(
    r: &mut VirRef,
    table: &VirTypeTable,
    ret_ty: VirTypeId,
    entities: &VirEntityMetadata,
    call_ctx: Option<&RederiveCallCtx<'_>>,
) {
    rederive_expr(r.as_mut(), table, ret_ty, entities, call_ctx);
}

fn rederive_expr(
    expr: &mut VirExpr,
    table: &VirTypeTable,
    ret_ty: VirTypeId,
    entities: &VirEntityMetadata,
    call_ctx: Option<&RederiveCallCtx<'_>>,
) {
    match expr {
        // Literals & construction — recurse into sub-expressions only
        VirExpr::IntLiteral { .. }
        | VirExpr::WideLiteral { .. }
        | VirExpr::FloatLiteral { .. }
        | VirExpr::BoolLiteral(_)
        | VirExpr::StringLiteral(_)
        | VirExpr::NilLiteral
        | VirExpr::Unreachable { .. }
        | VirExpr::Import { .. }
        | VirExpr::TypeLiteral => {}

        VirExpr::Range { start, end, .. } => {
            rederive_ref(start, table, ret_ty, entities, call_ctx);
            rederive_ref(end, table, ret_ty, entities, call_ctx);
        }
        VirExpr::ArrayLiteral { elements, .. } => {
            for elem in elements {
                rederive_ref(elem, table, ret_ty, entities, call_ctx);
            }
        }
        VirExpr::RepeatLiteral { element, .. } => {
            rederive_ref(element, table, ret_ty, entities, call_ctx);
        }
        VirExpr::StructLiteral { fields, .. } => {
            for (_, val) in fields {
                rederive_ref(val, table, ret_ty, entities, call_ctx);
            }
        }
        VirExpr::ClassInstance {
            fields,
            field_coercions,
            type_def,
            vir_ty,
            ..
        } => {
            for (_, val) in fields.iter_mut() {
                rederive_ref(val, table, ret_ty, entities, call_ctx);
            }
            rederive_field_coercions(fields, field_coercions, *type_def, *vir_ty, table, entities);
        }

        // Operators
        VirExpr::BinaryOp {
            lhs,
            rhs,
            op,
            lhs_is_optional,
            rhs_is_optional,
            lhs_is_unsigned,
            ..
        } => {
            rederive_ref(lhs, table, ret_ty, entities, call_ctx);
            rederive_ref(rhs, table, ret_ty, entities, call_ctx);
            // Re-derive optional hints from now-concrete operand types.
            if matches!(op, crate::expr::VirBinOp::Eq | crate::expr::VirBinOp::Ne) {
                if let Some(lhs_vir_ty) = extract_vir_ty(lhs) {
                    *lhs_is_optional = table.is_optional(lhs_vir_ty);
                }
                if let Some(rhs_vir_ty) = extract_vir_ty(rhs) {
                    *rhs_is_optional = table.is_optional(rhs_vir_ty);
                }
            }
            // Re-derive signedness hint from now-concrete left operand type.
            if let Some(lhs_vir_ty) = extract_vir_ty(lhs) {
                *lhs_is_unsigned = lhs_vir_ty.is_unsigned_int();
            }
        }
        VirExpr::UnaryOp { operand, .. } => {
            rederive_ref(operand, table, ret_ty, entities, call_ctx);
        }

        // Strings — re-derive StringConversion::Generic
        VirExpr::StringConcat { parts } => {
            for part in parts {
                rederive_ref(part, table, ret_ty, entities, call_ctx);
            }
        }
        VirExpr::InterpolatedString { parts } => {
            rederive_string_parts(parts, table, ret_ty, entities, call_ctx);
        }

        // Calls — rederive fallible hint and reclassify Unresolved targets
        VirExpr::Call {
            target,
            args,
            vir_ty,
            result_is_fallible,
            ..
        } => {
            for arg in args {
                rederive_ref(arg, table, ret_ty, entities, call_ctx);
            }
            // Re-derive fallible hint from now-concrete result type.
            *result_is_fallible = table.is_fallible(*vir_ty);
            // Reclassify Unresolved call targets with concrete type information.
            if let Some(ctx) = call_ctx {
                rederive_call_target(target, table, entities, ctx);
            }
        }
        VirExpr::MethodCall {
            receiver,
            args,
            dispatch,
            ..
        } => {
            rederive_ref(receiver, table, ret_ty, entities, call_ctx);
            for arg in args {
                rederive_ref(arg, table, ret_ty, entities, call_ctx);
            }
            // Re-derive receiver_is_interface from the now-concrete receiver type.
            if let Some(recv_vir_ty) = extract_vir_ty(receiver) {
                dispatch.receiver_is_interface = table.is_interface(recv_vir_ty);
            }
        }

        // Fields — rederive ByName -> Direct/Heap for concrete types
        VirExpr::FieldLoad {
            object,
            field,
            storage,
            ..
        } => {
            rederive_ref(object, table, ret_ty, entities, call_ctx);
            rederive_field_storage(object, *field, storage, table, entities);
        }
        VirExpr::FieldStore {
            object,
            field,
            storage,
            value,
        } => {
            rederive_ref(object, table, ret_ty, entities, call_ctx);
            rederive_ref(value, table, ret_ty, entities, call_ctx);
            rederive_field_storage(object, *field, storage, table, entities);
        }

        // Indexing
        VirExpr::Index {
            object,
            index,
            union_storage,
            ..
        } => {
            rederive_ref(object, table, ret_ty, entities, call_ctx);
            rederive_ref(index, table, ret_ty, entities, call_ctx);
            rederive_union_storage_from_array_expr(object, union_storage, table);
        }
        VirExpr::IndexStore {
            object,
            index,
            value,
            union_storage,
            ..
        } => {
            rederive_ref(object, table, ret_ty, entities, call_ctx);
            rederive_ref(index, table, ret_ty, entities, call_ctx);
            rederive_ref(value, table, ret_ty, entities, call_ctx);
            rederive_union_storage_from_array_expr(object, union_storage, table);
        }

        // RC — rederive cleanup strategy from the concrete value type
        VirExpr::RcInc { value, cleanup } => {
            rederive_ref(value, table, ret_ty, entities, call_ctx);
            rederive_rc_cleanup(value, cleanup, table);
        }
        VirExpr::RcDec { value, cleanup } => {
            rederive_ref(value, table, ret_ty, entities, call_ctx);
            rederive_rc_cleanup(value, cleanup, table);
        }
        VirExpr::RcMove { value } => {
            rederive_ref(value, table, ret_ty, entities, call_ctx);
        }

        // Coercion
        VirExpr::Coerce { value, .. } => rederive_ref(value, table, ret_ty, entities, call_ctx),

        // Control flow
        VirExpr::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            rederive_ref(cond, table, ret_ty, entities, call_ctx);
            rederive_body(then_body, table, ret_ty, entities, call_ctx);
            if let Some(eb) = else_body {
                rederive_body(eb, table, ret_ty, entities, call_ctx);
            }
        }
        VirExpr::Match {
            scrutinee,
            arms,
            vir_ty,
            result_is_union,
            ..
        } => {
            rederive_ref(scrutinee, table, ret_ty, entities, call_ctx);
            *result_is_union = table.is_union(*vir_ty);
            let scrutinee_vir_ty = extract_vir_ty(scrutinee);
            for arm in arms {
                rederive_pattern(&mut arm.pattern, scrutinee_vir_ty, table, ret_ty, entities);
                if let Some(guard) = &mut arm.guard {
                    rederive_ref(guard, table, ret_ty, entities, call_ctx);
                }
                rederive_body(&mut arm.body, table, ret_ty, entities, call_ctx);
            }
        }
        VirExpr::Block {
            stmts, trailing, ..
        } => {
            for stmt in stmts {
                rederive_stmt(stmt, table, ret_ty, entities, call_ctx);
            }
            if let Some(t) = trailing {
                rederive_ref(t, table, ret_ty, entities, call_ctx);
            }
        }

        // Type operations — re-derive IsCheckResult
        VirExpr::IsCheck { value, result, .. } => {
            rederive_ref(value, table, ret_ty, entities, call_ctx);
            rederive_is_check_from_expr(value, result, table);
        }
        VirExpr::AsCast { value, result, .. } => {
            rederive_ref(value, table, ret_ty, entities, call_ctx);
            rederive_is_check_from_expr(value, result, table);
        }

        // Reflection — re-derive TypeParam meta-kind from concrete VIR types.
        VirExpr::MetaAccess { kind, .. } => {
            rederive_meta_kind(kind, table, ret_ty, entities);
        }

        // Variables
        VirExpr::LocalLoad { .. } => {}
        VirExpr::LocalStore { value, .. } => {
            rederive_ref(value, table, ret_ty, entities, call_ctx);
        }

        // Lambda — use the lambda's own return type, not the enclosing function's.
        // Also rederive RC kind for each capture.
        // Save/restore local_vars and captures so lambda-internal state
        // doesn't leak to the outer scope.
        VirExpr::Lambda {
            body,
            captures,
            vir_ty,
            ..
        } => {
            let lambda_ret_ty = table
                .unwrap_function(*vir_ty)
                .map(|(_, ret)| ret)
                .unwrap_or(ret_ty);
            // Snapshot outer locals and captures; lambda body gets its own
            // scope.  Any let-bindings inside the lambda body won't leak out,
            // and the lambda's captures replace the outer captures.
            let saved_locals = call_ctx.map(|ctx| ctx.local_vars.borrow().clone());
            let saved_captures = call_ctx.map(|ctx| ctx.captures.borrow().clone());
            // Push this lambda's captures into the captures map so that calls
            // inside the lambda body can be resolved as CapturedClosure.
            // Also remove captured names from local_vars — inside the lambda
            // these are captures, not locals.
            if let Some(ctx) = call_ctx {
                let mut cap_map = ctx.captures.borrow_mut();
                cap_map.clear();
                let mut locals = ctx.local_vars.borrow_mut();
                for cap in captures.iter() {
                    // Use the capture's vir_ty if it's a known callable type
                    // (function or interface).  Fall back to the local_vars type
                    // if the capture's vir_ty is Unknown (can happen when the
                    // type table entry wasn't populated during rewrite).
                    let is_callable =
                        |ty: VirTypeId| table.is_function(ty) || table.is_interface(ty);
                    let fn_vir_ty = if is_callable(cap.vir_ty) {
                        Some(cap.vir_ty)
                    } else {
                        locals.get(&cap.name).copied().filter(|&ty| is_callable(ty))
                    };
                    locals.remove(&cap.name);
                    if let Some(vir_ty) = fn_vir_ty {
                        cap_map.insert(cap.name, vir_ty);
                    }
                }
            }
            rederive_body(body, table, lambda_ret_ty, entities, call_ctx);
            if let Some(ctx) = call_ctx {
                if let Some(saved) = saved_locals {
                    *ctx.local_vars.borrow_mut() = saved;
                }
                if let Some(saved) = saved_captures {
                    *ctx.captures.borrow_mut() = saved;
                }
            }
            for cap in captures.iter_mut() {
                cap.rc_kind = classify_capture_rc_kind(cap.vir_ty, table);
            }
        }

        // Optional / null
        VirExpr::NullCoalesce { value, default, .. } => {
            rederive_ref(value, table, ret_ty, entities, call_ctx);
            rederive_ref(default, table, ret_ty, entities, call_ctx);
        }
        VirExpr::OptionalChain { object, .. } => {
            rederive_ref(object, table, ret_ty, entities, call_ctx);
        }
        VirExpr::OptionalMethodCall {
            object,
            method_args,
            dispatch,
            ..
        } => {
            rederive_ref(object, table, ret_ty, entities, call_ctx);
            for arg in method_args {
                rederive_ref(arg, table, ret_ty, entities, call_ctx);
            }
            // Re-derive receiver_is_interface from the now-concrete object type.
            if let Some(obj_vir_ty) = extract_vir_ty(object) {
                dispatch.receiver_is_interface = table.is_interface(obj_vir_ty);
            }
        }
        VirExpr::Try { value, .. } => rederive_ref(value, table, ret_ty, entities, call_ctx),
        VirExpr::Yield { value } => rederive_ref(value, table, ret_ty, entities, call_ctx),
    }
}

fn rederive_stmt(
    stmt: &mut VirStmt,
    table: &VirTypeTable,
    ret_ty: VirTypeId,
    entities: &VirEntityMetadata,
    call_ctx: Option<&RederiveCallCtx<'_>>,
) {
    match stmt {
        VirStmt::Let {
            name,
            value,
            vir_ty,
            storage,
            needs_struct_copy,
            ..
        } => {
            let name = *name;
            let binding_vir_ty = *vir_ty;
            let init_vir_ty = extract_vir_ty(value);
            *storage = rederive_let_storage(binding_vir_ty, init_vir_ty, storage, table);
            // Re-derive struct copy flag: after monomorphization a type param
            // may have been substituted with a concrete struct type.
            // Sentinels (Nil, Done, user-defined empties) are stored as
            // VirType::Struct internally but are NOT value-type structs —
            // exclude them to match codegen's `vir_is_struct()` semantics.
            if !*needs_struct_copy && let Some(init_vir_ty) = init_vir_ty {
                *needs_struct_copy =
                    !table.is_sentinel(init_vir_ty) && table.is_struct(init_vir_ty);
            }
            rederive_ref(value, table, ret_ty, entities, call_ctx);
            // Track function-typed and interface-typed let bindings for
            // closure variable and functional interface resolution.
            if let Some(ctx) = call_ctx
                && (table.is_function(binding_vir_ty) || table.is_interface(binding_vir_ty))
            {
                ctx.local_vars.borrow_mut().insert(name, binding_vir_ty);
            }
        }
        VirStmt::LetTuple { pattern, value, .. } => {
            rederive_destructure_pattern(pattern, table, entities);
            rederive_ref(value, table, ret_ty, entities, call_ctx);
        }
        VirStmt::Assign { target, value } => {
            rederive_assign_target(target, table, ret_ty, entities, call_ctx);
            rederive_ref(value, table, ret_ty, entities, call_ctx);
        }
        VirStmt::Expr { value } => rederive_ref(value, table, ret_ty, entities, call_ctx),
        VirStmt::While { cond, body } => {
            rederive_ref(cond, table, ret_ty, entities, call_ctx);
            rederive_body(body, table, ret_ty, entities, call_ctx);
        }
        VirStmt::For(vir_for) => {
            rederive_ref(&mut vir_for.iterable, table, ret_ty, entities, call_ctx);
            rederive_body(&mut vir_for.body, table, ret_ty, entities, call_ctx);
            rederive_iter_kind(&mut vir_for.kind, table);
        }
        VirStmt::Return { value, convention } => {
            if let Some(v) = value {
                rederive_ref(v, table, ret_ty, entities, call_ctx);
            }
            *convention = rederive_return_convention(ret_ty, table);
        }
        VirStmt::Break | VirStmt::Continue | VirStmt::Noop => {}
        VirStmt::Raise { fields, .. } => {
            for (_, val) in fields {
                rederive_ref(val, table, ret_ty, entities, call_ctx);
            }
        }
        VirStmt::RcInc { value, cleanup } => {
            rederive_ref(value, table, ret_ty, entities, call_ctx);
            rederive_rc_cleanup(value, cleanup, table);
        }
        VirStmt::RcDec { value, cleanup } => {
            rederive_ref(value, table, ret_ty, entities, call_ctx);
            rederive_rc_cleanup(value, cleanup, table);
        }
    }
}

fn rederive_assign_target(
    target: &mut crate::stmt::AssignTarget,
    table: &VirTypeTable,
    ret_ty: VirTypeId,
    entities: &VirEntityMetadata,
    call_ctx: Option<&RederiveCallCtx<'_>>,
) {
    use crate::stmt::AssignTarget;
    match target {
        AssignTarget::Local(_) => {}
        AssignTarget::Field {
            object,
            field,
            storage,
        } => {
            rederive_ref(object, table, ret_ty, entities, call_ctx);
            rederive_field_storage(object, *field, storage, table, entities);
        }
        AssignTarget::Index { array, index } => {
            rederive_ref(array, table, ret_ty, entities, call_ctx);
            rederive_ref(index, table, ret_ty, entities, call_ctx);
        }
    }
}

fn rederive_pattern(
    pat: &mut VirPattern,
    scrutinee_vir_ty: Option<VirTypeId>,
    table: &VirTypeTable,
    ret_ty: VirTypeId,
    entities: &VirEntityMetadata,
) {
    match pat {
        VirPattern::Wildcard | VirPattern::Binding { .. } | VirPattern::Val { .. } => {}
        VirPattern::TypeCheck {
            result,
            tested_type,
            vir_tested_type,
            ..
        } => {
            if let Some(scrutinee_vir_ty) = scrutinee_vir_ty {
                *result =
                    derive_is_check_result(scrutinee_vir_ty, *tested_type, *vir_tested_type, table);
            }
        }
        VirPattern::Literal { value, .. } => rederive_ref(value, table, ret_ty, entities, None),
        VirPattern::Success {
            inner,
            vir_success_type,
            ..
        } => {
            if let Some(p) = inner {
                rederive_pattern(p, Some(*vir_success_type), table, ret_ty, entities);
            }
        }
        VirPattern::Error { .. } => {}
        VirPattern::Tuple { bindings } => {
            for b in bindings {
                rederive_pattern(&mut b.pattern, Some(b.vir_ty), table, ret_ty, entities);
            }
        }
        VirPattern::Record {
            type_check,
            tested_type,
            vir_tested_type,
            fields,
            ..
        } => {
            if let (Some(tc), Some(tested_type), Some(vir_tested_type), Some(scrutinee_vir_ty)) =
                (type_check, *tested_type, *vir_tested_type, scrutinee_vir_ty)
            {
                *tc = derive_is_check_result(scrutinee_vir_ty, tested_type, vir_tested_type, table);
            }
            // Field patterns are simple bindings — no decisions to re-derive.
            let _ = fields;
        }
    }
}

// ---------------------------------------------------------------------------
// Call target reclassification
// ---------------------------------------------------------------------------

/// Check if a variable's type is a functional interface (single abstract method).
///
/// Returns `Some(CallTarget::FunctionalInterface { .. })` if the VIR type is
/// an interface with exactly one non-default method, otherwise `None`.
fn try_as_functional_interface(
    var_name: Symbol,
    vir_type: VirTypeId,
    table: &VirTypeTable,
    entities: &VirEntityMetadata,
) -> Option<CallTarget> {
    if !table.is_interface(vir_type) {
        return None;
    }
    let type_def_id = table.type_def_id(vir_type)?;
    let method_id = entities.is_functional(type_def_id)?;
    Some(CallTarget::FunctionalInterface {
        var_name,
        vir_type,
        interface_type_def_id: type_def_id,
        method_id,
    })
}

/// Attempt to reclassify a `CallTarget::Unresolved` using concrete post-monomorphization info.
///
/// After monomorphization, types are concrete but calls inside generic templates
/// were all emitted as `Unresolved` (except `GenericCall`).  This function
/// re-classifies what it can:
///
/// 1. **Hardcoded intrinsics** (`assert`, `print_char`) by resolving `callee_sym`.
/// 2. **Direct function calls** via `NameTable` + `VirEntityMetadata` lookup.
/// 3. **Compiler intrinsics** (`panic`, etc.) via `VirImplementDispatch`.
/// 4. **Functional interface calls** when the callee is a variable (param,
///    local, or capture) whose type is a single-method interface.
/// 5. **Closure variable calls** when the callee matches a function-typed
///    parameter or a let-bound local with function type.
/// 6. **Captured closure calls** when the callee matches a function-typed
///    capture from an enclosing lambda scope.
/// 7. **Global closure calls** via `NameTable` + `VirEntityMetadata` global
///    variable lookup.
///
/// **Not reclassified** (left for codegen's `call_dispatch`):
/// - Regular FFI external calls (would need `&mut Interner` to create `Symbol`s)
fn rederive_call_target(
    target: &mut CallTarget,
    table: &VirTypeTable,
    entities: &VirEntityMetadata,
    ctx: &RederiveCallCtx<'_>,
) {
    let CallTarget::Unresolved {
        callee_sym,
        line,
        resolved_call_args,
        lambda_defaults,
        monomorph_key,
        ..
    } = target
    else {
        return;
    };

    let callee_sym = *callee_sym;
    let line = *line;
    let rca = resolved_call_args.clone();
    let ld = *lambda_defaults;
    let mk = monomorph_key.clone();

    // Resolve the callee symbol to a string first. If the interner can't
    // resolve it (e.g. during early monomorphization with a temporary empty
    // interner), leave the call as Unresolved for later resolution.
    let Some(callee_name) = ctx.interner.try_resolve(callee_sym) else {
        return;
    };

    // 1. Hardcoded intrinsics (assert, print_char).
    match callee_name {
        "assert" => {
            *target = CallTarget::Intrinsic {
                key: IntrinsicKey::Assert,
                line,
            };
            return;
        }
        "print_char" => {
            *target = CallTarget::Intrinsic {
                key: IntrinsicKey::PrintChar,
                line,
            };
            return;
        }
        _ => {}
    }

    // 2. Callable variable: callee matches a parameter with function or
    //    functional-interface type.
    for &(param_sym, param_vir_ty) in &ctx.params {
        if param_sym == callee_sym {
            if let Some(fi) = try_as_functional_interface(callee_sym, param_vir_ty, table, entities)
            {
                *target = fi;
                return;
            }
            if table.is_function(param_vir_ty) {
                *target = CallTarget::ClosureVariable {
                    var_name: callee_sym,
                    vir_type: param_vir_ty,
                    resolved_call_args: rca,
                    lambda_defaults: ld,
                };
                return;
            }
        }
    }

    // 2b. Closure variable call: callee matches a let-bound function-typed local.
    // Guard: skip if the callee is a module-level global — globals are handled
    // in step 3b below, not as local closure variables.
    let is_global = ctx
        .name_table
        .name_id_raw(ctx.module_id, &[callee_name])
        .and_then(|nid| entities.global_by_name(nid))
        .is_some();
    if !is_global && let Some(&local_vir_ty) = ctx.local_vars.borrow().get(&callee_sym) {
        if let Some(fi) = try_as_functional_interface(callee_sym, local_vir_ty, table, entities) {
            *target = fi;
            return;
        }
        *target = CallTarget::ClosureVariable {
            var_name: callee_sym,
            vir_type: local_vir_ty,
            resolved_call_args: rca,
            lambda_defaults: ld,
        };
        return;
    }

    // 2c. Captured closure call: callee matches a function-typed capture
    // from an enclosing scope (populated when entering a Lambda body).
    if let Some(&capture_vir_ty) = ctx.captures.borrow().get(&callee_sym) {
        if let Some(fi) = try_as_functional_interface(callee_sym, capture_vir_ty, table, entities) {
            *target = fi;
            return;
        }
        *target = CallTarget::CapturedClosure {
            var_name: callee_sym,
            vir_type: capture_vir_ty,
            resolved_call_args: rca,
            lambda_defaults: ld,
        };
        return;
    }

    // 3. Direct or generic function call: look up in the name table.
    // Use name_id_raw (string-based) instead of name_id (Symbol-based)
    // to avoid panicking when the interner doesn't contain the symbol.
    if let Some(name_id) = ctx.name_table.name_id_raw(ctx.module_id, &[callee_name])
        && let Some(func_id) = entities.function_by_name(name_id)
        && let Some(func_def) = entities.get_function_def(func_id)
    {
        if func_def.is_generic {
            // Generic function with monomorph key: convert to GenericCall so
            // the resolve pass can look it up in the instance index and
            // convert to VirDirect.  This handles test-scoped calls to
            // generic functions that were Unresolved at VIR lowering time.
            if let Some(key) = &mk {
                *target = CallTarget::GenericCall {
                    function_id: func_id,
                    type_args: key.type_keys.clone(),
                };
                return;
            }
        } else if !func_def.is_external {
            *target = CallTarget::Direct {
                function_id: func_id,
            };
            return;
        }
    }

    // 3b. Global closure call: callee is a module-level global variable.
    if is_global {
        *target = CallTarget::GlobalClosure {
            var_name: callee_sym,
            resolved_call_args: rca,
            lambda_defaults: ld,
            monomorph_key: mk,
        };
        return;
    }

    // 4. Compiler intrinsics via implement-dispatch (e.g. `panic`).
    if let Some(ext_info) = ctx.implement_dispatch.external_func_by_name(callee_name) {
        let module_path_str = ctx
            .name_table
            .last_segment_str(ext_info.module_path)
            .unwrap_or_default();
        if module_path_str == "vole:compiler_intrinsic" {
            let native_name_str = ctx
                .name_table
                .last_segment_str(ext_info.native_name)
                .unwrap_or_default();
            if let Some(key) = IntrinsicKey::try_from_name(&native_name_str) {
                *target = CallTarget::Intrinsic { key, line };
            }
        }
        // Regular FFI external calls are NOT reclassified here because
        // producing CallTarget::Native requires interning new Symbol values
        // (module_path, native_name) which needs &mut Interner.
        // These remain Unresolved for codegen's call_dispatch().
    }
}

// ---------------------------------------------------------------------------
// Decision re-derivation logic
// ---------------------------------------------------------------------------

/// Re-derive `CheckUnknown` for expression-level `is`/`as` checks.
///
/// Expression nodes do not carry `tested_type` separately from `IsCheckResult`,
/// so we only refine the `CheckUnknown` case here.
fn rederive_is_check_from_expr(value: &VirExpr, result: &mut IsCheckResult, table: &VirTypeTable) {
    let IsCheckResult::CheckUnknown(tested_type, tested_vir_ty) = *result else {
        return;
    };

    let Some(scrutinee_vir_ty) = extract_vir_ty(value) else {
        return;
    };
    *result = derive_is_check_result(scrutinee_vir_ty, tested_type, tested_vir_ty, table);
}

/// Derive an IsCheckResult from concrete VIR types.
fn derive_is_check_result(
    scrutinee_vir_ty: VirTypeId,
    tested_type: VirTypeId,
    tested_vir_ty: VirTypeId,
    table: &VirTypeTable,
) -> IsCheckResult {
    // If either side is still unresolved, keep runtime check behavior.
    if matches!(
        table.get(scrutinee_vir_ty),
        VirType::Param { .. } | VirType::Unknown
    ) || matches!(
        table.get(tested_vir_ty),
        VirType::Param { .. } | VirType::Unknown
    ) {
        return IsCheckResult::CheckUnknown(tested_type, tested_vir_ty);
    }

    match table.get(scrutinee_vir_ty) {
        VirType::Union { variants } => variants
            .iter()
            .position(|&variant| variant == tested_vir_ty)
            .map(|idx| IsCheckResult::CheckTag(idx as u32))
            .unwrap_or(IsCheckResult::AlwaysFalse),

        // Optional lowers as a dedicated VIR type and does not preserve sema's
        // union variant order, so we conservatively keep runtime checking when
        // testing either possible optional variant.
        VirType::Optional { inner } => {
            if tested_vir_ty == *inner || tested_vir_ty == VirTypeId::NIL {
                IsCheckResult::CheckUnknown(tested_type, tested_vir_ty)
            } else {
                IsCheckResult::AlwaysFalse
            }
        }

        _ => {
            if scrutinee_vir_ty == tested_vir_ty {
                IsCheckResult::AlwaysTrue
            } else {
                IsCheckResult::AlwaysFalse
            }
        }
    }
}

/// Re-derive StringConversion::Generic to a concrete conversion.
///
/// Inspects the expression's VirTypeId to determine the correct primitive
/// string conversion.  Complex cases (custom toString, optionals, unions)
/// require EntityRegistry and are left as Generic (see vol-b4d0).
fn rederive_string_conversion(
    conv: &mut StringConversion,
    vir_ty: VirTypeId,
    table: &VirTypeTable,
) {
    if !matches!(conv, StringConversion::Generic { .. }) {
        return;
    }

    *conv = derive_string_conversion_from_vir_type(vir_ty, table);
}

/// Derive a StringConversion from a concrete VirTypeId.
fn derive_string_conversion_from_vir_type(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
) -> StringConversion {
    // Check nil by reserved VirTypeId before pattern-matching the VirType.
    if vir_ty == VirTypeId::NIL {
        return StringConversion::NilToString;
    }

    let vir_type = table.get(vir_ty);
    match vir_type {
        VirType::Primitive(prim) => match prim {
            VirPrimitiveKind::String => StringConversion::Identity,
            VirPrimitiveKind::I8
            | VirPrimitiveKind::I16
            | VirPrimitiveKind::I32
            | VirPrimitiveKind::I64
            | VirPrimitiveKind::U8
            | VirPrimitiveKind::U16
            | VirPrimitiveKind::U32
            | VirPrimitiveKind::U64 => StringConversion::I64ToString,
            VirPrimitiveKind::I128 => StringConversion::I128ToString,
            VirPrimitiveKind::F32 => StringConversion::F32ToString,
            VirPrimitiveKind::F64 => StringConversion::F64ToString,
            VirPrimitiveKind::F128 => StringConversion::F128ToString,
            VirPrimitiveKind::Bool => StringConversion::BoolToString,
            VirPrimitiveKind::Handle => StringConversion::I64ToString,
        },
        VirType::Array { .. } | VirType::FixedArray { .. } => StringConversion::ArrayToString,

        // TODO(vol-b4d0): Optional, Union, Class, Struct, Interface need
        // EntityRegistry to determine if they implement Stringable or have
        // custom toString methods.  Leave as Generic for now; codegen handles
        // Generic with a runtime fallback.
        _ => StringConversion::I64ToString,
    }
}

/// Re-derive VirIterKind::Generic to a concrete iteration kind.
///
/// Inspects the iterable expression's type to determine the correct iteration
/// strategy.  Only handles cases derivable from VirTypeTable alone: Range,
/// Array, String.  Complex cases (CustomIterator, CustomIterable,
/// IteratorInterface) require EntityRegistry.
fn rederive_iter_kind(kind: &mut VirIterKind, table: &VirTypeTable) {
    match kind {
        VirIterKind::Array {
            vir_elem_type,
            union_storage,
            ..
        } => {
            *union_storage = derive_union_storage_from_elem(*vir_elem_type, table);
        }
        VirIterKind::Generic { .. }
        | VirIterKind::Range
        | VirIterKind::String
        | VirIterKind::RuntimeIterator { .. }
        | VirIterKind::IteratorInterface { .. }
        | VirIterKind::CustomIterator { .. }
        | VirIterKind::CustomIterable { .. } => {
            // Re-deriving Generic -> concrete iteration strategy still needs
            // iterable-type metadata not carried by VirIterKind::Generic.
        }
    }
}

fn rederive_union_storage_from_array_expr(
    object_expr: &VirExpr,
    union_storage: &mut Option<UnionStorageKind>,
    table: &VirTypeTable,
) {
    let Some(object_vir_ty) = extract_vir_ty(object_expr) else {
        return;
    };
    let derived = match table.get(object_vir_ty) {
        VirType::Array { elem } | VirType::FixedArray { elem, .. } => {
            Some(derive_union_storage_from_elem(*elem, table))
        }
        _ => None,
    };
    if let Some(kind) = derived {
        *union_storage = kind;
    }
}

fn derive_union_storage_from_elem(
    elem_vir_ty: VirTypeId,
    table: &VirTypeTable,
) -> Option<UnionStorageKind> {
    match table.get(elem_vir_ty) {
        VirType::Union { variants } => {
            Some(if union_array_prefers_inline_storage(variants, table) {
                UnionStorageKind::Inline
            } else {
                UnionStorageKind::Heap
            })
        }
        VirType::Optional { inner } => {
            let variants = [*inner, VirTypeId::NIL];
            Some(if union_array_prefers_inline_storage(&variants, table) {
                UnionStorageKind::Inline
            } else {
                UnionStorageKind::Heap
            })
        }
        _ => None,
    }
}

fn union_array_prefers_inline_storage(variants: &[VirTypeId], table: &VirTypeTable) -> bool {
    let mut seen_tags: FxHashSet<RuntimeTagCategory> = FxHashSet::default();

    for &variant in variants {
        if !supports_inline_union_array_variant(variant, table) {
            return false;
        }

        let tag = runtime_tag_category(variant, table);
        if tag == RuntimeTagCategory::I64
            && !is_integer(variant, table)
            && !is_sentinel(variant, table)
        {
            return false;
        }

        if !seen_tags.insert(tag) {
            return false;
        }
    }

    true
}

fn supports_inline_union_array_variant(variant: VirTypeId, table: &VirTypeTable) -> bool {
    !matches!(
        table.get(variant),
        VirType::Union { .. }
            | VirType::Optional { .. }
            | VirType::Interface { .. }
            | VirType::Class { .. }
            | VirType::Struct { .. }
            | VirType::Unknown
            | VirType::Tuple { .. }
            | VirType::Fallible { .. }
            | VirType::Param { .. }
    )
}

fn runtime_tag_category(ty: VirTypeId, table: &VirTypeTable) -> RuntimeTagCategory {
    match table.get(ty) {
        VirType::Primitive(VirPrimitiveKind::String) => RuntimeTagCategory::String,
        VirType::Primitive(
            VirPrimitiveKind::I8
            | VirPrimitiveKind::I16
            | VirPrimitiveKind::I32
            | VirPrimitiveKind::I64
            | VirPrimitiveKind::U8
            | VirPrimitiveKind::U16
            | VirPrimitiveKind::U32
            | VirPrimitiveKind::U64,
        ) => RuntimeTagCategory::I64,
        VirType::Primitive(VirPrimitiveKind::F32 | VirPrimitiveKind::F64) => {
            RuntimeTagCategory::F64
        }
        VirType::Primitive(VirPrimitiveKind::Bool) => RuntimeTagCategory::Bool,
        VirType::Array { .. } | VirType::FixedArray { .. } => RuntimeTagCategory::Array,
        VirType::Function { .. } => RuntimeTagCategory::Closure,
        VirType::Class { .. } => RuntimeTagCategory::Instance,
        _ => RuntimeTagCategory::I64,
    }
}

fn is_integer(ty: VirTypeId, table: &VirTypeTable) -> bool {
    matches!(
        table.get(ty),
        VirType::Primitive(
            VirPrimitiveKind::I8
                | VirPrimitiveKind::I16
                | VirPrimitiveKind::I32
                | VirPrimitiveKind::I64
                | VirPrimitiveKind::U8
                | VirPrimitiveKind::U16
                | VirPrimitiveKind::U32
                | VirPrimitiveKind::U64
        )
    )
}

fn is_sentinel(ty: VirTypeId, table: &VirTypeTable) -> bool {
    table.is_sentinel(ty)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum RuntimeTagCategory {
    String,
    I64,
    F64,
    Bool,
    Array,
    Closure,
    Instance,
}

fn rederive_string_parts(
    parts: &mut [VirStringPart],
    table: &VirTypeTable,
    ret_ty: VirTypeId,
    entities: &VirEntityMetadata,
    call_ctx: Option<&RederiveCallCtx<'_>>,
) {
    for part in parts {
        if let VirStringPart::Expr { value, conversion } = part {
            rederive_ref(value, table, ret_ty, entities, call_ctx);
            // Extract the expression's VirTypeId to re-derive the conversion.
            let vir_ty = extract_vir_ty(value);
            if let Some(vir_ty) = vir_ty {
                rederive_string_conversion(conversion, vir_ty, table);
            }
        }
    }
}

fn rederive_meta_kind(
    kind: &mut VirMetaKind,
    table: &VirTypeTable,
    ret_ty: VirTypeId,
    entities: &VirEntityMetadata,
) {
    match kind {
        VirMetaKind::Static { object, type_def } => {
            if let Some(obj) = object {
                rederive_ref(obj, table, ret_ty, entities, None);
                if let Some(obj_vir_ty) = extract_vir_ty(obj)
                    && let Some(concrete_type_def) =
                        nominal_type_def_from_vir_type(obj_vir_ty, table)
                {
                    *type_def = concrete_type_def;
                }
            }
        }
        VirMetaKind::Dynamic { value } => rederive_ref(value, table, ret_ty, entities, None),
        VirMetaKind::TypeParam { value, .. } => {
            rederive_ref(value, table, ret_ty, entities, None);
            let Some(value_vir_ty) = extract_vir_ty(value) else {
                return;
            };
            match table.get(value_vir_ty) {
                VirType::Class { def, .. } | VirType::Struct { def, .. } => {
                    let value = value.clone();
                    *kind = VirMetaKind::Static {
                        type_def: *def,
                        object: Some(value),
                    };
                }
                VirType::Interface { .. } => {
                    let value = value.clone();
                    *kind = VirMetaKind::Dynamic { value };
                }
                _ => {
                    // Non-nominal concrete types stay as TypeParam; codegen
                    // reports unsupported `T.@meta` for those cases.
                }
            }
        }
    }
}

fn nominal_type_def_from_vir_type(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
) -> Option<vole_identity::TypeDefId> {
    match table.get(vir_ty) {
        VirType::Class { def, .. }
        | VirType::Struct { def, .. }
        | VirType::Interface { def, .. } => Some(*def),
        _ => None,
    }
}

/// Extract the VirTypeId from a VirExpr, if it carries one.
fn extract_vir_ty(expr: &VirExpr) -> Option<VirTypeId> {
    match expr {
        // Variants with a `vir_ty` field
        VirExpr::IntLiteral { vir_ty, .. }
        | VirExpr::WideLiteral { vir_ty, .. }
        | VirExpr::FloatLiteral { vir_ty, .. }
        | VirExpr::Import { vir_ty, .. }
        | VirExpr::ArrayLiteral { vir_ty, .. }
        | VirExpr::RepeatLiteral { vir_ty, .. }
        | VirExpr::StructLiteral { vir_ty, .. }
        | VirExpr::ClassInstance { vir_ty, .. }
        | VirExpr::BinaryOp { vir_ty, .. }
        | VirExpr::UnaryOp { vir_ty, .. }
        | VirExpr::Call { vir_ty, .. }
        | VirExpr::MethodCall { vir_ty, .. }
        | VirExpr::FieldLoad { vir_ty, .. }
        | VirExpr::Index { vir_ty, .. }
        | VirExpr::If { vir_ty, .. }
        | VirExpr::Match { vir_ty, .. }
        | VirExpr::Block { vir_ty, .. }
        | VirExpr::IsCheck { vir_ty, .. }
        | VirExpr::MetaAccess { vir_ty, .. }
        | VirExpr::LocalLoad { vir_ty, .. }
        | VirExpr::Lambda { vir_ty, .. }
        | VirExpr::NullCoalesce { vir_ty, .. }
        | VirExpr::OptionalChain { vir_ty, .. }
        | VirExpr::OptionalMethodCall { vir_ty, .. } => Some(*vir_ty),

        // Fixed-type expressions
        VirExpr::BoolLiteral(_) => Some(VirTypeId::BOOL),
        VirExpr::StringLiteral(_) => Some(VirTypeId::STRING),
        VirExpr::NilLiteral => Some(VirTypeId::NIL),
        VirExpr::Range { .. } => Some(VirTypeId::RANGE),
        VirExpr::TypeLiteral => Some(VirTypeId::METATYPE),
        VirExpr::Unreachable { .. } => Some(VirTypeId::NEVER),
        VirExpr::StringConcat { .. } | VirExpr::InterpolatedString { .. } => {
            Some(VirTypeId::STRING)
        }

        // Variants with non-standard type fields
        VirExpr::Coerce { vir_to, .. } => Some(*vir_to),
        VirExpr::Try {
            vir_success_type, ..
        } => Some(*vir_success_type),
        VirExpr::AsCast { vir_target_ty, .. } => Some(*vir_target_ty),

        // Void / side-effect only
        VirExpr::FieldStore { .. }
        | VirExpr::IndexStore { .. }
        | VirExpr::LocalStore { .. }
        | VirExpr::RcInc { .. }
        | VirExpr::RcDec { .. }
        | VirExpr::RcMove { .. }
        | VirExpr::Yield { .. } => None,
    }
}

/// Re-derive `FieldStorage::ByName` to a concrete `Direct` or `Heap` storage
/// after monomorphization resolves the object type to a concrete struct/class.
///
/// For structs, resolves to `Direct { slot }` where slot is the logical field
/// index.  For classes, resolves to `Heap { slot }` where slot is the physical
/// slot accounting for wide types (i128 occupying 2 consecutive slots).
fn rederive_field_storage(
    object: &VirRef,
    field: Symbol,
    storage: &mut FieldStorage,
    table: &VirTypeTable,
    entities: &VirEntityMetadata,
) {
    if !matches!(storage, FieldStorage::ByName) {
        return;
    }
    let Some(obj_vir_ty) = extract_vir_ty(object) else {
        return;
    };
    if let Some(resolved) = resolve_field_storage(obj_vir_ty, field, table, entities) {
        *storage = resolved;
    }
}

/// Resolve a field's storage from the concrete object type and field symbol.
///
/// Returns `None` if the type is not a struct/class, or the field cannot be
/// found in the entity metadata (keeps `ByName` for module fields, etc.).
fn resolve_field_storage(
    obj_vir_ty: VirTypeId,
    field: Symbol,
    table: &VirTypeTable,
    entities: &VirEntityMetadata,
) -> Option<FieldStorage> {
    match table.get(obj_vir_ty) {
        VirType::Struct { def, .. } => {
            let fd = entities.find_field_by_symbol(*def, field)?;
            Some(FieldStorage::Direct {
                slot: fd.slot as u32,
            })
        }
        VirType::Class { def, .. } => {
            let slot = compute_class_physical_slot(*def, field, table, entities)?;
            Some(FieldStorage::Heap { slot })
        }
        _ => None,
    }
}

/// Compute the physical slot for a class field, accounting for wide types.
///
/// Iterates fields in declaration order, accumulating physical slots.
/// Wide types (i128) occupy 2 consecutive slots; all others use 1.
fn compute_class_physical_slot(
    type_def_id: vole_identity::TypeDefId,
    target: Symbol,
    table: &VirTypeTable,
    entities: &VirEntityMetadata,
) -> Option<u32> {
    let td = entities.get_type_def(type_def_id)?;
    let mut physical_slot: u32 = 0;
    for &field_id in &td.fields {
        let fd = entities.get_field_def(field_id)?;
        if fd.symbol == Some(target) {
            return Some(physical_slot);
        }
        physical_slot += if table.is_wide(fd.vir_ty) { 2 } else { 1 };
    }
    None
}

/// Re-derive `FieldCoercionHint::Unresolved` entries in a `ClassInstance` after
/// monomorphization.
///
/// For each `Unresolved` hint, looks up the field's concrete VIR type via
/// type parameter substitution, then classifies:
/// - Field is interface, value is interface → `InterfaceCopy`
/// - Field is interface, value is concrete → `InterfaceBox`
/// - Otherwise → `None`
fn rederive_field_coercions(
    fields: &[(Symbol, VirRef)],
    coercions: &mut [FieldCoercionHint],
    type_def_id: vole_identity::TypeDefId,
    instance_vir_ty: VirTypeId,
    table: &VirTypeTable,
    entities: &VirEntityMetadata,
) {
    if !coercions.contains(&FieldCoercionHint::Unresolved) {
        return;
    }
    let subs = build_type_param_subs(instance_vir_ty, type_def_id, table, entities);
    for (i, hint) in coercions.iter_mut().enumerate() {
        if *hint != FieldCoercionHint::Unresolved {
            continue;
        }
        let (field_sym, val_ref) = &fields[i];
        *hint =
            resolve_single_field_coercion(*field_sym, val_ref, type_def_id, &subs, table, entities);
    }
}

/// Build a type parameter → concrete type substitution map from the
/// concrete `ClassInstance` VIR type and the original generic type def.
fn build_type_param_subs(
    instance_vir_ty: VirTypeId,
    type_def_id: vole_identity::TypeDefId,
    table: &VirTypeTable,
    entities: &VirEntityMetadata,
) -> FxHashMap<vole_identity::NameId, VirTypeId> {
    let type_args = match table.get(instance_vir_ty) {
        VirType::Class { type_args, .. } => type_args,
        _ => return FxHashMap::default(),
    };
    let Some(td) = entities.get_type_def(type_def_id) else {
        return FxHashMap::default();
    };
    td.type_params
        .iter()
        .zip(type_args.iter())
        .map(|(param, arg)| (*param, *arg))
        .collect()
}

/// Resolve a single field's coercion hint using the now-concrete types.
fn resolve_single_field_coercion(
    field_sym: Symbol,
    val_ref: &VirRef,
    type_def_id: vole_identity::TypeDefId,
    subs: &FxHashMap<vole_identity::NameId, VirTypeId>,
    table: &VirTypeTable,
    entities: &VirEntityMetadata,
) -> FieldCoercionHint {
    let Some(fd) = entities.find_field_by_symbol(type_def_id, field_sym) else {
        return FieldCoercionHint::Unresolved;
    };
    // Substitute generic type params to get the concrete field type.
    let concrete_field_ty = if subs.is_empty() {
        fd.vir_ty
    } else {
        match table.substitute_vir_ids(fd.vir_ty, subs) {
            Some(ty) => ty,
            None => return FieldCoercionHint::Unresolved,
        }
    };
    if !table.is_interface(concrete_field_ty) {
        return FieldCoercionHint::None;
    }
    // Field is interface-typed. Check if the init value is already an interface.
    let val_is_iface = extract_vir_ty(val_ref).is_some_and(|vt| table.is_interface(vt));
    if val_is_iface {
        FieldCoercionHint::InterfaceCopy
    } else {
        FieldCoercionHint::InterfaceBox
    }
}

/// Re-derive `FieldStorage` on destructure pattern fields after monomorphization.
///
/// Walks the pattern recursively.  For `Record` patterns, resolves any
/// `ByName` storage on each field to a concrete `Direct`/`Heap` variant
/// using the now-concrete source type.
fn rederive_destructure_pattern(
    pattern: &mut VirDestructurePattern,
    table: &VirTypeTable,
    entities: &VirEntityMetadata,
) {
    match pattern {
        VirDestructurePattern::Record {
            fields, source_ty, ..
        } => {
            let source = *source_ty;
            for field in fields.iter_mut() {
                if matches!(field.storage, FieldStorage::ByName)
                    && let Some(resolved) =
                        resolve_field_storage(source, field.field_name, table, entities)
                {
                    field.storage = resolved;
                }
            }
        }
        VirDestructurePattern::Tuple { elements, .. } => {
            for elem in elements.iter_mut() {
                rederive_destructure_pattern(&mut elem.pattern, table, entities);
            }
        }
        VirDestructurePattern::Bind { .. }
        | VirDestructurePattern::Wildcard
        | VirDestructurePattern::Module { .. } => {}
    }
}

/// Re-derive the `VirRcCleanup` for an RC node after monomorphization.
///
/// Extracts the value's VirTypeId from the inner expression and classifies
/// it into a concrete cleanup strategy using the VirTypeTable.  If the value
/// type cannot be extracted (should not happen for well-formed VIR), leaves
/// the cleanup unchanged.
fn rederive_rc_cleanup(
    value: &VirRef,
    cleanup: &mut crate::expr::VirRcCleanup,
    table: &VirTypeTable,
) {
    let Some(vir_ty) = extract_vir_ty(value) else {
        return;
    };
    *cleanup = classify_rc_cleanup(vir_ty, table);
}

/// Classify a VIR type into an RC cleanup strategy.
///
/// Mirrors the logic in codegen's `is_simple_rc_type` / `rc_state.rs` but
/// operates on `VirType` instead of `SemaType`.
///
/// This is public so that VIR lowering and the builder can eagerly classify
/// cleanup strategies for concrete types, avoiding the `Unresolved` fallback
/// at codegen time.
pub fn classify_rc_cleanup(vir_ty: VirTypeId, table: &VirTypeTable) -> crate::expr::VirRcCleanup {
    use crate::expr::VirRcCleanup;
    use crate::types::VirType;

    // Well-known primitives
    if vir_ty == VirTypeId::STRING {
        return VirRcCleanup::SimpleDecRef;
    }
    if vir_ty == VirTypeId::UNKNOWN {
        return VirRcCleanup::UnknownHeapCleanup;
    }

    // Guard against out-of-range type IDs (e.g., raw sema TypeIds that
    // haven't been translated yet).
    if (vir_ty.raw() as usize) >= table.len() {
        return VirRcCleanup::Unresolved;
    }

    let ty = table.get(vir_ty);

    match ty {
        // Simple RC types: single pointer to RC-managed heap object.
        VirType::Array { .. }
        | VirType::Function { .. }
        | VirType::Class { .. }
        | VirType::RuntimeIterator { .. } => VirRcCleanup::SimpleDecRef,

        // Interface: fat pointer — must extract data word first.
        VirType::Interface { .. } => VirRcCleanup::InterfaceDecRef,

        // Handle is a well-known primitive but RC-managed.
        VirType::Primitive(VirPrimitiveKind::Handle) => VirRcCleanup::SimpleDecRef,

        // Non-RC types (sentinels are Struct with zero layout, also non-RC).
        VirType::Primitive(_)
        | VirType::Struct { .. }
        | VirType::Void
        | VirType::Never
        | VirType::Range
        | VirType::MetaType
        | VirType::Error { .. } => VirRcCleanup::None,

        // Composite types — RC nodes don't handle these (scope cleanup does).
        VirType::FixedArray { .. } | VirType::Tuple { .. } => VirRcCleanup::None,

        // Union — RC nodes don't handle union-level cleanup directly.
        // The scope-based union cleanup system handles tag-based dispatch.
        VirType::Union { .. } | VirType::Optional { .. } => VirRcCleanup::None,

        // Fallible return types — not RC-managed themselves.
        VirType::Fallible { .. } => VirRcCleanup::None,

        // Unresolved generic parameter — keep unresolved.
        VirType::Param { .. } | VirType::Unknown => VirRcCleanup::Unresolved,
    }
}

/// Classify a VIR type into a capture RC kind for lambda captures.
///
/// Capture-eligible types are the subset of RC types that closures manage
/// via `rc_inc` on capture and `rc_dec` on drop: String, Array, Function,
/// Class.  Interfaces, handles, and iterators are RC but NOT capture-
/// eligible (interfaces are fat pointers, handles/iterators have different
/// lifecycle management).
///
/// This mirrors codegen's `vir_is_capture_rc_type()` but operates on
/// `VirType` directly so VIR can pre-classify during rederive.
pub fn classify_capture_rc_kind(
    vir_ty: VirTypeId,
    table: &VirTypeTable,
) -> crate::expr::VirCaptureRcKind {
    use crate::expr::VirCaptureRcKind;
    use crate::types::VirType;

    // String is a well-known capture-eligible RC type.
    if vir_ty == VirTypeId::STRING {
        return VirCaptureRcKind::Rc;
    }

    // UNKNOWN types are not capture-eligible.
    if vir_ty == VirTypeId::UNKNOWN {
        return VirCaptureRcKind::Unresolved;
    }

    // Guard against out-of-range type IDs.
    if (vir_ty.raw() as usize) >= table.len() {
        return VirCaptureRcKind::Unresolved;
    }

    match table.get(vir_ty) {
        // Capture-eligible RC types: string, array, function, class.
        VirType::Array { .. } | VirType::Function { .. } | VirType::Class { .. } => {
            VirCaptureRcKind::Rc
        }

        // NOT capture-eligible despite being RC: interface (fat pointer),
        // handle, iterator.
        VirType::Interface { .. }
        | VirType::RuntimeIterator { .. }
        | VirType::Primitive(VirPrimitiveKind::Handle) => VirCaptureRcKind::None,

        // Non-RC types.
        VirType::Primitive(_)
        | VirType::Struct { .. }
        | VirType::Void
        | VirType::Never
        | VirType::Range
        | VirType::MetaType
        | VirType::Error { .. }
        | VirType::FixedArray { .. }
        | VirType::Tuple { .. }
        | VirType::Union { .. }
        | VirType::Optional { .. }
        | VirType::Fallible { .. } => VirCaptureRcKind::None,

        // Unresolved generic parameter.
        VirType::Param { .. } | VirType::Unknown => VirCaptureRcKind::Unresolved,
    }
}

/// Re-derive the `LetStorageHint` for a `VirStmt::Let` after monomorphization.
///
/// After type substitution a generic `T` may resolve to a union, interface,
/// unknown, numeric, or scalar type.  This mirrors the classification in
/// `classify_let_storage` (sema side) but works on VirType / VirTypeTable
/// instead of TypeArena.
/// Re-derive the `ReturnConvention` for `VirStmt::Return` after
/// monomorphization.
///
/// After type substitution a generic return type may resolve to interface,
/// unknown, fallible, struct, union, or scalar.  This mirrors the
/// classification in `classify_return_convention` (sema side) but works on
/// VirType / VirTypeTable instead of TypeArena.
fn rederive_return_convention(vir_return_ty: VirTypeId, table: &VirTypeTable) -> ReturnConvention {
    match table.get(vir_return_ty) {
        VirType::Void => ReturnConvention::Void,
        VirType::Interface { .. } => ReturnConvention::InterfaceBox,
        VirType::Unknown => ReturnConvention::UnknownBox,
        VirType::Fallible { success, .. } => {
            if table.is_wide(*success) {
                ReturnConvention::WideFallible
            } else {
                ReturnConvention::Fallible
            }
        }
        VirType::Struct { .. } => ReturnConvention::Struct,
        VirType::Union { .. } | VirType::Optional { .. } => ReturnConvention::Union,
        _ => ReturnConvention::Scalar,
    }
}

fn rederive_let_storage(
    vir_ty: VirTypeId,
    init_vir_ty: Option<VirTypeId>,
    existing: &LetStorageHint,
    table: &VirTypeTable,
) -> LetStorageHint {
    match table.get(vir_ty) {
        VirType::Unknown => LetStorageHint::Unknown,
        VirType::Union { .. } | VirType::Optional { .. } => {
            // Re-derive init_is_union from the init expression's now-concrete
            // VIR type.  If the init type cannot be extracted, preserve the
            // existing annotation.
            let init_is_union = init_vir_ty.is_some_and(|t| table.is_union(t));
            // If the existing storage is already Union with a pre-computed
            // tag hint, preserve it — the rewrite pass has already remapped
            // the VirTypeIds inside the hint.  Otherwise (e.g. the storage
            // was Scalar before monomorphization resolved the type to a
            // union), leave the hint as None.
            match existing {
                LetStorageHint::Union { tag_hint, .. } => LetStorageHint::Union {
                    tag_hint: *tag_hint,
                    init_is_union,
                },
                _ => LetStorageHint::Union {
                    tag_hint: None,
                    init_is_union,
                },
            }
        }
        VirType::Interface { .. } => {
            // If the existing hint is already RuntimeIterator (pre-classified
            // by sema lowering), preserve it.
            if matches!(existing, LetStorageHint::RuntimeIterator) {
                LetStorageHint::RuntimeIterator
            } else {
                LetStorageHint::Interface
            }
        }
        VirType::Primitive(p) if p.is_numeric() => LetStorageHint::Numeric,
        _ => LetStorageHint::Scalar,
    }
}

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::func::VirBody;
    use crate::monomorph::substitute::{TypeSubstitution, substitute_types};
    use vole_identity::{FunctionId, MethodId, NameId, Symbol, TypeDefId, TypeId};

    /// Helper: create a NameId for testing.
    fn name(n: u32) -> NameId {
        NameId::new_for_test(n)
    }

    /// Helper: create a VirTypeId for testing.
    fn type_id(n: u32) -> VirTypeId {
        VirTypeId::from_raw(n)
    }

    /// Helper: create a sema TypeId for StringConversion tests.
    fn sema_type_id(n: u32) -> TypeId {
        TypeId::from_raw(n)
    }

    /// Helper: create a Symbol for testing.
    fn sym(n: u32) -> Symbol {
        Symbol::synthetic(n)
    }

    /// Helper: create an empty VirEntityMetadata for tests that don't
    /// exercise field storage rederivation.
    fn empty_entities() -> VirEntityMetadata {
        VirEntityMetadata::new()
    }

    /// Helper: build a minimal VirFunction wrapping a trailing expression.
    fn func_with_trailing(expr: VirExpr) -> VirFunction {
        VirFunction {
            id: FunctionId::new(1),
            name: "test_fn".to_string(),
            params: vec![],
            return_type: VirTypeId::VOID,
            vir_return_type: VirTypeId::VOID,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(expr)),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        }
    }

    /// Helper: build a minimal VirFunction wrapping statements.
    fn func_with_stmts(stmts: Vec<VirStmt>) -> VirFunction {
        VirFunction {
            id: FunctionId::new(1),
            name: "test_fn".to_string(),
            params: vec![],
            return_type: VirTypeId::VOID,
            vir_return_type: VirTypeId::VOID,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts,
                trailing: None,
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        }
    }

    // -----------------------------------------------------------------------
    // IsCheckResult tests
    // -----------------------------------------------------------------------

    #[test]
    fn is_check_already_resolved_unchanged() {
        let table = VirTypeTable::new();
        let mut func = func_with_trailing(VirExpr::IsCheck {
            value: Box::new(VirExpr::LocalLoad {
                name: sym(1),
                ty: type_id(10),
                vir_ty: VirTypeId::I64,
            }),
            result: IsCheckResult::AlwaysTrue,
            ty: type_id(20),
            vir_ty: VirTypeId::BOOL,
        });

        rederive_decisions(&mut func, &table, &empty_entities());

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::IsCheck { result, .. } => {
                assert_eq!(*result, IsCheckResult::AlwaysTrue);
            }
            other => panic!("expected IsCheck, got {other:?}"),
        }
    }

    #[test]
    fn is_check_tag_unchanged() {
        let table = VirTypeTable::new();
        let mut func = func_with_trailing(VirExpr::IsCheck {
            value: Box::new(VirExpr::LocalLoad {
                name: sym(1),
                ty: type_id(10),
                vir_ty: VirTypeId::I64,
            }),
            result: IsCheckResult::CheckTag(2),
            ty: type_id(20),
            vir_ty: VirTypeId::BOOL,
        });

        rederive_decisions(&mut func, &table, &empty_entities());

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::IsCheck { result, .. } => {
                assert_eq!(*result, IsCheckResult::CheckTag(2));
            }
            other => panic!("expected IsCheck, got {other:?}"),
        }
    }

    #[test]
    fn is_check_unknown_concrete_equal_becomes_always_true() {
        let table = VirTypeTable::new();
        let mut func = func_with_trailing(VirExpr::IsCheck {
            value: Box::new(VirExpr::LocalLoad {
                name: sym(1),
                ty: type_id(10),
                vir_ty: VirTypeId::I64,
            }),
            result: IsCheckResult::CheckUnknown(type_id(20), VirTypeId::I64),
            ty: type_id(30),
            vir_ty: VirTypeId::BOOL,
        });

        rederive_decisions(&mut func, &table, &empty_entities());

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::IsCheck { result, .. } => {
                assert_eq!(*result, IsCheckResult::AlwaysTrue);
            }
            other => panic!("expected IsCheck, got {other:?}"),
        }
    }

    #[test]
    fn is_check_unknown_with_param_type_unchanged() {
        // CheckUnknown where tested VirTypeId still points to a Param
        // (substitution incomplete) should stay as CheckUnknown.
        let mut table = VirTypeTable::new();
        let param_id = table.intern(VirType::Param { name: name(100) }, None);

        let mut func = func_with_trailing(VirExpr::IsCheck {
            value: Box::new(VirExpr::LocalLoad {
                name: sym(1),
                ty: type_id(10),
                vir_ty: param_id,
            }),
            result: IsCheckResult::CheckUnknown(type_id(20), param_id),
            ty: type_id(30),
            vir_ty: VirTypeId::BOOL,
        });

        rederive_decisions(&mut func, &table, &empty_entities());

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::IsCheck { result, .. } => {
                assert_eq!(*result, IsCheckResult::CheckUnknown(type_id(20), param_id));
            }
            other => panic!("expected IsCheck, got {other:?}"),
        }
    }

    #[test]
    fn is_check_unknown_union_variant_becomes_check_tag() {
        let mut table = VirTypeTable::new();
        let union_ty = table.intern(
            VirType::Union {
                variants: vec![VirTypeId::BOOL, VirTypeId::STRING],
            },
            None,
        );

        let mut func = func_with_trailing(VirExpr::IsCheck {
            value: Box::new(VirExpr::LocalLoad {
                name: sym(1),
                ty: type_id(10),
                vir_ty: union_ty,
            }),
            result: IsCheckResult::CheckUnknown(type_id(20), VirTypeId::STRING),
            ty: type_id(30),
            vir_ty: VirTypeId::BOOL,
        });

        rederive_decisions(&mut func, &table, &empty_entities());

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::IsCheck { result, .. } => {
                assert_eq!(*result, IsCheckResult::CheckTag(1));
            }
            other => panic!("expected IsCheck, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // StringConversion tests
    // -----------------------------------------------------------------------

    #[test]
    fn string_conversion_generic_i64_becomes_i64_to_string() {
        let table = VirTypeTable::new();
        let mut func = func_with_trailing(VirExpr::InterpolatedString {
            parts: vec![VirStringPart::Expr {
                value: Box::new(VirExpr::LocalLoad {
                    name: sym(1),
                    ty: type_id(10),
                    vir_ty: VirTypeId::I64,
                }),
                conversion: StringConversion::Generic {
                    type_id: sema_type_id(10),
                },
            }],
        });

        rederive_decisions(&mut func, &table, &empty_entities());

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::InterpolatedString { parts } => match &parts[0] {
                VirStringPart::Expr { conversion, .. } => {
                    assert_eq!(*conversion, StringConversion::I64ToString);
                }
                other => panic!("expected Expr part, got {other:?}"),
            },
            other => panic!("expected InterpolatedString, got {other:?}"),
        }
    }

    #[test]
    fn string_conversion_generic_f64_becomes_f64_to_string() {
        let table = VirTypeTable::new();
        let mut func = func_with_trailing(VirExpr::InterpolatedString {
            parts: vec![VirStringPart::Expr {
                value: Box::new(VirExpr::LocalLoad {
                    name: sym(1),
                    ty: type_id(10),
                    vir_ty: VirTypeId::F64,
                }),
                conversion: StringConversion::Generic {
                    type_id: sema_type_id(10),
                },
            }],
        });

        rederive_decisions(&mut func, &table, &empty_entities());

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::InterpolatedString { parts } => match &parts[0] {
                VirStringPart::Expr { conversion, .. } => {
                    assert_eq!(*conversion, StringConversion::F64ToString);
                }
                other => panic!("expected Expr part, got {other:?}"),
            },
            other => panic!("expected InterpolatedString, got {other:?}"),
        }
    }

    #[test]
    fn string_conversion_generic_bool_becomes_bool_to_string() {
        let table = VirTypeTable::new();
        let mut func = func_with_trailing(VirExpr::InterpolatedString {
            parts: vec![VirStringPart::Expr {
                value: Box::new(VirExpr::LocalLoad {
                    name: sym(1),
                    ty: type_id(10),
                    vir_ty: VirTypeId::BOOL,
                }),
                conversion: StringConversion::Generic {
                    type_id: sema_type_id(10),
                },
            }],
        });

        rederive_decisions(&mut func, &table, &empty_entities());

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::InterpolatedString { parts } => match &parts[0] {
                VirStringPart::Expr { conversion, .. } => {
                    assert_eq!(*conversion, StringConversion::BoolToString);
                }
                other => panic!("expected Expr part, got {other:?}"),
            },
            other => panic!("expected InterpolatedString, got {other:?}"),
        }
    }

    #[test]
    fn string_conversion_generic_string_becomes_identity() {
        let table = VirTypeTable::new();
        let mut func = func_with_trailing(VirExpr::InterpolatedString {
            parts: vec![VirStringPart::Expr {
                value: Box::new(VirExpr::LocalLoad {
                    name: sym(1),
                    ty: type_id(10),
                    vir_ty: VirTypeId::STRING,
                }),
                conversion: StringConversion::Generic {
                    type_id: sema_type_id(10),
                },
            }],
        });

        rederive_decisions(&mut func, &table, &empty_entities());

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::InterpolatedString { parts } => match &parts[0] {
                VirStringPart::Expr { conversion, .. } => {
                    assert_eq!(*conversion, StringConversion::Identity);
                }
                other => panic!("expected Expr part, got {other:?}"),
            },
            other => panic!("expected InterpolatedString, got {other:?}"),
        }
    }

    #[test]
    fn string_conversion_generic_i128_becomes_i128_to_string() {
        let table = VirTypeTable::new();
        let mut func = func_with_trailing(VirExpr::InterpolatedString {
            parts: vec![VirStringPart::Expr {
                value: Box::new(VirExpr::LocalLoad {
                    name: sym(1),
                    ty: type_id(10),
                    vir_ty: VirTypeId::I128,
                }),
                conversion: StringConversion::Generic {
                    type_id: sema_type_id(10),
                },
            }],
        });

        rederive_decisions(&mut func, &table, &empty_entities());

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::InterpolatedString { parts } => match &parts[0] {
                VirStringPart::Expr { conversion, .. } => {
                    assert_eq!(*conversion, StringConversion::I128ToString);
                }
                other => panic!("expected Expr part, got {other:?}"),
            },
            other => panic!("expected InterpolatedString, got {other:?}"),
        }
    }

    #[test]
    fn string_conversion_generic_nil_becomes_nil_to_string() {
        let table = VirTypeTable::new();
        let mut func = func_with_trailing(VirExpr::InterpolatedString {
            parts: vec![VirStringPart::Expr {
                value: Box::new(VirExpr::NilLiteral),
                conversion: StringConversion::Generic {
                    type_id: sema_type_id(10),
                },
            }],
        });

        rederive_decisions(&mut func, &table, &empty_entities());

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::InterpolatedString { parts } => match &parts[0] {
                VirStringPart::Expr { conversion, .. } => {
                    assert_eq!(*conversion, StringConversion::NilToString);
                }
                other => panic!("expected Expr part, got {other:?}"),
            },
            other => panic!("expected InterpolatedString, got {other:?}"),
        }
    }

    #[test]
    fn string_conversion_generic_array_becomes_array_to_string() {
        let mut table = VirTypeTable::new();
        let arr_ty = table.intern(
            VirType::Array {
                elem: VirTypeId::I64,
            },
            None,
        );

        let mut func = func_with_trailing(VirExpr::InterpolatedString {
            parts: vec![VirStringPart::Expr {
                value: Box::new(VirExpr::LocalLoad {
                    name: sym(1),
                    ty: type_id(10),
                    vir_ty: arr_ty,
                }),
                conversion: StringConversion::Generic {
                    type_id: sema_type_id(10),
                },
            }],
        });

        rederive_decisions(&mut func, &table, &empty_entities());

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::InterpolatedString { parts } => match &parts[0] {
                VirStringPart::Expr { conversion, .. } => {
                    assert_eq!(*conversion, StringConversion::ArrayToString);
                }
                other => panic!("expected Expr part, got {other:?}"),
            },
            other => panic!("expected InterpolatedString, got {other:?}"),
        }
    }

    #[test]
    fn string_conversion_non_generic_unchanged() {
        let table = VirTypeTable::new();
        let mut func = func_with_trailing(VirExpr::InterpolatedString {
            parts: vec![VirStringPart::Expr {
                value: Box::new(VirExpr::LocalLoad {
                    name: sym(1),
                    ty: type_id(10),
                    vir_ty: VirTypeId::I64,
                }),
                conversion: StringConversion::F64ToString,
            }],
        });

        rederive_decisions(&mut func, &table, &empty_entities());

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::InterpolatedString { parts } => match &parts[0] {
                VirStringPart::Expr { conversion, .. } => {
                    assert_eq!(*conversion, StringConversion::F64ToString);
                }
                other => panic!("expected Expr part, got {other:?}"),
            },
            other => panic!("expected InterpolatedString, got {other:?}"),
        }
    }

    #[test]
    fn string_conversion_generic_f32_becomes_f32_to_string() {
        let table = VirTypeTable::new();
        let mut func = func_with_trailing(VirExpr::InterpolatedString {
            parts: vec![VirStringPart::Expr {
                value: Box::new(VirExpr::LocalLoad {
                    name: sym(1),
                    ty: type_id(10),
                    vir_ty: VirTypeId::F32,
                }),
                conversion: StringConversion::Generic {
                    type_id: sema_type_id(10),
                },
            }],
        });

        rederive_decisions(&mut func, &table, &empty_entities());

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::InterpolatedString { parts } => match &parts[0] {
                VirStringPart::Expr { conversion, .. } => {
                    assert_eq!(*conversion, StringConversion::F32ToString);
                }
                other => panic!("expected Expr part, got {other:?}"),
            },
            other => panic!("expected InterpolatedString, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // MetaAccess tests
    // -----------------------------------------------------------------------

    #[test]
    fn meta_access_type_param_rederived_to_static_for_nominal() {
        let mut table = VirTypeTable::new();
        let class_def = TypeDefId::new(42);
        let class_ty = table.intern(
            VirType::Class {
                def: class_def,
                type_args: vec![],
            },
            None,
        );

        let mut func = func_with_trailing(VirExpr::MetaAccess {
            kind: VirMetaKind::TypeParam {
                name_id: name(100),
                value: Box::new(VirExpr::LocalLoad {
                    name: sym(1),
                    ty: type_id(10),
                    vir_ty: class_ty,
                }),
            },
            ty: type_id(20),
            vir_ty: VirTypeId::METATYPE,
        });

        rederive_decisions(&mut func, &table, &empty_entities());

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::MetaAccess { kind, .. } => match kind {
                VirMetaKind::Static { type_def, object } => {
                    assert_eq!(*type_def, class_def);
                    match object.as_deref() {
                        Some(VirExpr::LocalLoad { vir_ty, .. }) => assert_eq!(*vir_ty, class_ty),
                        other => panic!("expected LocalLoad object, got {other:?}"),
                    }
                }
                other => panic!("expected Static meta kind, got {other:?}"),
            },
            other => panic!("expected MetaAccess, got {other:?}"),
        }
    }

    #[test]
    fn meta_access_type_param_rederived_to_dynamic_for_interface() {
        let mut table = VirTypeTable::new();
        let interface_ty = table.intern(
            VirType::Interface {
                def: TypeDefId::new(7),
                type_args: vec![],
            },
            None,
        );

        let mut func = func_with_trailing(VirExpr::MetaAccess {
            kind: VirMetaKind::TypeParam {
                name_id: name(200),
                value: Box::new(VirExpr::LocalLoad {
                    name: sym(1),
                    ty: type_id(10),
                    vir_ty: interface_ty,
                }),
            },
            ty: type_id(20),
            vir_ty: VirTypeId::METATYPE,
        });

        rederive_decisions(&mut func, &table, &empty_entities());

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::MetaAccess { kind, .. } => match kind {
                VirMetaKind::Dynamic { value } => match value.as_ref() {
                    VirExpr::LocalLoad { vir_ty, .. } => assert_eq!(*vir_ty, interface_ty),
                    other => panic!("expected LocalLoad value, got {other:?}"),
                },
                other => panic!("expected Dynamic meta kind, got {other:?}"),
            },
            other => panic!("expected MetaAccess, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // VirIterKind tests
    // -----------------------------------------------------------------------

    #[test]
    fn iter_kind_generic_stays_generic_without_iterable_type() {
        // VirIterKind::Generic cannot be resolved without the iterable's
        // VirTypeId.  It stays Generic, which codegen handles at runtime.
        let table = VirTypeTable::new();
        let mut func = func_with_stmts(vec![VirStmt::For(crate::stmt::VirFor {
            var_name: sym(1),
            var_type: type_id(10),
            vir_var_type: VirTypeId::I64,
            iterable: Box::new(VirExpr::LocalLoad {
                name: sym(2),
                ty: type_id(20),
                vir_ty: VirTypeId::RANGE,
            }),
            body: VirBody {
                stmts: vec![],
                trailing: None,
            },
            kind: VirIterKind::Generic {
                elem_type: type_id(10),
                vir_elem_type: VirTypeId::I64,
            },
        })]);

        rederive_decisions(&mut func, &table, &empty_entities());

        match &func.body.stmts[0] {
            VirStmt::For(vir_for) => match &vir_for.kind {
                VirIterKind::Generic { vir_elem_type, .. } => {
                    assert_eq!(*vir_elem_type, VirTypeId::I64);
                }
                other => panic!("expected Generic, got {other:?}"),
            },
            other => panic!("expected For, got {other:?}"),
        }
    }

    #[test]
    fn iter_kind_concrete_unchanged() {
        // Non-generic VirIterKind variants should pass through unchanged.
        let table = VirTypeTable::new();
        let mut func = func_with_stmts(vec![VirStmt::For(crate::stmt::VirFor {
            var_name: sym(1),
            var_type: type_id(10),
            vir_var_type: VirTypeId::I64,
            iterable: Box::new(VirExpr::Range {
                start: Box::new(VirExpr::IntLiteral {
                    value: 0,
                    ty: type_id(10),
                    vir_ty: VirTypeId::I64,
                }),
                end: Box::new(VirExpr::IntLiteral {
                    value: 10,
                    ty: type_id(10),
                    vir_ty: VirTypeId::I64,
                }),
                inclusive: false,
            }),
            body: VirBody {
                stmts: vec![],
                trailing: None,
            },
            kind: VirIterKind::Range,
        })]);

        rederive_decisions(&mut func, &table, &empty_entities());

        match &func.body.stmts[0] {
            VirStmt::For(vir_for) => assert!(matches!(vir_for.kind, VirIterKind::Range)),
            other => panic!("expected For, got {other:?}"),
        }
    }

    #[test]
    fn iter_array_union_storage_rederived_inline() {
        let mut table = VirTypeTable::new();
        let elem_union = table.intern(
            VirType::Union {
                variants: vec![VirTypeId::STRING, VirTypeId::BOOL],
            },
            None,
        );

        let mut func = func_with_stmts(vec![VirStmt::For(crate::stmt::VirFor {
            var_name: sym(1),
            var_type: type_id(10),
            vir_var_type: VirTypeId::STRING,
            iterable: Box::new(VirExpr::NilLiteral),
            body: VirBody {
                stmts: vec![],
                trailing: None,
            },
            kind: VirIterKind::Array {
                elem_type: type_id(10),
                vir_elem_type: elem_union,
                union_storage: None,
            },
        })]);

        rederive_decisions(&mut func, &table, &empty_entities());

        match &func.body.stmts[0] {
            VirStmt::For(vir_for) => match vir_for.kind {
                VirIterKind::Array { union_storage, .. } => {
                    assert_eq!(union_storage, Some(UnionStorageKind::Inline));
                }
                _ => panic!("expected array iter kind"),
            },
            _ => panic!("expected for stmt"),
        }
    }

    #[test]
    fn index_union_storage_rederived_heap() {
        let mut table = VirTypeTable::new();
        let elem_union = table.intern(
            VirType::Union {
                variants: vec![VirTypeId::I64, VirTypeId::NIL],
            },
            None,
        );
        let array_ty = table.intern(VirType::Array { elem: elem_union }, None);

        let mut func = func_with_trailing(VirExpr::Index {
            object: Box::new(VirExpr::LocalLoad {
                name: sym(1),
                ty: type_id(10),
                vir_ty: array_ty,
            }),
            index: Box::new(VirExpr::IntLiteral {
                value: 0,
                ty: type_id(20),
                vir_ty: VirTypeId::I64,
            }),
            ty: type_id(30),
            vir_ty: elem_union,
            union_storage: None,
        });

        rederive_decisions(&mut func, &table, &empty_entities());

        let trailing = func.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::Index { union_storage, .. } => {
                assert_eq!(*union_storage, Some(UnionStorageKind::Heap));
            }
            other => panic!("expected Index, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // End-to-end: substitution + rewrite + rederive
    // -----------------------------------------------------------------------

    #[test]
    fn end_to_end_string_conversion_generic_resolves_after_monomorph() {
        use crate::monomorph::rewrite::{RewriteCtx, rewrite_function};

        // Source: fn show(x: T) -> string { "${x}" }
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);

        let func = VirFunction {
            id: FunctionId::new(1),
            name: "show".to_string(),
            params: vec![(sym(1), type_id(10), param_id)],
            return_type: type_id(20),
            vir_return_type: VirTypeId::STRING,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::InterpolatedString {
                    parts: vec![VirStringPart::Expr {
                        value: Box::new(VirExpr::LocalLoad {
                            name: sym(1),
                            ty: type_id(10),
                            vir_ty: param_id,
                        }),
                        conversion: StringConversion::Generic {
                            type_id: sema_type_id(10),
                        },
                    }],
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        // Substitute T -> I64
        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I64);
        let mapping = substitute_types(&source, &mut target, &subs);

        // Rewrite
        let ctx = RewriteCtx::new(mapping);
        let mut result = rewrite_function(&func, &ctx);

        // Re-derive decisions
        rederive_decisions(&mut result, &target, &empty_entities());

        // Verify: StringConversion::Generic should now be I64ToString
        let trailing = result.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::InterpolatedString { parts } => match &parts[0] {
                VirStringPart::Expr { conversion, .. } => {
                    assert_eq!(*conversion, StringConversion::I64ToString);
                }
                other => panic!("expected Expr part, got {other:?}"),
            },
            other => panic!("expected InterpolatedString, got {other:?}"),
        }
    }

    #[test]
    fn end_to_end_is_check_pattern_rederived() {
        use crate::monomorph::rewrite::{RewriteCtx, rewrite_function};

        // Source: fn check(x: T) -> bool { x is T }
        let mut source = VirTypeTable::new();
        let t_name = name(100);
        let param_id = source.intern(VirType::Param { name: t_name }, None);

        let func = VirFunction {
            id: FunctionId::new(1),
            name: "check".to_string(),
            params: vec![(sym(1), type_id(10), param_id)],
            return_type: type_id(20),
            vir_return_type: VirTypeId::BOOL,
            return_abi: crate::func::ReturnAbi::Single,
            body: VirBody {
                stmts: vec![],
                trailing: Some(Box::new(VirExpr::Match {
                    scrutinee: Box::new(VirExpr::LocalLoad {
                        name: sym(1),
                        ty: type_id(10),
                        vir_ty: param_id,
                    }),
                    arms: vec![crate::expr::VirMatchArm {
                        pattern: VirPattern::TypeCheck {
                            result: IsCheckResult::CheckUnknown(type_id(10), param_id),
                            tested_type: type_id(10),
                            vir_tested_type: param_id,
                            binding: None,
                        },
                        guard: None,
                        body: VirBody {
                            stmts: vec![],
                            trailing: Some(Box::new(VirExpr::BoolLiteral(true))),
                        },
                        ty: type_id(20),
                        vir_ty: VirTypeId::BOOL,
                    }],
                    ty: type_id(20),
                    vir_ty: VirTypeId::BOOL,
                    result_is_union: false,
                })),
            },
            mangled_name_id: None,
            method_id: None,
            type_params: Vec::new(),
        };

        // Substitute T -> I64
        let mut target = VirTypeTable::new();
        let mut subs = TypeSubstitution::default();
        subs.insert(t_name, VirTypeId::I64);
        let mapping = substitute_types(&source, &mut target, &subs);

        let ctx = RewriteCtx::new(mapping);
        let mut result = rewrite_function(&func, &ctx);

        rederive_decisions(&mut result, &target, &empty_entities());

        // TypeCheck result is recomputed from concrete VIR types.
        let trailing = result.body.trailing.as_ref().unwrap();
        match trailing.as_ref() {
            VirExpr::Match { arms, .. } => match &arms[0].pattern {
                VirPattern::TypeCheck { result, .. } => {
                    assert_eq!(*result, IsCheckResult::AlwaysTrue);
                }
                other => panic!("expected TypeCheck, got {other:?}"),
            },
            other => panic!("expected Match, got {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // extract_vir_ty tests
    // -----------------------------------------------------------------------

    #[test]
    fn extract_vir_ty_from_local_load() {
        let expr = VirExpr::LocalLoad {
            name: sym(1),
            ty: type_id(10),
            vir_ty: VirTypeId::F64,
        };
        assert_eq!(extract_vir_ty(&expr), Some(VirTypeId::F64));
    }

    #[test]
    fn extract_vir_ty_from_bool_literal() {
        assert_eq!(
            extract_vir_ty(&VirExpr::BoolLiteral(true)),
            Some(VirTypeId::BOOL)
        );
    }

    #[test]
    fn extract_vir_ty_from_nil_literal() {
        assert_eq!(extract_vir_ty(&VirExpr::NilLiteral), Some(VirTypeId::NIL));
    }

    #[test]
    fn extract_vir_ty_from_string_literal() {
        assert_eq!(
            extract_vir_ty(&VirExpr::StringLiteral(sym(1))),
            Some(VirTypeId::STRING)
        );
    }

    #[test]
    fn extract_vir_ty_from_void_expr_is_none() {
        let expr = VirExpr::RcInc {
            value: Box::new(VirExpr::NilLiteral),
            cleanup: crate::expr::VirRcCleanup::Unresolved,
        };
        assert_eq!(extract_vir_ty(&expr), None);
    }

    // -----------------------------------------------------------------------
    // Call target reclassification tests
    // -----------------------------------------------------------------------

    /// Helper: build a RederiveCallCtx for testing with the given interner.
    fn call_ctx_with_interner<'a>(
        interner: &'a Interner,
        name_table: &'a vole_identity::NameTable,
        params: Vec<(Symbol, VirTypeId)>,
    ) -> RederiveCallCtx<'a> {
        let impl_dispatch = Box::leak(Box::new(VirImplementDispatch::new()));
        RederiveCallCtx {
            interner,
            name_table,
            module_id: vole_identity::ModuleId::new(0),
            implement_dispatch: impl_dispatch,
            params,
            local_vars: RefCell::new(FxHashMap::default()),
            captures: RefCell::new(FxHashMap::default()),
        }
    }

    /// Helper: build an Unresolved CallTarget for testing.
    fn unresolved_target(callee_sym: Symbol, line: u32) -> CallTarget {
        CallTarget::Unresolved {
            callee_sym,
            call_node_id: vole_identity::NodeId::new_for_test(0),
            line,
            resolved_call_args: None,
            lambda_defaults: None,
            monomorph_key: None,
        }
    }

    #[test]
    fn rederive_unresolved_assert_to_intrinsic() {
        let mut interner = Interner::new();
        let assert_sym = interner.intern("assert");
        let name_table = vole_identity::NameTable::new();

        let mut target = unresolved_target(assert_sym, 42);
        let table = VirTypeTable::new();
        let entities = empty_entities();
        let ctx = call_ctx_with_interner(&interner, &name_table, vec![]);

        rederive_call_target(&mut target, &table, &entities, &ctx);

        assert!(matches!(
            target,
            CallTarget::Intrinsic {
                key: IntrinsicKey::Assert,
                line: 42,
            }
        ));
    }

    #[test]
    fn rederive_unresolved_print_char_to_intrinsic() {
        let mut interner = Interner::new();
        let pc_sym = interner.intern("print_char");
        let name_table = vole_identity::NameTable::new();

        let mut target = unresolved_target(pc_sym, 10);
        let table = VirTypeTable::new();
        let entities = empty_entities();
        let ctx = call_ctx_with_interner(&interner, &name_table, vec![]);

        rederive_call_target(&mut target, &table, &entities, &ctx);

        assert!(matches!(
            target,
            CallTarget::Intrinsic {
                key: IntrinsicKey::PrintChar,
                line: 10,
            }
        ));
    }

    #[test]
    fn rederive_unresolved_closure_param_to_closure_variable() {
        let mut interner = Interner::new();
        let callback_sym = interner.intern("callback");
        let name_table = vole_identity::NameTable::new();

        let mut table = VirTypeTable::new();
        let func_ty = table.intern(
            VirType::Function {
                params: vec![VirTypeId::I64],
                ret: VirTypeId::STRING,
            },
            None,
        );

        let mut target = unresolved_target(callback_sym, 5);
        let entities = empty_entities();
        let ctx = call_ctx_with_interner(&interner, &name_table, vec![(callback_sym, func_ty)]);

        rederive_call_target(&mut target, &table, &entities, &ctx);

        match &target {
            CallTarget::ClosureVariable {
                var_name, vir_type, ..
            } => {
                assert_eq!(*var_name, callback_sym);
                assert_eq!(*vir_type, func_ty);
            }
            other => panic!("expected ClosureVariable, got {other:?}"),
        }
    }

    #[test]
    fn rederive_unresolved_local_closure_to_closure_variable() {
        let mut interner = Interner::new();
        let add_five_sym = interner.intern("add_five");
        let name_table = vole_identity::NameTable::new();

        let mut table = VirTypeTable::new();
        let func_ty = table.intern(
            VirType::Function {
                params: vec![VirTypeId::I64],
                ret: VirTypeId::I64,
            },
            None,
        );

        let mut target = unresolved_target(add_five_sym, 38);
        let entities = empty_entities();
        let ctx = call_ctx_with_interner(&interner, &name_table, vec![]);

        // Simulate a let-bound function-typed local by inserting into local_vars.
        ctx.local_vars.borrow_mut().insert(add_five_sym, func_ty);

        rederive_call_target(&mut target, &table, &entities, &ctx);

        match &target {
            CallTarget::ClosureVariable {
                var_name, vir_type, ..
            } => {
                assert_eq!(*var_name, add_five_sym);
                assert_eq!(*vir_type, func_ty);
            }
            other => panic!("expected ClosureVariable, got {other:?}"),
        }
    }

    #[test]
    fn rederive_unresolved_non_function_param_stays_unresolved() {
        let mut interner = Interner::new();
        let x_sym = interner.intern("x");
        let name_table = vole_identity::NameTable::new();

        let table = VirTypeTable::new();
        let mut target = unresolved_target(x_sym, 1);
        let entities = empty_entities();
        let ctx = call_ctx_with_interner(&interner, &name_table, vec![(x_sym, VirTypeId::I64)]);

        rederive_call_target(&mut target, &table, &entities, &ctx);

        assert!(matches!(target, CallTarget::Unresolved { .. }));
    }

    #[test]
    fn rederive_non_unresolved_target_unchanged() {
        let interner = Interner::new();
        let name_table = vole_identity::NameTable::new();

        let mut target = CallTarget::Direct {
            function_id: FunctionId::new(42),
        };

        let table = VirTypeTable::new();
        let entities = empty_entities();
        let ctx = call_ctx_with_interner(&interner, &name_table, vec![]);

        rederive_call_target(&mut target, &table, &entities, &ctx);

        assert!(matches!(target, CallTarget::Direct { .. }));
    }

    #[test]
    fn rederive_unresolved_direct_function() {
        let mut interner = Interner::new();
        let helper_sym = interner.intern("helper");
        let mut name_table = vole_identity::NameTable::new();
        let module_id = name_table.module_id("main");
        let helper_name = name_table.intern(module_id, &[helper_sym], &interner);

        let func_id = FunctionId::new(99);
        let mut entities = VirEntityMetadata::new();
        entities.insert_function_def(crate::entity_metadata::VirFunctionDef {
            id: func_id,
            name_id: helper_name,
            full_name_id: helper_name,
            module: module_id,
            param_types: vec![VirTypeId::I64],
            return_type: VirTypeId::I64,
            param_names: vec!["x".to_string()],
            required_params: 1,
            has_defaults: vec![false],
            is_generic: false,
            is_external: false,
            generator_element_type: None,
            sema_param_types: vec![],
            sema_return_type: TypeId::from_raw(0),
            sema_generator_element_type: None,
        });
        entities.insert_function_by_name(helper_name, func_id);

        let mut target = unresolved_target(helper_sym, 7);
        let table = VirTypeTable::new();
        let impl_dispatch = VirImplementDispatch::new();
        let ctx = RederiveCallCtx {
            interner: &interner,
            name_table: &name_table,
            module_id,
            implement_dispatch: &impl_dispatch,
            params: vec![],
            local_vars: RefCell::new(FxHashMap::default()),
            captures: RefCell::new(FxHashMap::default()),
        };

        rederive_call_target(&mut target, &table, &entities, &ctx);

        match &target {
            CallTarget::Direct { function_id } => {
                assert_eq!(*function_id, func_id);
            }
            other => panic!("expected Direct, got {other:?}"),
        }
    }

    /// Helper: build a VirEntityMetadata with a single-method interface (functional interface).
    fn entities_with_functional_interface(
        type_def_id: TypeDefId,
        method_id: MethodId,
    ) -> VirEntityMetadata {
        let mut entities = VirEntityMetadata::new();
        entities.insert_type_def(crate::entity_metadata::VirTypeDef {
            id: type_def_id,
            name_id: name(200),
            kind: crate::entity_metadata::VirTypeDefKind::Interface,
            fields: vec![],
            field_types: vec![],
            methods: vec![method_id],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: vole_identity::ModuleId::new(0),
            is_generic: false,
            generic_field_types: None,
            generic_field_names: None,
        });
        entities.insert_method_def(crate::entity_metadata::VirMethodDef {
            id: method_id,
            name_id: name(201),
            full_name_id: name(202),
            defining_type: type_def_id,
            signature_id: sema_type_id(0),
            has_default: false,
            is_static: false,
            external_binding: None,
            has_param_defaults: vec![false],
            method_type_params: vec![],
            required_params: 1,
            param_names: vec!["x".to_string()],
            param_types: vec![VirTypeId::I64],
            return_type: VirTypeId::I64,
        });
        entities
    }

    #[test]
    fn rederive_param_functional_interface() {
        let mut interner = Interner::new();
        let m_sym = interner.intern("m");
        let name_table = vole_identity::NameTable::new();

        let type_def_id = TypeDefId::new(112);
        let method_id = MethodId::new(50);

        let mut table = VirTypeTable::new();
        let iface_ty = table.intern(
            VirType::Interface {
                def: type_def_id,
                type_args: vec![],
            },
            None,
        );

        let mut target = unresolved_target(m_sym, 60);
        let entities = entities_with_functional_interface(type_def_id, method_id);
        let ctx = call_ctx_with_interner(&interner, &name_table, vec![(m_sym, iface_ty)]);

        rederive_call_target(&mut target, &table, &entities, &ctx);

        match &target {
            CallTarget::FunctionalInterface {
                var_name,
                vir_type,
                interface_type_def_id,
                method_id: mid,
            } => {
                assert_eq!(*var_name, m_sym);
                assert_eq!(*vir_type, iface_ty);
                assert_eq!(*interface_type_def_id, type_def_id);
                assert_eq!(*mid, method_id);
            }
            other => panic!("expected FunctionalInterface, got {other:?}"),
        }
    }

    #[test]
    fn rederive_local_functional_interface() {
        let mut interner = Interner::new();
        let m_sym = interner.intern("m");
        let name_table = vole_identity::NameTable::new();

        let type_def_id = TypeDefId::new(112);
        let method_id = MethodId::new(50);

        let mut table = VirTypeTable::new();
        let iface_ty = table.intern(
            VirType::Interface {
                def: type_def_id,
                type_args: vec![],
            },
            None,
        );

        let mut target = unresolved_target(m_sym, 31);
        let entities = entities_with_functional_interface(type_def_id, method_id);
        let ctx = call_ctx_with_interner(&interner, &name_table, vec![]);

        // Simulate a let-bound interface-typed local.
        ctx.local_vars.borrow_mut().insert(m_sym, iface_ty);

        rederive_call_target(&mut target, &table, &entities, &ctx);

        match &target {
            CallTarget::FunctionalInterface {
                var_name,
                vir_type,
                interface_type_def_id,
                method_id: mid,
            } => {
                assert_eq!(*var_name, m_sym);
                assert_eq!(*vir_type, iface_ty);
                assert_eq!(*interface_type_def_id, type_def_id);
                assert_eq!(*mid, method_id);
            }
            other => panic!("expected FunctionalInterface, got {other:?}"),
        }
    }

    #[test]
    fn rederive_captured_functional_interface() {
        let mut interner = Interner::new();
        let m_sym = interner.intern("m");
        let name_table = vole_identity::NameTable::new();

        let type_def_id = TypeDefId::new(112);
        let method_id = MethodId::new(50);

        let mut table = VirTypeTable::new();
        let iface_ty = table.intern(
            VirType::Interface {
                def: type_def_id,
                type_args: vec![],
            },
            None,
        );

        let mut target = unresolved_target(m_sym, 45);
        let entities = entities_with_functional_interface(type_def_id, method_id);
        let ctx = call_ctx_with_interner(&interner, &name_table, vec![]);

        // Simulate a captured interface-typed variable.
        ctx.captures.borrow_mut().insert(m_sym, iface_ty);

        rederive_call_target(&mut target, &table, &entities, &ctx);

        match &target {
            CallTarget::FunctionalInterface {
                var_name,
                vir_type,
                interface_type_def_id,
                method_id: mid,
            } => {
                assert_eq!(*var_name, m_sym);
                assert_eq!(*vir_type, iface_ty);
                assert_eq!(*interface_type_def_id, type_def_id);
                assert_eq!(*mid, method_id);
            }
            other => panic!("expected FunctionalInterface, got {other:?}"),
        }
    }
}
