// rederive.rs
//
// Decision re-derivation for monomorphized VIR functions.
//
// After type substitution and tree rewriting, VirTypeId fields are concrete
// but some embedded decision values (IsCheckResult, StringConversion,
// VirIterKind, VirMetaKind) may still carry generic/placeholder values.
// This pass walks the VIR tree and re-derives those decisions from the
// now-concrete types.

use rustc_hash::FxHashSet;
use vole_identity::{StringConversion, UnionStorageKind, VirTypeId};

use crate::expr::{IsCheckResult, VirExpr, VirMetaKind, VirPattern, VirStringPart};
use crate::func::{VirBody, VirFunction};
use crate::refs::VirRef;
use crate::stmt::{LetStorageHint, ReturnConvention, VirIterKind, VirStmt};
use crate::type_table::VirTypeTable;
use crate::types::{VirPrimitiveKind, VirType};

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
pub fn rederive_decisions(func: &mut VirFunction, table: &VirTypeTable) {
    let ret_ty = func.vir_return_type;
    rederive_body(&mut func.body, table, ret_ty);
}

// ---------------------------------------------------------------------------
// Body / statement / expression walkers
// ---------------------------------------------------------------------------

fn rederive_body(body: &mut VirBody, table: &VirTypeTable, ret_ty: VirTypeId) {
    for stmt in &mut body.stmts {
        rederive_stmt(stmt, table, ret_ty);
    }
    if let Some(ref mut trailing) = body.trailing {
        rederive_ref(trailing, table, ret_ty);
    }
}

fn rederive_ref(r: &mut VirRef, table: &VirTypeTable, ret_ty: VirTypeId) {
    rederive_expr(r.as_mut(), table, ret_ty);
}

fn rederive_expr(expr: &mut VirExpr, table: &VirTypeTable, ret_ty: VirTypeId) {
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
            rederive_ref(start, table, ret_ty);
            rederive_ref(end, table, ret_ty);
        }
        VirExpr::ArrayLiteral { elements, .. } => {
            for elem in elements {
                rederive_ref(elem, table, ret_ty);
            }
        }
        VirExpr::RepeatLiteral { element, .. } => rederive_ref(element, table, ret_ty),
        VirExpr::StructLiteral { fields, .. } | VirExpr::ClassInstance { fields, .. } => {
            for (_, val) in fields {
                rederive_ref(val, table, ret_ty);
            }
        }

        // Operators
        VirExpr::BinaryOp { lhs, rhs, .. } => {
            rederive_ref(lhs, table, ret_ty);
            rederive_ref(rhs, table, ret_ty);
        }
        VirExpr::UnaryOp { operand, .. } => rederive_ref(operand, table, ret_ty),

        // Strings — re-derive StringConversion::Generic
        VirExpr::StringConcat { parts } => {
            for part in parts {
                rederive_ref(part, table, ret_ty);
            }
        }
        VirExpr::InterpolatedString { parts } => rederive_string_parts(parts, table, ret_ty),

        // Calls
        VirExpr::Call { args, .. } => {
            for arg in args {
                rederive_ref(arg, table, ret_ty);
            }
        }
        VirExpr::MethodCall { receiver, args, .. } => {
            rederive_ref(receiver, table, ret_ty);
            for arg in args {
                rederive_ref(arg, table, ret_ty);
            }
        }

        // Fields, indexing
        VirExpr::FieldLoad { object, .. } => rederive_ref(object, table, ret_ty),
        VirExpr::FieldStore { object, value, .. } => {
            rederive_ref(object, table, ret_ty);
            rederive_ref(value, table, ret_ty);
        }
        VirExpr::Index {
            object,
            index,
            union_storage,
            ..
        } => {
            rederive_ref(object, table, ret_ty);
            rederive_ref(index, table, ret_ty);
            rederive_union_storage_from_array_expr(object, union_storage, table);
        }
        VirExpr::IndexStore {
            object,
            index,
            value,
            union_storage,
            ..
        } => {
            rederive_ref(object, table, ret_ty);
            rederive_ref(index, table, ret_ty);
            rederive_ref(value, table, ret_ty);
            rederive_union_storage_from_array_expr(object, union_storage, table);
        }

        // RC
        VirExpr::RcInc { value } | VirExpr::RcDec { value } | VirExpr::RcMove { value } => {
            rederive_ref(value, table, ret_ty);
        }

        // Coercion
        VirExpr::Coerce { value, .. } => rederive_ref(value, table, ret_ty),

        // Control flow
        VirExpr::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            rederive_ref(cond, table, ret_ty);
            rederive_body(then_body, table, ret_ty);
            if let Some(eb) = else_body {
                rederive_body(eb, table, ret_ty);
            }
        }
        VirExpr::Match {
            scrutinee, arms, ..
        } => {
            rederive_ref(scrutinee, table, ret_ty);
            let scrutinee_vir_ty = extract_vir_ty(scrutinee);
            for arm in arms {
                rederive_pattern(&mut arm.pattern, scrutinee_vir_ty, table, ret_ty);
                if let Some(guard) = &mut arm.guard {
                    rederive_ref(guard, table, ret_ty);
                }
                rederive_body(&mut arm.body, table, ret_ty);
            }
        }
        VirExpr::Block {
            stmts, trailing, ..
        } => {
            for stmt in stmts {
                rederive_stmt(stmt, table, ret_ty);
            }
            if let Some(t) = trailing {
                rederive_ref(t, table, ret_ty);
            }
        }

        // Type operations — re-derive IsCheckResult
        VirExpr::IsCheck { value, result, .. } => {
            rederive_ref(value, table, ret_ty);
            rederive_is_check_from_expr(value, result, table);
        }
        VirExpr::AsCast { value, result, .. } => {
            rederive_ref(value, table, ret_ty);
            rederive_is_check_from_expr(value, result, table);
        }

        // Reflection — re-derive TypeParam meta-kind from concrete VIR types.
        VirExpr::MetaAccess { kind, .. } => rederive_meta_kind(kind, table, ret_ty),

        // Variables
        VirExpr::LocalLoad { .. } => {}
        VirExpr::LocalStore { value, .. } => rederive_ref(value, table, ret_ty),

        // Lambda
        VirExpr::Lambda { body, .. } => rederive_body(body, table, ret_ty),

        // Optional / null
        VirExpr::NullCoalesce { value, default, .. } => {
            rederive_ref(value, table, ret_ty);
            rederive_ref(default, table, ret_ty);
        }
        VirExpr::OptionalChain { object, .. } => rederive_ref(object, table, ret_ty),
        VirExpr::OptionalMethodCall {
            object,
            method_args,
            ..
        } => {
            rederive_ref(object, table, ret_ty);
            for arg in method_args {
                rederive_ref(arg, table, ret_ty);
            }
        }
        VirExpr::Try { value, .. } => rederive_ref(value, table, ret_ty),
        VirExpr::Yield { value } => rederive_ref(value, table, ret_ty),
    }
}

fn rederive_stmt(stmt: &mut VirStmt, table: &VirTypeTable, ret_ty: VirTypeId) {
    match stmt {
        VirStmt::Let {
            value,
            vir_ty,
            storage,
            ..
        } => {
            *storage = rederive_let_storage(*vir_ty, storage, table);
            rederive_ref(value, table, ret_ty);
        }
        VirStmt::LetTuple { value, .. } => rederive_ref(value, table, ret_ty),
        VirStmt::Assign { target, value } => {
            rederive_assign_target(target, table, ret_ty);
            rederive_ref(value, table, ret_ty);
        }
        VirStmt::Expr { value } => rederive_ref(value, table, ret_ty),
        VirStmt::While { cond, body } => {
            rederive_ref(cond, table, ret_ty);
            rederive_body(body, table, ret_ty);
        }
        VirStmt::For(vir_for) => {
            rederive_ref(&mut vir_for.iterable, table, ret_ty);
            rederive_body(&mut vir_for.body, table, ret_ty);
            rederive_iter_kind(&mut vir_for.kind, table);
        }
        VirStmt::Return { value, convention } => {
            if let Some(v) = value {
                rederive_ref(v, table, ret_ty);
            }
            *convention = rederive_return_convention(ret_ty, table);
        }
        VirStmt::Break | VirStmt::Continue | VirStmt::Noop => {}
        VirStmt::Raise { fields, .. } => {
            for (_, val) in fields {
                rederive_ref(val, table, ret_ty);
            }
        }
        VirStmt::RcInc { value } | VirStmt::RcDec { value } => rederive_ref(value, table, ret_ty),
    }
}

fn rederive_assign_target(
    target: &mut crate::stmt::AssignTarget,
    table: &VirTypeTable,
    ret_ty: VirTypeId,
) {
    use crate::stmt::AssignTarget;
    match target {
        AssignTarget::Local(_) => {}
        AssignTarget::Field { object, .. } => rederive_ref(object, table, ret_ty),
        AssignTarget::Index { array, index } => {
            rederive_ref(array, table, ret_ty);
            rederive_ref(index, table, ret_ty);
        }
    }
}

fn rederive_pattern(
    pat: &mut VirPattern,
    scrutinee_vir_ty: Option<VirTypeId>,
    table: &VirTypeTable,
    ret_ty: VirTypeId,
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
        VirPattern::Literal { value, .. } => rederive_ref(value, table, ret_ty),
        VirPattern::Success {
            inner,
            vir_success_type,
            ..
        } => {
            if let Some(p) = inner {
                rederive_pattern(p, Some(*vir_success_type), table, ret_ty);
            }
        }
        VirPattern::Error { .. } => {}
        VirPattern::Tuple { bindings } => {
            for b in bindings {
                rederive_pattern(&mut b.pattern, Some(b.vir_ty), table, ret_ty);
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
            VirPrimitiveKind::Bool => StringConversion::BoolToString,
            VirPrimitiveKind::Handle => StringConversion::I64ToString,
        },
        VirType::Nil => StringConversion::NilToString,
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
    matches!(table.get(ty), VirType::Nil | VirType::Done)
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

fn rederive_string_parts(parts: &mut [VirStringPart], table: &VirTypeTable, ret_ty: VirTypeId) {
    for part in parts {
        if let VirStringPart::Expr { value, conversion } = part {
            rederive_ref(value, table, ret_ty);
            // Extract the expression's VirTypeId to re-derive the conversion.
            let vir_ty = extract_vir_ty(value);
            if let Some(vir_ty) = vir_ty {
                rederive_string_conversion(conversion, vir_ty, table);
            }
        }
    }
}

fn rederive_meta_kind(kind: &mut VirMetaKind, table: &VirTypeTable, ret_ty: VirTypeId) {
    match kind {
        VirMetaKind::Static { object, type_def } => {
            if let Some(obj) = object {
                rederive_ref(obj, table, ret_ty);
                if let Some(obj_vir_ty) = extract_vir_ty(obj)
                    && let Some(concrete_type_def) =
                        nominal_type_def_from_vir_type(obj_vir_ty, table)
                {
                    *type_def = concrete_type_def;
                }
            }
        }
        VirMetaKind::Dynamic { value } => rederive_ref(value, table, ret_ty),
        VirMetaKind::TypeParam { value, .. } => {
            rederive_ref(value, table, ret_ty);
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
    existing: &LetStorageHint,
    table: &VirTypeTable,
) -> LetStorageHint {
    match table.get(vir_ty) {
        VirType::Unknown => LetStorageHint::Unknown,
        VirType::Union { .. } | VirType::Optional { .. } => {
            // If the existing storage is already Union with a pre-computed
            // tag hint, preserve it — the rewrite pass has already remapped
            // the VirTypeIds inside the hint.  Otherwise (e.g. the storage
            // was Scalar before monomorphization resolved the type to a
            // union), leave the hint as None.
            match existing {
                LetStorageHint::Union { tag_hint } => LetStorageHint::Union {
                    tag_hint: *tag_hint,
                },
                _ => LetStorageHint::Union { tag_hint: None },
            }
        }
        VirType::Interface { .. } => LetStorageHint::Interface,
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
    use vole_identity::{FunctionId, NameId, Symbol, TypeDefId, TypeId};

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

    /// Helper: build a minimal VirFunction wrapping a trailing expression.
    fn func_with_trailing(expr: VirExpr) -> VirFunction {
        VirFunction {
            id: FunctionId::new(1),
            name: "test_fn".to_string(),
            params: vec![],
            return_type: VirTypeId::VOID,
            vir_return_type: VirTypeId::VOID,
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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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

        rederive_decisions(&mut func, &table);

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
        rederive_decisions(&mut result, &target);

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

        rederive_decisions(&mut result, &target);

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
        };
        assert_eq!(extract_vir_ty(&expr), None);
    }
}
