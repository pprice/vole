// Lower annotation argument expressions from AST `Expr` nodes to VIR constants.
//
// Walks all field definitions in the entity registry and converts any
// `ValidatedAnnotation` args (raw AST Expr) into `VirAnnotation` with
// `VirConstant` values. The resulting map is stored on `VirProgram` so
// codegen can build annotation instances without reaching back to AST.

use rustc_hash::FxHashMap;

use vole_frontend::Interner;
use vole_frontend::ast::ExprKind;
use vole_identity::{FieldId, NameId, NameTable};
use vole_sema::LoweringEntityLookup;
use vole_sema::entity_defs::ValidatedAnnotation;
use vole_vir::types::{VirAnnotation, VirAnnotationValue, VirConstant};

/// Lower all field annotations in the entity registry to VIR constants.
///
/// Returns a map from `FieldId` to lowered annotations. Only fields that
/// have at least one annotation are included.
pub(crate) fn lower_annotation_inits<E: LoweringEntityLookup>(
    entities: &E,
    interner: &mut Interner,
    names: &NameTable,
) -> FxHashMap<FieldId, Vec<VirAnnotation>> {
    let registry = entities.as_entity_registry();
    let mut result = FxHashMap::default();

    for (idx, field_def) in registry.all_field_defs().iter().enumerate() {
        if field_def.annotations.is_empty() {
            continue;
        }
        let field_id = FieldId::new(idx as u32);
        let lowered: Vec<VirAnnotation> = field_def
            .annotations
            .iter()
            .map(|ann| lower_single_annotation(ann, interner, names))
            .collect();
        result.insert(field_id, lowered);
    }

    result
}

/// Lower a single `ValidatedAnnotation` to a `VirAnnotation`.
///
/// Each argument expression is converted to a `VirConstant`. Annotation
/// arguments are restricted to simple literals (strings, integers, floats,
/// booleans) so this conversion is straightforward.
fn lower_single_annotation(
    ann: &ValidatedAnnotation,
    interner: &mut Interner,
    names: &NameTable,
) -> VirAnnotation {
    let fields = ann
        .args
        .iter()
        .map(|(name_id, expr)| {
            let sym = name_id_to_symbol(*name_id, interner, names);
            let constant = lower_expr_to_constant(expr);
            (sym, constant)
        })
        .collect();

    VirAnnotation {
        type_def: ann.type_def_id,
        value: VirAnnotationValue::Instance { fields },
    }
}

/// Convert a `NameId` to a `Symbol` by looking up the last segment in the
/// name table and interning the result.
fn name_id_to_symbol(
    name_id: NameId,
    interner: &mut Interner,
    names: &NameTable,
) -> vole_identity::Symbol {
    let name_str = names
        .last_segment_str(name_id)
        .unwrap_or_else(|| "?".to_string());
    interner.intern(&name_str)
}

/// Convert an AST literal expression to a `VirConstant`.
///
/// Panics if the expression is not a simple literal -- annotation arguments
/// are validated by sema to be constant expressions.
fn lower_expr_to_constant(expr: &vole_frontend::Expr) -> VirConstant {
    match &expr.kind {
        ExprKind::IntLiteral(value, _suffix) => VirConstant::Int(*value),
        ExprKind::FloatLiteral(value, _suffix) => VirConstant::Float(*value),
        ExprKind::BoolLiteral(value) => VirConstant::Bool(*value),
        ExprKind::StringLiteral(s) => VirConstant::String(s.clone()),
        ExprKind::Unary(unary) => lower_unary_to_constant(unary),
        other => panic!("annotation argument: unsupported expression kind {other:?}"),
    }
}

/// Convert a unary expression to a `VirConstant` (handles negative literals).
fn lower_unary_to_constant(unary: &vole_frontend::ast::UnaryExpr) -> VirConstant {
    if !matches!(unary.op, vole_frontend::ast::UnaryOp::Neg) {
        panic!("annotation argument: unsupported unary op {:?}", unary.op);
    }
    match &unary.operand.kind {
        ExprKind::IntLiteral(value, _) => VirConstant::Int(-value),
        ExprKind::FloatLiteral(value, _) => VirConstant::Float(-value),
        other => panic!("annotation argument: unsupported unary operand {other:?}"),
    }
}
