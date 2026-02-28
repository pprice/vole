//! Vole Intermediate Representation (VIR).
//!
//! A typed IR that sits between sema and codegen.  All type parameters have
//! been monomorphized, RC operations are explicit, and every node carries
//! its concrete type.  Codegen becomes a mechanical translation from VIR to
//! Cranelift IR.
//!
//! All expression and statement kinds are fully lowered to typed VIR nodes.
//! Method call nodes carry explicit VIR dispatch metadata; there are no
//! generic AST escape hatches.
//!
//! AST-to-VIR lowering lives in `vole-codegen::vir_lower` (moved out of this
//! crate to break the `vole-frontend` dependency).

pub mod builder;
pub mod calls;
pub mod entity_metadata;
pub mod expr;
pub mod func;
pub mod implement_dispatch;
pub mod intrinsics;
pub mod monomorph;
pub mod numeric_model;
pub mod program;
pub mod refs;
pub mod stmt;
pub mod type_table;
pub mod types;

// Re-export paste so the define_int_op_enum macro works from downstream crates.
#[doc(hidden)]
pub use paste;
pub use vole_identity::{NodeId, Span};

pub use builder::VirBuilder;
pub use calls::{BuiltinMethod, CallTarget, LambdaDefaultsInfo, NativeAbi};
pub use entity_metadata::{
    VirEntityMetadata, VirFieldDef, VirFunctionDef, VirGlobalDef, VirImplementation,
    VirMethodBinding, VirMethodDef, VirTypeDef, VirTypeDefKind,
};
pub use expr::{
    AsCastKind, CoerceKind, FieldStorage, IsCheckResult, VirBinOp, VirCapture,
    VirClassMethodMonomorphKey, VirErrorFieldBinding, VirErrorPatternKind, VirExpr,
    VirExternalMethodInfo, VirFunctionMonomorphKey, VirMatchArm, VirMetaKind,
    VirMethodDispatchKind, VirMethodDispatchMeta, VirMethodReceiverCoercion, VirPattern,
    VirRecordFieldBinding, VirResolvedMethod, VirStaticMethodMonomorphKey, VirStringPart,
    VirTupleBinding, VirUnOp,
};
pub use func::{VirBody, VirFunction, VirTest};
pub use implement_dispatch::{
    VirExternalFuncInfo, VirFuncSignature, VirGenericExternalInfo, VirImplementDispatch,
    VirMethodImplInfo, VirTypeMappingEntry, VirTypeMappingKind,
};
pub use intrinsics::IntrinsicKey;
pub use monomorph::{
    InstanceIndex, MonomorphInstance, MonomorphResult, RewriteCtx, TypeSubstitution, monomorphize,
    monomorphize_with_seeds, rederive_decisions, resolve_generic_calls, rewrite_function,
    substitute_types,
};
pub use numeric_model::{
    NumericCoercion, integer_result_type, numeric_coercion, numeric_result_type,
};
pub use program::VirProgram;
pub use refs::VirRef;
pub use stmt::{
    AssignTarget, DestructureTupleKind, LetStorageHint, ReturnConvention, VirDestructureElement,
    VirDestructureField, VirDestructurePattern, VirFor, VirIterKind, VirModuleBinding, VirStmt,
};
pub use type_table::VirTypeTable;
pub use types::{
    StorageClass, VirAnnotation, VirAnnotationValue, VirConstant, VirFieldInfo, VirFieldMeta,
    VirLayout, VirPrimitiveKind, VirStructLayout, VirType, VirTypeLayout, VirTypeMeta,
    VirUnionLayout,
};
