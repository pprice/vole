//! Vole Intermediate Representation (VIR).
//!
//! A typed IR that sits between sema and codegen.  All type parameters have
//! been monomorphized, RC operations are explicit, and every node carries
//! its concrete type.  Codegen becomes a mechanical translation from VIR to
//! Cranelift IR.
//!
//! All expression and statement kinds are fully lowered to typed VIR nodes.
//! A few variants (`MethodCall`, `OptionalMethodCall`) still carry AST
//! fragments for codegen dispatch, but there are no generic escape hatches.
//!
//! AST-to-VIR lowering lives in `vole-codegen::vir_lower` (moved out of this
//! crate to break the `vole-frontend` dependency).

pub mod builder;
pub mod calls;
pub mod expr;
pub mod func;
pub mod intrinsics;
pub mod monomorph;
pub mod program;
pub mod refs;
pub mod stmt;
pub mod type_table;
pub mod types;

// Re-export paste so the define_int_op_enum macro works from downstream crates.
#[doc(hidden)]
pub use paste;

pub use builder::VirBuilder;
pub use calls::{BuiltinMethod, CallTarget, NativeAbi};
pub use expr::{
    AsCastKind, CoerceKind, FieldStorage, IsCheckResult, VirBinOp, VirCapture,
    VirErrorFieldBinding, VirErrorPatternKind, VirExpr, VirMatchArm, VirMetaKind, VirPattern,
    VirRecordFieldBinding, VirStringPart, VirTupleBinding, VirUnOp,
};
pub use func::{VirBody, VirFunction, VirTest};
pub use intrinsics::IntrinsicKey;
pub use monomorph::{
    RewriteCtx, TypeSubstitution, rederive_decisions, rewrite_function, substitute_types,
};
pub use program::VirProgram;
pub use refs::VirRef;
pub use stmt::{
    AssignTarget, DestructureTupleKind, VirDestructureElement, VirDestructureField,
    VirDestructurePattern, VirFor, VirIterKind, VirModuleBinding, VirStmt,
};
pub use type_table::VirTypeTable;
pub use types::{
    StorageClass, VirAnnotation, VirAnnotationValue, VirConstant, VirFieldInfo, VirFieldMeta,
    VirLayout, VirPrimitiveKind, VirStructLayout, VirType, VirTypeLayout, VirTypeMeta,
    VirUnionLayout,
};
