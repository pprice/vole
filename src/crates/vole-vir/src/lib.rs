//! Vole Intermediate Representation (VIR).
//!
//! A typed IR that sits between sema and codegen.  All type parameters have
//! been monomorphized, RC operations are explicit, and every node carries
//! its concrete type.  Codegen becomes a mechanical translation from VIR to
//! Cranelift IR.
//!
//! During the incremental migration, `VirExpr::Ast` and `VirStmt::Ast`
//! escape hatches allow individual expression/statement kinds to be lowered
//! one at a time.

pub mod builder;
pub mod calls;
pub mod expr;
pub mod func;
pub mod lower;
pub mod refs;
pub mod stmt;
pub mod types;

pub use builder::VirBuilder;
pub use calls::{BuiltinMethod, CallTarget, NativeAbi};
pub use expr::{
    AsCastKind, CoerceKind, FieldStorage, IsCheckResult, VirBinOp, VirCapture, VirExpr,
    VirMatchArm, VirMetaKind, VirPattern, VirUnOp,
};
pub use func::{VirBody, VirFunction};
pub use lower::{lower_function, lower_monomorphized_function};
pub use refs::VirRef;
pub use stmt::{AssignTarget, VirFor, VirIterKind, VirStmt};
pub use types::{
    BitWidth, VirAnnotation, VirAnnotationValue, VirConstant, VirFieldInfo, VirFieldMeta,
    VirLayout, VirStructLayout, VirType, VirTypeMeta, VirUnionLayout,
};
