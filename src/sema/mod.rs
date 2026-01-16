// src/sema/mod.rs
pub mod analysis_cache;
pub mod analyzer;
pub mod compatibility;
pub mod entity_defs;
pub mod entity_registry;
pub mod expression_data;
pub mod generic;
pub mod implement_registry;
pub mod infer;
pub mod query;
pub mod resolution;
pub mod resolve;
pub mod scope;
pub mod type_arena;
pub mod type_table;
pub mod types;
pub mod well_known;

pub use analysis_cache::{CachedModule, ModuleCache};
pub use analyzer::{AnalysisOutput, Analyzer, TypeError, TypeWarning};
pub use entity_defs::{FieldDef, FunctionDef, MethodDef, TypeDef, TypeDefKind};
pub use entity_registry::EntityRegistry;
pub use expression_data::ExpressionData;
pub use implement_registry::{ImplTypeId, ImplementRegistry, MethodImpl, MethodKey, PrimitiveTypeId};
pub use infer::{InferCtx, InferType, InferVarId, UnifyError};
pub use query::{CallInfo, ProgramQuery};
pub use resolution::{MethodResolutions, ResolvedMethod};
pub use type_table::{TypeInfo, TypeKey, TypeTable};
pub use types::{
    ClassType, ErrorTypeInfo, FunctionType, LegacyType, ModuleType, PrimitiveType, RecordType,
    StructField,
};
pub use well_known::{WellKnownMethods, WellKnownTypes};

// TypeArena for interned type representation (Phase 1 of TypeArena refactor)
// Note: type_arena::TypeId is accessed via module path to avoid conflict with implement_registry::TypeId
pub use type_arena::TypeArena;
