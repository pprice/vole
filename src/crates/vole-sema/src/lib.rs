//! Vole semantic analysis: type checking, entity registry, and type inference.

// Public modules (used by vole-codegen and tools)
pub(crate) mod analyzer;
pub mod compilation_db;
pub mod entity_defs;
pub mod entity_registry;
pub mod errors;
pub mod expression_data;
pub mod generic;
pub mod implement_registry;
pub mod memory_kind;
pub mod module;
// Not wired to any callers yet — will become the primary store once
// ExpressionData callers are migrated (vol-yaix).
pub mod node_map;
pub mod numeric_model;
pub mod optimizer;
pub mod query;
pub mod resolution;
pub mod transforms;
pub mod type_arena;
pub mod types;

// Internal modules (not part of the public API)
pub(crate) mod analysis_cache;
pub(crate) mod compatibility;
pub(crate) mod resolve;
pub(crate) mod scope;
pub(crate) mod type_display;
pub(crate) mod well_known;

// Re-exports: public API surface
pub use analysis_cache::{CachedModule, IsCheckResult, ModuleCache};
pub use analyzer::{AnalysisOutput, Analyzer, AnalyzerBuilder, TypeError, TypeWarning};
pub use compilation_db::{CodegenDb, CompilationDb};
pub use entity_defs::{FieldDef, FunctionDef, MethodDef, TypeDef, TypeDefKind};
pub use entity_registry::{EntityRegistry, MethodDefBuilder};
pub use errors::{SemanticError, SemanticWarning};
pub use expression_data::{
    CoercionKind, ExpressionData, ItLambdaInfo, IterableKind, LambdaAnalysis, OptionalChainInfo,
    OptionalChainKind, StringConversion,
};
pub use implement_registry::{
    ImplTypeId, ImplementRegistry, MethodImpl, MethodKey, PrimitiveTypeId,
};
pub use memory_kind::MemoryKind;
pub use module::{LoadError, ModuleInfo, ModuleLoader};
pub use numeric_model::{
    NumericCoercion, integer_result_type, numeric_coercion, numeric_result_type,
};
pub use optimizer::{OptimizerStats, optimize_all};
pub use query::ProgramQuery;
pub use resolution::{MethodResolutions, ResolvedMethod};
pub use type_arena::{SemaType, TypeArena};
pub use types::{ClassType, ErrorTypeInfo, FunctionType, PrimitiveType};
