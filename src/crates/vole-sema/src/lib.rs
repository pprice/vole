//! Vole semantic analysis: type checking, entity registry, and type inference.

pub mod analysis_cache;
pub mod analyzer;
pub mod compatibility;
pub mod compilation_db;
pub mod entity_defs;
pub mod entity_registry;
pub mod errors;
pub mod expression_data;
pub mod generic;
pub mod implement_registry;
pub mod infer;
pub mod module;
pub mod optimizer;
pub mod query;
pub mod resolution;
pub mod resolve;
pub mod scope;
pub mod type_arena;
pub mod type_display;
pub mod types;
pub mod well_known;

pub use analysis_cache::{CachedModule, IsCheckResult, ModuleCache};
pub use analyzer::{AnalysisOutput, Analyzer, AnalyzerBuilder, TypeError, TypeWarning};
pub use compilation_db::{CodegenDb, CompilationDb};
pub use entity_defs::{FieldDef, FunctionDef, MethodDef, TypeDef, TypeDefKind};
pub use entity_registry::EntityRegistry;
pub use expression_data::ExpressionData;
pub use implement_registry::{
    ImplTypeId, ImplementRegistry, MethodImpl, MethodKey, PrimitiveTypeId,
};
pub use infer::{InferCtx, InferType, InferVarId, UnifyError};
pub use query::ProgramQuery;
pub use resolution::{MethodResolutions, ResolvedMethod};
pub use resolve::ResolverEntityExt;
pub use types::{ClassType, ErrorTypeInfo, FunctionType, PrimitiveType};
pub use well_known::{WellKnownMethods, WellKnownTypes};

// TypeArena for interned type representation
// SemaType is the canonical type representation - use TypeId handles for O(1) equality
// Note: type_arena::TypeId is accessed via module path to avoid conflict with implement_registry::TypeId
pub use type_arena::{SemaType, TypeArena};

// Error types
pub use errors::{SemanticError, SemanticWarning};

// Module loading
pub use module::{LoadError, ModuleInfo, ModuleLoader};

// Optimizer
pub use optimizer::{OptimizerConfig, OptimizerStats, optimize, optimize_all};
