// src/sema/mod.rs
pub mod analysis_cache;
pub mod analyzer;
pub mod compatibility;
pub mod entity_defs;
pub mod entity_registry;
pub mod expression_data;
pub mod generic;
pub mod implement_registry;
pub mod query;
pub mod resolution;
pub mod resolve;
pub mod scope;
pub mod type_table;
pub mod types;
pub mod well_known;

pub use analysis_cache::{CachedModule, ModuleCache};
pub use analyzer::{AnalysisOutput, Analyzer, TypeError, TypeWarning};
pub use entity_defs::{FieldDef, FunctionDef, MethodDef, TypeDef, TypeDefKind};
pub use entity_registry::EntityRegistry;
pub use expression_data::ExpressionData;
pub use implement_registry::{ImplementRegistry, MethodImpl, MethodKey, PrimitiveTypeId, TypeId};
pub use query::{CallInfo, ProgramQuery};
pub use resolution::{MethodResolutions, ResolvedMethod};
pub use type_table::{TypeInfo, TypeKey, TypeTable};
pub use types::{
    ClassType, ErrorTypeInfo, FunctionType, ModuleType, PrimitiveType, RecordType, StructField,
    Type,
};
pub use well_known::{WellKnownMethods, WellKnownTypes};
