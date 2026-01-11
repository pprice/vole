// src/sema/mod.rs
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

pub use analyzer::{Analyzer, TypeError, TypeWarning};
pub use entity_defs::{FieldDef, FunctionDef, MethodDef, TypeDef, TypeDefKind};
pub use expression_data::ExpressionData;
pub use entity_registry::EntityRegistry;
pub use query::{CallInfo, ProgramQuery};
pub use implement_registry::{ImplementRegistry, MethodImpl, MethodKey, PrimitiveTypeId, TypeId};
pub use resolution::{MethodResolutions, ResolvedMethod};
pub use type_table::{TypeInfo, TypeKey, TypeTable};
pub use types::{
    ClassType, ErrorTypeInfo, FunctionType, ModuleType, RecordType, StructField, Type,
};
pub use well_known::{WellKnownMethods, WellKnownTypes};
