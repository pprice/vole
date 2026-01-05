// src/sema/mod.rs
pub mod analyzer;
pub mod compatibility;
pub mod implement_registry;
pub mod interface_registry;
pub mod resolution;
pub mod resolve;
pub mod scope;
pub mod types;

pub use analyzer::{Analyzer, TypeError};
pub use implement_registry::{ImplementRegistry, MethodImpl, MethodKey, PrimitiveTypeId, TypeId};
pub use interface_registry::{
    InterfaceDef, InterfaceFieldDef, InterfaceMethodDef, InterfaceRegistry,
};
pub use resolution::{MethodResolutions, ResolvedMethod};
pub use types::{ClassType, ErrorTypeInfo, FunctionType, RecordType, StructField, Type};
