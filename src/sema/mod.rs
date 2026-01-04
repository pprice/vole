// src/sema/mod.rs
pub mod analyzer;
pub mod implement_registry;
pub mod interface_registry;
pub mod scope;
pub mod types;

pub use analyzer::{Analyzer, TypeError};
pub use implement_registry::{ImplementRegistry, MethodImpl, MethodKey, TypeId, PrimitiveTypeId};
pub use interface_registry::{InterfaceDef, InterfaceFieldDef, InterfaceMethodDef, InterfaceRegistry};
pub use types::{ClassType, FunctionType, RecordType, StructField, Type};
