// src/sema/mod.rs
pub mod analyzer;
pub mod interface_registry;
pub mod scope;
pub mod types;

pub use analyzer::{Analyzer, TypeError};
pub use interface_registry::{InterfaceDef, InterfaceFieldDef, InterfaceMethodDef, InterfaceRegistry};
pub use types::{ClassType, FunctionType, RecordType, StructField, Type};
