// src/runtime/mod.rs
pub mod value;
pub mod string;
pub mod builtins;

pub use value::{RcHeader, Context, TYPE_STRING};
pub use string::RcString;
