//! Module system for Vole.
//!
//! Handles locating and loading modules, including the standard library.

pub mod loader;
pub mod locator;

pub use loader::{LoadError, ModuleInfo, ModuleLoader};
pub use locator::{LocationSource, StdlibLocation, StdlibLocator};
