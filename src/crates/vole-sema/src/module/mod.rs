//! Module system for Vole.
//!
//! Handles locating and loading modules, including the standard library.

pub mod loader;
pub mod locator;
pub mod parallel_parse;

pub use loader::{LoadError, ModuleInfo, ModuleLoader};
pub use locator::{LocationSource, StdlibLocation, StdlibLocator};
pub use parallel_parse::{ParsedModule, WavefrontError, parallel_parse};
