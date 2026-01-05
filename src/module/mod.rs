//! Module system for Vole.
//!
//! Handles locating and loading modules, including the standard library.

pub mod locator;

pub use locator::{LocationSource, StdlibLocation, StdlibLocator};
