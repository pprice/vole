// src/sema/compatibility/mod.rs
//
// Type compatibility checking for Vole.
//
// This module provides:
// - `TypeCompatibility` trait: unified interface for type compatibility checks
// - Core compatibility functions: types_compatible_core, literal_fits, etc.

mod core;
mod traits;

pub use core::{
    function_compatible_with_interface, literal_fits, types_compatible_core, types_compatible_core_id,
};
pub use traits::TypeCompatibility;
