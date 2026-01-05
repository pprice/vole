// src/runtime/stdlib/mod.rs
//! Standard library native modules for Vole.

pub mod math;
pub mod string;

use super::native_registry::NativeRegistry;

/// Register all standard library modules
pub fn register_stdlib(registry: &mut NativeRegistry) {
    registry.register_module("std:math", math::module());
    registry.register_module("std:string", string::module());
}
