// src/runtime/stdlib/mod.rs
//! Standard library native modules for Vole.

pub mod collections;
pub mod intrinsics;
pub mod math;
pub mod string;

use super::native_registry::NativeRegistry;

/// Register all standard library modules
pub fn register_stdlib(registry: &mut NativeRegistry) {
    registry.register_module("std:collections", collections::module());
    registry.register_module("std:intrinsics", intrinsics::module());
    registry.register_module("std:math", math::module());
    registry.register_module("std:string", string::module());
}
