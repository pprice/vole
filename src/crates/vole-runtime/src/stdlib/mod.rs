// src/runtime/stdlib/mod.rs
//! Standard library native modules for Vole.

pub mod buffer;
pub mod builtins;
pub mod crypto;
pub mod env;
pub mod fs;
pub mod intrinsics;
pub mod io;
pub mod math;
pub mod random;
pub mod string;
pub mod task;
pub mod time;

use super::native_registry::NativeRegistry;

/// Register all standard library modules
pub fn register_stdlib(registry: &mut NativeRegistry) {
    registry.register_module("std:buffer", buffer::module());
    registry.register_module("vole:builtins", builtins::module());
    registry.register_module("std:crypto/hash", crypto::module());
    registry.register_module("std:env", env::module());
    registry.register_module("std:fs/sync", fs::module());
    registry.register_module("std:io", io::module());
    registry.register_module("vole:std:runtime", intrinsics::module());
    registry.register_module("std:math", math::module());
    registry.register_module("std:random", random::module());
    registry.register_module("std:string", string::module());
    registry.register_module("std:task", task::module());
    registry.register_module("std:time", time::module());
}
