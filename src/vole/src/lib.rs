// src/lib.rs

// Public modules (the vole driver API)
#[cfg(feature = "bench")]
pub mod bench;
pub mod cli;
pub mod commands;
pub mod errors;
pub mod util;

// Internal crate aliases (not part of the public API).
// These are used within the vole crate but should not be accessed by external
// tools. Tools should depend on sub-crates (vole-codegen, vole-sema, etc.)
// directly for types they need.
pub(crate) use vole_codegen as codegen;
pub(crate) use vole_fmt as fmt;
pub(crate) use vole_frontend as frontend;
pub(crate) use vole_runtime as runtime;
pub(crate) use vole_sema as sema;

// Targeted re-exports for the vole binary and external tools.
// Only expose what the public API actually needs.
pub use vole_runtime::install_segfault_handler;
