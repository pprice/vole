// type_arena/mod.rs
//
// Interned type system using TypeId handles for O(1) equality and minimal allocations.
//
// This module provides the canonical type representation for Vole's semantic analysis:
// - TypeId: u32 handle to an interned type (Copy, trivial Eq/Hash)
// - TypeArena: per-compilation storage with automatic deduplication
// - SemaType: the canonical type representation using TypeId for child types

mod arena;
mod query;
pub mod sema_type;
mod substitution;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_substitution;
pub mod type_id;

// Re-export all public items so `crate::type_arena::*` continues to work.
pub use arena::*;
pub use sema_type::*;
pub use type_id::*;
