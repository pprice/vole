// src/cli/mod.rs
pub mod args;
pub mod paths;

#[cfg(feature = "bench")]
pub use args::{BenchArgs, BenchCommands};
pub use args::{Cli, ColorMode, Commands, InspectType};
pub use paths::{ExpandedPaths, PathError, expand_paths, expand_paths_flat, should_skip_path};
