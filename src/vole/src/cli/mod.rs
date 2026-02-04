// src/cli/mod.rs
pub mod args;
pub mod paths;

pub use args::{BenchArgs, BenchCommands, Cli, ColorMode, Commands, InspectType};
pub use paths::{ExpandedPaths, PathError, expand_paths, expand_paths_flat, should_skip_path};
