// src/cli/mod.rs
pub mod args;
pub mod paths;

pub use args::{Cli, ColorMode, Commands, InspectType, ReportMode};
pub use paths::{PathError, expand_paths};
