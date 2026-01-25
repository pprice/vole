// src/snap/mod.rs

use clap::ValueEnum;

pub mod diff;
pub mod runner;
pub mod snapshot;

/// Report mode for snapshot tests
#[derive(Clone, Copy, Debug, Default, ValueEnum)]
pub enum ReportMode {
    /// Show all tests
    #[default]
    All,
    /// Show only failed tests
    Failures,
}

pub use runner::{TestSummary, bless_tests, run_tests};
pub use snapshot::Snapshot;
