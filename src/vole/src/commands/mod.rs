// src/commands/mod.rs
#[cfg(feature = "bench")]
pub mod bench;
pub mod check;
pub mod common;
pub mod fmt;
pub mod inspect;
pub mod mir_format;
pub mod run;
pub mod test;
pub mod version;
