//! Manifest generation for vole-stress output.
//!
//! Creates a `vole-stress.json` file containing generation metadata for
//! reproducibility and debugging.

use serde::{Deserialize, Serialize};
use std::fs;
use std::io;
use std::path::Path;
use std::time::{SystemTime, UNIX_EPOCH};

const VERSION: &str = env!("CARGO_PKG_VERSION");
const GIT_SHA: &str = env!("VERGEN_GIT_SHA");
const GIT_DIRTY: &str = env!("VERGEN_GIT_DIRTY");
const BUILD_DATE: &str = env!("VERGEN_BUILD_DATE");

/// Generation options stored in the manifest.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GenerationOptions {
    pub layers: usize,
    pub modules_per_layer: usize,
}

/// Generator version information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GeneratorInfo {
    pub version: String,
    pub git_sha: String,
    pub build_date: String,
}

impl GeneratorInfo {
    /// Create generator info from build-time constants.
    pub fn current() -> Self {
        let git_sha = if GIT_DIRTY == "true" {
            format!("{}+", short_sha(GIT_SHA))
        } else {
            short_sha(GIT_SHA).to_string()
        };

        Self {
            version: VERSION.to_string(),
            git_sha,
            build_date: BUILD_DATE.to_string(),
        }
    }
}

/// The complete manifest written to vole-stress.json.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Manifest {
    pub seed: u64,
    pub profile: String,
    pub options: GenerationOptions,
    pub generated_at: String,
    pub generator: GeneratorInfo,
}

impl Manifest {
    /// Create a new manifest with the given parameters.
    pub fn new(seed: u64, profile: String, options: GenerationOptions) -> Self {
        Self {
            seed,
            profile,
            options,
            generated_at: iso_timestamp(),
            generator: GeneratorInfo::current(),
        }
    }

    /// Write the manifest to a directory as `vole-stress.json`.
    pub fn write_to_dir(&self, dir: &Path) -> io::Result<()> {
        let path = dir.join("vole-stress.json");
        let json = serde_json::to_string_pretty(self)
            .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
        fs::write(path, json)
    }
}

/// Get the short form of a git SHA (first 7 characters).
fn short_sha(sha: &str) -> &str {
    if sha.len() >= 7 { &sha[..7] } else { sha }
}

/// Generate an ISO 8601 timestamp string.
fn iso_timestamp() -> String {
    let duration = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    let secs = duration.as_secs();

    // Simple ISO 8601 formatting without external crate
    // Unix timestamp to YYYY-MM-DDTHH:MM:SSZ
    let days_since_epoch = secs / 86400;
    let time_of_day = secs % 86400;

    let hours = time_of_day / 3600;
    let minutes = (time_of_day % 3600) / 60;
    let seconds = time_of_day % 60;

    // Calculate year, month, day from days since epoch (1970-01-01)
    let (year, month, day) = days_to_ymd(days_since_epoch);

    format!("{year:04}-{month:02}-{day:02}T{hours:02}:{minutes:02}:{seconds:02}Z")
}

/// Convert days since Unix epoch to (year, month, day).
fn days_to_ymd(days: u64) -> (u64, u64, u64) {
    // Algorithm based on Howard Hinnant's date algorithms
    // https://howardhinnant.github.io/date_algorithms.html
    let z = days + 719468;
    let era = z / 146097;
    let doe = z - era * 146097;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    (y, m, d)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generator_info_has_version() {
        let info = GeneratorInfo::current();
        assert!(!info.version.is_empty());
        assert!(!info.git_sha.is_empty());
        assert!(!info.build_date.is_empty());
    }

    #[test]
    fn manifest_serializes_to_json() {
        let manifest = Manifest::new(
            12345,
            "full".to_string(),
            GenerationOptions {
                layers: 3,
                modules_per_layer: 5,
            },
        );
        let json = serde_json::to_string(&manifest).expect("should serialize");
        assert!(json.contains("\"seed\":12345"));
        assert!(json.contains("\"profile\":\"full\""));
        assert!(json.contains("\"layers\":3"));
    }

    #[test]
    fn iso_timestamp_format() {
        let ts = iso_timestamp();
        // Should match YYYY-MM-DDTHH:MM:SSZ pattern
        assert_eq!(ts.len(), 20, "timestamp should be 20 chars: {ts}");
        assert!(ts.ends_with('Z'), "timestamp should end with Z: {ts}");
        assert_eq!(&ts[4..5], "-", "should have dash after year: {ts}");
        assert_eq!(&ts[7..8], "-", "should have dash after month: {ts}");
        assert_eq!(&ts[10..11], "T", "should have T separator: {ts}");
    }

    #[test]
    fn days_to_ymd_epoch() {
        // 1970-01-01
        let (y, m, d) = days_to_ymd(0);
        assert_eq!((y, m, d), (1970, 1, 1));
    }

    #[test]
    fn days_to_ymd_known_date() {
        // 2024-01-01 is day 19723 since epoch
        let (y, m, d) = days_to_ymd(19723);
        assert_eq!((y, m, d), (2024, 1, 1));
    }
}
