// src/util.rs
//
// Shared utilities for the Vole compiler.

use std::time::Duration;

/// Format a duration with appropriate units (ns, us, ms, s)
pub fn format_duration(d: Duration) -> String {
    let nanos = d.as_nanos();
    if nanos < 1_000 {
        format!("{}ns", nanos)
    } else if nanos < 1_000_000 {
        format!("{:.2}us", nanos as f64 / 1_000.0)
    } else if nanos < 1_000_000_000 {
        format!("{:.2}ms", nanos as f64 / 1_000_000.0)
    } else {
        format!("{:.2}s", d.as_secs_f64())
    }
}

/// Format a byte count with appropriate units (B, KB, MB, GB)
pub fn format_bytes(bytes: u64) -> String {
    const KB: u64 = 1024;
    const MB: u64 = 1024 * 1024;
    const GB: u64 = 1024 * 1024 * 1024;

    if bytes >= GB {
        format!("{:.2}GB", bytes as f64 / GB as f64)
    } else if bytes >= MB {
        format!("{:.2}MB", bytes as f64 / MB as f64)
    } else if bytes >= KB {
        format!("{:.2}KB", bytes as f64 / KB as f64)
    } else {
        format!("{}B", bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_duration_ns() {
        assert_eq!(format_duration(Duration::from_nanos(500)), "500ns");
    }

    #[test]
    fn test_format_duration_us() {
        assert_eq!(format_duration(Duration::from_nanos(1_500)), "1.50us");
    }

    #[test]
    fn test_format_duration_ms() {
        assert_eq!(format_duration(Duration::from_micros(1_500)), "1.50ms");
    }

    #[test]
    fn test_format_duration_s() {
        assert_eq!(format_duration(Duration::from_millis(1_500)), "1.50s");
    }

    #[test]
    fn test_format_bytes() {
        assert_eq!(format_bytes(500), "500B");
        assert_eq!(format_bytes(1536), "1.50KB");
        assert_eq!(format_bytes(1_572_864), "1.50MB");
        assert_eq!(format_bytes(1_610_612_736), "1.50GB");
    }
}
