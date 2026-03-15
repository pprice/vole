use tracing_subscriber::EnvFilter;
use tracing_subscriber::Layer as _;
use tracing_subscriber::fmt::format::FmtSpan;
use tracing_subscriber::fmt::time::FormatTime;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;

use crate::{CompileTimingConfig, CompileTimingLayer};

/// A timer that outputs nothing but still enables span timing calculation.
struct NoTimestamp;

impl FormatTime for NoTimestamp {
    fn format_time(
        &self,
        _w: &mut tracing_subscriber::fmt::format::Writer<'_>,
    ) -> std::fmt::Result {
        Ok(())
    }
}

/// Initialize the tracing subscriber stack.
///
/// - If `timing_value` is `Some`, a `CompileTimingLayer` is added.
/// - If `VOLE_LOG` env var is set, a fmt layer is added.
/// - Both can be active simultaneously.
pub fn init_logging(timing_value: Option<&str>) {
    let timing_layer = timing_value.map(|value| {
        let config = parse_timing_config(value);
        CompileTimingLayer::new(config)
    });

    let env_filter = EnvFilter::try_from_env("VOLE_LOG").ok();
    let has_env_log = env_filter.is_some();

    let style = std::env::var("VOLE_LOG_STYLE").unwrap_or_default();
    let use_full_style = style == "full";

    // Build the fmt layer only when VOLE_LOG is set.
    // Split into two paths because `with_timer` changes the concrete type.
    match (env_filter, use_full_style) {
        (Some(filter), true) => {
            let fmt_layer = tracing_subscriber::fmt::layer()
                .with_target(true)
                .with_level(true)
                .with_span_events(FmtSpan::NEW | FmtSpan::CLOSE)
                .with_writer(std::io::stderr);

            tracing_subscriber::registry()
                .with(timing_layer)
                .with(fmt_layer.with_filter(filter))
                .init();
        }
        (Some(filter), false) => {
            let fmt_layer = tracing_subscriber::fmt::layer()
                .with_timer(NoTimestamp)
                .with_target(true)
                .with_level(true)
                .with_span_events(FmtSpan::NEW | FmtSpan::CLOSE)
                .with_writer(std::io::stderr);

            tracing_subscriber::registry()
                .with(timing_layer)
                .with(fmt_layer.with_filter(filter))
                .init();
        }
        (None, _) => {
            if timing_layer.is_some() {
                tracing_subscriber::registry().with(timing_layer).init();
            }
        }
    }

    if has_env_log {
        tracing::debug!("tracing initialized");
    }
}

/// Parse the `--timing` value into a `CompileTimingConfig`.
///
/// Grammar:
/// - `""` (empty / no value) → level=DEBUG, filter=None
/// - `"trace"` → level=TRACE, filter=None
/// - contains `/` or `.` → level=DEBUG, filter=Some(value)
/// - `"trace:pattern"` → level=TRACE, filter=Some(pattern)
fn parse_timing_config(value: &str) -> CompileTimingConfig {
    if value.is_empty() {
        return CompileTimingConfig::default();
    }

    if value == "trace" {
        return CompileTimingConfig {
            level: tracing::Level::TRACE,
            filter: None,
        };
    }

    if let Some(pattern) = value.strip_prefix("trace:") {
        return CompileTimingConfig {
            level: tracing::Level::TRACE,
            filter: Some(pattern.to_string()),
        };
    }

    // Value is a file path filter pattern.
    CompileTimingConfig {
        level: tracing::Level::DEBUG,
        filter: Some(value.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_empty_gives_debug_no_filter() {
        let config = parse_timing_config("");
        assert_eq!(config.level, tracing::Level::DEBUG);
        assert!(config.filter.is_none());
    }

    #[test]
    fn parse_trace_gives_trace_no_filter() {
        let config = parse_timing_config("trace");
        assert_eq!(config.level, tracing::Level::TRACE);
        assert!(config.filter.is_none());
    }

    #[test]
    fn parse_trace_with_pattern() {
        let config = parse_timing_config("trace:generics/basic");
        assert_eq!(config.level, tracing::Level::TRACE);
        assert_eq!(config.filter.as_deref(), Some("generics/basic"));
    }

    #[test]
    fn parse_path_pattern() {
        let config = parse_timing_config("generics/basic.vole");
        assert_eq!(config.level, tracing::Level::DEBUG);
        assert_eq!(config.filter.as_deref(), Some("generics/basic.vole"));
    }

    #[test]
    fn parse_plain_word_pattern() {
        let config = parse_timing_config("generics");
        assert_eq!(config.level, tracing::Level::DEBUG);
        assert_eq!(config.filter.as_deref(), Some("generics"));
    }
}
