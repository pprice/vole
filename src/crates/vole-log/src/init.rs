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
/// - When chrome trace output is configured, a `tracing_chrome::ChromeLayer` is
///   added with a filter so it only captures `vole::compile_timing` spans.
///
/// Returns the `FlushGuard` for the chrome layer if one was created. The caller
/// must hold this guard until after command execution to ensure the trace file
/// is flushed.
pub fn init_logging(timing_value: Option<&str>) -> Option<tracing_chrome::FlushGuard> {
    let mut chrome_output = None;

    let timing_layer = timing_value.map(|value| {
        let config = parse_timing_config(value);
        chrome_output = config.chrome_output.clone();
        CompileTimingLayer::new(config)
    });

    let env_filter = EnvFilter::try_from_env("VOLE_LOG").ok();
    let has_env_log = env_filter.is_some();

    let style = std::env::var("VOLE_LOG_STYLE").unwrap_or_default();
    let use_full_style = style == "full";

    // Build the chrome layer when chrome trace output is requested.
    let (chrome_layer, flush_guard) = if let Some(ref path) = chrome_output {
        let (layer, guard) = tracing_chrome::ChromeLayerBuilder::new()
            .file(path)
            .include_args(true)
            .build();

        let chrome_filter = tracing_subscriber::filter::filter_fn(|metadata| {
            metadata.target() == "vole::compile_timing"
        });

        (Some(layer.with_filter(chrome_filter)), Some(guard))
    } else {
        (None, None)
    };

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
                .with(chrome_layer)
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
                .with(chrome_layer)
                .with(fmt_layer.with_filter(filter))
                .init();
        }
        (None, _) => {
            if timing_layer.is_some() || chrome_layer.is_some() {
                tracing_subscriber::registry()
                    .with(timing_layer)
                    .with(chrome_layer)
                    .init();
            }
        }
    }

    if has_env_log {
        tracing::debug!("tracing initialized");
    }

    flush_guard
}

/// Parse the `--timing` value into a `CompileTimingConfig`.
///
/// Grammar:
/// - `""` (empty / no value) → level=DEBUG, filter=None
/// - `"trace"` → level=TRACE, filter=None
/// - `"trace:pattern"` → level=TRACE, filter=Some(pattern)
/// - `"chrome:path.json"` → level=DEBUG, chrome_output=Some(path.json)
/// - `"chrome:trace:path.json"` → level=TRACE, chrome_output=Some(path.json)
/// - `"pattern"` → level=DEBUG, filter=Some(value)
fn parse_timing_config(value: &str) -> CompileTimingConfig {
    if value.is_empty() {
        return CompileTimingConfig::default();
    }

    // Chrome trace output: "chrome:path" or "chrome:trace:path"
    if let Some(rest) = value.strip_prefix("chrome:") {
        if let Some(path) = rest.strip_prefix("trace:") {
            return CompileTimingConfig {
                level: tracing::Level::TRACE,
                filter: None,
                chrome_output: Some(path.to_string()),
            };
        }
        return CompileTimingConfig {
            level: tracing::Level::DEBUG,
            filter: None,
            chrome_output: Some(rest.to_string()),
        };
    }

    if value == "trace" {
        return CompileTimingConfig {
            level: tracing::Level::TRACE,
            filter: None,
            chrome_output: None,
        };
    }

    if let Some(pattern) = value.strip_prefix("trace:") {
        return CompileTimingConfig {
            level: tracing::Level::TRACE,
            filter: Some(pattern.to_string()),
            chrome_output: None,
        };
    }

    // Value is a file path filter pattern.
    CompileTimingConfig {
        level: tracing::Level::DEBUG,
        filter: Some(value.to_string()),
        chrome_output: None,
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

    #[test]
    fn parse_chrome_with_path() {
        let config = parse_timing_config("chrome:/tmp/trace.json");
        assert_eq!(config.level, tracing::Level::DEBUG);
        assert!(config.filter.is_none());
        assert_eq!(config.chrome_output.as_deref(), Some("/tmp/trace.json"));
    }

    #[test]
    fn parse_chrome_trace_with_path() {
        let config = parse_timing_config("chrome:trace:/tmp/trace.json");
        assert_eq!(config.level, tracing::Level::TRACE);
        assert!(config.filter.is_none());
        assert_eq!(config.chrome_output.as_deref(), Some("/tmp/trace.json"));
    }

    #[test]
    fn parse_empty_has_no_chrome_output() {
        let config = parse_timing_config("");
        assert!(config.chrome_output.is_none());
    }

    #[test]
    fn parse_trace_has_no_chrome_output() {
        let config = parse_timing_config("trace");
        assert!(config.chrome_output.is_none());
    }
}
