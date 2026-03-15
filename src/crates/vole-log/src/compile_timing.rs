use std::cell::RefCell;
use std::io::Write;
use std::time::Instant;

use tracing::Subscriber;
use tracing::span;
use tracing_subscriber::Layer;
use tracing_subscriber::layer::Context;
use tracing_subscriber::registry::LookupSpan;

const TARGET: &str = "vole::compile_timing";

// ── Configuration ────────────────────────────────────────────────────

/// Configuration for the compile timing layer.
pub struct CompileTimingConfig {
    /// Minimum level to capture (DEBUG by default).
    pub level: tracing::Level,
    /// Optional file path pattern filter. When set, only spans whose `path`
    /// field contains this substring are captured.
    pub filter: Option<String>,
    /// Optional path to write Chrome trace JSON output.
    pub chrome_output: Option<String>,
}

impl Default for CompileTimingConfig {
    fn default() -> Self {
        Self {
            level: tracing::Level::DEBUG,
            filter: None,
            chrome_output: None,
        }
    }
}

// ── Tree node ────────────────────────────────────────────────────────

/// A node in the compile-timing tree.
#[derive(Debug, Clone)]
pub struct TimingSpan {
    pub name: String,
    pub duration_us: u64,
    pub fields: Vec<(String, String)>,
    pub children: Vec<TimingSpan>,
}

// ── Layer ────────────────────────────────────────────────────────────

/// A tracing subscriber layer that captures `compile_timing!` span durations
/// and builds a renderable tree.
pub struct CompileTimingLayer {
    level: tracing::Level,
    filter: Option<String>,
}

impl CompileTimingLayer {
    pub fn new(config: CompileTimingConfig) -> Self {
        Self {
            level: config.level,
            filter: config.filter,
        }
    }
}

/// Marker stored in span extensions to indicate this span is tracked.
struct Tracked;

/// Stored in span extensions to collect field values captured at span creation.
struct FieldData {
    fields: Vec<(String, String)>,
}

/// A `tracing::field::Visit` implementation that collects field key-value pairs.
struct FieldVisitor {
    fields: Vec<(String, String)>,
}

impl FieldVisitor {
    fn new() -> Self {
        Self { fields: Vec::new() }
    }
}

impl tracing::field::Visit for FieldVisitor {
    fn record_debug(&mut self, field: &tracing::field::Field, value: &dyn std::fmt::Debug) {
        self.fields
            .push((field.name().to_string(), format!("{value:?}")));
    }

    fn record_str(&mut self, field: &tracing::field::Field, value: &str) {
        self.fields
            .push((field.name().to_string(), value.to_string()));
    }

    fn record_u64(&mut self, field: &tracing::field::Field, value: u64) {
        self.fields
            .push((field.name().to_string(), value.to_string()));
    }

    fn record_i64(&mut self, field: &tracing::field::Field, value: i64) {
        self.fields
            .push((field.name().to_string(), value.to_string()));
    }

    fn record_bool(&mut self, field: &tracing::field::Field, value: bool) {
        self.fields
            .push((field.name().to_string(), value.to_string()));
    }
}

/// A span on the in-progress stack, tracking start time and accumulated children.
struct StackEntry {
    name: String,
    fields: Vec<(String, String)>,
    start: Instant,
    children: Vec<TimingSpan>,
}

impl<S> Layer<S> for CompileTimingLayer
where
    S: Subscriber + for<'a> LookupSpan<'a>,
{
    fn on_new_span(&self, attrs: &span::Attributes<'_>, id: &span::Id, ctx: Context<'_, S>) {
        let meta = attrs.metadata();

        if meta.target() != TARGET {
            return;
        }

        // Level filter: ignore spans more verbose than configured level.
        if *meta.level() > self.level {
            return;
        }

        // Collect fields from the span attributes.
        let mut visitor = FieldVisitor::new();
        attrs.record(&mut visitor);

        // If a file path filter is set, check if the span has a matching `path` field.
        // Spans without a `path` field always pass (they are sub-phases like "sema").
        if let Some(ref pattern) = self.filter
            && let Some((_, path_value)) = visitor.fields.iter().find(|(k, _)| k == "path")
            && !path_value.contains(pattern.as_str())
        {
            return;
        }

        if let Some(span) = ctx.span(id) {
            let mut extensions = span.extensions_mut();
            extensions.insert(Tracked);
            extensions.insert(FieldData {
                fields: visitor.fields,
            });
        }
    }

    fn on_enter(&self, id: &span::Id, ctx: Context<'_, S>) {
        let Some(span) = ctx.span(id) else {
            return;
        };

        let extensions = span.extensions();
        if extensions.get::<Tracked>().is_none() {
            return;
        }

        let name = span.name().to_string();
        let fields = extensions
            .get::<FieldData>()
            .map(|fd| fd.fields.clone())
            .unwrap_or_default();

        drop(extensions);

        SPAN_STACK.with(|stack| {
            stack.borrow_mut().push(StackEntry {
                name,
                fields,
                start: Instant::now(),
                children: Vec::new(),
            });
        });
    }

    fn on_exit(&self, id: &span::Id, ctx: Context<'_, S>) {
        let Some(span) = ctx.span(id) else {
            return;
        };

        if span.extensions().get::<Tracked>().is_none() {
            return;
        }

        SPAN_STACK.with(|stack| {
            let mut stack = stack.borrow_mut();
            if let Some(entry) = stack.pop() {
                let completed = TimingSpan {
                    name: entry.name,
                    duration_us: entry.start.elapsed().as_micros() as u64,
                    fields: entry.fields,
                    children: entry.children,
                };

                if let Some(parent) = stack.last_mut() {
                    parent.children.push(completed);
                } else {
                    COMPLETED_ROOTS.with(|roots| {
                        roots.borrow_mut().push(completed);
                    });
                }
            }
        });
    }
}

// ── Thread-local storage ─────────────────────────────────────────────

thread_local! {
    /// Stack of in-progress spans. When a span exits, it is popped and
    /// attached as a child of the new top-of-stack (or moved to roots).
    static SPAN_STACK: RefCell<Vec<StackEntry>> = const { RefCell::new(Vec::new()) };

    /// Completed top-level timing spans.
    static COMPLETED_ROOTS: RefCell<Vec<TimingSpan>> = const { RefCell::new(Vec::new()) };
}

// ── Public API ───────────────────────────────────────────────────────

/// Extract the captured timing tree, clearing the thread-local storage.
pub fn take_timing_tree() -> Vec<TimingSpan> {
    COMPLETED_ROOTS.with(|roots| std::mem::take(&mut *roots.borrow_mut()))
}

/// Render the captured timing tree to `writer`.
pub fn render_timing_tree(writer: &mut dyn Write) {
    let roots = take_timing_tree();
    render_timing_spans(writer, &roots);
}

/// Render pre-collected timing spans to `writer` (does not drain the tree).
pub fn render_timing_spans(writer: &mut dyn Write, spans: &[TimingSpan]) {
    for root in spans {
        render_span(writer, root, 0);
    }
}

/// Render the captured timing tree as Chrome trace JSON to `writer`.
///
/// Produces a JSON array of "X" (complete) events compatible with
/// `chrome://tracing` and [speedscope.dev](https://speedscope.dev).
pub fn render_chrome_trace(spans: &[TimingSpan], writer: &mut dyn Write) -> std::io::Result<()> {
    writer.write_all(b"[\n")?;
    let mut first = true;
    for span in spans {
        write_chrome_events(writer, span, 0, &mut first)?;
    }
    writer.write_all(b"\n]\n")?;
    Ok(())
}

/// Recursively write Chrome trace events for a span and its children.
///
/// `ts_offset` is the start time of this span in microseconds (relative to
/// the beginning of the trace). Children are laid out sequentially within
/// the parent's duration window.
fn write_chrome_events(
    writer: &mut dyn Write,
    span: &TimingSpan,
    ts_offset: u64,
    first: &mut bool,
) -> std::io::Result<()> {
    let label = format_span_label(span);
    // Escape JSON string characters.
    let name = label.replace('\\', "\\\\").replace('"', "\\\"");

    if !*first {
        writer.write_all(b",\n")?;
    }
    *first = false;

    write!(
        writer,
        r#"  {{"name":"{}","ph":"X","ts":{},"dur":{},"pid":0,"tid":0}}"#,
        name, ts_offset, span.duration_us
    )?;

    // Lay out children sequentially within this span's time window.
    // Clamp so children never exceed parent's end time.
    let span_end = ts_offset + span.duration_us;
    let mut child_offset = ts_offset;
    for child in &span.children {
        let clamped_dur = child.duration_us.min(span_end.saturating_sub(child_offset));
        if clamped_dur == 0 {
            break; // no more room in parent
        }
        let clamped_child = TimingSpan {
            duration_us: clamped_dur,
            ..child.clone()
        };
        write_chrome_events(writer, &clamped_child, child_offset, first)?;
        child_offset += clamped_dur;
    }

    Ok(())
}

fn render_span(writer: &mut dyn Write, span: &TimingSpan, depth: usize) {
    let indent = "  ".repeat(depth);
    let label = format_span_label(span);
    let duration = format_duration(span.duration_us);

    // Right-align durations at column 60 (after the [timing] prefix).
    let prefix = format!("[timing] {indent}{label}");
    let padding = if prefix.len() < 60 {
        " ".repeat(60 - prefix.len())
    } else {
        " ".to_string()
    };

    let _ = writeln!(writer, "{prefix}{padding}{duration}");

    for child in &span.children {
        render_span(writer, child, depth + 1);
    }
}

/// Build a display label from the span name and its fields.
fn format_span_label(span: &TimingSpan) -> String {
    if span.fields.is_empty() {
        return span.name.clone();
    }

    let field_str: String = span
        .fields
        .iter()
        .map(|(_, v)| v.as_str())
        .collect::<Vec<_>>()
        .join(" ");

    format!("{} {field_str}", span.name)
}

/// Adaptive duration formatting.
pub fn format_duration(us: u64) -> String {
    if us >= 1_000_000 {
        let secs = us as f64 / 1_000_000.0;
        format!("{secs:.1}s")
    } else if us >= 1_000 {
        let ms = us as f64 / 1_000.0;
        format!("{ms:.1}ms")
    } else {
        format!("{us}\u{b5}s")
    }
}

// ── Tests ────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use tracing_subscriber::layer::SubscriberExt;

    /// Helper: set up a subscriber with CompileTimingLayer configured as given,
    /// run `f` inside it, then return the captured timing tree.
    fn with_timing_layer<F>(config: CompileTimingConfig, f: F) -> Vec<TimingSpan>
    where
        F: FnOnce(),
    {
        // Clear any leftover state from previous tests.
        SPAN_STACK.with(|s| s.borrow_mut().clear());
        COMPLETED_ROOTS.with(|r| r.borrow_mut().clear());

        let layer = CompileTimingLayer::new(config);
        let subscriber = tracing_subscriber::registry().with(layer);

        tracing::subscriber::with_default(subscriber, f);

        take_timing_tree()
    }

    #[test]
    fn span_nesting_produces_correct_tree() {
        let tree = with_timing_layer(CompileTimingConfig::default(), || {
            let outer = tracing::debug_span!(target: "vole::compile_timing", "sema");
            let _outer_guard = outer.entered();

            let inner = tracing::debug_span!(target: "vole::compile_timing", "resolve_types");
            let _inner_guard = inner.entered();
        });

        assert_eq!(tree.len(), 1, "should have one root span");
        assert_eq!(tree[0].name, "sema");
        assert_eq!(tree[0].children.len(), 1);
        assert_eq!(tree[0].children[0].name, "resolve_types");
        assert!(tree[0].children[0].children.is_empty());
    }

    #[test]
    fn file_path_filtering_works() {
        let config = CompileTimingConfig {
            filter: Some("generics".to_string()),
            ..Default::default()
        };

        let tree = with_timing_layer(config, || {
            // This span has a `path` field that matches the filter.
            let matching = tracing::debug_span!(
                target: "vole::compile_timing",
                "file",
                path = "test/unit/generics/basic.vole"
            );
            let _g1 = matching.entered();

            // This span has a `path` field that does NOT match.
            let non_matching = tracing::debug_span!(
                target: "vole::compile_timing",
                "file",
                path = "test/unit/strings/concat.vole"
            );
            let _g2 = non_matching.entered();
        });

        // Only the matching span should be captured.
        assert_eq!(tree.len(), 1);
        assert_eq!(tree[0].name, "file");
        assert!(
            tree[0]
                .fields
                .iter()
                .any(|(k, v)| k == "path" && v.contains("generics"))
        );
    }

    #[test]
    fn level_filtering_works() {
        let config = CompileTimingConfig::default();

        let tree = with_timing_layer(config, || {
            let debug_span = tracing::debug_span!(target: "vole::compile_timing", "sema");
            let _g1 = debug_span.entered();

            let trace_span =
                tracing::trace_span!(target: "vole::compile_timing", "compile_function");
            let _g2 = trace_span.entered();
        });

        // The DEBUG span should be captured, the TRACE span should not.
        assert_eq!(tree.len(), 1);
        assert_eq!(tree[0].name, "sema");
        assert!(tree[0].children.is_empty());
    }

    #[test]
    fn duration_formatting() {
        assert_eq!(format_duration(500), "500\u{b5}s");
        assert_eq!(format_duration(0), "0\u{b5}s");
        assert_eq!(format_duration(999), "999\u{b5}s");
        assert_eq!(format_duration(1_000), "1.0ms");
        assert_eq!(format_duration(1_500), "1.5ms");
        assert_eq!(format_duration(42_000), "42.0ms");
        assert_eq!(format_duration(999_999), "1000.0ms");
        assert_eq!(format_duration(1_000_000), "1.0s");
        assert_eq!(format_duration(2_500_000), "2.5s");
    }

    #[test]
    fn render_timing_tree_output_format() {
        // Build a tree manually to test rendering with known durations.
        SPAN_STACK.with(|s| s.borrow_mut().clear());
        COMPLETED_ROOTS.with(|r| r.borrow_mut().clear());

        let tree = vec![TimingSpan {
            name: "file".to_string(),
            duration_us: 6_200,
            fields: vec![(
                "path".to_string(),
                "test/unit/generics/basic.vole".to_string(),
            )],
            children: vec![
                TimingSpan {
                    name: "parse".to_string(),
                    duration_us: 42,
                    fields: vec![],
                    children: vec![],
                },
                TimingSpan {
                    name: "sema".to_string(),
                    duration_us: 580,
                    fields: vec![],
                    children: vec![],
                },
            ],
        }];

        COMPLETED_ROOTS.with(|r| {
            *r.borrow_mut() = tree;
        });

        let mut output = Vec::new();
        render_timing_tree(&mut output);
        let text = String::from_utf8(output).unwrap();

        let lines: Vec<&str> = text.lines().collect();
        assert_eq!(lines.len(), 3);

        // Every line starts with [timing].
        for line in &lines {
            assert!(
                line.starts_with("[timing]"),
                "line should start with [timing]: {line}"
            );
        }

        // Check content.
        assert!(lines[0].contains("file"));
        assert!(lines[0].contains("test/unit/generics/basic.vole"));
        assert!(lines[0].contains("6.2ms"));
        assert!(lines[1].contains("parse"));
        assert!(lines[1].contains("42\u{b5}s"));
        assert!(lines[2].contains("sema"));
        assert!(lines[2].contains("580\u{b5}s"));

        // Child lines should be indented more than root.
        let root_timing_idx = lines[0].find("file").unwrap();
        let child_timing_idx = lines[1].find("parse").unwrap();
        assert!(
            child_timing_idx > root_timing_idx,
            "children should be indented further"
        );
    }

    #[test]
    fn non_timing_spans_are_ignored() {
        let tree = with_timing_layer(CompileTimingConfig::default(), || {
            let other = tracing::debug_span!(target: "vole::other", "something_else");
            let _g = other.entered();
        });

        assert!(tree.is_empty(), "non-timing spans should be ignored");
    }

    #[test]
    fn spans_without_path_pass_filter() {
        let config = CompileTimingConfig {
            filter: Some("generics".to_string()),
            ..Default::default()
        };

        let tree = with_timing_layer(config, || {
            let span = tracing::debug_span!(target: "vole::compile_timing", "sema");
            let _g = span.entered();
        });

        assert_eq!(
            tree.len(),
            1,
            "spans without path field should pass the filter"
        );
        assert_eq!(tree[0].name, "sema");
    }

    #[test]
    fn chrome_trace_produces_valid_json() {
        let tree = vec![TimingSpan {
            name: "file".to_string(),
            duration_us: 6_200,
            fields: vec![(
                "path".to_string(),
                "test/unit/generics/basic.vole".to_string(),
            )],
            children: vec![
                TimingSpan {
                    name: "parse".to_string(),
                    duration_us: 42,
                    fields: vec![],
                    children: vec![],
                },
                TimingSpan {
                    name: "sema".to_string(),
                    duration_us: 580,
                    fields: vec![],
                    children: vec![],
                },
            ],
        }];

        let mut output = Vec::new();
        render_chrome_trace(&tree, &mut output).unwrap();
        let text = String::from_utf8(output).unwrap();

        // Should be valid JSON: starts with '[', ends with ']'
        let trimmed = text.trim();
        assert!(trimmed.starts_with('['), "should start with [");
        assert!(trimmed.ends_with(']'), "should end with ]");

        // Should contain the root event and both children (3 events).
        assert_eq!(
            text.matches("\"ph\":\"X\"").count(),
            3,
            "should have 3 complete events"
        );

        // Root event starts at ts=0 with full duration.
        assert!(text.contains("\"ts\":0,\"dur\":6200"));

        // First child starts at ts=0 (same as parent).
        assert!(text.contains("\"dur\":42"));

        // Second child starts after first child (ts=42).
        assert!(text.contains("\"ts\":42,\"dur\":580"));

        // Check the name includes fields.
        assert!(text.contains("file test/unit/generics/basic.vole"));
    }

    #[test]
    fn chrome_trace_escapes_special_chars() {
        let tree = vec![TimingSpan {
            name: "test".to_string(),
            duration_us: 100,
            fields: vec![("path".to_string(), "file \"with\" quotes".to_string())],
            children: vec![],
        }];

        let mut output = Vec::new();
        render_chrome_trace(&tree, &mut output).unwrap();
        let text = String::from_utf8(output).unwrap();

        // Quotes should be escaped.
        assert!(
            text.contains(r#"\"with\" quotes"#),
            "quotes should be escaped in JSON: {text}"
        );
    }

    #[test]
    fn chrome_trace_empty_tree() {
        let tree: Vec<TimingSpan> = vec![];
        let mut output = Vec::new();
        render_chrome_trace(&tree, &mut output).unwrap();
        let text = String::from_utf8(output).unwrap();
        assert_eq!(text, "[\n\n]\n");
    }
}
