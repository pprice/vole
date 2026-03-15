mod compile_timing;
mod init;

pub use compile_timing::{
    CompileTimingConfig, CompileTimingLayer, TimingSpan, format_duration, render_timing_spans,
    render_timing_tree, take_timing_tree,
};
pub use init::init_logging;

/// Macro for compiler timing instrumentation.
///
/// Creates a tracing span with target `vole::compile_timing` at the specified level.
/// Use `.entered()` on the result to activate the span.
///
/// # Levels
/// - `INFO`: phase and file boundaries (parse, sema, vir_lower, codegen)
/// - `DEBUG`: sub-phases (lower_test_bodies, compile_monomorphized_instances)
/// - `TRACE`: per-function granularity (compile_function, lower_function)
///
/// # Examples
/// ```ignore
/// let _span = compile_timing!(INFO, "codegen").entered();
/// let _span = compile_timing!(INFO, "file", path = %file_path).entered();
/// let _span = compile_timing!(DEBUG, "lower_test_bodies").entered();
/// let _span = compile_timing!(TRACE, "compile_function", name = %func_name).entered();
/// ```
#[macro_export]
macro_rules! compile_timing {
    (INFO, $name:expr $(, $($field:tt)*)?) => {
        $crate::tracing::info_span!(target: "vole::compile_timing", $name $(, $($field)*)?)
    };
    (DEBUG, $name:expr $(, $($field:tt)*)?) => {
        $crate::tracing::debug_span!(target: "vole::compile_timing", $name $(, $($field)*)?)
    };
    (TRACE, $name:expr $(, $($field:tt)*)?) => {
        $crate::tracing::trace_span!(target: "vole::compile_timing", $name $(, $($field)*)?)
    };
}

// Re-export tracing so the macro expansion can reference it, and so callers
// don't need a direct tracing dependency for common types.
pub use tracing;
pub use tracing::Span;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compile_timing_info_creates_span() {
        let span = compile_timing!(INFO, "codegen");
        let _entered = span.entered();
    }

    #[test]
    fn compile_timing_debug_creates_span() {
        let span = compile_timing!(DEBUG, "lower_test_bodies");
        let _entered = span.entered();
    }

    #[test]
    fn compile_timing_trace_creates_span() {
        let span = compile_timing!(TRACE, "compile_function");
        let _entered = span.entered();
    }

    #[test]
    fn compile_timing_with_fields() {
        let file_path = "test.vole";
        let span = compile_timing!(INFO, "file", path = %file_path);
        let _entered = span.entered();
    }

    #[test]
    fn span_type_is_accessible() {
        let _span: Span = compile_timing!(INFO, "test");
    }
}
