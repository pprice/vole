// passes/import_trimming.rs
//! Pass 2: Import trimming.
//!
//! Attempts to remove individual import statements (`let x = import "..."` and
//! `let { a, b } = import "..."`) from each surviving `.vole` file.
//!
//! The pass first tries AST-aware removal using parser spans. If parsing
//! fails (e.g. the file was previously mangled or the parser can't handle it),
//! it falls back to line-based removal using a regex.

use std::path::Path;

use regex::Regex;
use vole_frontend::Parser;
use vole_frontend::ast::{Decl, ExprKind, LetInit};

use crate::oracle::MatchResult;
use crate::reducer::Reducer;
use crate::span_remove;

use super::file_utils::{discover_vole_files, read_file, relative_display, write_file};

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Run the import trimming pass over all `.vole` files in the workspace.
pub fn run(reducer: &mut Reducer<'_>) -> Result<(), String> {
    println!("Pass 2: import trimming");

    let vole_files = discover_vole_files(&reducer.workspace.result)?;

    if vole_files.is_empty() {
        println!("  No .vole files found — skipping.");
        println!();
        return Ok(());
    }

    let mut total_removed = 0u32;
    let mut files_touched = 0u32;

    for path in &vole_files {
        let removed = trim_imports_in_file(reducer, path)?;
        if removed > 0 {
            files_touched += 1;
            total_removed += removed;
        }
    }

    println!("  Pass 2 complete: {total_removed} import(s) removed from {files_touched} file(s)",);
    println!();
    Ok(())
}

// ---------------------------------------------------------------------------
// Per-file import trimming
// ---------------------------------------------------------------------------

/// Trim imports from a single file. Returns how many imports were removed.
fn trim_imports_in_file(reducer: &mut Reducer<'_>, path: &Path) -> Result<u32, String> {
    // Re-read the file each time since earlier removals mutate it.
    let source = read_file(path)?;

    // Attempt AST-based removal first.
    let imports = parse_import_spans(&source);
    match imports {
        Some(spans) if !spans.is_empty() => {
            try_remove_imports_by_span(reducer, path, &source, &spans)
        }
        Some(_) => Ok(0), // Parsed successfully but no imports found.
        None => {
            // Parse failed — fall back to line-based removal.
            try_remove_imports_by_line(reducer, path, &source)
        }
    }
}

// ---------------------------------------------------------------------------
// AST-based import discovery
// ---------------------------------------------------------------------------

/// Information about a single import declaration found in source.
struct ImportInfo {
    /// Byte range `[start, end)` covering the entire declaration.
    start: usize,
    end: usize,
    /// Human-readable display text (e.g. `let x = import "foo"`).
    display: String,
    /// 1-indexed source line number.
    line: u32,
}

/// Parse the source and return spans of all import declarations.
///
/// Returns `None` if parsing fails (signals caller to use line-based fallback).
fn parse_import_spans(source: &str) -> Option<Vec<ImportInfo>> {
    let mut parser = Parser::new(source);
    let program = parser.parse_program().ok()?;

    let mut imports = Vec::new();
    for decl in &program.declarations {
        if let Some(info) = extract_import_info(decl, source) {
            imports.push(info);
        }
    }
    Some(imports)
}

/// If `decl` is an import declaration, extract its span and display text.
fn extract_import_info(decl: &Decl, source: &str) -> Option<ImportInfo> {
    match decl {
        Decl::Let(let_stmt) => {
            if let LetInit::Expr(expr) = &let_stmt.init
                && matches!(expr.kind, ExprKind::Import(_))
            {
                let span = let_stmt.span;
                Some(ImportInfo {
                    start: span.start,
                    end: span.end,
                    display: snippet_from_source(source, span.start, span.end),
                    line: span.line,
                })
            } else {
                None
            }
        }
        Decl::LetTuple(let_tuple) => {
            if matches!(let_tuple.init.kind, ExprKind::Import(_)) {
                let span = let_tuple.span;
                Some(ImportInfo {
                    start: span.start,
                    end: span.end,
                    display: snippet_from_source(source, span.start, span.end),
                    line: span.line,
                })
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Extract a display snippet from source, truncated to 80 chars.
fn snippet_from_source(source: &str, start: usize, end: usize) -> String {
    let raw = &source[start..end];
    // Take only the first line to keep it concise.
    let first_line = raw.lines().next().unwrap_or(raw);
    if first_line.len() > 80 {
        format!("{}...", &first_line[..77])
    } else {
        first_line.to_string()
    }
}

// ---------------------------------------------------------------------------
// Span-based removal loop
// ---------------------------------------------------------------------------

/// Try removing each import by span, one at a time. Returns count removed.
///
/// Imports are tried in reverse order (last first) so that span offsets
/// for earlier imports remain valid after each removal.
fn try_remove_imports_by_span(
    reducer: &mut Reducer<'_>,
    path: &Path,
    original_source: &str,
    imports: &[ImportInfo],
) -> Result<u32, String> {
    let mut removed = 0u32;
    // Work on a mutable copy of the source; after each successful removal
    // we re-parse to get fresh spans.
    let mut current_source = original_source.to_string();

    // Process imports in reverse order so byte offsets stay valid.
    for import in imports.iter().rev() {
        let modified = span_remove::remove_span(&current_source, import.start, import.end);
        let outcome = test_modification(reducer, path, &current_source, &modified)?;

        match outcome {
            TrialOutcome::Accepted => {
                let display_name = relative_display(path, &reducer.workspace.result);
                println!(
                    "  Removed import: {} (line {}, {})",
                    import.display, import.line, display_name,
                );
                current_source = modified;
                removed += 1;
            }
            TrialOutcome::Rejected | TrialOutcome::Divergent => {
                // Keep the import — source unchanged.
            }
        }
    }

    Ok(removed)
}

// ---------------------------------------------------------------------------
// Line-based fallback
// ---------------------------------------------------------------------------

/// Fallback: try removing lines that look like imports (regex-based).
///
/// Used when the parser cannot handle the file.
fn try_remove_imports_by_line(
    reducer: &mut Reducer<'_>,
    path: &Path,
    original_source: &str,
) -> Result<u32, String> {
    let import_re =
        Regex::new(r"(?m)^[ \t]*let\s.*=\s*import\s").expect("import regex should compile");

    let lines: Vec<&str> = original_source.lines().collect();
    let import_line_indices: Vec<usize> = lines
        .iter()
        .enumerate()
        .filter(|(_, line)| import_re.is_match(line))
        .map(|(i, _)| i)
        .collect();

    if import_line_indices.is_empty() {
        return Ok(0);
    }

    let display_name = relative_display(path, &reducer.workspace.result);
    if reducer.verbose {
        println!(
            "  Falling back to line-based import removal for {} ({} candidate line(s))",
            display_name,
            import_line_indices.len(),
        );
    }

    let mut removed = 0u32;
    let mut current_source = original_source.to_string();

    // Process in reverse so line numbers stay valid.
    for &line_idx in import_line_indices.iter().rev() {
        let modified = remove_line(&current_source, line_idx);
        let display_text = lines[line_idx].trim().to_string();

        let outcome = test_modification(reducer, path, &current_source, &modified)?;

        match outcome {
            TrialOutcome::Accepted => {
                println!(
                    "  Removed import: {} (line {}, {})",
                    snippet_truncated(&display_text, 80),
                    line_idx + 1,
                    display_name,
                );
                current_source = modified;
                removed += 1;
            }
            TrialOutcome::Rejected | TrialOutcome::Divergent => {}
        }
    }

    Ok(removed)
}

/// Remove a single line (0-indexed) from source, including its trailing newline.
fn remove_line(source: &str, line_idx: usize) -> String {
    let mut result = String::with_capacity(source.len());
    for (i, line) in source.lines().enumerate() {
        if i != line_idx {
            result.push_str(line);
            result.push('\n');
        }
    }
    // Preserve lack of trailing newline if original didn't have one.
    if !source.ends_with('\n') && result.ends_with('\n') {
        result.pop();
    }
    result
}

/// Truncate a string for display.
fn snippet_truncated(s: &str, max: usize) -> String {
    if s.len() > max {
        format!("{}...", &s[..max.saturating_sub(3)])
    } else {
        s.to_string()
    }
}

// ---------------------------------------------------------------------------
// Oracle trial
// ---------------------------------------------------------------------------

/// Outcome of trying a single modification.
enum TrialOutcome {
    /// Oracle said Same — keep the modification.
    Accepted,
    /// Oracle said Pass — revert.
    Rejected,
    /// Oracle said Different — revert (divergent snapshot already saved by
    /// the module_elimination pass infrastructure; here we just log).
    Divergent,
}

/// Write `modified` to `path`, run the oracle, and restore `original` if needed.
fn test_modification(
    reducer: &mut Reducer<'_>,
    path: &Path,
    original: &str,
    modified: &str,
) -> Result<TrialOutcome, String> {
    write_file(path, modified)?;

    let result = reducer.oracle.run(
        &reducer.workspace.result,
        &reducer.file_path,
        &reducer.dir_path,
    );
    reducer.stats.oracle_invocations += 1;

    let verdict = reducer.oracle.check(&result, reducer.baseline);

    match verdict {
        MatchResult::Same => {
            reducer.stats.successful_reductions += 1;
            Ok(TrialOutcome::Accepted)
        }
        MatchResult::Pass => {
            // Bug disappeared — restore original.
            write_file(path, original)?;
            Ok(TrialOutcome::Rejected)
        }
        MatchResult::Different => {
            // Different failure — restore original.
            write_file(path, original)?;

            if reducer.verbose {
                let display_name = relative_display(path, &reducer.workspace.result);
                println!("  Different failure while trimming import in {display_name}");
            }
            Ok(TrialOutcome::Divergent)
        }
    }
}
