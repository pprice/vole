// passes/decl_elimination.rs
//! Pass 3: Declaration elimination (AST-aware).
//!
//! Removes entire top-level declarations from each `.vole` file, one at a time,
//! largest first. The "protected" declaration (entrypoint test block or main
//! function) is never removed. After each successful removal the file is
//! re-parsed so that spans stay accurate.
//!
//! Falls back to line-based removal when span-based removal produces
//! unparseable output.

use std::path::Path;

use vole_frontend::Parser;
use vole_frontend::ast::Decl;

use crate::oracle::MatchResult;
use crate::reducer::Reducer;
use crate::span_remove;

use super::file_utils::{discover_vole_files, read_file, relative_display, write_file};

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Run the declaration elimination pass over all `.vole` files.
pub fn run(reducer: &mut Reducer<'_>) -> Result<(), String> {
    println!("Pass 3: declaration elimination");

    let vole_files = discover_vole_files(&reducer.workspace.result)?;

    if vole_files.is_empty() {
        println!("  No .vole files found — skipping.");
        println!();
        return Ok(());
    }

    let mut total_removed = 0u32;
    let mut total_lines_eliminated = 0u64;
    let mut files_touched = 0u32;

    for path in &vole_files {
        let (removed, lines) = eliminate_decls_in_file(reducer, path)?;
        if removed > 0 {
            files_touched += 1;
            total_removed += removed;
            total_lines_eliminated += lines;
        }
    }

    println!(
        "  Pass 3 complete: {total_removed} declaration(s) removed, \
         {total_lines_eliminated} lines eliminated from {files_touched} file(s)",
    );
    println!();
    Ok(())
}

// ---------------------------------------------------------------------------
// Per-file declaration elimination
// ---------------------------------------------------------------------------

/// Eliminate declarations from a single file.
///
/// Returns `(declarations_removed, lines_eliminated)`.
fn eliminate_decls_in_file(reducer: &mut Reducer<'_>, path: &Path) -> Result<(u32, u64), String> {
    let mut total_removed = 0u32;
    let mut total_lines = 0u64;

    loop {
        let source = read_file(path)?;

        let decls = match parse_decl_infos(&source, reducer) {
            Some(d) => d,
            None => {
                // Parse failed — try line-based fallback for this file.
                let (r, l) = try_line_based_fallback(reducer, path, &source)?;
                total_removed += r;
                total_lines += l;
                break;
            }
        };

        if decls.is_empty() {
            break;
        }

        let round_removed = try_remove_decls_by_span(reducer, path, &source, &decls)?;

        if round_removed == 0 {
            break;
        }

        let new_source = read_file(path)?;
        let lines_diff = line_count(&source).saturating_sub(line_count(&new_source));
        total_removed += round_removed;
        total_lines += lines_diff as u64;
    }

    Ok((total_removed, total_lines))
}

// ---------------------------------------------------------------------------
// Declaration info extraction
// ---------------------------------------------------------------------------

/// Information about a single top-level declaration.
struct DeclInfo {
    /// Byte range `[start, end)` covering the entire declaration.
    start: usize,
    end: usize,
    /// Size in bytes (used for sorting largest-first).
    size: usize,
    /// 1-indexed start line number.
    start_line: u32,
    /// 1-indexed end line number.
    end_line: u32,
    /// Human-readable description (e.g. `func helper_calc`).
    display: String,
}

/// Parse the source and extract info for all removable top-level declarations.
///
/// Returns `None` if parsing fails (signals the caller to use line-based
/// fallback). Returns an empty vec if there are no removable declarations.
fn parse_decl_infos(source: &str, reducer: &Reducer<'_>) -> Option<Vec<DeclInfo>> {
    let mut parser = Parser::new(source, ModuleId::new(0));
    let program = parser.parse_program().ok()?;
    let interner = parser.interner();

    let mut infos = Vec::new();

    for decl in &program.declarations {
        if is_protected(decl, interner, reducer) {
            continue;
        }

        if let Some(info) = extract_decl_info(decl, interner, source) {
            infos.push(info);
        }
    }

    // Sort by size descending — biggest first for maximum reduction per oracle call.
    infos.sort_by(|a, b| b.size.cmp(&a.size));

    Some(infos)
}

/// Check whether a declaration is the "protected" entrypoint that must not be
/// removed.
///
/// - If `--test` was given, protect the `TestsDecl` containing a test whose
///   name matches the filter.
/// - If no `--test`, protect any `func main`.
/// - If neither matches, nothing is protected (individual decls can still be
///   removed; the entrypoint *file* is protected by Pass 1).
fn is_protected(decl: &Decl, interner: &vole_frontend::Interner, reducer: &Reducer<'_>) -> bool {
    if let Some(ref filter) = reducer.test_filter {
        return is_tests_decl_matching(decl, filter);
    }
    // No --test: protect func main.
    is_main_func(decl, interner)
}

/// Returns `true` if `decl` is a `TestsDecl` containing a test case whose
/// name matches `filter` (substring match, like `vole test --filter`).
fn is_tests_decl_matching(decl: &Decl, filter: &str) -> bool {
    if let Decl::Tests(tests) = decl {
        return tests.tests.iter().any(|tc| tc.name.contains(filter));
    }
    false
}

/// Returns `true` if `decl` is `func main`.
fn is_main_func(decl: &Decl, interner: &vole_frontend::Interner) -> bool {
    if let Decl::Function(f) = decl {
        return interner.resolve(f.name) == "main";
    }
    false
}

/// Extract span and display info from a declaration.
fn extract_decl_info(
    decl: &Decl,
    interner: &vole_frontend::Interner,
    source: &str,
) -> Option<DeclInfo> {
    let (start, end, start_line, end_line, display) = match decl {
        Decl::Function(f) => {
            let name = interner.resolve(f.name);
            let sp = &f.span;
            (
                sp.start,
                sp.end,
                sp.line,
                sp.end_line,
                format!("func {name}"),
            )
        }
        Decl::Tests(t) => {
            let label = t.label.as_deref().unwrap_or("<unlabeled>");
            let sp = &t.span;
            (
                sp.start,
                sp.end,
                sp.line,
                sp.end_line,
                format!("tests \"{label}\""),
            )
        }
        Decl::Class(c) => {
            let name = interner.resolve(c.name);
            let sp = &c.span;
            (
                sp.start,
                sp.end,
                sp.line,
                sp.end_line,
                format!("class {name}"),
            )
        }
        Decl::Struct(s) => {
            let name = interner.resolve(s.name);
            let sp = &s.span;
            (
                sp.start,
                sp.end,
                sp.line,
                sp.end_line,
                format!("struct {name}"),
            )
        }
        Decl::Interface(i) => {
            let name = interner.resolve(i.name);
            let sp = &i.span;
            (
                sp.start,
                sp.end,
                sp.line,
                sp.end_line,
                format!("interface {name}"),
            )
        }
        Decl::Implement(im) => {
            let sp = &im.span;
            let snippet = snippet_from_source(source, sp.start, sp.end);
            (
                sp.start,
                sp.end,
                sp.line,
                sp.end_line,
                format!("implement ({snippet})"),
            )
        }
        Decl::Error(e) => {
            let name = interner.resolve(e.name);
            let sp = &e.span;
            (
                sp.start,
                sp.end,
                sp.line,
                sp.end_line,
                format!("error {name}"),
            )
        }
        Decl::Sentinel(s) => {
            let name = interner.resolve(s.name);
            let sp = &s.span;
            (
                sp.start,
                sp.end,
                sp.line,
                sp.end_line,
                format!("sentinel {name}"),
            )
        }
        Decl::External(ex) => {
            let sp = &ex.span;
            let snippet = snippet_from_source(source, sp.start, sp.end);
            (
                sp.start,
                sp.end,
                sp.line,
                sp.end_line,
                format!("external ({snippet})"),
            )
        }
        Decl::Let(l) => {
            let name = interner.resolve(l.name);
            let sp = &l.span;
            (
                sp.start,
                sp.end,
                sp.line,
                sp.end_line,
                format!("let {name}"),
            )
        }
        Decl::LetTuple(lt) => {
            let sp = &lt.span;
            let snippet = snippet_from_source(source, sp.start, sp.end);
            (
                sp.start,
                sp.end,
                sp.line,
                sp.end_line,
                format!("let tuple ({snippet})"),
            )
        }
    };

    // Guard against bad spans.
    if end <= start || end > source.len() {
        return None;
    }

    Some(DeclInfo {
        start,
        end,
        size: end - start,
        start_line,
        end_line,
        display,
    })
}

/// Extract a display snippet from source, truncated to 60 chars.
fn snippet_from_source(source: &str, start: usize, end: usize) -> String {
    let raw = &source[start..end.min(source.len())];
    let first_line = raw.lines().next().unwrap_or(raw);
    if first_line.len() > 60 {
        format!("{}...", &first_line[..57])
    } else {
        first_line.to_string()
    }
}

// ---------------------------------------------------------------------------
// Span-based removal loop
// ---------------------------------------------------------------------------

/// Try removing each declaration by span, one at a time.
///
/// Returns the count of declarations successfully removed in this round.
/// After each successful removal the caller should re-parse the file
/// (spans shift), so we return early to let that happen.
fn try_remove_decls_by_span(
    reducer: &mut Reducer<'_>,
    path: &Path,
    current_source: &str,
    decls: &[DeclInfo],
) -> Result<u32, String> {
    let mut removed = 0u32;
    let mut source = current_source.to_string();

    for decl in decls {
        // After a prior removal in this round the in-memory source has changed,
        // but our DeclInfo spans are from the original parse. Once we do one
        // removal we must re-parse, so break out after the first success.
        if removed > 0 {
            break;
        }

        let modified = span_remove::remove_span(&source, decl.start, decl.end);

        // Verify the modified source still parses; if not, try line-based
        // fallback for this specific declaration.
        let effective_modified = if parses_ok(&modified) {
            modified
        } else {
            let fallback = remove_lines(&source, decl.start_line, decl.end_line);
            if parses_ok(&fallback) {
                fallback
            } else {
                // Neither approach works — skip this declaration.
                continue;
            }
        };

        let outcome = test_modification(reducer, path, &source, &effective_modified)?;

        match outcome {
            TrialOutcome::Accepted => {
                let display_name = relative_display(path, &reducer.workspace.result);
                println!(
                    "  Removed {}: lines {}-{} ({} lines, {})",
                    decl.display,
                    decl.start_line,
                    decl.end_line,
                    decl.end_line.saturating_sub(decl.start_line) + 1,
                    display_name,
                );
                source = effective_modified;
                removed += 1;
            }
            TrialOutcome::Rejected | TrialOutcome::Divergent => {
                // Keep the declaration — source unchanged.
            }
        }
    }

    Ok(removed)
}

/// Check whether source parses without errors.
fn parses_ok(source: &str) -> bool {
    let mut parser = Parser::new(source, ModuleId::new(0));
    parser.parse_program().is_ok()
}

// ---------------------------------------------------------------------------
// Line-based fallback
// ---------------------------------------------------------------------------

/// Remove lines `[start_line, end_line]` (1-indexed, inclusive) from source.
fn remove_lines(source: &str, start_line: u32, end_line: u32) -> String {
    let mut result = String::with_capacity(source.len());
    for (i, line) in source.lines().enumerate() {
        let line_num = (i as u32) + 1;
        if line_num < start_line || line_num > end_line {
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

/// Fallback for files that don't parse at all: try removing line ranges that
/// look like declaration boundaries.
///
/// Returns `(declarations_removed, lines_eliminated)`.
fn try_line_based_fallback(
    reducer: &mut Reducer<'_>,
    path: &Path,
    source: &str,
) -> Result<(u32, u64), String> {
    let boundaries = find_decl_line_boundaries(source);

    if boundaries.is_empty() {
        return Ok((0, 0));
    }

    let display_name = relative_display(path, &reducer.workspace.result);
    if reducer.verbose {
        println!(
            "  Falling back to line-based decl removal for {} ({} candidate(s))",
            display_name,
            boundaries.len(),
        );
    }

    let mut removed = 0u32;
    let mut lines_eliminated = 0u64;
    let mut current_source = source.to_string();

    // Process in reverse so line numbers stay valid.
    for boundary in boundaries.iter().rev() {
        let modified = remove_lines(&current_source, boundary.start_line, boundary.end_line);

        let outcome = test_modification(reducer, path, &current_source, &modified)?;

        match outcome {
            TrialOutcome::Accepted => {
                let line_count = boundary.end_line - boundary.start_line + 1;
                println!(
                    "  Removed {}: lines {}-{} ({} lines, {})",
                    boundary.display,
                    boundary.start_line,
                    boundary.end_line,
                    line_count,
                    display_name,
                );
                current_source = modified;
                removed += 1;
                lines_eliminated += line_count as u64;
            }
            TrialOutcome::Rejected | TrialOutcome::Divergent => {}
        }
    }

    Ok((removed, lines_eliminated))
}

/// A declaration boundary found by heuristic line scanning.
struct LineBoundary {
    start_line: u32,
    end_line: u32,
    display: String,
}

/// Heuristic: find line ranges that look like top-level declarations.
///
/// Looks for lines starting with declaration keywords at column 0, and
/// extends each range to the next such keyword (or end of file).
fn find_decl_line_boundaries(source: &str) -> Vec<LineBoundary> {
    let keywords = [
        "func ",
        "class ",
        "struct ",
        "interface ",
        "implement ",
        "error ",
        "sentinel ",
        "tests ",
        "external(",
        "external \"",
        "statics ",
        "let ",
    ];

    let lines: Vec<&str> = source.lines().collect();
    let mut starts: Vec<(usize, String)> = Vec::new();

    for (i, line) in lines.iter().enumerate() {
        let trimmed = line.trim_start();
        for kw in &keywords {
            if trimmed.starts_with(kw) {
                let display = if trimmed.len() > 60 {
                    format!("{}...", &trimmed[..57])
                } else {
                    trimmed.to_string()
                };
                starts.push((i, display));
                break;
            }
        }
    }

    let mut boundaries = Vec::new();

    for (idx, (start_idx, display)) in starts.iter().enumerate() {
        let end_idx = if idx + 1 < starts.len() {
            starts[idx + 1].0.saturating_sub(1)
        } else {
            lines.len().saturating_sub(1)
        };

        boundaries.push(LineBoundary {
            start_line: (*start_idx as u32) + 1,
            end_line: (end_idx as u32) + 1,
            display: display.clone(),
        });
    }

    // Sort by size descending.
    boundaries.sort_by(|a, b| {
        let size_a = a.end_line - a.start_line;
        let size_b = b.end_line - b.start_line;
        size_b.cmp(&size_a)
    });

    boundaries
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
    /// Oracle said Different — revert.
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
            write_file(path, original)?;
            Ok(TrialOutcome::Rejected)
        }
        MatchResult::Different => {
            write_file(path, original)?;

            if reducer.verbose {
                let display_name = relative_display(path, &reducer.workspace.result);
                println!("  Different failure while eliminating decl in {display_name}");
            }
            Ok(TrialOutcome::Divergent)
        }
    }
}

/// Count lines in a string.
fn line_count(s: &str) -> usize {
    s.lines().count()
}
