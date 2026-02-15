// passes/body_reduction.rs
//! Pass 4: Declaration body reduction (AST-aware).
//!
//! Goes one level deeper than declaration elimination: removes *inner* members
//! from surviving declarations. For each declaration kind the pass tries
//! removing fields, methods, statements, test cases, and interface signatures
//! one at a time, largest first, re-parsing after each successful removal.

use std::path::Path;

use vole_frontend::ast::{
    Block, ClassDecl, Decl, FuncBody, FuncDecl, ImplementBlock, InterfaceDecl, InterfaceMethod,
    StaticsBlock, Stmt, StructDecl, TestsDecl,
};
use vole_frontend::{Interner, Parser};

use crate::oracle::MatchResult;
use crate::reducer::Reducer;
use crate::span_remove;

use super::file_utils::{discover_vole_files, read_file, relative_display, write_file};

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Run the body reduction pass over all `.vole` files.
pub fn run(reducer: &mut Reducer<'_>) -> Result<(), String> {
    println!("Pass 4: declaration body reduction");

    let vole_files = discover_vole_files(&reducer.workspace.result)?;

    if vole_files.is_empty() {
        println!("  No .vole files found — skipping.");
        println!();
        return Ok(());
    }

    let mut total_removed = 0u32;
    let mut files_touched = 0u32;

    for path in &vole_files {
        let removed = reduce_bodies_in_file(reducer, path)?;
        if removed > 0 {
            files_touched += 1;
            total_removed += removed;
        }
    }

    println!("  Pass 4 complete: {total_removed} member(s) removed from {files_touched} file(s)",);
    println!();
    Ok(())
}

// ---------------------------------------------------------------------------
// Per-file body reduction loop
// ---------------------------------------------------------------------------

/// Reduce inner members in a single file until fixpoint.
///
/// Returns the total number of members removed.
fn reduce_bodies_in_file(reducer: &mut Reducer<'_>, path: &Path) -> Result<u32, String> {
    let mut total_removed = 0u32;

    loop {
        let source = read_file(path)?;

        let items = match collect_removable_items(&source, reducer) {
            Some(items) if !items.is_empty() => items,
            _ => break,
        };

        let removed = try_remove_items(reducer, path, &source, &items)?;

        if removed == 0 {
            break;
        }
        total_removed += removed;
    }

    Ok(total_removed)
}

// ---------------------------------------------------------------------------
// Removable item collection
// ---------------------------------------------------------------------------

/// A single inner member that can potentially be removed.
struct RemovableItem {
    /// Byte range `[start, end)`.
    start: usize,
    end: usize,
    /// Size in bytes (for sorting largest-first).
    size: usize,
    /// 1-indexed start line.
    start_line: u32,
    /// 1-indexed end line.
    end_line: u32,
    /// Human-readable description for logging.
    display: String,
}

/// Parse a file and collect all removable inner members across declarations.
///
/// Returns `None` if parsing fails. Returns empty vec if nothing is removable.
fn collect_removable_items(source: &str, reducer: &Reducer<'_>) -> Option<Vec<RemovableItem>> {
    let mut parser = Parser::new(source);
    let program = parser.parse_program().ok()?;
    let interner = parser.interner();

    let mut items = Vec::new();

    for decl in &program.declarations {
        collect_items_from_decl(decl, interner, source, reducer, &mut items);
    }

    // Sort by size descending — biggest first for maximum reduction.
    items.sort_by(|a, b| b.size.cmp(&a.size));

    Some(items)
}

/// Dispatch to the appropriate collector based on declaration kind.
fn collect_items_from_decl(
    decl: &Decl,
    interner: &Interner,
    source: &str,
    reducer: &Reducer<'_>,
    out: &mut Vec<RemovableItem>,
) {
    match decl {
        Decl::Class(c) => collect_class_items(c, interner, source, out),
        Decl::Struct(s) => collect_struct_items(s, interner, source, out),
        Decl::Implement(im) => collect_implement_items(im, interner, source, out),
        Decl::Interface(iface) => collect_interface_items(iface, interner, source, out),
        Decl::Function(f) => collect_func_body_stmts(f, interner, source, out),
        Decl::Tests(t) => collect_tests_items(t, interner, source, reducer, out),
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Class members
// ---------------------------------------------------------------------------

/// Collect removable fields and methods from a ClassDecl.
fn collect_class_items(
    class: &ClassDecl,
    interner: &Interner,
    source: &str,
    out: &mut Vec<RemovableItem>,
) {
    let class_name = interner.resolve(class.name);

    for field in &class.fields {
        let sp = &field.span;
        if let Some(item) = make_item(sp.start, sp.end, sp.line, sp.end_line, source) {
            let field_name = interner.resolve(field.name);
            out.push(RemovableItem {
                display: format!("field: {class_name}.{field_name} (line {})", sp.line),
                ..item
            });
        }
    }

    for method in &class.methods {
        collect_method_as_item(method, class_name, interner, source, out);
        collect_func_body_stmts(method, interner, source, out);
    }

    if let Some(ref statics) = class.statics {
        collect_statics_items(statics, class_name, interner, source, out);
    }
}

// ---------------------------------------------------------------------------
// Struct members
// ---------------------------------------------------------------------------

/// Collect removable fields and methods from a StructDecl.
fn collect_struct_items(
    st: &StructDecl,
    interner: &Interner,
    source: &str,
    out: &mut Vec<RemovableItem>,
) {
    let struct_name = interner.resolve(st.name);

    for field in &st.fields {
        let sp = &field.span;
        if let Some(item) = make_item(sp.start, sp.end, sp.line, sp.end_line, source) {
            let field_name = interner.resolve(field.name);
            out.push(RemovableItem {
                display: format!("field: {struct_name}.{field_name} (line {})", sp.line),
                ..item
            });
        }
    }

    for method in &st.methods {
        collect_method_as_item(method, struct_name, interner, source, out);
        collect_func_body_stmts(method, interner, source, out);
    }

    if let Some(ref statics) = st.statics {
        collect_statics_items(statics, struct_name, interner, source, out);
    }
}

// ---------------------------------------------------------------------------
// Implement block members
// ---------------------------------------------------------------------------

/// Collect removable methods from an ImplementBlock.
fn collect_implement_items(
    im: &ImplementBlock,
    interner: &Interner,
    source: &str,
    out: &mut Vec<RemovableItem>,
) {
    let owner = snippet_from_source(source, im.span.start, im.span.end);

    for method in &im.methods {
        collect_method_as_item(method, &owner, interner, source, out);
        collect_func_body_stmts(method, interner, source, out);
    }

    if let Some(ref statics) = im.statics {
        collect_statics_items(statics, &owner, interner, source, out);
    }
}

// ---------------------------------------------------------------------------
// Interface members
// ---------------------------------------------------------------------------

/// Collect removable method signatures from an InterfaceDecl.
fn collect_interface_items(
    iface: &InterfaceDecl,
    interner: &Interner,
    source: &str,
    out: &mut Vec<RemovableItem>,
) {
    let iface_name = interner.resolve(iface.name);

    for field in &iface.fields {
        let sp = &field.span;
        if let Some(item) = make_item(sp.start, sp.end, sp.line, sp.end_line, source) {
            let field_name = interner.resolve(field.name);
            out.push(RemovableItem {
                display: format!("field: {iface_name}.{field_name} (line {})", sp.line),
                ..item
            });
        }
    }

    for method in &iface.methods {
        collect_iface_method_as_item(method, iface_name, interner, source, out);
    }

    if let Some(ref statics) = iface.statics {
        collect_statics_items(statics, iface_name, interner, source, out);
    }
}

/// Collect a single interface method signature as a removable item.
fn collect_iface_method_as_item(
    method: &InterfaceMethod,
    owner: &str,
    interner: &Interner,
    source: &str,
    out: &mut Vec<RemovableItem>,
) {
    let sp = &method.span;
    if let Some(item) = make_item(sp.start, sp.end, sp.line, sp.end_line, source) {
        let method_name = interner.resolve(method.name);
        out.push(RemovableItem {
            display: format!("method sig: {owner}.{method_name} (line {})", sp.line),
            ..item
        });
    }
}

// ---------------------------------------------------------------------------
// Statics block members
// ---------------------------------------------------------------------------

/// Collect removable methods from a StaticsBlock.
fn collect_statics_items(
    statics: &StaticsBlock,
    owner: &str,
    interner: &Interner,
    source: &str,
    out: &mut Vec<RemovableItem>,
) {
    for method in &statics.methods {
        let sp = &method.span;
        if let Some(item) = make_item(sp.start, sp.end, sp.line, sp.end_line, source) {
            let method_name = interner.resolve(method.name);
            out.push(RemovableItem {
                display: format!("static method: {owner}.{method_name} (line {})", sp.line),
                ..item
            });
        }
    }
}

// ---------------------------------------------------------------------------
// Function body statements
// ---------------------------------------------------------------------------

/// Collect removable statements from a FuncDecl body.
///
/// Statements are collected bottom-up (last first) since later statements are
/// more likely to be removable without breaking the function.
fn collect_func_body_stmts(
    func: &FuncDecl,
    interner: &Interner,
    source: &str,
    out: &mut Vec<RemovableItem>,
) {
    let func_name = interner.resolve(func.name);
    if let FuncBody::Block(ref block) = func.body {
        collect_block_stmts(block, func_name, source, out);
    }
}

/// Collect removable statements from a block.
///
/// Skips the final statement if it looks like a return-producing expression
/// (the function's implicit return value).
fn collect_block_stmts(block: &Block, context: &str, source: &str, out: &mut Vec<RemovableItem>) {
    let stmts = &block.stmts;
    if stmts.is_empty() {
        return;
    }

    let last_idx = stmts.len() - 1;

    // Process bottom-up (reversed), skipping the last statement if it is a
    // return-producing expression (bare Expr statement without semicolon
    // semantics). We keep return statements too as they are explicit returns.
    for (idx, stmt) in stmts.iter().enumerate().rev() {
        if idx == last_idx && is_return_producing(stmt) {
            continue;
        }

        let sp = stmt.span();
        if let Some(item) = make_item(sp.start, sp.end, sp.line, sp.end_line, source) {
            out.push(RemovableItem {
                display: format!("statement in {context} at line {}", sp.line,),
                ..item
            });
        }
    }
}

/// Check if a statement is a return-producing expression (should not be
/// removed as it may be the function's implicit return value).
fn is_return_producing(stmt: &Stmt) -> bool {
    matches!(stmt, Stmt::Return(_) | Stmt::Expr(_))
}

// ---------------------------------------------------------------------------
// Tests block members
// ---------------------------------------------------------------------------

/// Collect removable items from a TestsDecl.
///
/// For the *target* test block (containing the test we are reducing for),
/// we remove other test cases and scoped declarations. For non-target test
/// blocks the whole block would have been handled by Pass 3.
fn collect_tests_items(
    tests: &TestsDecl,
    interner: &Interner,
    source: &str,
    reducer: &Reducer<'_>,
    out: &mut Vec<RemovableItem>,
) {
    // Only drill into the target test block.
    let is_target = match reducer.test_filter {
        Some(ref filter) => tests
            .tests
            .iter()
            .any(|tc| tc.name.contains(filter.as_str())),
        None => false,
    };

    if !is_target {
        return;
    }

    // Try removing other test cases (not the target).
    for tc in &tests.tests {
        let is_target_case = reducer
            .test_filter
            .as_ref()
            .is_some_and(|f| tc.name.contains(f.as_str()));

        if is_target_case {
            continue;
        }

        let sp = &tc.span;
        if let Some(item) = make_item(sp.start, sp.end, sp.line, sp.end_line, source) {
            out.push(RemovableItem {
                display: format!("test case \"{}\" (line {})", tc.name, sp.line),
                ..item
            });
        }
    }

    // Try removing scoped declarations inside the tests block.
    for decl in &tests.decls {
        if let Some(item) = decl_to_removable_item(decl, interner, source) {
            out.push(item);
        }
        // Also recurse into function bodies of scoped declarations.
        collect_items_from_decl(decl, interner, source, reducer, out);
    }
}

/// Convert a scoped declaration (inside a tests block) into a removable item.
fn decl_to_removable_item(decl: &Decl, interner: &Interner, source: &str) -> Option<RemovableItem> {
    let (start, end, line, end_line, display) = match decl {
        Decl::Function(f) => {
            let name = interner.resolve(f.name);
            let sp = &f.span;
            (
                sp.start,
                sp.end,
                sp.line,
                sp.end_line,
                format!("scoped func {name}"),
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
                format!("scoped let {name}"),
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
                format!("scoped class {name}"),
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
                format!("scoped struct {name}"),
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
                format!("scoped interface {name}"),
            )
        }
        Decl::Implement(im) => {
            let sp = &im.span;
            let snip = snippet_from_source(source, sp.start, sp.end);
            (
                sp.start,
                sp.end,
                sp.line,
                sp.end_line,
                format!("scoped implement ({snip})"),
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
                format!("scoped error {name}"),
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
                format!("scoped sentinel {name}"),
            )
        }
        _ => return None,
    };

    make_item(start, end, line, end_line, source).map(|item| RemovableItem {
        display: format!("{display} (line {line})"),
        ..item
    })
}

// ---------------------------------------------------------------------------
// Shared method helper
// ---------------------------------------------------------------------------

/// Collect a FuncDecl method as a removable item.
fn collect_method_as_item(
    method: &FuncDecl,
    owner: &str,
    interner: &Interner,
    source: &str,
    out: &mut Vec<RemovableItem>,
) {
    let sp = &method.span;
    if let Some(item) = make_item(sp.start, sp.end, sp.line, sp.end_line, source) {
        let method_name = interner.resolve(method.name);
        out.push(RemovableItem {
            display: format!("method: {owner}.{method_name} (line {})", sp.line),
            ..item
        });
    }
}

// ---------------------------------------------------------------------------
// Span-based removal loop
// ---------------------------------------------------------------------------

/// Try removing each item by span, one at a time.
///
/// After the first successful removal we return (the caller re-parses to get
/// fresh spans).
fn try_remove_items(
    reducer: &mut Reducer<'_>,
    path: &Path,
    current_source: &str,
    items: &[RemovableItem],
) -> Result<u32, String> {
    let mut removed = 0u32;
    let mut source = current_source.to_string();

    for item in items {
        // Once we have a successful removal, re-parse needed — break.
        if removed > 0 {
            break;
        }

        let modified = span_remove::remove_span(&source, item.start, item.end);

        let effective = if parses_ok(&modified) {
            modified
        } else {
            let fallback = remove_lines(&source, item.start_line, item.end_line);
            if parses_ok(&fallback) {
                fallback
            } else {
                continue;
            }
        };

        let outcome = test_modification(reducer, path, &source, &effective)?;

        match outcome {
            TrialOutcome::Accepted => {
                let display_name = relative_display(path, &reducer.workspace.result);
                println!("  Removed {} ({})", item.display, display_name);
                source = effective;
                removed += 1;
            }
            TrialOutcome::Rejected | TrialOutcome::Divergent => {}
        }
    }

    Ok(removed)
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
                println!("  Different failure while reducing body in {display_name}");
            }
            Ok(TrialOutcome::Divergent)
        }
    }
}

// ---------------------------------------------------------------------------
// Item construction helper
// ---------------------------------------------------------------------------

/// Build a `RemovableItem` from span info, validating bounds.
///
/// The `display` field is left as a placeholder; callers should override it.
fn make_item(
    start: usize,
    end: usize,
    start_line: u32,
    end_line: u32,
    source: &str,
) -> Option<RemovableItem> {
    if end <= start || end > source.len() {
        return None;
    }
    Some(RemovableItem {
        start,
        end,
        size: end - start,
        start_line,
        end_line,
        display: String::new(),
    })
}

// ---------------------------------------------------------------------------
// Parse / line helpers
// ---------------------------------------------------------------------------

/// Check whether source parses without errors.
fn parses_ok(source: &str) -> bool {
    let mut parser = Parser::new(source);
    parser.parse_program().is_ok()
}

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
    if !source.ends_with('\n') && result.ends_with('\n') {
        result.pop();
    }
    result
}

// ---------------------------------------------------------------------------
// Display helpers
// ---------------------------------------------------------------------------

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
