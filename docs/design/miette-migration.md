# Design: Migrate to miette + thiserror

## Summary

Replace the custom `src/errors/` diagnostic system (~370 LOC) with miette + thiserror derive macros while preserving error codes, hints, related locations, and formatted output.

## Current State

### Dependencies (unused)
```toml
thiserror = "2.0"
miette = { version = "7.4", features = ["fancy"] }
```

### Custom Implementation

| File | LOC | Purpose |
|------|-----|---------|
| `codes.rs` | 248 | `ErrorInfo` structs with static metadata |
| `diagnostic.rs` | 144 | `Diagnostic`, `RelatedInfo`, `DiagnosticBuilder` |
| `render.rs` | 369 | ANSI console renderer |
| **Total** | ~370 | (excluding tests) |

### Current Error Flow
```
Lexer/Parser/Sema
  → DiagnosticBuilder::error()
  → Diagnostic struct
  → render_diagnostics()
  → stderr
```

## Proposed Design

### Error Type Hierarchy

```rust
// src/errors/mod.rs
use miette::{Diagnostic, NamedSource, SourceSpan};
use thiserror::Error;

/// Wrapper holding source for all vole errors
#[derive(Debug)]
pub struct SourcedError<E: Diagnostic> {
    pub error: E,
    pub src: NamedSource<String>,
}

impl<E: Diagnostic + std::error::Error> std::error::Error for SourcedError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.error.source()
    }
}
```

### Lexer Errors (E0xxx)

```rust
// src/errors/lexer.rs
#[derive(Error, Debug, Diagnostic)]
pub enum LexerError {
    #[error("unexpected character '{ch}'")]
    #[diagnostic(code(vole::lexer::E0001))]
    UnexpectedCharacter {
        ch: char,
        #[label("unexpected character")]
        span: SourceSpan,
    },

    #[error("unterminated string literal")]
    #[diagnostic(
        code(vole::lexer::E0002),
        help("add a closing '\"' to terminate the string")
    )]
    UnterminatedString {
        #[label("string starts here")]
        span: SourceSpan,
    },

    #[error("invalid number literal")]
    #[diagnostic(code(vole::lexer::E0005))]
    InvalidNumber {
        #[label("invalid number")]
        span: SourceSpan,
    },
}
```

### Parser Errors (E1xxx)

```rust
// src/errors/parser.rs
#[derive(Error, Debug, Diagnostic)]
pub enum ParserError {
    #[error("expected expression, found '{found}'")]
    #[diagnostic(code(vole::parser::E1001))]
    ExpectedExpression {
        found: String,
        #[label("expected expression")]
        span: SourceSpan,
    },

    #[error("expected '{expected}', found '{found}'")]
    #[diagnostic(code(vole::parser::E1002))]
    ExpectedToken {
        expected: String,
        found: String,
        #[label("unexpected token")]
        span: SourceSpan,
    },

    #[error("expected block")]
    #[diagnostic(
        code(vole::parser::E1007),
        help("blocks start with '{{'")
    )]
    ExpectedBlock {
        #[label("expected block here")]
        span: SourceSpan,
    },
    // ... other parser errors
}
```

### Semantic Errors (E2xxx)

```rust
// src/errors/sema.rs
#[derive(Error, Debug, Diagnostic)]
pub enum SemanticError {
    #[error("expected {expected}, found {found}")]
    #[diagnostic(code(vole::sema::E2001))]
    TypeMismatch {
        expected: String,
        found: String,
        #[label("type mismatch")]
        span: SourceSpan,
    },

    #[error("undefined variable '{name}'")]
    #[diagnostic(code(vole::sema::E2002))]
    UndefinedVariable {
        name: String,
        #[label("not found in scope")]
        span: SourceSpan,
    },

    #[error("cannot assign to immutable variable '{name}'")]
    #[diagnostic(
        code(vole::sema::E2006),
        help("consider declaring with 'let mut' to make it mutable")
    )]
    ImmutableAssignment {
        name: String,
        #[label("cannot assign")]
        span: SourceSpan,
        #[label("declared as immutable here")]
        declaration: SourceSpan,
    },

    #[error("break outside of loop")]
    #[diagnostic(code(vole::sema::E2008))]
    InvalidBreak {
        #[label("not inside a loop")]
        span: SourceSpan,
    },

    #[error("expected {expected} arguments, found {found}")]
    #[diagnostic(code(vole::sema::E2012))]
    WrongArgumentCount {
        expected: usize,
        found: usize,
        #[label("wrong number of arguments")]
        span: SourceSpan,
    },

    #[error("condition must be boolean, found {found}")]
    #[diagnostic(code(vole::sema::E2027))]
    ConditionNotBool {
        found: String,
        #[label("expected bool")]
        span: SourceSpan,
    },
}
```

### Unified Error Type

```rust
// src/errors/mod.rs
#[derive(Error, Debug, Diagnostic)]
pub enum VoleError {
    #[error(transparent)]
    #[diagnostic(transparent)]
    Lexer(#[from] LexerError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    Parser(#[from] ParserError),

    #[error(transparent)]
    #[diagnostic(transparent)]
    Semantic(#[from] SemanticError),
}

/// Attach source code to an error for rendering
pub fn with_source(error: VoleError, filename: &str, source: String) -> miette::Report {
    miette::Report::new(error).with_source_code(NamedSource::new(filename, source))
}
```

### Span Conversion

```rust
// src/frontend/span.rs (add impl)
impl From<Span> for SourceSpan {
    fn from(span: Span) -> Self {
        // miette uses byte offsets
        (span.start, span.end - span.start).into()
    }
}

impl From<&Span> for SourceSpan {
    fn from(span: &Span) -> Self {
        (span.start, span.end - span.start).into()
    }
}
```

### Main Setup

```rust
// src/main.rs
fn main() -> miette::Result<()> {
    miette::set_hook(Box::new(|_| {
        Box::new(
            miette::MietteHandlerOpts::new()
                .terminal_links(true)
                .context_lines(2)
                .build()
        )
    }))?;

    // ... rest of main
}
```

### Usage in Analyzer

```rust
// Before (current)
let diag = self.diag_builder.error(
    &codes::SEMA_UNDEFINED_VARIABLE,
    expr.span,
    format!("undefined variable '{}'", name),
);
self.errors.push(TypeError { diagnostic: diag });

// After (miette)
self.errors.push(SemanticError::UndefinedVariable {
    name: name.to_string(),
    span: expr.span.into(),
});
```

## Migration Steps

### Phase 1: Add Infrastructure
1. Create `src/errors/lexer.rs`, `parser.rs`, `sema.rs` with miette error enums
2. Add `From<Span> for SourceSpan` conversion
3. Keep existing system working in parallel

### Phase 2: Migrate Lexer
1. Update `Lexer` to collect `Vec<LexerError>` instead of `Vec<Diagnostic>`
2. Update error creation sites
3. Update tests

### Phase 3: Migrate Parser
1. Change `ParseError` to wrap `ParserError`
2. Update parser error creation
3. Handle lexer error propagation

### Phase 4: Migrate Semantic Analyzer
1. Change `TypeError` to wrap `SemanticError`
2. Update all `diag_builder.error()` calls
3. Handle related locations with multiple labels

### Phase 5: Integrate Reporting
1. Add `miette::set_hook()` in main
2. Update `parse_and_analyze()` to return `miette::Result`
3. Remove `render_diagnostics()` calls

### Phase 6: Cleanup
1. Delete `src/errors/codes.rs`
2. Delete `src/errors/diagnostic.rs`
3. Delete `src/errors/render.rs`
4. Update `mod.rs` exports

## Trade-offs

### Advantages
- **Less code**: ~370 LOC → ~150 LOC
- **Derive macros**: Error definition at point of use
- **Maintained**: miette is actively developed
- **Features**: URL links, graphical output, multiple output formats
- **Ecosystem**: IDE integration, standard Rust error patterns

### Disadvantages
- **Owned source**: Each error carries source copy (memory)
- **Error code format**: Changes from `E2001` to `vole::sema::E2001`
- **Less control**: Rendering controlled by miette, not custom
- **Dependency**: External crate vs. self-contained

### Mitigations
- Source cloning: Use `Arc<String>` if memory becomes issue
- Error codes: Can use `code(E2001)` for shorter codes
- Rendering: `MietteHandlerOpts` provides customization
- Snapshots: Tests may need updating for new format

## Testing Strategy

1. Update snapshot tests to match miette output format
2. Verify error codes appear correctly
3. Verify hints/help text appears
4. Verify related locations (multiple labels) work
5. Test color output detection

## Snapshot Testing (vole-snap)

The current system uses `render_diagnostics_to(&diagnostics, &mut buffer, false)` to render
errors to a buffer without colors for snapshot comparison. Miette supports this:

```rust
use miette::{GraphicalReportHandler, GraphicalTheme, ThemeStyles, ThemeCharacters};

/// Create a handler for terminal output (unicode + colors)
pub fn terminal_handler() -> GraphicalReportHandler {
    let theme = GraphicalTheme {
        characters: ThemeCharacters::unicode(),
        styles: ThemeStyles::ansi(),
    };
    GraphicalReportHandler::new_themed(theme)
}

/// Create a handler for snapshot testing (ascii + no colors)
pub fn snapshot_handler() -> GraphicalReportHandler {
    let theme = GraphicalTheme {
        characters: ThemeCharacters::ascii(),
        styles: ThemeStyles::none(),
    };
    GraphicalReportHandler::new_themed(theme)
}

/// Render to stderr with unicode/colors
pub fn render_to_stderr(report: &miette::Report) {
    let handler = terminal_handler();
    let mut output = String::new();
    handler.render_report(&mut output, report.as_ref()).ok();
    eprint!("{}", output);
}

/// Render to a buffer without colors (for snapshots/testing)
pub fn render_to_string(report: &miette::Report) -> String {
    let mut output = String::new();
    let handler = snapshot_handler();
    handler.render_report(&mut output, report.as_ref()).ok();
    output
}

/// Render to any Write impl
pub fn render_to_writer<W: std::io::Write>(
    report: &miette::Report,
    mut writer: W,
) -> std::io::Result<()> {
    let output = render_to_string(report);
    writer.write_all(output.as_bytes())
}
```

Key points:
- `ThemeStyles::none()` → disables all ANSI color codes
- `ThemeCharacters::ascii()` → deterministic ASCII output (`|`, `-`, `^`)
- `render_report(&mut impl fmt::Write, ...)` → writes to `String`, buffer, etc.
- Snapshots will need re-blessing since miette format differs from custom renderer

### Migration for check_captured/run_captured

```rust
pub fn check_captured<W: Write>(
    source: &str,
    file_path: &str,
    mut stderr: W,
) -> Result<(), ()> {
    match compile_and_check(source, file_path) {
        Ok(program) => Ok(program),
        Err(err) => {
            let report = miette::Report::new(err)
                .with_source_code(NamedSource::new(file_path, source.to_string()));
            render_to_writer(&report, &mut stderr).ok();
            Err(())
        }
    }
}
```

## Decisions

1. **Output modes**:
   - **Terminal**: Unicode box-drawing + ANSI colors (via `ThemeCharacters::unicode()`, `ThemeStyles::ansi()`)
   - **Snapshots**: ASCII + no colors (via `ThemeCharacters::ascii()`, `ThemeStyles::none()`)

2. **Snapshot format**: Accept miette's format, re-bless all snapshots after migration

## Open Questions

1. **Error code format**: Keep `vole::sema::E2001` or use bare `E2001`?
2. **Source ownership**: Clone source per-error or use `Arc`?
3. **Gradual migration**: Run both systems during migration?
4. **Warning support**: Add warnings now or defer?

## Decision

Recommend proceeding with migration because:
1. The dependencies are already declared but unused
2. miette provides equivalent functionality with less maintenance
3. The derive macro pattern is more idiomatic Rust
4. Error handling becomes more composable with standard traits
