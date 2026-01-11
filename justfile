# Default recipe - show available commands
default:
    @just --list

# Build in debug mode
build:
    cargo build

# Build in release mode
build-release:
    cargo build --release

# Fast type checking (no codegen) - use this to verify changes quickly
check:
    cargo check --all-targets

# Run tests in debug mode
test:
    cargo test

# Run tests in release mode
test-release:
    cargo test --release

# Run snapshot tests in debug mode
snap:
    cargo run --bin vole-snap -- test test/snapshot/

# Run snapshot tests in release mode
snap-release:
    cargo run --release --bin vole-snap -- test test/snapshot/

# Run vole unit tests in debug mode
unit:
    cargo run --bin vole -- test test/unit/

# Run vole unit tests in release mode
unit-release:
    cargo run --release --bin vole -- test test/unit/

# Run clippy lints
clippy:
    cargo clippy -- -D warnings

# Run clippy with auto-fix
clippy-fix:
    cargo clippy --fix --allow-dirty --allow-staged -- -D warnings

# Format code
fmt:
    cargo fmt

# Check formatting (for CI)
fmt-check:
    cargo fmt -- --check

# Run all checks locally (mirrors CI)
ci: fmt-check clippy build test snap-ci unit-ci

# Pre-commit checks and fixes
pre-commit: fmt clippy-fix clippy build test snap-ci unit-ci

# Snapshot tests for CI (failures only)
snap-ci:
    cargo run --bin vole-snap -- test test/snapshot/ --report=failures

# Vole unit tests for CI (failures only)
unit-ci:
    cargo run --bin vole -- test test/unit/ --report=failures

# Show next available error code for a category (lexer, parser, sema)
dev-next-error category:
    #!/usr/bin/env bash
    case "{{category}}" in
        lexer|lex|l)
            file="src/errors/lexer.rs"
            prefix="E0"
            ;;
        parser|parse|p)
            file="src/errors/parser.rs"
            prefix="E1"
            ;;
        sema|semantic|s)
            file="src/errors/sema.rs"
            prefix="E2"
            ;;
        *)
            echo "Usage: just next-error <lexer|parser|sema>"
            exit 1
            ;;
    esac
    max=$(grep -oP 'code\(E\d+\)' "$file" | grep -oP '\d+' | sort -n | tail -1)
    next=$((max + 1))
    printf "${prefix}%03d\n" $((next % 1000))

# Trace a keyword through the compiler pipeline
dev-trace-keyword keyword:
    #!/usr/bin/env bash
    echo "=== Lexer (frontend/lexer.rs, frontend/token.rs) ==="
    grep -n -i "{{keyword}}" src/frontend/lexer.rs src/frontend/token.rs 2>/dev/null || echo "(not found)"
    echo ""
    echo "=== Parser (frontend/parser.rs, frontend/parse_*.rs) ==="
    grep -n -i "{{keyword}}" src/frontend/parser.rs src/frontend/parse_*.rs 2>/dev/null || echo "(not found)"
    echo ""
    echo "=== AST (frontend/ast.rs) ==="
    grep -n -i "{{keyword}}" src/frontend/ast.rs 2>/dev/null || echo "(not found)"
    echo ""
    echo "=== Sema (sema/) ==="
    grep -n -i "{{keyword}}" src/sema/*.rs 2>/dev/null || echo "(not found)"
    echo ""
    echo "=== Codegen (codegen/) ==="
    grep -n -i "{{keyword}}" src/codegen/*.rs 2>/dev/null || echo "(not found)"

# Show equivalent Void (Zig) reference file
dev-void-ref path:
    #!/usr/bin/env bash
    void_base="$HOME/code/personal/void"
    # Convert .rs to .zig and adjust path
    void_path=$(echo "{{path}}" | sed 's/\.rs$/.zig/')
    full_path="$void_base/$void_path"
    if [ -f "$full_path" ]; then
        echo "=== $full_path ==="
        cat "$full_path"
    else
        echo "File not found: $full_path"
        echo "Searching for similar files..."
        basename=$(basename "$void_path" .zig)
        find "$void_base/src" -name "*${basename}*" -type f 2>/dev/null | head -5
    fi

# List all error codes with messages
dev-list-errors category="all":
    #!/usr/bin/env bash
    if [ "{{category}}" = "all" ]; then
        files="src/errors/lexer.rs src/errors/parser.rs src/errors/sema.rs"
    else
        case "{{category}}" in
            lexer|lex|l) files="src/errors/lexer.rs" ;;
            parser|parse|p) files="src/errors/parser.rs" ;;
            sema|semantic|s) files="src/errors/sema.rs" ;;
            *) echo "Usage: just dev-list-errors [lexer|parser|sema|all]"; exit 1 ;;
        esac
    fi
    for file in $files; do
        echo "=== $(basename $file .rs) ==="
        grep -oP 'code\(E\d+\)' "$file" | while read -r code; do
            code_num=$(echo "$code" | grep -oP 'E\d+')
            # Find the error message (line with #[error before this code)
            msg=$(grep -B5 "$code" "$file" | grep '#\[error' | tail -1 | sed 's/.*#\[error("\([^"]*\)".*/\1/')
            echo "$code_num: $msg"
        done | sort
        echo ""
    done

# List all token types
dev-tokens:
    @grep -A200 "^pub enum TokenType" src/frontend/token.rs | grep -E "^\s+\w+," | sed 's/,.*//' | sed 's/^\s*//'

# List TODOs and FIXMEs in the codebase
dev-todos:
    #!/usr/bin/env bash
    echo "=== TODO comments ==="
    grep -rn "TODO" src/ --include="*.rs" | grep -v "target/" || echo "(none)"
    echo ""
    echo "=== FIXME comments ==="
    grep -rn "FIXME" src/ --include="*.rs" | grep -v "target/" || echo "(none)"
    echo ""
    echo "=== todo!() macros ==="
    grep -rn "todo!()" src/ --include="*.rs" | grep -v "target/" || echo "(none)"
    echo ""
    echo "=== unimplemented!() macros ==="
    grep -rn "unimplemented!()" src/ --include="*.rs" | grep -v "target/" || echo "(none)"

# Find test files related to a feature
dev-test-for feature:
    #!/usr/bin/env bash
    echo "=== Unit tests (test/unit/) ==="
    grep -rl -i "{{feature}}" test/unit/ 2>/dev/null || echo "(not found)"
    echo ""
    echo "=== Snapshot tests (test/snapshot/) ==="
    grep -rl -i "{{feature}}" test/snapshot/ 2>/dev/null || echo "(not found)"
    echo ""
    echo "=== Test file names matching '{{feature}}' ==="
    find test/ -name "*{{feature}}*" -type f 2>/dev/null || echo "(not found)"

# Debug a test file with lldb (builds debug, runs under debugger)
dev-debug-test file:
    #!/usr/bin/env bash
    cargo build --bin vole 2>&1
    echo "Starting lldb - use 'run' to execute, 'bt' for backtrace on crash"
    lldb -- ./target/debug/vole test "{{file}}"

# Debug running a vole program with lldb
dev-debug-run file:
    #!/usr/bin/env bash
    cargo build --bin vole 2>&1
    echo "Starting lldb - use 'run' to execute, 'bt' for backtrace on crash"
    lldb -- ./target/debug/vole run "{{file}}"

# Get backtrace from a crashing test (non-interactive)
dev-backtrace-test file:
    #!/usr/bin/env bash
    cargo build --bin vole 2>&1
    echo "Running test under lldb to capture backtrace..."
    lldb -b -o "run" -o "bt" -o "quit" -- ./target/debug/vole test "{{file}}" 2>&1 | head -100

# Disassemble around a crash address (usage: just dev-disasm 0x12345)
dev-disasm addr:
    #!/usr/bin/env bash
    cargo build --bin vole 2>&1
    lldb -b -o "disassemble -s {{addr}} -c 20" ./target/debug/vole 2>&1

# Run with tracing enabled (shows pipeline phases, compact output)
trace file:
    VOLE_LOG=vole=info cargo run --quiet -- run "{{file}}" 2>&1

# Run with verbose tracing (includes nested spans)
trace-verbose file:
    VOLE_LOG=vole=debug cargo run --quiet -- run "{{file}}" 2>&1

# Run with full timestamps (for human debugging)
trace-full file:
    VOLE_LOG=vole=info VOLE_LOG_STYLE=full cargo run --quiet -- run "{{file}}" 2>&1

# Run with tracing for a specific module (e.g., codegen, sema)
trace-module module file:
    VOLE_LOG=vole::{{module}}=debug cargo run --quiet -- run "{{file}}" 2>&1

# Run tests with tracing enabled
trace-test path:
    VOLE_LOG=vole=info cargo run --quiet -- test "{{path}}" 2>&1
