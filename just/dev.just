# Development and debugging utilities

# Run from project root, not just/
set working-directory := ".."

# List dev commands
default:
    @just --list dev

# Show next available error code for a category (lexer, parser, sema)
next-error category:
    #!/usr/bin/env bash
    case "{{category}}" in
        lexer|lex|l)
            file="src/crates/vole-frontend/src/errors/lexer.rs"
            prefix="E0"
            ;;
        parser|parse|p)
            file="src/crates/vole-frontend/src/errors/parser.rs"
            prefix="E1"
            ;;
        sema|semantic|s)
            file="src/crates/vole-sema/src/errors/mod.rs"
            prefix="E2"
            ;;
        *)
            echo "Usage: just dev next-error <lexer|parser|sema>"
            exit 1
            ;;
    esac
    max=$(grep -oP 'code\(E\d+\)' "$file" | grep -oP '\d+' | sort -n | tail -1)
    next=$((max + 1))
    printf "${prefix}%03d\n" $((next % 1000))

# Trace a keyword through the compiler pipeline
trace-keyword keyword:
    #!/usr/bin/env bash
    echo "=== Lexer (lexer.rs, token.rs) ==="
    grep -n -i "{{keyword}}" src/crates/vole-frontend/src/lexer.rs src/crates/vole-frontend/src/token.rs 2>/dev/null || echo "(not found)"
    echo ""
    echo "=== Parser (parser/, parse_*.rs) ==="
    grep -rn -i "{{keyword}}" src/crates/vole-frontend/src/parser/ src/crates/vole-frontend/src/parse_*.rs 2>/dev/null || echo "(not found)"
    echo ""
    echo "=== AST (ast.rs) ==="
    grep -n -i "{{keyword}}" src/crates/vole-frontend/src/ast.rs 2>/dev/null || echo "(not found)"
    echo ""
    echo "=== Sema ==="
    grep -rn -i "{{keyword}}" src/crates/vole-sema/src/ 2>/dev/null || echo "(not found)"
    echo ""
    echo "=== Codegen ==="
    grep -rn -i "{{keyword}}" src/crates/vole-codegen/src/ 2>/dev/null || echo "(not found)"

# List all error codes with messages
list-errors category="all":
    #!/usr/bin/env bash
    if [ "{{category}}" = "all" ]; then
        files="src/crates/vole-frontend/src/errors/lexer.rs src/crates/vole-frontend/src/errors/parser.rs src/crates/vole-sema/src/errors/mod.rs"
    else
        case "{{category}}" in
            lexer|lex|l) files="src/crates/vole-frontend/src/errors/lexer.rs" ;;
            parser|parse|p) files="src/crates/vole-frontend/src/errors/parser.rs" ;;
            sema|semantic|s) files="src/crates/vole-sema/src/errors/mod.rs" ;;
            *) echo "Usage: just dev list-errors [lexer|parser|sema|all]"; exit 1 ;;
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
tokens:
    @grep -A200 "^pub enum TokenType" src/crates/vole-frontend/src/token.rs | grep -E "^\s+\w+," | sed 's/,.*//' | sed 's/^\s*//'

# List TODOs and FIXMEs in the codebase
todos:
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
test-for feature:
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
debug-test file:
    #!/usr/bin/env bash
    cargo build --bin vole 2>&1
    echo "Starting lldb - use 'run' to execute, 'bt' for backtrace on crash"
    lldb -- ./target/debug/vole test "{{file}}"

# Debug running a vole program with lldb
debug-run file:
    #!/usr/bin/env bash
    cargo build --bin vole 2>&1
    echo "Starting lldb - use 'run' to execute, 'bt' for backtrace on crash"
    lldb -- ./target/debug/vole run "{{file}}"

# Get backtrace from a crashing test (non-interactive)
backtrace-test file:
    #!/usr/bin/env bash
    cargo build --bin vole 2>&1
    echo "Running test under lldb to capture backtrace..."
    lldb -b -o "run" -o "bt" -o "quit" -- ./target/debug/vole test "{{file}}" 2>&1 | head -100

# Disassemble around a crash address (usage: just dev disasm 0x12345)
disasm addr:
    #!/usr/bin/env bash
    cargo build --bin vole 2>&1
    lldb -b -o "disassemble -s {{addr}} -c 20" ./target/debug/vole 2>&1
