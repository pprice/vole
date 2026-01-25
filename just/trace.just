# Tracing and debugging output

# Run from project root
set working-directory := ".."

# List trace commands
default:
    @just --list trace

# Run with tracing enabled (shows pipeline phases, compact output)
run file:
    VOLE_LOG=vole=info cargo run --quiet -- run "{{file}}" 2>&1

# Run with verbose tracing (includes nested spans)
verbose file:
    VOLE_LOG=vole=debug cargo run --quiet -- run "{{file}}" 2>&1

# Run with full timestamps (for human debugging)
full file:
    VOLE_LOG=vole=info VOLE_LOG_STYLE=full cargo run --quiet -- run "{{file}}" 2>&1

# Run with tracing for a specific module (e.g., codegen, sema)
module mod file:
    VOLE_LOG=vole::{{mod}}=debug cargo run --quiet -- run "{{file}}" 2>&1

# Run tests with tracing enabled
test path:
    VOLE_LOG=vole=info cargo run --quiet -- test "{{path}}" 2>&1
