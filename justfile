# Vole justfile - run `just` to see available commands

mod dev 'just/dev.just'

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

# Run tests in debug mode (quiet - only shows failures)
test:
    cargo test --quiet

# Run tests in release mode (quiet - only shows failures)
test-release:
    cargo test --release --quiet

# Run snapshot tests in debug mode
snap:
    cargo run -p vole-snap -- test test/snapshot/

# Run snapshot tests in release mode
snap-release:
    cargo run --release -p vole-snap -- test test/snapshot/

# Run vole unit tests in debug mode (failures only)
unit:
    cargo run --bin vole -- test test/unit/ --report=failures

# Run vole unit tests in release mode (failures only)
unit-release:
    cargo run --release --bin vole -- test test/unit/ --report=failures

# Run vole unit tests with verbose output (all tests)
unit-verbose:
    cargo run --bin vole -- test test/unit/

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
    cargo run -p vole-snap -- test test/snapshot/ --report=failures

# Vole unit tests for CI (failures only)
unit-ci:
    cargo run --bin vole -- test test/unit/ --report=failures

# Update all dependencies
update:
    cargo update

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
