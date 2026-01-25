# Vole justfile - run `just` to see available commands

mod ci 'just/ci.just'
mod dev 'just/dev.just'
mod trace 'just/trace.just'

# Default recipe - show available commands
default:
    @just --list

# === Build ===

# Build in debug mode
build:
    cargo build

# Build in release mode
build-release:
    cargo build --release

# Fast type checking (no codegen)
check:
    cargo check --all-targets

# === Test ===

# Run Rust tests (quiet - only shows failures)
test:
    cargo test --quiet

# Run Rust tests in release mode
test-release:
    cargo test --release --quiet

# Run snapshot tests
snap:
    cargo run -p vole-snap -- test test/snapshot/

# Run snapshot tests in release mode
snap-release:
    cargo run --release -p vole-snap -- test test/snapshot/

# Run vole unit tests (failures only)
unit:
    cargo run --bin vole -- test test/unit/ --report=failures

# Run vole unit tests in release mode
unit-release:
    cargo run --release --bin vole -- test test/unit/ --report=failures

# Run vole unit tests with verbose output
unit-verbose:
    cargo run --bin vole -- test test/unit/

# === Format & Lint ===

# Format code
fmt:
    cargo fmt

# Run clippy lints
clippy:
    cargo clippy -- -D warnings

# === Dependencies ===

# Update all dependencies
update:
    cargo update

# Pre-commit checks with auto-fixes
pre-commit:
    @just ci pre-commit

