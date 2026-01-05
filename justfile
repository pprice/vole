# Default recipe - show available commands
default:
    @just --list

# Build in debug mode
build:
    cargo build

# Build in release mode
build-release:
    cargo build --release

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

# Format code
fmt:
    cargo fmt

# Check formatting (for CI)
fmt-check:
    cargo fmt -- --check

# Run all checks locally (mirrors CI)
ci: fmt-check clippy build test snap

# Pre-commit checks and fixes
pre-commit: fmt clippy build test snap
