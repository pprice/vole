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
ci: fmt-check clippy test test-release
