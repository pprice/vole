# CI and pre-commit checks

# Run from project root
set working-directory := ".."

# Run all checks (mirrors CI) - default command
default: fmt-check clippy build test snap unit

# Pre-commit checks with auto-fixes
pre-commit: fmt clippy-fix clippy build test snap unit

# Check formatting (no changes)
fmt-check:
    cargo fmt -- --check

# Run clippy lints
clippy:
    cargo clippy -- -D warnings

# Run clippy with auto-fix
clippy-fix:
    cargo clippy --fix --allow-dirty --allow-staged -- -D warnings

# Build
build:
    cargo build

# Run Rust tests
test:
    cargo test --quiet

# Snapshot tests (failures only)
snap:
    cargo run -p vole-snap -- test test/snapshot/ --report=failures

# Vole unit tests (failures only)
unit:
    cargo run --bin vole -- test test/unit/ --report=failures

# Format code
fmt:
    cargo fmt
