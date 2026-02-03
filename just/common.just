# Common cargo commands with profile support
# Import this file to get build, test, snap, unit, fmt recipes

# Build profile: "dev" (default) or "release" - from env var
export PROFILE := env("PROFILE", "dev")

# Cargo flags based on profile
cargo_profile := if PROFILE == "release" { "--release" } else { "" }

# Build (use PROFILE=release for release build)
build:
    cargo build {{cargo_profile}}

# Run Rust tests (quiet - only shows failures)
test:
    cargo test --quiet {{cargo_profile}}

# Run snapshot tests
snap:
    cargo run -p vole-snap {{cargo_profile}} -- test test/snapshot/

# Run vole unit tests (failures only)
unit:
    cargo run --bin vole {{cargo_profile}} -- test test/unit/ --report=failures

# Run vole unit tests with verbose output
unit-verbose:
    cargo run --bin vole {{cargo_profile}} -- test test/unit/

# Run memory leak tests
mem:
    cargo run -p vole-leak {{cargo_profile}} -- test/unit/mem/

# Run memory leak tests on all unit tests
mem-all:
    cargo run -p vole-leak {{cargo_profile}} -- test/unit/

# Format code
fmt:
    cargo fmt

# Run clippy lints
clippy:
    cargo clippy -- -D warnings
