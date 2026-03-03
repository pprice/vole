# CI and pre-commit checks

set working-directory := ".."

import 'common.just'

# Run all checks (mirrors CI) - default command
default: fmt-check clippy build test unit verify-all-ci

# Pre-commit checks with auto-fixes
pre-commit: fmt clippy-fix build test unit verify-all

# Parallel verification: snap + mem + doc-check run concurrently
[parallel]
verify-all: _snap _mem _doc-check

# CI variant uses mem-all (full leak check)
[parallel]
verify-all-ci: _snap _mem-all _doc-check

# Prefixed wrappers for parallel output (set -o pipefail preserves exit codes)
_snap:
    #!/usr/bin/env bash
    set -o pipefail
    cargo run -p vole-snap {{cargo_profile}} -- test test/snapshot/ 2>&1 | sed 's/^/[snap] /'

_mem:
    #!/usr/bin/env bash
    set -o pipefail
    cargo run -p vole-leak {{cargo_profile}} -- test/unit/mem/ 2>&1 | sed 's/^/[mem]  /'

_mem-all:
    #!/usr/bin/env bash
    set -o pipefail
    cargo run -p vole-leak {{cargo_profile}} -- test/unit/ 2>&1 | sed 's/^/[mem]  /'

_doc-check:
    #!/usr/bin/env bash
    set -o pipefail
    cargo run -p vole-doccheck {{cargo_profile}} -- docs/language/ 2>&1 | sed 's/^/[docs] /'

# === CI-specific recipes ===

# Check formatting (no changes)
fmt-check:
    cargo fmt -- --check

# Run clippy with auto-fix
clippy-fix:
    cargo clippy --fix --allow-dirty --allow-staged -- -D warnings
