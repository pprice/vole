# CI and pre-commit checks

set working-directory := ".."

import 'common.just'

# Run all checks (mirrors CI) - default command
default: fmt-check clippy build test snap unit

# Pre-commit checks with auto-fixes
pre-commit: fmt clippy-fix clippy build test snap unit

# === CI-specific recipes ===

# Check formatting (no changes)
fmt-check:
    cargo fmt -- --check

# Run clippy with auto-fix
clippy-fix:
    cargo clippy --fix --allow-dirty --allow-staged -- -D warnings
