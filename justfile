# Vole justfile - run `just` to see available commands
#
# Override profile: PROFILE=release just build
# Or use alias:     just release build

import 'just/common.just'

mod ci 'just/ci.just'
mod dev 'just/dev.just'
mod trace 'just/trace.just'

# Default recipe - show available commands
default:
    @just --list

# Alias to run any recipe in release mode
release +args:
    @PROFILE=release just {{args}}

# Fast type checking (no codegen)
check:
    cargo check --all-targets

# Update all dependencies
update:
    cargo update

# Pre-commit checks with auto-fixes
pre-commit:
    @just ci pre-commit
