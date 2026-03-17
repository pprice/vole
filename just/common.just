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

# Run vole unit tests (parallel across cores)
unit:
    #!/usr/bin/env bash
    set -euo pipefail

    # Build once, then run the binary directly to avoid cargo lock contention
    cargo build --bin vole {{cargo_profile}} 2>&1
    VOLE=$(cargo build --bin vole {{cargo_profile}} --message-format=json 2>/dev/null \
        | jq -r 'select(.executable != null) | .executable' | tail -1)
    if [[ -z "$VOLE" || ! -x "$VOLE" ]]; then
        echo "error: could not find vole binary"
        exit 1
    fi

    NCPU=$(( ($(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4) + 1) / 2 ))
    WORK=$(mktemp -d)
    trap 'rm -rf "$WORK"' EXIT

    # Collect test files, filter _prefixed
    mapfile -t FILES < <(find test/unit -name '*.vole' ! -name '_*' | sort)
    NFILES=${#FILES[@]}
    if [[ $NFILES -eq 0 ]]; then
        echo "error: no test files found"
        exit 1
    fi

    # Distribute files round-robin into shards
    for ((i=0; i<NCPU; i++)); do > "$WORK/shard_$i.txt"; done
    for ((i=0; i<NFILES; i++)); do
        echo "${FILES[$i]}" >> "$WORK/shard_$((i % NCPU)).txt"
    done

    # Launch shards in background (30s timeout per shard, SIGKILL after 10s grace, 256 MB memory limit)
    PIDS=()
    for ((i=0; i<NCPU; i++)); do
        [[ -s "$WORK/shard_$i.txt" ]] || continue
        mapfile -t SHARD_FILES < "$WORK/shard_$i.txt"
        (
            timeout -k 10 30 "$VOLE" --mem-limit 256mb test -q --color=never "${SHARD_FILES[@]}" > "$WORK/raw_$i.txt" 2>&1 || true
            STATUS=${PIPESTATUS[0]:-$?}
            sed "s/^/[test:$i] /" "$WORK/raw_$i.txt" > "$WORK/out_$i.txt" 2>/dev/null
            if [[ $STATUS -eq 124 || $STATUS -eq 137 ]]; then
                echo "[test:$i] error: shard timed out (30s limit)" >> "$WORK/out_$i.txt"
            elif [[ $STATUS -ne 0 ]]; then
                echo "[test:$i] error: process killed (exit $STATUS) — possible causes: memory limit (256 MB), segfault, assertion failure" >> "$WORK/out_$i.txt"
            fi
            echo $STATUS > "$WORK/exit_$i.txt"
        ) 2>/dev/null &
        PIDS+=($!)
    done

    ANY_FAIL=0
    for pid in "${PIDS[@]}"; do wait "$pid" || true; done
    for ((i=0; i<NCPU; i++)); do
        [[ -f "$WORK/out_$i.txt" ]] || continue
        cat "$WORK/out_$i.txt"
        if [[ -f "$WORK/exit_$i.txt" ]] && [[ $(cat "$WORK/exit_$i.txt") -ne 0 ]]; then
            ANY_FAIL=1
        fi
    done
    exit $ANY_FAIL

# Run vole unit tests with verbose output
unit-verbose:
    cargo run --bin vole {{cargo_profile}} -- test test/unit/ -v

# Run memory leak tests
mem:
    cargo run -p vole-leak {{cargo_profile}} -- test/unit/mem/

# Run memory leak tests on all unit tests
mem-all:
    cargo run -p vole-leak {{cargo_profile}} -- test/unit/

# Format code
fmt:
    cargo fmt

# Validate code blocks in documentation
doc-check:
    cargo run -p vole-doccheck {{cargo_profile}} -- docs/language/

# Run clippy lints
clippy:
    cargo clippy -- -D warnings
