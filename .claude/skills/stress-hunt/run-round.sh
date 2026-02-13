#!/usr/bin/env bash
set -euo pipefail

# run-round.sh — Generate and test vole-stress seeds, output JSONL results.
#
# Usage: run-round.sh [--release] [--diff] [--asan] <output-dir> <seed1:profile1> [seed2:profile2 ...]
#
# Options:
#   --release    Build and run with release-local profile (optimized + symbols)
#   --diff       Differential testing: run each seed under both debug and
#                release-local, report mismatches (exit code or stdout diffs)
#   --asan       Build vole with AddressSanitizer (nightly, separate target dir).
#                Catches heap corruption, double-free, use-after-free.
#                Mutually exclusive with --release and --diff.
#
# Each seed:profile pair is generated, tested (60s timeout), and run (30s timeout).
# JSONL results go to stdout; progress to stderr.

REPO_ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
TEST_TIMEOUT=60
RUN_TIMEOUT=30
CARGO_PROFILE="dev"
TARGET_DIR="debug"
DIFF_MODE=false
ASAN_MODE=false

usage() {
    echo "Usage: $0 [--release] [--diff] [--asan] <output-dir> <seed:profile> [seed:profile ...]" >&2
    exit 1
}

# Parse flags
while [[ $# -gt 0 && "$1" == --* ]]; do
    case "$1" in
        --release)
            CARGO_PROFILE="release-local"
            TARGET_DIR="release-local"
            shift
            ;;
        --diff)
            DIFF_MODE=true
            shift
            ;;
        --asan)
            ASAN_MODE=true
            shift
            ;;
        *)
            echo >&2 "Unknown flag: $1"
            usage
            ;;
    esac
done

# Validate flag combinations
if [[ "$ASAN_MODE" == true ]]; then
    if [[ "$DIFF_MODE" == true || "$CARGO_PROFILE" != "dev" ]]; then
        echo >&2 "ERROR: --asan is mutually exclusive with --release and --diff"
        exit 1
    fi
fi

if [[ $# -lt 2 ]]; then
    usage
fi

OUTPUT_DIR="$1"
shift

# Simple JSON string escaper — no jq dependency.
# Escapes backslashes, double quotes, and control characters.
json_escape() {
    local s="$1"
    s="${s//\\/\\\\}"
    s="${s//\"/\\\"}"
    s="${s//$'\n'/\\n}"
    s="${s//$'\r'/\\r}"
    s="${s//$'\t'/\\t}"
    printf '%s' "$s"
}

# Run test+run for a seed directory with a given vole binary.
# Sets: _test_status, _run_status, _test_stdout, _run_stdout, _error_summary
run_seed() {
    local vole="$1" dir="$2"
    _test_status="skip"
    _run_status="skip"
    _test_stdout=""
    _run_stdout=""
    _error_summary=""

    if [[ ! -d "$dir" ]]; then
        _test_status="fail"
        _error_summary="directory not found"
        return
    fi

    local test_output="" test_exit=0
    test_output=$(timeout "$TEST_TIMEOUT" "${VOLE_ENV[@]}" "$vole" test "$dir/" 2>&1) || test_exit=$?
    _test_stdout="$test_output"

    if [[ $test_exit -eq 0 ]]; then
        _test_status="pass"
    elif [[ $test_exit -eq 124 ]]; then
        _test_status="timeout"
        _error_summary="test timed out after ${TEST_TIMEOUT}s"
    else
        _test_status="fail"
        _error_summary=$(echo "$test_output" | head -20 | tr '\n' ' ')
    fi

    if [[ "$_test_status" == "pass" && -f "$dir/main.vole" ]]; then
        local run_output="" run_exit=0
        run_output=$(timeout "$RUN_TIMEOUT" "${VOLE_ENV[@]}" "$vole" run "$dir/main.vole" 2>&1) || run_exit=$?
        _run_stdout="$run_output"

        if [[ $run_exit -eq 0 ]]; then
            _run_status="pass"
        elif [[ $run_exit -eq 124 ]]; then
            _run_status="timeout"
            _error_summary="run timed out after ${RUN_TIMEOUT}s"
        else
            _run_status="fail"
            _error_summary=$(echo "$run_output" | head -20 | tr '\n' ' ')
        fi
    elif [[ "$_test_status" == "pass" ]]; then
        _run_status="pass"
    fi
}

# Env prefix for running vole (empty normally, sets ASAN_OPTIONS for --asan)
VOLE_ENV=()

# Build binaries.
if [[ "$ASAN_MODE" == true ]]; then
    # ASan mode: vole-stress normal, vole with ASan via nightly
    echo >&2 "Building vole-stress (debug) and vole (ASan/nightly)..."
    cargo build -p vole-stress --manifest-path "$REPO_ROOT/Cargo.toml" 2>&1 | tail -1 >&2
    RUSTFLAGS="-Zsanitizer=address" CARGO_TARGET_DIR="$REPO_ROOT/target-asan" \
        cargo +nightly build --target x86_64-unknown-linux-gnu \
        --manifest-path "$REPO_ROOT/Cargo.toml" 2>&1 | tail -1 >&2
    echo >&2 "Build complete."

    VOLE_STRESS="$REPO_ROOT/target/debug/vole-stress"
    VOLE="$REPO_ROOT/target-asan/x86_64-unknown-linux-gnu/debug/vole"
    VOLE_ENV=(env ASAN_OPTIONS=detect_leaks=0)
elif [[ "$DIFF_MODE" == true ]]; then
    # Diff mode: build both debug and release-local
    echo >&2 "Building vole-stress and vole (debug + release-local for diff)..."
    cargo build -p vole-stress --manifest-path "$REPO_ROOT/Cargo.toml" 2>&1 | tail -1 >&2
    cargo build --manifest-path "$REPO_ROOT/Cargo.toml" 2>&1 | tail -1 >&2
    cargo build --manifest-path "$REPO_ROOT/Cargo.toml" --profile release-local 2>&1 | tail -1 >&2
    echo >&2 "Build complete."

    VOLE_STRESS="$REPO_ROOT/target/debug/vole-stress"
    VOLE_DEBUG="$REPO_ROOT/target/debug/vole"
    VOLE_RELEASE="$REPO_ROOT/target/release-local/vole"
else
    # Normal mode: build one profile
    PROFILE_FLAG=()
    if [[ "$CARGO_PROFILE" != "dev" ]]; then
        PROFILE_FLAG=(--profile "$CARGO_PROFILE")
    fi

    echo >&2 "Building vole-stress and vole (profile=$CARGO_PROFILE)..."
    cargo build -p vole-stress --manifest-path "$REPO_ROOT/Cargo.toml" "${PROFILE_FLAG[@]}" 2>&1 | tail -1 >&2
    cargo build --manifest-path "$REPO_ROOT/Cargo.toml" "${PROFILE_FLAG[@]}" 2>&1 | tail -1 >&2
    echo >&2 "Build complete."

    VOLE_STRESS="$REPO_ROOT/target/$TARGET_DIR/vole-stress"
    VOLE="$REPO_ROOT/target/$TARGET_DIR/vole"
fi

for pair in "$@"; do
    seed="${pair%%:*}"
    profile="${pair#*:}"

    if [[ "$seed" == "$pair" ]]; then
        echo >&2 "ERROR: invalid format '$pair', expected seed:profile"
        continue
    fi

    echo >&2 "--- seed=$seed profile=$profile ---"

    dir_name=""
    dir=""
    test_status="skip"
    run_status="skip"
    error_summary=""

    # Generate (always use debug vole-stress — generation is the same)
    gen_output=""
    if gen_output=$("$VOLE_STRESS" --seed "$seed" --profile "$profile" --output "$OUTPUT_DIR" 2>&1); then
        dir=$(echo "$gen_output" | grep '^ *output:' | sed 's/^ *output: *//')
        if [[ -n "$dir" ]]; then
            dir_name=$(basename "$dir")
        else
            error_summary="failed to parse output dir from vole-stress"
            test_status="fail"
        fi
    else
        error_summary="vole-stress generation failed: $(echo "$gen_output" | tail -5 | tr '\n' ' ')"
        test_status="fail"
    fi

    if [[ "$DIFF_MODE" == true && -n "$dir" && -d "$dir" ]]; then
        # Run under both debug and release-local, compare results
        run_seed "$VOLE_DEBUG" "$dir"
        dbg_test="$_test_status"; dbg_run="$_run_status"
        dbg_test_out="$_test_stdout"; dbg_run_out="$_run_stdout"
        dbg_error="$_error_summary"

        run_seed "$VOLE_RELEASE" "$dir"
        rel_test="$_test_status"; rel_run="$_run_status"
        rel_test_out="$_test_stdout"; rel_run_out="$_run_stdout"
        rel_error="$_error_summary"

        # Detect mismatches
        diff_mismatch=""
        if [[ "$dbg_test" != "$rel_test" ]]; then
            diff_mismatch="test_status: debug=$dbg_test release=$rel_test"
        elif [[ "$dbg_run" != "$rel_run" ]]; then
            diff_mismatch="run_status: debug=$dbg_run release=$rel_run"
        elif [[ "$dbg_test" == "pass" && "$rel_test" == "pass" && "$dbg_run_out" != "$rel_run_out" ]]; then
            diff_mismatch="stdout differs between debug and release"
        fi

        # Use the worse status for the overall result
        if [[ "$dbg_test" == "fail" || "$rel_test" == "fail" ]]; then
            test_status="fail"
        elif [[ "$dbg_test" == "timeout" || "$rel_test" == "timeout" ]]; then
            test_status="timeout"
        else
            test_status="$dbg_test"
        fi

        if [[ "$dbg_run" == "fail" || "$rel_run" == "fail" ]]; then
            run_status="fail"
        elif [[ "$dbg_run" == "timeout" || "$rel_run" == "timeout" ]]; then
            run_status="timeout"
        else
            run_status="$dbg_run"
        fi

        if [[ -n "$diff_mismatch" ]]; then
            error_summary="DIFF MISMATCH: $diff_mismatch | debug_error: $dbg_error | release_error: $rel_error"
        elif [[ -n "$dbg_error" ]]; then
            error_summary="$dbg_error"
        else
            error_summary="$rel_error"
        fi

        esc_dir_name=$(json_escape "${dir_name}")
        esc_dir=$(json_escape "${dir}")
        esc_error=$(json_escape "${error_summary}")
        esc_mismatch=$(json_escape "${diff_mismatch}")

        echo "{\"seed\":${seed},\"profile\":\"${profile}\",\"dir_name\":\"${esc_dir_name}\",\"dir\":\"${esc_dir}\",\"test_status\":\"${test_status}\",\"run_status\":\"${run_status}\",\"error_summary\":\"${esc_error}\",\"diff_mismatch\":\"${esc_mismatch}\"}"

        if [[ -n "$diff_mismatch" ]]; then
            echo >&2 "  ** DIFF MISMATCH: $diff_mismatch"
        fi
        echo >&2 "  test=$test_status run=$run_status"
    elif [[ -n "$dir" && -d "$dir" ]]; then
        # Normal mode
        run_seed "$VOLE" "$dir"
        test_status="$_test_status"
        run_status="$_run_status"
        error_summary="$_error_summary"

        esc_dir_name=$(json_escape "${dir_name}")
        esc_dir=$(json_escape "${dir}")
        esc_error=$(json_escape "${error_summary}")

        echo "{\"seed\":${seed},\"profile\":\"${profile}\",\"dir_name\":\"${esc_dir_name}\",\"dir\":\"${esc_dir}\",\"test_status\":\"${test_status}\",\"run_status\":\"${run_status}\",\"error_summary\":\"${esc_error}\"}"
        echo >&2 "  test=$test_status run=$run_status"
    else
        # Generation failed
        esc_dir_name=$(json_escape "${dir_name}")
        esc_dir=$(json_escape "${dir}")
        esc_error=$(json_escape "${error_summary}")

        echo "{\"seed\":${seed},\"profile\":\"${profile}\",\"dir_name\":\"${esc_dir_name}\",\"dir\":\"${esc_dir}\",\"test_status\":\"${test_status}\",\"run_status\":\"${run_status}\",\"error_summary\":\"${esc_error}\"}"
        echo >&2 "  test=$test_status run=$run_status"
    fi
done
