#!/usr/bin/env python3
"""Generate benchmark workloads for perf-hunt.

Usage: gen-suite.py <output-dir> <name:seed:profile:layers:mods> [...]

Example:
    gen-suite.py /tmp/vole-perf \\
        perf-full-1000:1000:full:12:15 \\
        perf-many-modules-2000:2000:many-modules:12:25

Each argument is a colon-separated tuple:
    name:seed:profile:layers:modules_per_layer

Builds vole-stress once, then generates each workload.
Output (stdout): JSON array of generated workloads.
Progress goes to stderr.
"""

import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent.parent


def log(msg: str) -> None:
    print(msg, file=sys.stderr)


def build_vole_stress() -> Path:
    log("Building vole-stress...")
    subprocess.run(
        ["cargo", "build", "-p", "vole-stress", "--manifest-path", str(REPO_ROOT / "Cargo.toml")],
        check=True,
        capture_output=True,
    )
    binary = REPO_ROOT / "target" / "debug" / "vole-stress"
    if not binary.exists():
        print("ERROR: vole-stress binary not found after build", file=sys.stderr)
        sys.exit(1)
    log("Build complete.")
    return binary


def generate_workload(
    binary: Path, output_dir: Path, name: str, seed: str, profile: str, layers: str, mods: str
) -> dict | None:
    log(f"--- Generating: {name} (seed={seed} profile={profile} layers={layers} mods={mods}) ---")
    result = subprocess.run(
        [
            str(binary),
            "--seed", seed,
            "--profile", profile,
            "--layers", layers,
            "--modules-per-layer", mods,
            "--output", str(output_dir),
            "--name", name,
        ],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        log(f"  ERROR: generation failed")
        log(f"  {result.stdout.strip()}")
        log(f"  {result.stderr.strip()}")
        return None

    # Parse output directory from vole-stress output
    workload_dir = None
    for line in result.stdout.splitlines():
        if "output:" in line:
            workload_dir = line.split("output:")[-1].strip()
            break

    if not workload_dir or not Path(workload_dir).is_dir():
        workload_dir = str(output_dir / name)

    log(f"  output: {workload_dir}")
    return {"name": name, "dir": workload_dir}


def parse_spec(spec: str) -> tuple[str, str, str, str, str] | None:
    parts = spec.split(":")
    if len(parts) != 5:
        log(f"ERROR: invalid spec '{spec}', expected name:seed:profile:layers:mods")
        return None
    return tuple(parts)


def main() -> None:
    if len(sys.argv) < 3:
        print(f"Usage: {sys.argv[0]} <output-dir> <name:seed:profile:layers:mods> [...]", file=sys.stderr)
        sys.exit(1)

    output_dir = Path(sys.argv[1])
    output_dir.mkdir(parents=True, exist_ok=True)

    binary = build_vole_stress()

    results = []
    for spec_str in sys.argv[2:]:
        spec = parse_spec(spec_str)
        if spec is None:
            continue
        name, seed, profile, layers, mods = spec
        workload = generate_workload(binary, output_dir, name, seed, profile, layers, mods)
        if workload:
            results.append(workload)

    log("=== Suite generation complete ===")
    json.dump(results, sys.stdout, indent=2)
    print()


if __name__ == "__main__":
    main()
