#!/usr/bin/env python3
"""Profile vole workloads with perf, output structured JSON results.

Usage: profile-round.py <base-dir> <workload1> [workload2 ...]

For each workload directory under <base-dir>:
  1. Runs `perf record ... -- vole test <dir>/` for CPU sampling, timed for wall-clock
  2. Runs `perf report` to extract hotspots

Only one `vole test` invocation per workload (perf overhead is negligible).

Output (stdout): JSON object with timings and hotspots per workload.
Progress goes to stderr.
"""

import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent.parent
VOLE = REPO_ROOT / "target" / "release-local" / "vole"
PERF_FREQ = 99
PERF_PERCENT_LIMIT = 0.5

# Pattern matching perf report lines like:
#     12.34%     5.67%  vole  vole  [.] some::symbol::name
PERF_LINE_RE = re.compile(
    r"^\s*(?P<children>[\d.]+)%\s+(?P<self>[\d.]+)%\s+\S+\s+\S+\s+\[.\]\s+(?P<symbol>.+)$"
)


def log(msg: str) -> None:
    print(msg, file=sys.stderr)


def check_prereqs() -> None:
    if not VOLE.exists():
        log(f"ERROR: release-local binary not found at {VOLE}")
        log("Run: cargo build --profile release-local")
        sys.exit(1)
    if not shutil.which("perf"):
        log("ERROR: perf not found. Install linux-tools or perf.")
        sys.exit(1)


def profile_workload(base_dir: Path, workload: str) -> dict:
    workdir = base_dir / workload
    if not workdir.is_dir():
        log(f"WARNING: workload directory not found: {workdir} — skipping")
        return {"workload": workload, "error": "directory not found"}

    log(f"=== Profiling: {workload} ===")
    perf_data = Path(f"/tmp/vole-perf-data-{workload}.data")

    # Run perf record wrapping vole test, timed for wall-clock comparison.
    # perf record inherits child exit code; vole test may return non-zero for
    # stress-generated test failures — that's fine, we still get valid data.
    log(f"  Running perf record (F={PERF_FREQ}) on vole test...")
    t0 = time.monotonic()
    subprocess.run(
        [
            "perf", "record", "-g", "--call-graph=dwarf",
            "-F", str(PERF_FREQ),
            "-o", str(perf_data),
            "--", str(VOLE), "test", f"{workdir}/",
        ],
        capture_output=True,
    )
    elapsed = time.monotonic() - t0
    log(f"  Time: {elapsed:.3f}s")

    result = {
        "workload": workload,
        "time_s": round(elapsed, 3),
        "perf_data": str(perf_data),
        "hotspots": [],
    }

    if not perf_data.exists() or perf_data.stat().st_size == 0:
        log(f"  WARNING: perf record produced no data for {workload}")
        result["error"] = "no perf data"
        return result

    # Run perf report and parse hotspots
    log("  Running perf report...")
    report = subprocess.run(
        [
            "perf", "report", "--stdio",
            f"--percent-limit={PERF_PERCENT_LIMIT}",
            "-i", str(perf_data),
        ],
        capture_output=True,
        text=True,
    )

    for line in report.stdout.splitlines():
        m = PERF_LINE_RE.match(line)
        if m:
            result["hotspots"].append({
                "symbol": m.group("symbol").strip(),
                "children_pct": float(m.group("children")),
                "self_pct": float(m.group("self")),
            })

    log(f"  {len(result['hotspots'])} hotspots found")
    log(f"  perf.data: {perf_data}")
    log("  Done.")
    return result


def main() -> None:
    if len(sys.argv) < 3:
        print(f"Usage: {sys.argv[0]} <base-dir> <workload> [workload ...]", file=sys.stderr)
        sys.exit(1)

    base_dir = Path(sys.argv[1])
    workloads = sys.argv[2:]

    check_prereqs()

    results = []
    for workload in workloads:
        results.append(profile_workload(base_dir, workload))

    log("=== Profile round complete ===")
    json.dump(results, sys.stdout, indent=2)
    print()


if __name__ == "__main__":
    main()
