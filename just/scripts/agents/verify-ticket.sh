#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage:
  just agent verify-ticket <ticket-id>

Behavior:
  1) Resolves worktree path: .worktrees/<ticket-id>
  2) Runs `just ci` in that worktree
  3) Prints pass/fail summary
USAGE
}

ticket_id="${1:-}"
if [[ -z "${ticket_id}" ]]; then
  usage
  exit 1
fi

repo_root="$(git rev-parse --show-toplevel)"
worktree_dir="${repo_root}/.worktrees/${ticket_id}"

if [[ ! -d "${worktree_dir}" ]]; then
  echo "ERROR: worktree not found: ${worktree_dir}" >&2
  exit 1
fi

echo "Verifying ticket ${ticket_id} in ${worktree_dir}"
if (cd "${worktree_dir}" && just ci); then
  echo "VERIFY PASS: ${ticket_id}"
  exit 0
fi

echo "VERIFY FAIL: ${ticket_id}" >&2
exit 1
