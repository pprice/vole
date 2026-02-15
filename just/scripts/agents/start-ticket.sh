#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage:
  just agent start-ticket <ticket-id> [--agent <claude|codex>]

Behavior:
  1) Delegates to start-worktree
  2) Uses a standard bootstrap prompt for ticket implementation

Notes:
  - Worktree name is derived from ticket-id.
USAGE
}

ticket_id="${1:-}"
if [[ -z "${ticket_id}" ]]; then
  usage
  exit 1
fi
shift

agent="claude"
while [[ $# -gt 0 ]]; do
  case "${1}" in
    --agent)
      if [[ $# -lt 2 ]]; then
        echo "ERROR: --agent requires a value (claude|codex)" >&2
        exit 1
      fi
      agent="${2}"
      shift 2
      ;;
    *)
      echo "ERROR: unknown argument: ${1}" >&2
      usage
      exit 1
      ;;
  esac
done

if ! command -v tk >/dev/null 2>&1; then
  echo "ERROR: tk not found in PATH" >&2
  exit 1
fi

if ! tk show "${ticket_id}" >/dev/null 2>&1; then
  echo "ERROR: ticket not found: ${ticket_id}" >&2
  exit 1
fi

name="${ticket_id}"

merge_cmd="just agent merge-worktree ${name}"
prompt="You are in the worktree ${name}. Implement the tickets in ${ticket_id}, commit each ticket as you go, when you are complete, merge the work tree with ${merge_cmd}, and exit"

prompt_file="$(mktemp /tmp/vole-agent-prompt.XXXXXX)"
trap 'rm -f "${prompt_file}"' EXIT
printf '%s' "${prompt}" > "${prompt_file}"

bash "just/scripts/agents/start-worktree.sh" "${name}" --agent "${agent}" --prompt-file "${prompt_file}"
