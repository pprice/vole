#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  just agent start-worktree <name> [--agent <claude|codex>] [prompt...]
  just agent start-worktree <name> [--agent <claude|codex>] --prompt-file <path>

Behavior:
  1) Ensures worktree exists at .worktrees/<name> (creates if missing)
  2) Ensures .ticket symlink is present in the worktree
  3) Starts an agent in that worktree with initial prompt

Agent:
  - Optional --agent flag; defaults to claude
  - Allowed values: claude, codex

Prompt:
  - Provide either:
    a) positional prompt text (all remaining args), or
    b) --prompt-file <path>
  - If positional prompt text begins with `-`, use `--` before the prompt.
EOF
}

name="${1:-}"
if [[ -z "${name}" ]]; then
  usage
  exit 1
fi
shift

agent="claude"
prompt_file=""
prompt_text=""
prompt_args=()
parsing_options=1

while [[ $# -gt 0 ]]; do
  if [[ "${parsing_options}" -eq 1 ]]; then
    case "${1}" in
      --)
        parsing_options=0
        shift
        continue
        ;;
      --agent)
        if [[ $# -lt 2 ]]; then
          echo "ERROR: --agent requires a value (claude|codex)" >&2
          exit 1
        fi
        agent="${2}"
        shift 2
        continue
        ;;
      --prompt-file)
        if [[ $# -lt 2 ]]; then
          echo "ERROR: --prompt-file requires a path argument" >&2
          exit 1
        fi
        prompt_file="${2}"
        shift 2
        continue
        ;;
      *)
        parsing_options=0
        ;;
    esac
  fi

  prompt_args+=("${1}")
  shift
done

if [[ "${#prompt_args[@]}" -gt 0 ]]; then
  prompt_text="${prompt_args[*]}"
fi

case "${agent}" in
  codex|claude) ;;
  *)
    echo "ERROR: unknown agent '${agent}' (expected: codex|claude)" >&2
    exit 1
    ;;
esac

if ! command -v "${agent}" >/dev/null 2>&1; then
  echo "ERROR: requested agent not found in PATH: ${agent}" >&2
  exit 1
fi

if [[ -n "${prompt_file}" && -n "${prompt_text}" ]]; then
  echo "ERROR: provide either positional prompt text or --prompt-file, not both" >&2
  exit 1
fi

if [[ -n "${prompt_file}" ]]; then
  if [[ ! -f "${prompt_file}" ]]; then
    echo "ERROR: prompt file not found: ${prompt_file}" >&2
    exit 1
  fi
  prompt_contents="$(<"${prompt_file}")"
  prompt_source="${prompt_file}"
else
  if [[ -z "${prompt_text}" ]]; then
    echo "ERROR: missing prompt (provide positional prompt text or --prompt-file <path>)" >&2
    exit 1
  fi
  prompt_contents="${prompt_text}"
  prompt_source="<positional>"
fi

repo_root="$(git rev-parse --show-toplevel)"
cd "${repo_root}"

# Ensure the target worktree exists and has .ticket linked.
bash "just/scripts/agents/worktree.sh" --ensure "${name}" >/dev/null
worktree_dir="${repo_root}/.worktrees/${name}"

if [[ ! -d "${worktree_dir}" ]]; then
  echo "ERROR: expected worktree directory missing: ${worktree_dir}" >&2
  exit 1
fi

echo "Starting ${agent} in ${worktree_dir}"
echo "Prompt source: ${prompt_source}"

if [[ "${agent}" == "codex" ]]; then
  exec codex -C "${worktree_dir}" "${prompt_contents}"
fi

cd "${worktree_dir}"
exec claude "${prompt_contents}"
