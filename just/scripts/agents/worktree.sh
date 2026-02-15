#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  just agent worktree <ticket-id>
  just agent worktree --ensure <ticket-id>

Creates a git worktree at .worktrees/<ticket-id> on branch ticket/<ticket-id>.
Then links <worktree>/.ticket -> <main-worktree>/.ticket (if present).
EOF
}

ensure=0
if [[ "${1:-}" == "--ensure" ]]; then
  ensure=1
  shift
fi

ticket_id="${1:-}"
if [[ -z "${ticket_id}" ]]; then
  usage
  exit 1
fi

if ! command -v tk >/dev/null 2>&1; then
  echo "ERROR: tk not found in PATH" >&2
  exit 1
fi

repo_root="$(git rev-parse --show-toplevel)"
cd "${repo_root}"

if ! tk show "${ticket_id}" >/dev/null 2>&1; then
  echo "ERROR: ticket not found: ${ticket_id}" >&2
  exit 1
fi

branch="ticket/${ticket_id}"
worktree_dir="${repo_root}/.worktrees/${ticket_id}"

main_worktree="$(
  git worktree list --porcelain | awk '
    $1=="worktree" { wt=$2 }
    $1=="branch" && $2=="refs/heads/main" { print wt; exit }
  '
)"

if [[ -z "${main_worktree}" ]]; then
  # Fallback to first listed worktree if no explicit main branch worktree exists.
  main_worktree="$(git worktree list --porcelain | awk '$1=="worktree" { print $2; exit }')"
fi

if [[ -z "${main_worktree}" ]]; then
  echo "ERROR: failed to locate a base worktree" >&2
  exit 1
fi

if [[ -e "${worktree_dir}" ]]; then
  if [[ "${ensure}" -eq 0 ]]; then
    echo "ERROR: worktree path already exists: ${worktree_dir}" >&2
    exit 1
  fi
else
  if git show-ref --verify --quiet "refs/heads/${branch}"; then
    git worktree add "${worktree_dir}" "${branch}"
  else
    if git show-ref --verify --quiet "refs/heads/main"; then
      git worktree add -b "${branch}" "${worktree_dir}" main
    else
      git worktree add -b "${branch}" "${worktree_dir}" HEAD
    fi
  fi
fi

src_ticket="${main_worktree}/.ticket"
dst_ticket="${worktree_dir}/.ticket"

if [[ -e "${dst_ticket}" || -L "${dst_ticket}" ]]; then
  rm -f "${dst_ticket}"
fi

if [[ -e "${src_ticket}" || -L "${src_ticket}" ]]; then
  ln -s "${src_ticket}" "${dst_ticket}"
  echo "Linked ${dst_ticket} -> ${src_ticket}"
else
  echo "WARNING: ${src_ticket} does not exist; skipping .ticket link" >&2
fi

echo "Created worktree:"
echo "  ticket:   ${ticket_id}"
echo "  branch:   ${branch}"
echo "  path:     ${worktree_dir}"
echo
echo "Next:"
echo "  cd ${worktree_dir}"
echo "WORKTREE_PATH=${worktree_dir}"
