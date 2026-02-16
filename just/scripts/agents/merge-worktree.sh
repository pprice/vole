#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage:
  just agent merge-worktree <name>

Behavior:
  1) Resolves worktree path: .worktrees/<name>
  2) Runs `just ci` in that worktree (hard gate)
  3) Merges the worktree branch into `main` in the main worktree
EOF
}

name="${1:-}"
if [[ -z "${name}" ]]; then
  usage
  exit 1
fi

repo_root="$(git rev-parse --show-toplevel)"
worktree_dir="${repo_root}/.worktrees/${name}"

if [[ ! -d "${worktree_dir}" ]]; then
  echo "ERROR: worktree not found: ${worktree_dir}" >&2
  exit 1
fi

branch="$(git -C "${worktree_dir}" rev-parse --abbrev-ref HEAD)"
if [[ -z "${branch}" || "${branch}" == "HEAD" ]]; then
  echo "ERROR: could not resolve branch for worktree: ${worktree_dir}" >&2
  exit 1
fi

if [[ "${branch}" == "main" ]]; then
  echo "ERROR: refusing to merge branch 'main' from worktree ${worktree_dir}" >&2
  exit 1
fi

main_worktree="$(
  git worktree list --porcelain | awk '
    $1=="worktree" { wt=$2 }
    $1=="branch" && $2=="refs/heads/main" { print wt; exit }
  '
)"

if [[ -z "${main_worktree}" ]]; then
  echo "ERROR: could not locate worktree for branch main" >&2
  exit 1
fi

if [[ -n "$(git -C "${main_worktree}" status --porcelain)" ]]; then
  echo "ERROR: main worktree has uncommitted changes: ${main_worktree}" >&2
  echo "Please commit/stash there before merge-worktree." >&2
  exit 1
fi

echo "Running CI gate in worktree: ${worktree_dir}"
(cd "${worktree_dir}" && just ci)

echo "CI passed. Merging ${branch} -> main in ${main_worktree}"
git -C "${main_worktree}" checkout main
git -C "${main_worktree}" merge --no-ff --no-edit "${branch}"

echo "Merge complete."
echo "  source worktree: ${worktree_dir}"
echo "  source branch:   ${branch}"
echo "  target branch:   main"
