#!/usr/bin/env bash
# Generate release notes for a commit range using Claude.
# Usage: release-notes.sh [range]
#   range defaults to <last-tag>..HEAD
set -euo pipefail

PROMPT_FILE=".claude/prompts/release-notes.md"

if [ ! -f "$PROMPT_FILE" ]; then
    echo "error: $PROMPT_FILE not found" >&2
    exit 1
fi

# Determine range
if [ $# -ge 1 ]; then
    range="$1"
else
    prev_tag=$(git tag --sort=-version:refname | grep '^v' | head -1 || true)
    if [ -z "$prev_tag" ]; then
        range="HEAD~20..HEAD"
    else
        range="${prev_tag}..HEAD"
    fi
    echo "Range: ${range}" >&2
fi

commits=$(git log --pretty=format:"%s" "$range" --no-merges)

if [ -z "$commits" ]; then
    echo "No commits in range ${range}" >&2
    exit 0
fi

prompt=$(cat "$PROMPT_FILE")

echo "$commits" | CLAUDECODE= claude --print -p "$prompt"
