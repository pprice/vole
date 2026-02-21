#!/usr/bin/env bash
# Bump CalVer version, generate release notes, commit.
# Version format: YYYY.M.{incremental} (resets to .0 on month rollover)
set -euo pipefail

CARGO_TOML="Cargo.toml"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

# --- Bump version ---
current=$(grep -m1 '^version = ' "$CARGO_TOML" | sed 's/version = "\(.*\)"/\1/')
IFS='.' read -r cur_year cur_month cur_patch <<< "$current"

now_year=$(date +%Y)
now_month=$(date +%-m)

if [[ "$cur_year" == "$now_year" && "$cur_month" == "$now_month" ]]; then
    new_patch=$((cur_patch + 1))
else
    new_patch=0
fi

new_version="${now_year}.${now_month}.${new_patch}"
sed -i "s/^version = \"${current}\"/version = \"${new_version}\"/" "$CARGO_TOML"
echo "${current} -> ${new_version}"

# --- Generate release notes ---
echo "Generating release notes..." >&2
notes=$("$SCRIPT_DIR/release-notes.sh")

if [ -z "$notes" ]; then
    notes="Release ${new_version}"
fi

echo ""
echo "$notes"
echo ""

# --- Commit ---
git add "$CARGO_TOML"
git commit -m "$(cat <<EOF
release: Vole ${new_version}

<RELEASE-NOTES>
${notes}
</RELEASE-NOTES>
EOF
)"

echo "---"
echo "Committed. Push to trigger tag + release build."
