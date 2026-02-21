#!/usr/bin/env bash
# Bump the workspace CalVer version: YYYY.M.{incremental}
# Same year+month → increment patch; new month → reset to 0
set -euo pipefail

CARGO_TOML="Cargo.toml"
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
