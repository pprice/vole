#!/usr/bin/env bash
# Bump the workspace CalVer version: YYYY.M.{incremental}
# Same year+month → increment patch; new month → reset to 0
# Generates RELEASE_NOTES.md from categorized commit log
set -euo pipefail

CARGO_TOML="Cargo.toml"
NOTES="RELEASE_NOTES.md"

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
prev_tag=$(git tag --sort=-version:refname | grep '^v' | head -1)
if [ -z "$prev_tag" ]; then
    range="HEAD~20..HEAD"
else
    range="${prev_tag}..HEAD"
fi

declare -a features=() fixes=() tests=() docs=() perf=() refactor=() chores=() other=()

while IFS= read -r line; do
    msg="${line#* }"  # strip hash prefix
    case "$msg" in
        feat*)    features+=("$line") ;;
        fix*)     fixes+=("$line") ;;
        test*)    tests+=("$line") ;;
        doc*)     docs+=("$line") ;;
        perf*)    perf+=("$line") ;;
        refactor*) refactor+=("$line") ;;
        chore*|build*|ci*) chores+=("$line") ;;
        *)        other+=("$line") ;;
    esac
done < <(git log --pretty=format:"%h %s" "$range" --no-merges 2>/dev/null)

{
    echo "## Vole ${new_version}"
    echo ""

    print_section() {
        local title="$1"; shift
        local items=("$@")
        if [ ${#items[@]} -gt 0 ]; then
            echo "### ${title}"
            for item in "${items[@]}"; do
                echo "- ${item}"
            done
            echo ""
        fi
    }

    print_section "Features"      "${features[@]+"${features[@]}"}"
    print_section "Bug Fixes"     "${fixes[@]+"${fixes[@]}"}"
    print_section "Performance"   "${perf[@]+"${perf[@]}"}"
    print_section "Tests"         "${tests[@]+"${tests[@]}"}"
    print_section "Documentation" "${docs[@]+"${docs[@]}"}"
    print_section "Refactoring"   "${refactor[@]+"${refactor[@]}"}"
    print_section "Chores"        "${chores[@]+"${chores[@]}"}"
    print_section "Other"         "${other[@]+"${other[@]}"}"
} > "$NOTES"

echo "Release notes written to ${NOTES}"
