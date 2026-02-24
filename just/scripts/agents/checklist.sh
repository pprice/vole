#!/usr/bin/env bash
# Usage: checklist.sh <EnumName>
# Finds all files referencing an enum's variants and classifies by role.

set -euo pipefail

enum_name="${1:-}"

if [[ -z "$enum_name" ]]; then
  echo "Usage: just agent checklist <EnumName>"
  echo ""
  echo "Examples:"
  echo "  just agent checklist VirExpr"
  echo "  just agent checklist VirStmt"
  echo "  just agent checklist CallTarget"
  exit 1
fi

# Find all Rust files referencing this enum's variants
mapfile -t files < <(rg -l "${enum_name}::" src/crates/ --type rust 2>/dev/null | sort)

if [[ ${#files[@]} -eq 0 ]]; then
  echo "No files reference ${enum_name}::"
  exit 0
fi

total=${#files[@]}

# Classify files by directory into roles
declare -a definition=()
declare -a lowering=()
declare -a codegen=()
declare -a builder=()
declare -a printer=()
declare -a cache=()
declare -a tests=()
declare -a other=()

for f in "${files[@]}"; do
  case "$f" in
    */vole-vir/src/lower/tests/*) tests+=("$f") ;;
    */vole-vir/src/lower/*)       lowering+=("$f") ;;
    */vole-vir/src/builder.rs)    builder+=("$f") ;;
    */vole-vir/src/printer*)      printer+=("$f") ;;
    */vole-vir/src/cache/*)       cache+=("$f") ;;
    */vole-vir/src/*.rs)          definition+=("$f") ;;
    */vole-codegen/src/cache/*)   cache+=("$f") ;;
    */vole-codegen/src/*)         codegen+=("$f") ;;
    */tests/*)                    tests+=("$f") ;;
    *)                            other+=("$f") ;;
  esac
done

echo "${enum_name} — ${total} files"
echo ""

print_section() {
  local label="$1"
  shift
  local files=("$@")
  if [[ ${#files[@]} -gt 0 ]]; then
    echo "${label}:"
    for f in "${files[@]}"; do
      # Count references in this file
      count=$(rg -c "${enum_name}::" "$f" 2>/dev/null || echo "0")
      echo "  ${f}  (${count} refs)"
    done
    echo ""
  fi
}

print_section "DEFINITION" "${definition[@]+"${definition[@]}"}"
print_section "LOWERING (AST → VIR)" "${lowering[@]+"${lowering[@]}"}"
print_section "CODEGEN (VIR → Cranelift)" "${codegen[@]+"${codegen[@]}"}"
print_section "BUILDER" "${builder[@]+"${builder[@]}"}"
print_section "PRINTER" "${printer[@]+"${printer[@]}"}"
print_section "CACHE (remap/serialize)" "${cache[@]+"${cache[@]}"}"
print_section "TESTS" "${tests[@]+"${tests[@]}"}"
print_section "OTHER" "${other[@]+"${other[@]}"}"

# Check for clippy enforcement
echo "CLIPPY ENFORCEMENT:"
enforced=0
for f in "${codegen[@]+"${codegen[@]}"}"; do
  if [[ -n "$f" ]] && grep -q "deny.*wildcard_enum_match_arm" "$f" 2>/dev/null; then
    echo "  ✓ ${f}"
    enforced=$((enforced + 1))
  fi
done
if [[ $enforced -eq 0 ]]; then
  echo "  (none — see vol-veky)"
fi
