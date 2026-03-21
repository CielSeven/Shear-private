#!/bin/bash
# check_rocq.sh — Check generated _rel_lib.v files for Rocq syntax errors
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CONFIG_FILE="$REPO_ROOT/CONFIGURE"
[ -f "$CONFIG_FILE" ] || { echo "❌ CONFIGURE file not found: $CONFIG_FILE"; exit 1; }

# --- Load defaults from CONFIGURE
source "$CONFIG_FILE"

# --- Parse CLI overrides
FILE_ARG=""
for arg in "$@"; do
  case $arg in
    -COQ_LIB_DIR=*|--COQ_LIB_DIR=*) COQ_LIB_DIR="${arg#*=}";;
    -FILE=*|--FILE=*)                FILE_ARG="${arg#*=}";;
    *) echo "⚠️  Unknown arg: $arg";;
  esac
done

[ -n "${COQ_LIB_DIR:-}" ] || { echo "❌ COQ_LIB_DIR not set"; exit 1; }

case "$COQ_LIB_DIR" in
  /*) COQ_LIB_DIR_ABS="$COQ_LIB_DIR" ;;
  *)  COQ_LIB_DIR_ABS="$REPO_ROOT/$COQ_LIB_DIR" ;;
esac

# --- Resolve the Rocq project root (where _CoqProject lives)
# Walk up from COQ_LIB_DIR to find _CoqProject
find_coq_project() {
  local dir="$1"
  while [ "$dir" != "/" ]; do
    if [ -f "$dir/_CoqProject" ]; then
      echo "$dir"
      return 0
    fi
    dir="$(dirname "$dir")"
  done
  return 1
}

COQ_PROJECT_ROOT="$(find_coq_project "$COQ_LIB_DIR_ABS")" || {
  echo "❌ _CoqProject not found in any parent of $COQ_LIB_DIR_ABS"
  exit 1
}

# --- Parse _CoqProject into coqc flags
COQ_FLAGS=()
while IFS= read -r line; do
  # Skip empty lines and comments
  [[ -z "$line" || "$line" == \#* ]] && continue
  # Parse shell-like quoting so entries such as -Q dir "" survive intact.
  eval "set -- $line"
  for word in "$@"; do
    COQ_FLAGS+=("$word")
  done
done < "$COQ_PROJECT_ROOT/_CoqProject"

# --- Determine file list
if [ -n "$FILE_ARG" ]; then
  case "$FILE_ARG" in
    /*) file_abs="$FILE_ARG" ;;
    *)  file_abs="$REPO_ROOT/$FILE_ARG" ;;
  esac
  [ -f "$file_abs" ] || { echo "❌ FILE not found: $file_abs"; exit 1; }
  FILES=("$file_abs")
else
  shopt -s nullglob
  FILES=("$COQ_LIB_DIR_ABS"/*_rel_lib.v)
  shopt -u nullglob
  [ ${#FILES[@]} -gt 0 ] || { echo "❌ No *_rel_lib.v files found in $COQ_LIB_DIR_ABS"; exit 1; }
fi

echo "🔧 Checking ${#FILES[@]} file(s) with Rocq"
echo "   Project root: $COQ_PROJECT_ROOT"
echo

# --- Compile each file
PASS=0
FAIL=0
FAILED_FILES=()

for f in "${FILES[@]}"; do
  base="$(basename "$f")"
  printf "  %-40s" "$base"

  output=$(cd "$COQ_PROJECT_ROOT" && coqc "${COQ_FLAGS[@]}" "$f" 2>&1)
  if [ $? -eq 0 ]; then
    echo "✅"
    PASS=$((PASS + 1))
  else
    echo "❌"
    echo "$output" | sed 's/^/    /'
    FAIL=$((FAIL + 1))
    FAILED_FILES+=("$base")
  fi
done

# --- Summary
echo
TOTAL=$((PASS + FAIL))
if [ $FAIL -eq 0 ]; then
  echo "✅ All $TOTAL file(s) passed Rocq syntax check."
else
  echo "❌ $FAIL/$TOTAL file(s) failed:"
  for ff in "${FAILED_FILES[@]}"; do
    echo "   - $ff"
  done
  exit 1
fi
