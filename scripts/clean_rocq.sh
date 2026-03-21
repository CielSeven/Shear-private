#!/usr/bin/env bash
# clean_rocq.sh - Remove Rocq compilation artifacts (.vo, .vok, .vos, .glob)
#                 from the COQ_LIB_DIR directory
#
# Usage:
#   scripts/clean_rocq.sh                                    # clean default COQ_LIB_DIR
#   scripts/clean_rocq.sh --COQ_LIB_DIR=/path/to/lib        # clean specific dir
set -u

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CONFIG_FILE="$REPO_ROOT/CONFIGURE"
[ -f "$CONFIG_FILE" ] || { echo "❌ CONFIGURE file not found: $CONFIG_FILE"; exit 1; }

# --- Load defaults from CONFIGURE
source "$CONFIG_FILE"

# --- Parse CLI overrides
for arg in "$@"; do
  case $arg in
    -COQ_LIB_DIR=*|--COQ_LIB_DIR=*) COQ_LIB_DIR="${arg#*=}";;
    *) echo "⚠️  Unknown arg: $arg";;
  esac
done

[ -n "${COQ_LIB_DIR:-}" ] || { echo "❌ COQ_LIB_DIR not set"; exit 1; }
[ -d "$COQ_LIB_DIR" ] || { echo "❌ Directory not found: $COQ_LIB_DIR"; exit 1; }

count=0
while IFS= read -r -d '' f; do
  rm -f "$f"
  count=$((count + 1))
done < <(find "$COQ_LIB_DIR" -maxdepth 1 \( -name '*.vo' -o -name '*.vok' -o -name '*.vos' -o -name '*.glob' \) -print0)

echo "Removed $count Rocq artifact(s) from $COQ_LIB_DIR"
