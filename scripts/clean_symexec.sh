#!/bin/bash
# clean_symexec.sh — Remove generated output and logs matching C_DIR files
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CONFIG_FILE="$REPO_ROOT/CONFIGURE"
[ -f "$CONFIG_FILE" ] || { echo "CONFIGURE file not found: $CONFIG_FILE"; exit 1; }

source "$CONFIG_FILE"
START_DIR="$REPO_ROOT"

# --- Parse CLI overrides
for arg in "$@"; do
  case $arg in
    -C_DIR=*|--C_DIR=*)         C_DIR="${arg#*=}";;
    -LOGDIR=*|--LOGDIR=*)       LOGDIR="${arg#*=}";;
    -OUTPUT_PATH=*|--OUTPUT_PATH=*) OUTPUT_PATH="${arg#*=}";;
    *) echo "Unknown arg: $arg";;
  esac
done

abspath() {
  case "$1" in
    /*) printf '%s\n' "$1" ;;
    *)  printf '%s\n' "$START_DIR/$1" ;;
  esac
}

C_DIR_ABS="$(abspath "$C_DIR")"
LOGDIR_ABS="$(abspath "$LOGDIR")"
OUTPUT_ABS="$(abspath "$OUTPUT_PATH")"

[ -d "$C_DIR_ABS" ] || { echo "C_DIR not a directory: $C_DIR_ABS"; exit 1; }

count=0
for f in "$C_DIR_ABS"/*.c; do
  [ -f "$f" ] || continue
  base="$(basename "${f%.c}")"
  for target in \
    "$LOGDIR_ABS/${base}_log.txt" \
    "$OUTPUT_ABS/${base}_goal.v" \
    "$OUTPUT_ABS/${base}_auto.v" \
    "$OUTPUT_ABS/${base}_manual.v" \
    "$OUTPUT_ABS/${base}_goal_check.v"; do
    if [ -f "$target" ]; then
      rm -f "$target"
      count=$((count + 1))
    fi
  done
done

echo "Removed $count files for C_DIR=$C_DIR_ABS"
