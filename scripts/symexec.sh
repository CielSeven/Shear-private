#!/bin/bash
# symexec.sh — CONFIGURE + CLI overrides + OUTPUT_PATH for generated V files
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CONFIG_FILE="$REPO_ROOT/CONFIGURE"
[ -f "$CONFIG_FILE" ] || { echo "❌ CONFIGURE file not found: $CONFIG_FILE"; exit 1; }

# --- Load defaults from CONFIGURE (KEY=value)
source "$CONFIG_FILE"

# Backward compatibility for older CONFIGURE files.
if [ -z "${SYMEXEC_INCLUDE_DIRS:-}" ] && [ -n "${SYMEXEC_HEADER_DIR:-}" ]; then
  SYMEXEC_INCLUDE_DIRS="$SYMEXEC_HEADER_DIR"
fi

# --- Parse CLI overrides: support both - and -- prefix
FILE_ARG=""
for arg in "$@"; do
  case $arg in
    -C_DIR=*|--C_DIR=*)         C_DIR="${arg#*=}";;
    -LOGDIR=*|--LOGDIR=*)       LOGDIR="${arg#*=}";;
    -SYMEXEC=*|--SYMEXEC=*)     SYMEXEC="${arg#*=}";;
    -SYMEXEC_INCLUDE_DIRS=*|--SYMEXEC_INCLUDE_DIRS=*) SYMEXEC_INCLUDE_DIRS="${arg#*=}";;
    -SYMEXEC_HEADER_DIR=*|--SYMEXEC_HEADER_DIR=*) SYMEXEC_INCLUDE_DIRS="${arg#*=}";;
    -OUTPUT_PATH=*|--OUTPUT_PATH=*) OUTPUT_PATH="${arg#*=}";;
    -FILE=*|--FILE=*)           FILE_ARG="${arg#*=}";;
    *) echo "⚠️  Unknown arg: $arg";;
  esac
done

# --- Sanity check
[ -n "${C_DIR:-}" ]       || { echo "❌ C_DIR not set"; exit 1; }
[ -n "${LOGDIR:-}" ]      || { echo "❌ LOGDIR not set"; exit 1; }
[ -n "${SYMEXEC:-}" ]     || { echo "❌ SYMEXEC not set"; exit 1; }
[ -n "${SYMEXEC_INCLUDE_DIRS:-}" ] || { echo "❌ SYMEXEC_INCLUDE_DIRS not set"; exit 1; }
[ -n "${OUTPUT_PATH:-}" ] || { echo "❌ OUTPUT_PATH not set"; exit 1; }

# --- Resolve relative paths against repo root
START_DIR="$REPO_ROOT"

abspath() {
  case "$1" in
    /*) printf '%s\n' "$1" ;;
    *)  printf '%s\n' "$START_DIR/$1" ;;
  esac
}

C_DIR_ABS="$(abspath "$C_DIR")"
LOGDIR_ABS="$(abspath "$LOGDIR")"
SYMEXEC_ABS="$(abspath "$SYMEXEC")"
OUTPUT_ABS="$(abspath "$OUTPUT_PATH")"

IFS=':' read -r -a SYMEXEC_INCLUDE_DIR_LIST <<< "$SYMEXEC_INCLUDE_DIRS"
INCLUDE_FLAGS=()
INCLUDE_DIRS_ABS=()
for include_dir in "${SYMEXEC_INCLUDE_DIR_LIST[@]}"; do
  [ -n "$include_dir" ] || continue
  include_dir_abs="$(abspath "$include_dir")"
  [ -d "$include_dir_abs" ] || { echo "❌ symexec include directory not found: $include_dir_abs"; exit 1; }
  INCLUDE_DIRS_ABS+=("$include_dir_abs")
  INCLUDE_FLAGS+=("-I$include_dir_abs")
done
[ "${#INCLUDE_FLAGS[@]}" -gt 0 ] || { echo "❌ No valid symexec include directories configured"; exit 1; }

mkdir -p "$LOGDIR_ABS" "$OUTPUT_ABS"
[ -x "$SYMEXEC_ABS" ] || { echo "❌ symexec executable not found: $SYMEXEC_ABS"; exit 1; }

shopt -s nullglob

# --- Determine file list: single file or all *.c
if [ -n "$FILE_ARG" ]; then
  file_abs="$(abspath "$FILE_ARG")"
  [ -f "$file_abs" ] || { echo "❌ FILE not found: $file_abs"; exit 1; }
  FILES=("$file_abs")
  cd "$(dirname "$file_abs")" || { echo "❌ Cannot enter $(dirname "$file_abs")"; exit 1; }
else
  [ -d "$C_DIR_ABS" ] || { echo "❌ C_DIR not a directory: $C_DIR_ABS"; exit 1; }
  echo "🔧 Using:"
  echo "  C_DIR        = $C_DIR_ABS"
  echo "  LOGDIR       = $LOGDIR_ABS"
  echo "  OUTPUT_PATH  = $OUTPUT_ABS"
  echo "  SYMEXEC      = $SYMEXEC_ABS"
  echo "  INCLUDE_DIRS = ${INCLUDE_DIRS_ABS[*]}"
  echo
  cd "$C_DIR_ABS" || { echo "❌ Cannot enter $C_DIR_ABS"; exit 1; }
  FILES=(*.c)
fi

for f in "${FILES[@]}"; do
  base="$(basename "${f%.c}")"
  log="$LOGDIR_ABS/${base}_log.txt"
  goal_out="$OUTPUT_ABS/${base}_goal.v"
  auto_out="$OUTPUT_ABS/${base}_auto.v"
  manual_out="$OUTPUT_ABS/${base}_manual.v"

  [ -z "$FILE_ARG" ] && echo ">>> Processing $f"
  {
    echo "== $(date '+%F %T') : $f =="
    "$SYMEXEC_ABS" \
      "${INCLUDE_FLAGS[@]}" \
      --input-file="$f" \
      --goal-file="$goal_out" \
      --proof-auto-file="$auto_out" \
      --proof-manual-file="$manual_out" \
      --basic-assertion \
      --user-info=2
    echo "exit code: $?"
  } > "$log" 2>&1 || true

  exit_line=$(tail -n 1 "$log" | grep -Eo '[0-9]+$' || echo "unknown")
  if [ "$exit_line" = "0" ]; then
    [ -n "$FILE_ARG" ] && echo "✅ $base succeeded" || echo "✅ $f succeeded (exit code 0)"
  else
    [ -n "$FILE_ARG" ] && echo "❌ $base failed (exit code $exit_line)" || echo "❌ $f failed (exit code $exit_line)"
  fi
  [ -z "$FILE_ARG" ] && echo
done

if [ -z "$FILE_ARG" ]; then
  echo "✅ All done."
  echo "   Logs   → $LOGDIR_ABS"
  echo "   Output → $OUTPUT_ABS"
fi
