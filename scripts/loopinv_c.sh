#!/bin/bash
# loopinv_c.sh — CONFIGURE + CLI overrides + OUTPUT_PATH for generated V files
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CONFIG_FILE="$REPO_ROOT/CONFIGURE"
[ -f "$CONFIG_FILE" ] || { echo "❌ CONFIGURE file not found: $CONFIG_FILE"; exit 1; }

# --- Load defaults from CONFIGURE (KEY=value)
source "$CONFIG_FILE"

# --- Parse CLI overrides: support both - and -- prefix
for arg in "$@"; do
  case $arg in
    -C_DIR=*|--C_DIR=*)         C_DIR="${arg#*=}";;
    -LOGDIR=*|--LOGDIR=*)       LOGDIR="${arg#*=}";;
    -LOOPINV=*|--LOOPINV=*)     LOOPINV="${arg#*=}";;
    -OUTPUT_PATH=*|--OUTPUT_PATH=*) OUTPUT_PATH="${arg#*=}";;
    *) echo "⚠️  Unknown arg: $arg";;
  esac
done

# --- Sanity check
[ -n "${C_DIR:-}" ]       || { echo "❌ C_DIR not set"; exit 1; }
[ -n "${LOGDIR:-}" ]      || { echo "❌ LOGDIR not set"; exit 1; }
[ -n "${LOOPINV:-}" ]     || { echo "❌ LOOPINV not set"; exit 1; }
OUTPUT_PATH="${OUTPUT_PATH:-$LOGDIR}"   # default: same as LOGDIR

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
LOOPINV_ABS="$(abspath "$LOOPINV")"
OUTPUT_ABS="$(abspath "$OUTPUT_PATH")"

mkdir -p "$LOGDIR_ABS" "$OUTPUT_ABS"
[ -d "$C_DIR_ABS" ] || { echo "❌ C_DIR not a directory: $C_DIR_ABS"; exit 1; }
[ -x "$LOOPINV_ABS" ] || { echo "❌ loopinv executable not found: $LOOPINV_ABS"; exit 1; }

echo "🔧 Using:"
echo "  C_DIR        = $C_DIR_ABS"
echo "  LOGDIR       = $LOGDIR_ABS"
echo "  OUTPUT_PATH  = $OUTPUT_ABS"
echo "  LOOPINV      = $LOOPINV_ABS"
echo

cd "$C_DIR_ABS" || { echo "❌ Cannot enter $C_DIR_ABS"; exit 1; }

shopt -s nullglob

for f in *.c; do
  base="${f%.c}"
  log="$LOGDIR_ABS/${base}_log.txt"
  goal_out="$OUTPUT_ABS/${base}_goal.v"
  auto_out="$OUTPUT_ABS/${base}_auto.v"
  manual_out="$OUTPUT_ABS/${base}_manual.v"

  echo ">>> Processing $f"
  {
    echo "== $(date '+%F %T') : $f =="
    "$LOOPINV_ABS" \
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
    echo "✅ $f succeeded (exit code 0)"
  else
    echo "❌ $f failed (exit code $exit_line)"
  fi
  echo
done

echo "✅ All done."
echo "   Logs   → $LOGDIR_ABS"
echo "   Output → $OUTPUT_ABS"
