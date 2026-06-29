#!/bin/bash
# symexec.sh — CONFIGURE + CLI overrides + OUTPUT_PATH for generated V files
#
# Usage:
#   scripts/symexec.sh
#     Run with defaults from CONFIGURE.
#
#   scripts/symexec.sh --FILE=./shape_invdataset/sll/sll_copy.c
#     Run symexec for one C file.
#
#   scripts/symexec.sh --clean
#     Remove generated symexec outputs and logs for configured C_DIR.
#
#   scripts/symexec.sh --clean --FILE=./shape_invdataset/sll/sll_copy.c
#     Remove generated symexec outputs and logs for one C file.
#
#   scripts/symexec.sh --FULL_AUTO=true
#     Append --full-auto when invoking symexec.
#
#   scripts/symexec.sh --full-auto
#     Alias for --FULL_AUTO=true.
#
#   scripts/symexec.sh --FULL_AUTO=false
#     Explicitly skip --full-auto, even if enabled via environment/config.
#
#   scripts/symexec.sh --FILE=... --AUTO_VC
#     Also pass --Auto-VC-Checking to the binary, writing each VC's
#     WitnessTrySolve steps + result to <AUTOVC_DIR>/<base>_autovc.c.
#     AUTOVC_DIR defaults to <input-dir>/autovc (single FILE) or
#     <C_DIR>/autovc (directory mode); override with --AUTOVC_DIR=<dir>.
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

SYMEXEC_FULL_AUTO="${SYMEXEC_FULL_AUTO:-0}"
AUTO_VC="${SYMEXEC_AUTO_VC:-0}"
AUTOVC_DIR="${AUTOVC_DIR:-}"

parse_bool() {
  case "$1" in
    1|true|TRUE|True|yes|YES|on|ON) printf '1\n' ;;
    0|false|FALSE|False|no|NO|off|OFF) printf '0\n' ;;
    *)
      echo "❌ Invalid boolean value: $1"
      echo "   Expected one of: true, false, 1, 0, yes, no, on, off"
      return 1
      ;;
  esac
}

# --- Parse CLI overrides: support both - and -- prefix
FILE_ARG=""
CLEAN_FLAG=0
for arg in "$@"; do
  case $arg in
    -C_DIR=*|--C_DIR=*)         C_DIR="${arg#*=}";;
    -LOGDIR=*|--LOGDIR=*)       LOGDIR="${arg#*=}";;
    -SYMEXEC=*|--SYMEXEC=*)     SYMEXEC="${arg#*=}";;
    -SYMEXEC_INCLUDE_DIRS=*|--SYMEXEC_INCLUDE_DIRS=*) SYMEXEC_INCLUDE_DIRS="${arg#*=}";;
    -SYMEXEC_HEADER_DIR=*|--SYMEXEC_HEADER_DIR=*) SYMEXEC_INCLUDE_DIRS="${arg#*=}";;
    -SYMEXEC_STRATEGY_PATHS=*|--SYMEXEC_STRATEGY_PATHS=*) SYMEXEC_STRATEGY_PATHS="${arg#*=}";;
    -OUTPUT_PATH=*|--OUTPUT_PATH=*) OUTPUT_PATH="${arg#*=}";;
    -FILE=*|--FILE=*)           FILE_ARG="${arg#*=}";;
    -CLEAN|--CLEAN|-clean|--clean|clean) CLEAN_FLAG=1;;
    -FULL_AUTO|--FULL_AUTO|-full-auto|--full-auto|full-auto|-SYMEXEC_FULL_AUTO|--SYMEXEC_FULL_AUTO) SYMEXEC_FULL_AUTO=1;;
    -NO_FULL_AUTO|--NO_FULL_AUTO|-NO_SYMEXEC_FULL_AUTO|--NO_SYMEXEC_FULL_AUTO) SYMEXEC_FULL_AUTO=0;;
    -AUTO_VC|--AUTO_VC|-auto-vc|--auto-vc|-Auto-VC-Checking|--Auto-VC-Checking) AUTO_VC=1;;
    -NO_AUTO_VC|--NO_AUTO_VC) AUTO_VC=0;;
    -AUTOVC_DIR=*|--AUTOVC_DIR=*) AUTOVC_DIR="${arg#*=}"; AUTO_VC=1;;
    -FULL_AUTO=*|--FULL_AUTO=*|-SYMEXEC_FULL_AUTO=*|--SYMEXEC_FULL_AUTO=*)
      parsed_full_auto="$(parse_bool "${arg#*=}")" || exit 1
      SYMEXEC_FULL_AUTO="$parsed_full_auto"
      ;;
    *) echo "⚠️  Unknown arg: $arg";;
  esac
done

# --- Sanity check
[ -n "${C_DIR:-}" ]       || { echo "❌ C_DIR not set"; exit 1; }
[ -n "${LOGDIR:-}" ]      || { echo "❌ LOGDIR not set"; exit 1; }
[ -n "${OUTPUT_PATH:-}" ] || { echo "❌ OUTPUT_PATH not set"; exit 1; }
if [ "$CLEAN_FLAG" != "1" ]; then
  [ -n "${SYMEXEC:-}" ]     || { echo "❌ SYMEXEC not set"; exit 1; }
  [ -n "${SYMEXEC_INCLUDE_DIRS:-}" ] || { echo "❌ SYMEXEC_INCLUDE_DIRS not set"; exit 1; }
fi

# --- Resolve relative paths against repo root
START_DIR="$REPO_ROOT"

abspath() {
  local input_path="$1"
  local target_path

  case "$input_path" in
    /*) target_path="$input_path" ;;
    *)  target_path="$START_DIR/${input_path#./}" ;;
  esac

  [ "$target_path" = "/" ] || target_path="${target_path%/}"
  printf '%s\n' "${target_path//\/.\//\/}"
}

C_DIR_ABS="$(abspath "$C_DIR")"
LOGDIR_ABS="$(abspath "$LOGDIR")"
OUTPUT_ABS="$(abspath "$OUTPUT_PATH")"

shopt -s nullglob

if [ "$CLEAN_FLAG" = "1" ]; then
  if [ -n "$FILE_ARG" ]; then
    file_abs="$(abspath "$FILE_ARG")"
    [ -f "$file_abs" ] || { echo "❌ FILE not found: $file_abs"; exit 1; }
    FILES=("$file_abs")
  else
    [ -d "$C_DIR_ABS" ] || { echo "❌ C_DIR not a directory: $C_DIR_ABS"; exit 1; }
    FILES=("$C_DIR_ABS"/*.c)
  fi

  if [ -n "$AUTOVC_DIR" ]; then
    clean_autovc_dir="$(abspath "$AUTOVC_DIR")"
  elif [ -n "$FILE_ARG" ]; then
    clean_autovc_dir="$(dirname "$(abspath "$FILE_ARG")")/autovc"
  else
    clean_autovc_dir="$C_DIR_ABS/autovc"
  fi

  count=0
  for f in "${FILES[@]}"; do
    [ -f "$f" ] || continue
    base="$(basename "${f%.c}")"
    for target in \
      "$LOGDIR_ABS/${base}_log.txt" \
      "$OUTPUT_ABS/${base}_goal.v" \
      "$OUTPUT_ABS/${base}_proof_auto.v" \
      "$OUTPUT_ABS/${base}_proof_manual.v" \
      "$OUTPUT_ABS/${base}_goal_check.v" \
      "$clean_autovc_dir/${base}_autovc.c"; do
      if [ -f "$target" ]; then
        rm -f "$target"
        count=$((count + 1))
      fi
    done
  done

  if [ -n "$FILE_ARG" ]; then
    echo "Removed $count files for FILE=$FILE_ARG"
  else
    echo "Removed $count files for C_DIR=$C_DIR_ABS"
  fi
  exit 0
fi

SYMEXEC_ABS="$(abspath "$SYMEXEC")"

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

SLP_FLAGS=()
STRATEGY_PATHS_DISPLAY=()
if [ -n "${SYMEXEC_STRATEGY_PATHS:-}" ]; then
  IFS=':' read -r -a SYMEXEC_STRATEGY_PATH_LIST <<< "$SYMEXEC_STRATEGY_PATHS"
  for strategy_entry in "${SYMEXEC_STRATEGY_PATH_LIST[@]}"; do
    [ -n "$strategy_entry" ] || continue

    case "$strategy_entry" in
      *,*)
        strategy_physical="${strategy_entry%%,*}"
        strategy_logic="${strategy_entry#*,}"
        ;;
      *)
        echo "❌ Invalid SYMEXEC_STRATEGY_PATHS entry: $strategy_entry"
        echo "   Expected format: /physical/path,Logic.Module"
        exit 1
        ;;
    esac

    if [ "$strategy_logic" = '""' ] || [ "$strategy_logic" = "''" ]; then
      strategy_logic=""
    fi

    strategy_physical_abs="$(abspath "$strategy_physical")"
    [ -d "$strategy_physical_abs" ] || { echo "❌ symexec strategy directory not found: $strategy_physical_abs"; exit 1; }

    if [ -n "$strategy_logic" ]; then
      STRATEGY_PATHS_DISPLAY+=("$strategy_physical_abs -> $strategy_logic")
    else
      STRATEGY_PATHS_DISPLAY+=("$strategy_physical_abs -> \"\"")
    fi
    SLP_FLAGS+=("-slp" "$strategy_physical_abs" "$strategy_logic")
  done
fi

FULL_AUTO_FLAGS=()
if [ "$SYMEXEC_FULL_AUTO" = "1" ]; then
  FULL_AUTO_FLAGS+=(--full-auto)
fi

mkdir -p "$LOGDIR_ABS" "$OUTPUT_ABS"
[ -x "$SYMEXEC_ABS" ] || { echo "❌ symexec executable not found: $SYMEXEC_ABS"; exit 1; }

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
  echo "  FULL_AUTO    = $([ "$SYMEXEC_FULL_AUTO" = "1" ] && echo true || echo false)"
  [ "${#STRATEGY_PATHS_DISPLAY[@]}" -gt 0 ] && echo "  STRATEGY_MAP = ${STRATEGY_PATHS_DISPLAY[*]}"
  echo
  cd "$C_DIR_ABS" || { echo "❌ Cannot enter $C_DIR_ABS"; exit 1; }
  FILES=(*.c)
fi

# --- Resolve the --Auto-VC-Checking output directory (per-file path built in the loop)
autovc_dir_abs=""
if [ "$AUTO_VC" = "1" ]; then
  if [ -n "$AUTOVC_DIR" ]; then
    autovc_dir_abs="$(abspath "$AUTOVC_DIR")"
  elif [ -n "$FILE_ARG" ]; then
    autovc_dir_abs="$(dirname "$file_abs")/autovc"
  else
    autovc_dir_abs="$C_DIR_ABS/autovc"
  fi
  mkdir -p "$autovc_dir_abs"
fi

for f in "${FILES[@]}"; do
  base="$(basename "${f%.c}")"
  log="$LOGDIR_ABS/${base}_log.txt"
  goal_out="$OUTPUT_ABS/${base}_goal.v"
  auto_out="$OUTPUT_ABS/${base}_proof_auto.v"
  manual_out="$OUTPUT_ABS/${base}_proof_manual.v"
  symexec_cmd=("$SYMEXEC_ABS" "${INCLUDE_FLAGS[@]}")

  if [ "${#SLP_FLAGS[@]}" -gt 0 ]; then
    symexec_cmd+=("${SLP_FLAGS[@]}")
  fi

  if [ "${#FULL_AUTO_FLAGS[@]}" -gt 0 ]; then
    symexec_cmd+=("${FULL_AUTO_FLAGS[@]}")
  fi

  if [ "$AUTO_VC" = "1" ]; then
    symexec_cmd+=(--Auto-VC-Checking "$autovc_dir_abs/${base}_autovc.c")
  fi

  symexec_cmd+=(
    --input-file="$f"
    --goal-file="$goal_out"
    --proof-auto-file="$auto_out"
    --proof-manual-file="$manual_out"
    # --user-info=2
  )

  # --basic-assertion is incompatible with --Auto-VC-Checking; omit it then.
  # if [ "$AUTO_VC" != "1" ]; then
  #   symexec_cmd+=(--basic-assertion)
  # fi

  [ -z "$FILE_ARG" ] && echo ">>> Processing $f"
  {
    echo "== $(date '+%F %T') : $f =="
    "${symexec_cmd[@]}"
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

exit 0
