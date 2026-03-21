#!/usr/bin/env bash
# clean_rel.sh - Remove generated _rel.c translation output files
#
# Usage:
#   scripts/clean_rel.sh
#     Clean generated rel files for the configured C_DIR in CONFIGURE.
#
#   scripts/clean_rel.sh --REL_DIR=./output/shape/rel/sll
#     Clean all *_rel.c files under a specific rel output directory.
#
#   scripts/clean_rel.sh --FILE=./shape_invdataset/sll/sll_copy.c
#     Clean the generated rel file for one source file.
#
#   scripts/clean_rel.sh --C_DIR=./shape_invdataset/sll
#     Clean generated rel files for every *.c file in the source directory.
#
#   scripts/clean_rel.sh --ALL
#     Clean all *_rel.c files under REL_DIR recursively.
#
# Notes:
#   - FILE/C_DIR modes remove files by matching source basenames to *_rel.c.
#   - If REL_DIR is the rel root (default ./output/shape/rel), FILE/C_DIR
#     infer the generated subdirectory from the source file/directory basename.
set -u

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
CONFIG_FILE="$REPO_ROOT/CONFIGURE"
[ -f "$CONFIG_FILE" ] || { echo "CONFIGURE file not found: $CONFIG_FILE"; exit 1; }

# Load defaults from CONFIGURE. Existing env vars still override via ${VAR:-...}.
source "$CONFIG_FILE"

DEFAULT_REL_ROOT="${REL_DIR:-./output/shape/rel}"
REL_DIR="${REL_DIR:-$DEFAULT_REL_ROOT}"
FILE_ARG="${FILE:-}"
C_DIR="${C_DIR:-}"
ALL_MODE=0
USE_FILE_MODE=0
USE_C_DIR_MODE=0

[ -n "$FILE_ARG" ] && USE_FILE_MODE=1

# --- Parse CLI overrides
for arg in "$@"; do
  case $arg in
    -REL_DIR=*|--REL_DIR=*) REL_DIR="${arg#*=}";;
    -FILE=*|--FILE=*) FILE_ARG="${arg#*=}"; USE_FILE_MODE=1;;
    -C_DIR=*|--C_DIR=*) C_DIR="${arg#*=}"; USE_C_DIR_MODE=1;;
    -ALL|--ALL) ALL_MODE=1;;
    *) echo "Unknown arg: $arg";;
  esac
done

abspath() {
  case "$1" in
    /*) printf '%s\n' "$1" ;;
    *)  printf '%s\n' "$REPO_ROOT/$1" ;;
  esac
}

resolve_rel_dir_for_source() {
  local source_path="$1"
  local source_parent
  source_parent="$(basename "$(dirname "$source_path")")"

  if [ "$REL_DIR_ABS" = "$DEFAULT_REL_ROOT_ABS" ]; then
    printf '%s\n' "$REL_DIR_ABS/$source_parent"
  else
    printf '%s\n' "$REL_DIR_ABS"
  fi
}

remove_if_present() {
  local target="$1"
  if [ -f "$target" ]; then
    rm -f "$target"
    count=$((count + 1))
  fi
}

remove_for_name_in_dir() {
  local name="$1"
  local rel_dir="$2"
  local base="$name"

  case "$base" in
    *_rel.c) ;;
    *.c) base="${base%.c}_rel.c" ;;
    *) base="${base}_rel.c" ;;
  esac

  remove_if_present "$rel_dir/$base"
}

REL_DIR_ABS="$(abspath "$REL_DIR")"
DEFAULT_REL_ROOT_ABS="$(abspath "$DEFAULT_REL_ROOT")"

count=0

if [ $USE_FILE_MODE -eq 1 ] && [ $USE_C_DIR_MODE -eq 1 ]; then
  echo "Please provide only one of FILE or C_DIR."
  exit 1
fi

if [ $ALL_MODE -eq 1 ] && { [ $USE_FILE_MODE -eq 1 ] || [ $USE_C_DIR_MODE -eq 1 ]; }; then
  echo "Please use ALL by itself or with REL_DIR only."
  exit 1
fi

if [ $USE_FILE_MODE -eq 1 ]; then
  if [ -f "$(abspath "$FILE_ARG")" ]; then
    file_abs="$(abspath "$FILE_ARG")"
    rel_dir="$(resolve_rel_dir_for_source "$file_abs")"
    remove_for_name_in_dir "$(basename "$file_abs")" "$rel_dir"
    echo "Removed $count _rel.c file(s) for FILE=$FILE_ARG from $rel_dir"
  else
    [ -d "$REL_DIR_ABS" ] || { echo "Directory not found: $REL_DIR_ABS"; exit 1; }
    remove_for_name_in_dir "$(basename "$FILE_ARG")" "$REL_DIR_ABS"
    echo "Removed $count _rel.c file(s) for FILE=$FILE_ARG from $REL_DIR_ABS"
  fi
  exit 0
fi

if [ $ALL_MODE -eq 1 ]; then
  [ -d "$REL_DIR_ABS" ] || { echo "Directory not found: $REL_DIR_ABS"; exit 1; }
  while IFS= read -r -d '' f; do
    rm -f "$f"
    count=$((count + 1))
  done < <(find "$REL_DIR_ABS" -name '*_rel.c' -print0)

  echo "Removed $count _rel.c files from $REL_DIR_ABS"
  exit 0
fi

if [ $USE_C_DIR_MODE -eq 1 ]; then
  C_DIR_ABS="$(abspath "$C_DIR")"
  [ -d "$C_DIR_ABS" ] || { echo "C_DIR not a directory: $C_DIR_ABS"; exit 1; }

  if [ "$REL_DIR_ABS" = "$DEFAULT_REL_ROOT_ABS" ]; then
    TARGET_REL_DIR="$REL_DIR_ABS/$(basename "$C_DIR_ABS")"
  else
    TARGET_REL_DIR="$REL_DIR_ABS"
  fi

  shopt -s nullglob
  FILES=("$C_DIR_ABS"/*.c)
  shopt -u nullglob

  for f in "${FILES[@]}"; do
    remove_for_name_in_dir "$(basename "$f")" "$TARGET_REL_DIR"
  done

  echo "Removed $count _rel.c file(s) for C_DIR=$C_DIR_ABS from $TARGET_REL_DIR"
  exit 0
fi

[ -n "$C_DIR" ] || { echo "C_DIR not set"; exit 1; }
[ -d "$(abspath "$C_DIR")" ] || { echo "C_DIR not a directory: $(abspath "$C_DIR")"; exit 1; }
C_DIR_ABS="$(abspath "$C_DIR")"

if [ "$REL_DIR_ABS" = "$DEFAULT_REL_ROOT_ABS" ]; then
  TARGET_REL_DIR="$REL_DIR_ABS/$(basename "$C_DIR_ABS")"
else
  TARGET_REL_DIR="$REL_DIR_ABS"
fi

shopt -s nullglob
FILES=("$C_DIR_ABS"/*.c)
shopt -u nullglob

for f in "${FILES[@]}"; do
  remove_for_name_in_dir "$(basename "$f")" "$TARGET_REL_DIR"
done

echo "Removed $count _rel.c file(s) for configured C_DIR=$C_DIR_ABS from $TARGET_REL_DIR"
exit 0
