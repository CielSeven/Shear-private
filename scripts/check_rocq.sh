#!/bin/bash
# check_rocq.sh — Build/check Rocq files in a directory, or one file directly
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd -P)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd -P)"
CONFIG_FILE="$REPO_ROOT/CONFIGURE"
[ -f "$CONFIG_FILE" ] || { echo "❌ CONFIGURE file not found: $CONFIG_FILE"; exit 1; }

filter_rocq_output() {
  perl -0pe '
    s/^Warning:\n.*?\[overriding-logical-loadpath,filesystem,default\](?:\n|\z)//msg;
    s/^File ".*?", line \d+, characters \d+-\d+:\nWarning: Trying to mask the absolute name ".*?"!\n\[masking-absolute-name,deprecated-since-8\.8,deprecated,default\](?:\n|\z)//msg;
  '
}

# --- Load defaults from CONFIGURE
source "$CONFIG_FILE"

# --- Parse CLI overrides
FILE_ARG=""
CLEAN_FLAG=0
for arg in "$@"; do
  case $arg in
    -COQ_LIB_DIR=*|--COQ_LIB_DIR=*) COQ_LIB_DIR="${arg#*=}";;
    -FILE=*|--FILE=*)                FILE_ARG="${arg#*=}";;
    --clean)                         CLEAN_FLAG=1;;
    *) echo "⚠️  Unknown arg: $arg";;
  esac
done

[ -n "${COQ_LIB_DIR:-}" ] || { echo "❌ COQ_LIB_DIR not set"; exit 1; }

case "$COQ_LIB_DIR" in
  /*) COQ_LIB_DIR_ABS="$COQ_LIB_DIR" ;;
  *)  COQ_LIB_DIR_ABS="$REPO_ROOT/$COQ_LIB_DIR" ;;
esac

COQ_LIB_DIR_ABS="$(cd "$COQ_LIB_DIR_ABS" && pwd -P)"

[ -d "$COQ_LIB_DIR_ABS" ] || { echo "❌ Directory not found: $COQ_LIB_DIR_ABS"; exit 1; }

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

clean_file_artifacts() {
  local file_path="$1"
  local file_dir file_base stem removed
  file_dir="$(dirname "$file_path")"
  file_base="$(basename "$file_path")"
  stem="${file_base%.v}"
  removed=0

  for artifact in \
    "$file_dir/$stem.vo" \
    "$file_dir/$stem.vok" \
    "$file_dir/$stem.vos" \
    "$file_dir/$stem.glob" \
    "$file_dir/.$stem.aux"
  do
    if [ -e "$artifact" ]; then
      rm -f "$artifact"
      removed=$((removed + 1))
    fi
  done

  echo "$removed"
}

clean_dir_artifacts() {
  local target_dir="$1"
  local count
  count=0

  while IFS= read -r -d '' artifact; do
    rm -f "$artifact"
    count=$((count + 1))
  done < <(
    find "$target_dir" -maxdepth 1 -type f \
      \( -name '*.vo' -o -name '*.vok' -o -name '*.vos' -o -name '*.glob' -o -name '.*.aux' \) \
      -print0
  )

  echo "$count"
}

# --- Determine mode
if [ -n "$FILE_ARG" ]; then
  case "$FILE_ARG" in
    /*) file_abs="$FILE_ARG" ;;
    *)  file_abs="$REPO_ROOT/$FILE_ARG" ;;
  esac
  [ -f "$file_abs" ] || { echo "❌ FILE not found: $file_abs"; exit 1; }
  MODE="file"
else
  shopt -s nullglob
  FILES=("$COQ_LIB_DIR_ABS"/*.v)
  shopt -u nullglob
  if [ "$CLEAN_FLAG" -eq 0 ]; then
    [ ${#FILES[@]} -gt 0 ] || { echo "❌ No *.v files found in $COQ_LIB_DIR_ABS"; exit 1; }
  fi
  MODE="directory"
fi

if [ "$CLEAN_FLAG" -eq 1 ]; then
  if [ "$MODE" = "file" ]; then
    removed_count="$(clean_file_artifacts "$file_abs")"
    echo "🧹 Removed $removed_count Rocq artifact(s) for $file_abs"
  else
    removed_count="$(clean_dir_artifacts "$COQ_LIB_DIR_ABS")"
    echo "🧹 Removed $removed_count Rocq artifact(s) from $COQ_LIB_DIR_ABS"
  fi
  exit 0
fi

if [ "$MODE" = "file" ]; then
  command -v coqc >/dev/null 2>&1 || {
    echo "❌ coqc not found in PATH"
    exit 1
  }

  # Parse _CoqProject into coqc flags for single-file checking.
  COQ_FLAGS=()
  while IFS= read -r line; do
    [[ -z "$line" || "$line" == \#* ]] && continue
    eval "set -- $line"
    for word in "$@"; do
      COQ_FLAGS+=("$word")
    done
  done < "$COQ_PROJECT_ROOT/_CoqProject"

  echo "🔧 Checking 1 file with Rocq"
  echo "   Project root: $COQ_PROJECT_ROOT"
  echo

  base="$(basename "$file_abs")"
  printf "  %-40s" "$base"

  output=$(cd "$COQ_PROJECT_ROOT" && coqc "${COQ_FLAGS[@]}" "$file_abs" 2>&1)
  output_status=$?
  output="$(printf '%s' "$output" | filter_rocq_output)"
  if [ $output_status -eq 0 ]; then
    echo "✅"
    echo
    echo "✅ The file passed the Rocq syntax check."
  else
    echo "❌"
    echo "$output" | sed 's/^/    /'
    exit 1
  fi
  exit 0
fi

command -v coq_makefile >/dev/null 2>&1 || {
  echo "❌ coq_makefile not found in PATH"
  exit 1
}
command -v make >/dev/null 2>&1 || {
  echo "❌ make not found in PATH"
  exit 1
}

MAKE_BASENAME=".check_rocq.$$"
MAKEFILE_NAME="${MAKE_BASENAME}.Makefile"
MAKEFILE_CONF_NAME="${MAKE_BASENAME}.Makefile.conf"
VDFILE_NAME="${MAKE_BASENAME}.Makefile.d"

cleanup() {
  rm -f \
    "$COQ_PROJECT_ROOT/$MAKEFILE_NAME" \
    "$COQ_PROJECT_ROOT/$MAKEFILE_CONF_NAME" \
    "$COQ_PROJECT_ROOT/$VDFILE_NAME"
}
trap cleanup EXIT

REL_FILES=()
for f in "${FILES[@]}"; do
  case "$f" in
    "$COQ_PROJECT_ROOT"/*) REL_FILES+=("${f#$COQ_PROJECT_ROOT/}") ;;
    *) REL_FILES+=("$f") ;;
  esac
done

echo "🔧 Building ${#REL_FILES[@]} Rocq file(s) from directory"
echo "   Directory: $COQ_LIB_DIR_ABS"
echo "   Project root: $COQ_PROJECT_ROOT"
echo

echo "   [1/3] Generating Rocq Makefile"
makefile_output=$(
  cd "$COQ_PROJECT_ROOT" && \
  coq_makefile -f "_CoqProject" "${REL_FILES[@]}" -o "$MAKEFILE_NAME" 2>&1
)
makefile_status=$?
makefile_output="$(printf '%s' "$makefile_output" | filter_rocq_output)"
if [ $makefile_status -ne 0 ]; then
  echo "$makefile_output" | sed 's/^/    /'
  exit 1
fi

echo "   [2/3] Computing dependencies"
dep_output=$(
  cd "$COQ_PROJECT_ROOT" && \
  make -f "$MAKEFILE_NAME" "VDFILE=$VDFILE_NAME" "$VDFILE_NAME" 2>&1
)
dep_status=$?
dep_output="$(printf '%s' "$dep_output" | filter_rocq_output)"
if [ $dep_status -ne 0 ]; then
  echo "$dep_output" | sed 's/^/    /'
  exit 1
fi

echo "   [3/3] Running make"
build_output=$(
  cd "$COQ_PROJECT_ROOT" && \
  make -f "$MAKEFILE_NAME" "VDFILE=$VDFILE_NAME" all 2>&1
)
build_status=$?
build_output="$(printf '%s' "$build_output" | filter_rocq_output)"
if [ $build_status -ne 0 ]; then
  echo "$build_output" | sed 's/^/    /'
  exit 1
fi

echo "$build_output"
echo
echo "✅ Directory build passed."
