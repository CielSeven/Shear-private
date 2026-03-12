#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
extract_and_normalize_assertions.py
- Keep data_at(...)
- Keep quantifiers, but rename tokens
- Rename patterns:
    v_value_FIELD_n   -> v -> FIELD
    v_FIELD_n         -> v_FIELD         (UPDATED per request)
    v_value_n         -> v
    v_n_value         -> v
    v_n               -> v               (e.g., x_166 -> x, retval_176 -> retval)
    lK_n              -> lK              (logical variables)
- Remove 'branch name' / 'next branch name' lines
"""

import argparse
import re
import sys
from pathlib import Path
from typing import List, Tuple, Dict

# ========= EDIT THESE PATH SETTINGS =========
DEFAULT_INPUTS = ["../shapelogs/sll_copy_withdata_log.txt"]
DEFAULT_OUTPUT_DIR = "./normalizedinv"
RECURSIVE = False
# ===========================================

UNROLL_HDR_RE = re.compile(r'^Unrolling while loop\s+(\d+)\s+times\.\s*$', re.M)
ASSERTION_NORMAL_START_RE = re.compile(
    r'"Assertion normal":\s*\{[^$]*?-------Assertion begin---------', re.S)
ASSERTION_BLOCK_RE = re.compile(
    r'-------Assertion begin---------\s*(.*?)\s*-------Assertion end ----------',
    re.S)

NOISE_LINE_RE = re.compile(r'(?m)^\s*(branch name|next branch name)\s*:\s*.*$')
EXISTS_LINE_RE = re.compile(r'(?m)^\s*exists\s+(.*?)\s*,\s*$')

# 1) v_value_FIELD_n  -> v -> FIELD
VALUE_FIELD_RE = re.compile(r'\b([A-Za-z_]\w*)_value_([A-Za-z_]\w*)_(\d+)\b')
# 2) v_FIELD_n        -> v_FIELD   (UPDATED)
GENERIC_FIELD_RE = re.compile(r'\b([A-Za-z_]\w*)_([A-Za-z_]\w*)_(\d+)\b')
# 3) v_value_n        -> v
VALUE_BASE_RE_1 = re.compile(r'\b([A-Za-z_]\w*)_value_(\d+)\b')
# 4) v_n_value        -> v
VALUE_BASE_RE_2 = re.compile(r'\b([A-Za-z_]\w*)_(\d+)_value\b')
# 5) v_n              -> v
BASE_NUM_RE     = re.compile(r'\b([A-Za-z_]\w*)_(\d+)\b')
# 6) lK_n             -> lK
LOGIC_LVAR_RE   = re.compile(r'\b(l\d+)_\d+\b')

def find_unroll_blocks(text: str):
    out = []
    for m in UNROLL_HDR_RE.finditer(text):
        n = int(m.group(1))
        m_norm_start = ASSERTION_NORMAL_START_RE.search(text, m.end())
        if not m_norm_start:
            continue
        m_block = ASSERTION_BLOCK_RE.search(text, m_norm_start.start())
        if not m_block:
            continue
        out.append((n, m_block.group(1)))
    return out

def _strip_noise_lines(s: str) -> str:
    return NOISE_LINE_RE.sub("", s)

def _apply_name_rules(s: str) -> str:
    """
    Apply in this order:
      - v_value_FIELD_n  -> v -> FIELD
      - v_FIELD_n        -> v_FIELD                 (UPDATED)
      - v_value_n / v_n_value -> v
      - v_n              -> v
      - lK_n             -> lK
    """
    s = VALUE_FIELD_RE.sub(lambda m: f"{m.group(1)} -> {m.group(2)}", s)   # v_value_field_n
    s = GENERIC_FIELD_RE.sub(lambda m: f"{m.group(1)}_{m.group(2)}", s)    # v_field_n  -> v_field
    s = VALUE_BASE_RE_1.sub(lambda m: m.group(1), s)                       # v_value_n
    s = VALUE_BASE_RE_2.sub(lambda m: m.group(1), s)                       # v_n_value
    s = BASE_NUM_RE.sub(lambda m: m.group(1), s)                           # v_n
    s = LOGIC_LVAR_RE.sub(r'\1', s)                                        # lK_n
    return s

def _normalize_token(tok: str) -> str:
    return _apply_name_rules(tok)

def _extract_and_rename_exists(block: str) -> Tuple[str, str]:
    m = EXISTS_LINE_RE.search(block)
    if not m:
        return "", block
    tokens = [t for t in re.split(r'[\s,]+', m.group(1)) if t]
    renamed, seen = [], set()
    for tok in tokens:
        nt = _normalize_token(tok)
        if nt and nt not in seen:
            seen.add(nt)
            renamed.append(nt)
    exists_norm = f"exists {' '.join(renamed)}, "
    start, end = m.span()
    body_wo = block[:start] + block[end:]
    return exists_norm, body_wo

def _tidy_spaces(s: str) -> str:
    s = re.sub(r'\s*,\s*', ', ', s)
    s = re.sub(r'\)\s*&&\s*\n\s*\(', ') && (', s)
    s = re.sub(r'[ \t]+', ' ', s)
    s = re.sub(r' ?\n ?', '\n', s)
    s = re.sub(r'\n{3,}', '\n\n', s)
    return s.strip()

def normalize_assertion(raw_block: str) -> str:
    s = _strip_noise_lines(raw_block)
    exists_prefix, s = _extract_and_rename_exists(s)
    s = _apply_name_rules(s)     # rename everywhere (including inside data_at)
    s = _tidy_spaces(s)
    return (exists_prefix + s) if exists_prefix else s

def process_text(text: str) -> Dict[int, str]:
    out = {}
    for n, raw in find_unroll_blocks(text):
        out[n] = normalize_assertion(raw)
    return out

def process_file(path: Path):
    text = path.read_text(encoding='utf-8', errors='ignore')
    return path, process_text(text)

def collect_txt_files(paths, recursive: bool):
    files = []
    for p in paths:
        if p.is_dir():
            files.extend(sorted(p.rglob("*.txt") if recursive else p.glob("*.txt")))
        elif p.is_file() and p.suffix.lower() == ".txt":
            files.append(p)
    return files

def write_normalized_output(src: Path, results: Dict[int, str], out_dir: Path) -> Path:
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / (src.stem + ".normalized.txt")
    lines = []
    for n in sorted(results):
        lines.append(f"# Unrolling while loop {n} times\n")
        lines.append(results[n])
        lines.append("\n\n")
    out_path.write_text("".join(lines), encoding="utf-8")
    return out_path

def main():
    ap = argparse.ArgumentParser(description="Extract and normalize 'Assertion normal' after while-loop unrolling.")
    ap.add_argument("inputs", nargs="*", help="Files or directories. If omitted, uses DEFAULT_INPUTS.")
    ap.add_argument("--out-dir", default=None, help="Output directory. If omitted, uses DEFAULT_OUTPUT_DIR.")
    ap.add_argument("--recursive", action="store_true", help="Recursively scan subdirectories.")
    args = ap.parse_args()

    inputs = [Path(s).expanduser().resolve() for s in (args.inputs or DEFAULT_INPUTS)]
    out_dir = Path(args.out_dir).expanduser().resolve() if args.out_dir else Path(DEFAULT_OUTPUT_DIR).expanduser().resolve()
    recursive = bool(args.recursive) or RECURSIVE

    files = collect_txt_files(inputs, recursive=recursive)
    if not files:
        print("No .txt files found in provided inputs.", file=sys.stderr)
        sys.exit(1)

    any_found = False
    for f in files:
        src, res = process_file(f)
        if not res:
            print(f"[{src}] No 'Assertion normal' blocks found.")
            continue
        any_found = True
        outp = write_normalized_output(src, res, out_dir)
        print(f"[{src}] Extracted {len(res)} block(s) → {outp}")

    if not any_found:
        sys.exit(2)

if __name__ == "__main__":
    main()
