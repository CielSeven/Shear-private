"""Data-only translator for shape ``.h`` header files.

Sister to :mod:`translate_c_file`'s data-only path — translates a shape
header into its data counterpart by:

- rewriting ``#include "X"`` via :mod:`header_mapping`,
- augmenting any ``/*@ Extern Coq (pred : ...) ... */`` block with data
  predicates derived from :mod:`predicate_mapping`,
- rewriting ``/*@ Import Coq Require Import {lib} */`` lib names via the
  ``lib_mappings`` table in ``data/coq_resource_mappings.json``,
- rewriting ``/*@ include strategies "X" */`` paths via the
  ``strategy_mappings`` table in the same file,
- applying the data-only funcspec rewriter to each function declaration's
  ``/*@ Require ... Ensure ... */`` annotation.
"""

import json
import os
import re
from typing import Dict, List, Optional, Tuple

from GenMonads.header_mapping import translate_headers
from GenMonads.predicate_mapping import get_predicate_mappings
from GenMonads.transshape.preprocess import AnnotationExtractor
from GenMonads.transshape.translator import ShapeTranslator


_RESOURCE_FILE = os.path.join(
    os.path.dirname(__file__), "data", "coq_resource_mappings.json"
)


def _load_resource_mappings() -> Dict[str, Dict[str, str]]:
    try:
        with open(_RESOURCE_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError):
        return {"lib_mappings": {}, "strategy_mappings": {}}
    return {
        "lib_mappings": dict(data.get("lib_mappings") or {}),
        "strategy_mappings": dict(data.get("strategy_mappings") or {}),
    }


_EXTERN_COQ_BLOCK_RE = re.compile(r"/\*@\s*Extern\s+Coq\s+(.*?)\*/", re.DOTALL)
_PREDICATE_ENTRY_RE = re.compile(r"\(\s*([A-Za-z_][A-Za-z0-9_:]*)\s*:\s*([^()]+?)\)")


def augment_extern_coq_block(content: str) -> str:
    """For each ``Extern Coq`` block in *content*, append a data-predicate
    entry for every shape predicate listed inside that has a configured
    mapping.

    Original entries (including their types) are preserved verbatim.  Data
    entries are only added once per block (deduplicated against names
    already present).
    """
    mappings = get_predicate_mappings()

    def _augment(match: re.Match) -> str:
        body = match.group(1)
        entries = list(_PREDICATE_ENTRY_RE.finditer(body))
        existing_names = {m.group(1).strip() for m in entries}
        additions: List[str] = []
        for entry in entries:
            shape_name = entry.group(1).strip()
            mapping = mappings.get(shape_name)
            if mapping is None:
                continue
            if mapping.data_name in existing_names:
                continue
            existing_names.add(mapping.data_name)
            arrow = " -> ".join(
                ["Z"] * mapping.shape_arity
                + list(mapping.data_var_types)
                + ["Assertion"]
            )
            additions.append(f"({mapping.data_name} : {arrow})")
        if not additions:
            return match.group(0)

        # Match the indent used by continuation lines so additions align
        # under the first entry's opening paren.
        indent_match = re.search(r"\n([ \t]+)\(", body)
        indent = indent_match.group(1) if indent_match else "               "
        trimmed = body.rstrip()
        joined_additions = "\n".join(f"{indent}{a}" for a in additions)
        new_body = f"{trimmed}\n{joined_additions}\n "
        return f"/*@ Extern Coq {new_body}*/"

    return _EXTERN_COQ_BLOCK_RE.sub(_augment, content)


def _translate_imports_and_strategies(content: str) -> str:
    res = _load_resource_mappings()
    lib_map = res["lib_mappings"]
    strat_map = res["strategy_mappings"]

    def _rewrite_lib(match: re.Match) -> str:
        name = match.group(2).strip()
        new = lib_map.get(name, name)
        return f"{match.group(1)}{new}{match.group(3)}"

    def _rewrite_strat(match: re.Match) -> str:
        name = match.group(2).strip()
        new = strat_map.get(name, name)
        return f"{match.group(1)}{new}{match.group(3)}"

    content = re.sub(
        r'(/\*@\s*Import\s+Coq\s+Require\s+Import\s+)([A-Za-z0-9_]+)(\s*\*/)',
        _rewrite_lib, content,
    )
    content = re.sub(
        r'(/\*@\s*include\s+strategies\s+")([^"]+)("\s*\*/)',
        _rewrite_strat, content,
    )
    return content


def _format_funcspec_annotation(processed: Dict) -> str:
    parts: List[str] = []
    if processed.get("with"):
        parts.append(f"With {processed['with']['translated']}")
    if processed.get("require"):
        parts.append(f"Require {processed['require']['translated']}")
    if processed.get("ensure"):
        parts.append(f"Ensure {processed['ensure']['translated']}")
    body = "\n".join(f"    {p}" for p in parts)
    return f"/*@\n{body}\n */"


def _translate_funcspec_body(
    comment_body: str,
    struct_decls: Optional[Dict[str, Dict[str, str]]] = None,
    type_env: Optional[Dict[str, str]] = None,
) -> Optional[Dict]:
    """Run the shape→data translator on one ``/*@ With/Require/Ensure ... */``
    annotation body and return the resulting translated funcspec dict (same
    shape as ``process_and_translate_file`` would produce for one function).

    Passing ``struct_decls``/``type_env`` enables field-equality desugaring
    into ``store(addr, T, var)`` predicates — needed for
    :func:`extract_data_witnesses` to recognize data-field witnesses inside
    Ensure bodies.

    Returns ``None`` if there is no Require/Ensure to translate.
    """
    extractor = AnnotationExtractor()
    spec = extractor.parse_spec_content(comment_body)
    if not (spec.get("require") or spec.get("ensure")):
        return None

    from GenMonads.transshape.data_witness import extract_data_witnesses, extract_pre_existing_vars

    def _safe_translate(text: str, reset: bool):
        translated, vars_ = translator.translate_assertion(
            text, reset=reset,
            type_env=type_env, struct_decls=struct_decls,
        )
        return translated, vars_, list(translator.last_generated_var_types)

    translator = ShapeTranslator()
    translator.reset_var_counter()
    funcspec_translated: Dict = {}
    if spec.get("with"):
        funcspec_translated["with"] = {"original": spec["with"]}
    if spec.get("require"):
        translated, vars_, var_types = _safe_translate(spec["require"], reset=True)
        funcspec_translated["require"] = {
            "original": spec["require"],
            "translated": translated,
            "variables": vars_,
            "variable_types": var_types,
        }
    if spec.get("ensure"):
        translated, vars_, var_types = _safe_translate(spec["ensure"], reset=False)
        pre_existing = extract_pre_existing_vars(spec["ensure"])
        data_witnesses = extract_data_witnesses(translated, pre_existing)
        funcspec_translated["ensure"] = {
            "original": spec["ensure"],
            "translated": translated,
            "variables": vars_,
            "variable_types": var_types,
            "data_witnesses": data_witnesses,
        }
    return funcspec_translated


def _translate_one_funcspec(comment_body: str) -> Optional[str]:
    """Apply the data-only funcspec rewriter to one ``/*@ With/Require/Ensure
    ... */`` annotation body.  Returns the new annotation text (``/*@ */``
    included) or ``None`` if nothing translatable was found.
    """
    funcspec_translated = _translate_funcspec_body(comment_body)
    if funcspec_translated is None:
        return None
    from GenMonads.translate_c_file import _process_funcspec_data_only
    processed = _process_funcspec_data_only(funcspec_translated)
    if not processed:
        return None
    return _format_funcspec_annotation(processed)


_DECL_SPEC_RE = re.compile(
    r'(\b[A-Za-z_][A-Za-z0-9_\s\*]*?\b[A-Za-z_][A-Za-z0-9_]*\s*\([^)]*\)\s*)'
    r'(/\*@(.*?)\*/)(\s*;)',
    re.DOTALL,
)


def _build_decl_type_env(header_text: str) -> Dict[str, str]:
    """Build a per-declaration ``var → C-type`` map from one function
    declaration's header (the text up to and including the parameter list).
    Includes ``__return`` and every parameter name.
    """
    from GenMonads.transshape.c_types import _split_type_and_name

    env: Dict[str, str] = {}
    # Match ``<return-type> <name>(<params>)``.
    m = re.match(
        r'\s*(.*?)\b([A-Za-z_][A-Za-z0-9_]*)\s*\(([^)]*)\)\s*$',
        header_text, re.DOTALL,
    )
    if not m:
        return env
    ret_text = m.group(1).strip()
    if ret_text:
        env["__return"] = re.sub(r"\s+", " ", ret_text).strip()
    params_text = m.group(3).strip()
    if params_text and params_text != "void":
        for raw in params_text.split(","):
            split = _split_type_and_name(raw)
            if split:
                env[split[1]] = split[0]
    return env


def translate_header_funcspecs(content: str) -> str:
    """Rewrite every function-declaration ``/*@ ... */`` annotation in
    *content* using the data-only funcspec rewriter.  Declarations without
    Require/Ensure (e.g. pure With-only stubs) are left untouched.
    """

    def _rewrite(match: re.Match) -> str:
        header = match.group(1)
        body = match.group(3)
        tail = match.group(4)
        translated = _translate_one_funcspec(body)
        if translated is None:
            return match.group(0)
        return f"{header}{translated}{tail}"

    return _DECL_SPEC_RE.sub(_rewrite, content)


def translate_header_data_only(input_path: str, output_path: str) -> bool:
    """Translate one shape header to its data counterpart.  Returns True on
    success.
    """
    try:
        with open(input_path, "r", encoding="utf-8") as f:
            content = f.read()
    except OSError as e:
        print(f"Error reading file {input_path}: {e}")
        return False

    content = translate_headers(content)
    content = augment_extern_coq_block(content)
    content = _translate_imports_and_strategies(content)
    content = translate_header_funcspecs(content)

    try:
        os.makedirs(os.path.dirname(output_path), exist_ok=True)
        with open(output_path, "w", encoding="utf-8") as f:
            f.write(content)
        return True
    except OSError as e:
        print(f"Error writing file {output_path}: {e}")
        return False


def _safeexec_header_for_monad(monad: str) -> str:
    return "safeexecE_def.h" if monad == "staterr" else "safeexec_def.h"


def _insert_safeexec_include_in_header(content: str, monad: str) -> str:
    """Insert ``#include "safeexec[_E]_def.h"`` after the last existing
    ``#include`` line, or — for headers that have none — directly after the
    struct declaration block at the top.  Skips when already present.
    """
    target = _safeexec_header_for_monad(monad)
    if target in content:
        return content
    lines = content.split("\n")
    last_include_idx = -1
    for i, line in enumerate(lines):
        if re.match(r'\s*#include\s+[<"]', line):
            last_include_idx = i
    if last_include_idx == -1:
        # No existing #includes — find the first non-struct, non-blank line
        # past the leading struct/typedef block and insert there.
        for i, line in enumerate(lines):
            stripped = line.strip()
            if not stripped:
                continue
            if stripped.startswith(("struct", "typedef", "}", "{")) or stripped.endswith("{"):
                continue
            if stripped.endswith(";"):
                continue
            last_include_idx = i - 1
            break
        if last_include_idx == -1:
            # Conservative fallback: after the first blank line.
            for i, line in enumerate(lines):
                if not line.strip() and i > 0:
                    last_include_idx = i - 1
                    break
    lines.insert(last_include_idx + 1, f'#include "{target}"')
    return "\n".join(lines)


def _build_m_signature(info: Dict, mretty_name: str = "MretTy") -> str:
    """Build the ``Extern Coq`` declaration line for one function's M.

    Mirrors the formatter used by
    :func:`GenMonads.translate_c_file.generate_coq_blocks`.
    """
    from GenMonads.translate_c_file import (
        _normalize_var_types, _curried_type, _return_type,
    )
    fn = info["func_name"]
    req_types = _normalize_var_types(
        info.get("require_var_types"), info["require_var_count"]
    )
    ens_types = _normalize_var_types(
        info.get("ensure_var_types"), info.get("ensure_var_count", 1)
    )
    ret_type = _return_type(ens_types, info.get("ensure_var_count", 1))
    req_args = _curried_type(req_types)
    return f"({fn}_M: {req_args}program unit {ret_type})"


def _build_low_level_spec_aux_annotation(
    funcspec_translated: Dict,
    program: str,
    return_type: str,
) -> str:
    """Build the ``/*@ low_level_spec_aux With ... Require ... Ensure ... */``
    annotation for one in-directory-implemented function declared in a header.

    Reuses the rel.c-side pipeline:
        process_funcspec_with_safeexec → _build_helper_aux_funcspec
    then strips the ``<= low_level_spec`` qualifier from the header (a header
    declaration carries only the aux spec — there is no primary spec to chain
    to).
    """
    from GenMonads.addabstract import process_funcspec_with_safeexec
    from GenMonads.translate_c_file import _build_helper_aux_funcspec

    processed = process_funcspec_with_safeexec(
        funcspec_translated, program, return_type=return_type,
    )
    aux_text = _build_helper_aux_funcspec(
        processed, funcspec_translated, program, return_type=return_type,
    )
    return aux_text.replace(
        "low_level_spec_aux <= low_level_spec", "low_level_spec_aux",
    )


def _functions_implemented_in_dir(source_dir: str) -> set:
    """Set of function *names* whose body lives in any ``.c`` file inside
    *source_dir* — used to decide which header declarations get upgraded to
    the ``low_level_spec_aux`` form.
    """
    from GenMonads.absprog.gen_rel_lib import (
        _FUNC_DEF_RE, _C_KEYWORDS_AND_BUILTINS,
    )
    names: set = set()
    try:
        entries = os.listdir(source_dir)
    except OSError:
        return names
    for entry in sorted(entries):
        if not entry.endswith(".c"):
            continue
        path = os.path.join(source_dir, entry)
        try:
            with open(path, "r", encoding="utf-8") as f:
                text = f.read()
        except OSError:
            continue
        for m in _FUNC_DEF_RE.finditer(text):
            name = m.group(1)
            if name in _C_KEYWORDS_AND_BUILTINS:
                continue
            names.add(name)
    return names


def _rewrite_header_funcspecs_for_rel(
    content: str, in_dir_funcs: set, return_types: Dict[str, str],
    struct_decls: Optional[Dict[str, Dict[str, str]]] = None,
) -> str:
    """Walk the header's declarations and rewrite each ``/*@ ... */``
    annotation: data form for externally-implemented functions; the
    ``low_level_spec_aux`` form for in-directory implementations.
    """

    def _rewrite(match: re.Match) -> str:
        header = match.group(1)
        body = match.group(3)
        tail = match.group(4)
        # Extract the function name from the header prefix.
        name_match = re.search(
            r'\b([A-Za-z_][A-Za-z0-9_]*)\s*\(', header
        )
        if not name_match:
            return match.group(0)
        fn_name = name_match.group(1)
        type_env = _build_decl_type_env(header)
        funcspec_translated = _translate_funcspec_body(
            body, struct_decls=struct_decls, type_env=type_env,
        )
        if funcspec_translated is None:
            return match.group(0)

        if fn_name in in_dir_funcs:
            program = f"{fn_name}_M"
            return_type = return_types.get(fn_name, "")
            try:
                aux_annotation = _build_low_level_spec_aux_annotation(
                    funcspec_translated, program, return_type,
                )
            except Exception:
                return match.group(0)
            return f"{header}{aux_annotation}{tail}"

        # External callee — emit data form.
        from GenMonads.translate_c_file import _process_funcspec_data_only
        processed = _process_funcspec_data_only(funcspec_translated)
        if not processed:
            return match.group(0)
        return f"{header}{_format_funcspec_annotation(processed)}{tail}"

    return _DECL_SPEC_RE.sub(_rewrite, content)


def _extract_declaration_return_types(content: str) -> Dict[str, str]:
    """Return ``{func_name: return_type}`` for every function declaration in
    *content*.  Captures the part before the function name so the rel
    rewriter can pick the right ``_is_void_return_type`` answer.
    """
    out: Dict[str, str] = {}
    pattern = re.compile(
        r'(?P<rt>(?:[A-Za-z_][A-Za-z0-9_]*\s*[\s\*]+)+)'
        r'(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*\([^)]*\)\s*'
        r'(?:/\*@.*?\*/)?\s*;',
        re.DOTALL,
    )
    for m in pattern.finditer(content):
        rt = m.group("rt").strip()
        name = m.group("name")
        # Skip cases where the "return type" is actually a keyword like
        # ``return``/``if`` (call-site captures).
        last_tok = re.findall(r'\b\w+\b', rt)
        if last_tok and last_tok[-1] in (
            "return", "if", "else", "while", "for", "switch", "do", "case", "goto",
        ):
            continue
        out[name] = rt
    return out


def _emit_abstract_program_extern_block(
    func_data_list: List[Dict],
) -> Optional[str]:
    """Build a ``/*@ Extern Coq (maketuple ...) (fn_M ...) ... */`` block for
    the in-directory functions.  Returns ``None`` when none of them have a
    derivable M signature (e.g. headers without any implemented function).
    """
    from GenMonads.translate_c_file import collect_func_extern_info

    lines: List[str] = []
    needs_maketuple = False
    for func_data in func_data_list:
        try:
            info = collect_func_extern_info(
                func_data, include_helpers=True, function_source=None,
            )
        except Exception:
            info = None
        if info is None:
            continue
        try:
            sig = _build_m_signature(info)
        except Exception:
            continue
        lines.append(sig)
        if info.get("ensure_var_count", 1) > 1:
            needs_maketuple = True
    if not lines:
        return None
    decl_lines: List[str] = []
    if needs_maketuple:
        decl_lines.append("(maketuple: {A} {B} -> A -> B -> (A * B))")
    decl_lines.extend(lines)
    padding = "               "
    body = f"\n{padding}".join(decl_lines)
    return f"/*@ Extern Coq {body}\n */"


def _build_in_dir_funcspec_table(
    content: str,
    struct_decls: Optional[Dict[str, Dict[str, str]]] = None,
) -> List[Dict]:
    """Parse each function declaration in *content* and translate its spec
    into the shape ``process_and_translate_file`` would produce per function.
    Used to drive abstract-program signature emission.
    """
    func_data_list: List[Dict] = []
    for m in _DECL_SPEC_RE.finditer(content):
        header = m.group(1)
        body = m.group(3)
        name_match = re.search(r'\b([A-Za-z_][A-Za-z0-9_]*)\s*\(', header)
        if not name_match:
            continue
        fn_name = name_match.group(1)
        type_env = _build_decl_type_env(header)
        funcspec_translated = _translate_funcspec_body(
            body, struct_decls=struct_decls, type_env=type_env,
        )
        if funcspec_translated is None:
            continue
        return_type = ""
        rt_match = re.search(r'^([\s\S]*?)\b' + re.escape(fn_name) + r'\s*\(', header)
        if rt_match:
            return_type = rt_match.group(1).strip()
        func_data_list.append({
            "function": fn_name,
            "return_type": return_type,
            "funcspec": funcspec_translated,
            "inner_assertions": [],
        })
    return func_data_list


def translate_header_rel(
    input_path: str, output_path: str, source_dir: str, monad: str = "staterel",
) -> bool:
    """Translate a shape header into its rel form: data form + safeExec
    include + abstract-program ``Extern Coq`` block for in-directory
    implementations + ``low_level_spec_aux`` funcspecs for those.
    """
    try:
        with open(input_path, "r", encoding="utf-8") as f:
            content = f.read()
    except OSError as e:
        print(f"Error reading file {input_path}: {e}")
        return False

    in_dir_funcs = _functions_implemented_in_dir(source_dir)
    return_types = _extract_declaration_return_types(content)

    # Collect struct definitions from the header so the translator can
    # desugar field equalities (`x -> data == v`) into `store(addr, T, var)`
    # predicates — needed for data-witness detection to work the same way it
    # does for .c files.
    from GenMonads.transshape.c_types import collect_struct_decls
    struct_decls = collect_struct_decls(input_path)

    content = translate_headers(content)
    content = augment_extern_coq_block(content)
    content = _translate_imports_and_strategies(content)
    content = _insert_safeexec_include_in_header(content, monad)

    # Insert an Extern Coq block listing the abstract programs for every
    # in-dir-implemented function declared in this header.  If at least one
    # such function exists, also import the rel_lib that will define them.
    func_data_list = [
        fd for fd in _build_in_dir_funcspec_table(content, struct_decls=struct_decls)
        if fd["function"] in in_dir_funcs
    ]
    program_block = _emit_abstract_program_extern_block(func_data_list)
    blocks_to_insert: List[str] = []
    if func_data_list:
        stem = os.path.splitext(os.path.basename(input_path))[0]
        blocks_to_insert.append(
            f"/*@ Import Coq Require Import {stem}_rel_lib */"
        )
    if program_block:
        blocks_to_insert.append(program_block)
    if blocks_to_insert:
        joined = "\n\n".join(blocks_to_insert)
        # Place after the last ``Extern Coq`` / ``Import Coq`` /
        # ``include strategies`` directive, before the first function
        # declaration.  Search for any pre-existing top-level annotation
        # and insert directly after it.
        anchor = list(re.finditer(
            r'/\*@\s*(?:Extern\s+Coq|Import\s+Coq|include\s+strategies)\b'
            r'.*?\*/',
            content, flags=re.DOTALL,
        ))
        if anchor:
            insert_at = anchor[-1].end()
            content = (
                content[:insert_at] + "\n\n" + joined + content[insert_at:]
            )
        else:
            content += "\n\n" + joined + "\n"

    content = _rewrite_header_funcspecs_for_rel(
        content, in_dir_funcs, return_types, struct_decls=struct_decls,
    )

    try:
        os.makedirs(os.path.dirname(output_path), exist_ok=True)
        with open(output_path, "w", encoding="utf-8") as f:
            f.write(content)
        return True
    except OSError as e:
        print(f"Error writing file {output_path}: {e}")
        return False


_HEADER_REL_LIB_PRELUDE = (
    "Require Import Coq.ZArith.ZArith.\n"
    "Require Import Coq.Lists.List.\n"
    "Import ListNotations.\n"
    "Local Open Scope Z_scope.\n"
    "Local Open Scope list.\n"
)


def generate_header_rel_lib(
    input_header_path: str, source_dir: str, lib_dir: str,
) -> Optional[str]:
    """Generate ``{stem}_rel_lib.v`` next to the per-function rel_libs:
    a thin re-exporter for every function-level rel_lib whose source ``.c``
    lives in *source_dir* AND whose name is declared in *input_header_path*.

    Returns the output path, or ``None`` if no function declared in the
    header is implemented in *source_dir* (nothing to re-export).
    """
    in_dir_funcs = _functions_implemented_in_dir(source_dir)
    if not in_dir_funcs:
        return None

    try:
        with open(input_header_path, "r", encoding="utf-8") as f:
            content = f.read()
    except OSError:
        return None

    # Collect every function name declared in the header (any prototype, with
    # or without a ``/*@ ... */`` spec).
    declared_funcs: set = set()
    decl_pattern = re.compile(
        r'\b[A-Za-z_][A-Za-z0-9_\s\*]*?\b([A-Za-z_][A-Za-z0-9_]*)\s*'
        r'\([^)]*\)\s*'
        r'(?:/\*@.*?\*/\s*)?;',
        re.DOTALL,
    )
    from GenMonads.absprog.gen_rel_lib import _C_KEYWORDS_AND_BUILTINS
    for m in decl_pattern.finditer(content):
        name = m.group(1)
        if name in _C_KEYWORDS_AND_BUILTINS:
            continue
        declared_funcs.add(name)

    relevant = declared_funcs & in_dir_funcs
    if not relevant:
        return None

    # Map each relevant function to the basename of its defining ``.c``
    # file — the rel_lib stem is derived from the file, not the function.
    from GenMonads.absprog.gen_rel_lib import _build_sibling_function_table
    table = _build_sibling_function_table(
        os.path.join(source_dir, "__nonexistent__"),
    )
    lib_basenames: set = set()
    for fn in relevant:
        path = table.get(fn)
        if path is None:
            continue
        lib_basenames.add(os.path.splitext(os.path.basename(path))[0])

    if not lib_basenames:
        return None

    stem = os.path.splitext(os.path.basename(input_header_path))[0]
    out_path = os.path.join(lib_dir, f"{stem}_rel_lib.v")
    exports = "\n".join(
        f"Require Export {lib}_rel_lib." for lib in sorted(lib_basenames)
    )
    body = f"{_HEADER_REL_LIB_PRELUDE}\n{exports}\n"

    os.makedirs(lib_dir, exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(body)
    return out_path


def derive_output_header_name_rel(input_path: str) -> str:
    """Pick the rel-form header filename for *input_path*: ``{stem}_rel.h``."""
    stem, ext = os.path.splitext(os.path.basename(input_path))
    return f"{stem}_rel{ext}"


def derive_output_header_name(input_path: str) -> str:
    """Pick the data-form header filename for *input_path*.

    Uses :mod:`header_mapping` when the source basename is mapped (e.g.
    ``glibc_slist_clean.h`` → ``glibc_slist_clean_data.h``); otherwise
    appends ``_data`` before the ``.h`` suffix.
    """
    from GenMonads.header_mapping import get_header_mappings
    base = os.path.basename(input_path)
    mappings = get_header_mappings()
    if base in mappings:
        return mappings[base]
    stem, ext = os.path.splitext(base)
    return f"{stem}_data{ext}"
