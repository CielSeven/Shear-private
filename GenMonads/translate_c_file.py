"""
Translate C files with shape assertions to files with translated assertions.

This module processes C files to:
1. Replace function specifications with translated ones
2. Replace loop invariants with translated ones + safeExec predicate
3. Output the translated file as xxx_rel.c
"""

import os
import re
import sys
from typing import Dict, Optional, List, Set

from GenMonads.early_return import detect_early_return_shape
from GenMonads.cli_common import (
    add_input_path_arguments,
    add_output_path_argument,
    read_configure_value,
    resolve_cli_value,
)
from GenMonads.transshape.process_and_translate import process_and_translate_file
from GenMonads.addabstract import add_safeexec_predicate, process_funcspec_with_safeexec
from GenMonads.addabstract.addexec import (
    _is_void_return_type,
    extract_variables_from_assertion,
)
from GenMonads.header_mapping import translate_headers


LLM4PV_DEFAULT_BACKEND = "command"
# Workdir-mode owns the codex invocation internally — no shell template here.
# Retained as a legacy CLI default that's ignored by the rewired backend.
LLM4PV_DEFAULT_COMMAND = ""
LLM4PV_DEFAULT_MAX_RETRIES = 2


def collect_func_extern_info(
    func_data: Dict,
    include_helpers: bool = False,
    function_source: Optional[str] = None,
) -> Optional[Dict]:
    """Collect variable counts needed for Extern Coq declarations.

    By default, only functions with loop invariants are included so callers that
    build loop-oriented artifacts keep the previous behavior. When
    ``include_helpers`` is True, functions with translated funcspecs but no loop
    invariants are also returned so their ``{func}_M`` signature can be emitted.
    """
    inner = func_data.get('inner_assertions', [])
    inv_assertions = [a for a in inner if a.get('type') == 'Inv' and 'variables' in a]
    funcspec = func_data.get('funcspec')
    if not inv_assertions and not include_helpers:
        return None
    if not funcspec:
        return None
    require_var_count = 0
    require_var_names = []
    require_var_types: List[str] = []
    if funcspec and funcspec.get('require') and funcspec['require'].get('translated'):
        require_vars, require_var_types = _extract_generated_var_info(funcspec['require'])
        require_var_count = len(require_vars)
        require_var_names = [v.lstrip('?') for v in require_vars]

    ensure_var_count = 0
    ensure_var_types: List[str] = []
    if funcspec and funcspec.get('ensure') and funcspec['ensure'].get('translated'):
        ensure_vars, raw_ensure_types = _extract_generated_var_info(funcspec['ensure'])
        # Only count vars NOT already in Require (those are reused, not returned).
        ensure_only = [
            (name, var_type)
            for name, var_type in zip(ensure_vars, raw_ensure_types)
            if name.lstrip('?') not in require_var_names
        ]

        # Data witnesses bound by the original Ensure (e.g. ``exists d,
        # __return -> data == d``) are lifted into the abstract loop state,
        # so they widen the abstract program's return type as well.
        ensure_data_witnesses = funcspec['ensure'].get('data_witnesses', []) or []
        for witness in ensure_data_witnesses:
            ensure_only.append((witness, 'Z'))

        # If the C function has a non-void return type but the Ensure does
        # not mention __return, ``add_safeexec_to_ensure`` synthesizes a
        # witness ``r`` of type Z.  Mirror that here so the abstract program's
        # return type matches the emitted ``return(...)`` arity.
        ensure_body = funcspec['ensure'].get('translated', '')
        return_type = func_data.get('return_type', '')
        if (
            not _is_void_return_type(return_type)
            and '__return' not in ensure_body
        ):
            ensure_only.append(('r', 'Z'))

        ensure_var_count = len(ensure_only)
        ensure_var_types = [var_type for _, var_type in ensure_only]

    has_loop_program = bool(inv_assertions)
    inv_var_count = 0
    inv_var_types: List[str] = []
    if inv_assertions:
        inv_source = max(inv_assertions, key=lambda a: len(a.get('variables', [])))
        inv_var_count = len(inv_source.get('variables', []))
        inv_var_types = _normalize_var_types(inv_source.get('variable_types'), inv_var_count)

    early_return_shape = {
        'has_top_level_loop': False,
        'has_pre_loop_early_return': False,
        'has_loop_body_early_return': False,
        'needs_early_result': False,
    }
    if function_source:
        early_return_shape = detect_early_return_shape(function_source)

    return {
        'func_name': func_data['function'],
        'has_loop_program': has_loop_program,
        'require_var_count': require_var_count,
        'require_var_types': require_var_types,
        'inv_var_count': inv_var_count,
        'inv_var_types': inv_var_types,
        'ensure_var_count': ensure_var_count,
        'ensure_var_types': ensure_var_types,
        'has_top_level_loop': early_return_shape['has_top_level_loop'],
        'has_pre_loop_early_return': early_return_shape['has_pre_loop_early_return'],
        'has_loop_body_early_return': early_return_shape['has_loop_body_early_return'],
        'needs_early_result': early_return_shape['needs_early_result'],
    }


def _normalize_var_types(var_types: Optional[List[str]], count: int) -> List[str]:
    """Return a type list of exactly count entries, requiring explicit types."""
    if count == 0:
        return []
    if var_types is None:
        raise ValueError(f"Missing variable types for {count} generated variable(s)")

    normalized = list(var_types)
    if len(normalized) != count:
        raise ValueError(
            f"Variable type count mismatch: expected {count}, got {len(normalized)}"
        )
    return normalized


def _extract_generated_var_info(assertion_dict: Dict) -> tuple[List[str], List[str]]:
    """Extract generated variable names and their inferred types from a clause."""
    names = assertion_dict.get('variables') or extract_variables_from_assertion(assertion_dict['translated'])
    return names, _normalize_var_types(assertion_dict.get('variable_types'), len(names))


def _tuple_type(types: List[str]) -> str:
    """Build a Coq tuple type from a non-empty list of element types."""
    if not types:
        raise ValueError("Expected at least one type")
    if len(types) == 1:
        return types[0]
    return "(" + " * ".join(types) + ")"


def _curried_type(types: List[str]) -> str:
    """Build curried argument types."""
    if not types:
        return ""
    return " -> ".join(types) + " -> "


def _return_type(types: List[str], count: int) -> str:
    """Build return type from inferred ensure variable types."""
    if count == 0:
        return "unit"
    if count <= 1:
        return f"({_tuple_type(types)})"
    return _tuple_type(types)


def _extract_funcspec_return_info(funcspec: Dict) -> tuple[List[str], int]:
    """Infer the abstract program return type from translated Require/Ensure clauses."""
    require_var_names = []
    if funcspec.get('require') and funcspec['require'].get('translated'):
        require_vars, _ = _extract_generated_var_info(funcspec['require'])
        require_var_names = [v.lstrip('?') for v in require_vars]

    ensure_var_types: List[str] = []
    ensure_var_count = 0
    if funcspec.get('ensure') and funcspec['ensure'].get('translated'):
        ensure_vars, raw_ensure_types = _extract_generated_var_info(funcspec['ensure'])
        ensure_only = [
            (name, var_type)
            for name, var_type in zip(ensure_vars, raw_ensure_types)
            if name.lstrip('?') not in require_var_names
        ]
        ensure_var_count = len(ensure_only)
        ensure_var_types = [var_type for _, var_type in ensure_only]

    return ensure_var_types, ensure_var_count


def _build_return_call(clean_vars: List[str]) -> str:
    """Build the abstract return program for Ensure clauses."""
    if len(clean_vars) > 1:
        var_args = ', '.join(clean_vars)
        return f"return(maketuple({var_args}))"
    if len(clean_vars) == 1:
        return f"return({clean_vars[0]})"
    return "return"


_SAFEEXEC_HEADER_NAME = "safeexec_def.h"

# The C-side safeExec header differs per monad backend: the error-aware monad
# (staterr / MonadErr) needs `safeexecE_def.h` (which maps `program := MonadErr.M`),
# the relational monad (staterel) needs `safeexec_def.h`.
_SAFEEXEC_HEADER_NAMES = {
    "staterel": "safeexec_def.h",
    "staterr": "safeexecE_def.h",
}


def _safeexec_header_name(monad: str) -> str:
    return _SAFEEXEC_HEADER_NAMES.get(monad, _SAFEEXEC_HEADER_NAME)


def _quoted_includes(content: str) -> List[str]:
    """Return the list of ``#include "<name>"`` filenames in *content*."""
    return re.findall(r'^\s*#include\s+"([^"]+)"', content, flags=re.MULTILINE)


def _header_includes_safeexec(
    header_name: str,
    search_dirs: List[str],
    target_name: str = _SAFEEXEC_HEADER_NAME,
    visited: Optional[Set[str]] = None,
) -> bool:
    """Return True if *header_name* (or any header it #includes, recursively)
    contains ``#include "<target_name>"`` (default ``safeexec_def.h``).

    *search_dirs* is the list of directories to look in.  Missing or
    unreadable headers are silently skipped — we conservatively report False
    in that case.
    """
    if visited is None:
        visited = set()

    for directory in search_dirs:
        candidate = os.path.join(directory, header_name)
        try:
            real = os.path.realpath(candidate)
        except OSError:
            continue
        if real in visited:
            return False
        if not os.path.isfile(real):
            continue
        visited.add(real)
        try:
            with open(real, "r", encoding="utf-8") as f:
                header_text = f.read()
        except OSError:
            return False
        if target_name in header_text:
            return True
        # Recurse into nested ``#include "..."`` directives.
        for nested in _quoted_includes(header_text):
            if nested == header_name:
                continue
            nested_dirs = [os.path.dirname(real)] + search_dirs
            if _header_includes_safeexec(nested, nested_dirs, target_name, visited):
                return True
        return False
    return False


def insert_safeexec_include(
    content: str,
    header_search_dirs: Optional[List[str]] = None,
    monad: str = "staterel",
) -> str:
    """Insert the monad's safeExec header after the last ``#include`` line,
    unless it is already present in *content* or transitively reachable via
    one of the headers ``#include``d from *content*.

    The header is ``safeexec_def.h`` for ``staterel`` and ``safeexecE_def.h``
    for ``staterr`` (MonadErr).  Per the "find in the mapped header first" rule,
    we first search the included (mapped) headers for that exact header and only
    add it when it is not already reachable.

    *header_search_dirs* is the list of directories to look in when chasing
    quoted-form includes (usually the input C file's directory).  When
    omitted, only the literal text of *content* is checked.
    """
    target = _safeexec_header_name(monad)

    if target in content:
        return content

    if header_search_dirs:
        for header in _quoted_includes(content):
            if _header_includes_safeexec(header, header_search_dirs, target):
                return content

    lines = content.split('\n')
    last_include_idx = -1
    for i, line in enumerate(lines):
        if re.match(r'\s*#include\s+[<"]', line):
            last_include_idx = i

    if last_include_idx >= 0:
        lines.insert(last_include_idx + 1, f'#include "{target}"')
    return '\n'.join(lines)


def _strip_c_comments(text: str) -> str:
    """Remove block and line comments before lightweight call scanning."""
    text = re.sub(r'/\*.*?\*/', '', text, flags=re.DOTALL)
    return re.sub(r'//.*', '', text)


def _extract_function_body(content: str, func_name: str) -> Optional[str]:
    """Return the body text for a function definition, if present."""
    pattern = (
        rf'(?:[a-zA-Z_][a-zA-Z0-9_\s\*]*?)\b{re.escape(func_name)}\s*\([^)]*\)\s*'
        rf'(?:/\*@.*?\*/\s*)?\{{'
    )
    match = re.search(pattern, content, re.DOTALL)
    if not match:
        return None

    start = match.end()
    brace_count = 1
    pos = start
    while pos < len(content) and brace_count > 0:
        if content[pos] == '{':
            brace_count += 1
        elif content[pos] == '}':
            brace_count -= 1
        pos += 1

    if brace_count != 0:
        return None
    return content[start:pos - 1]


def _extract_function_source(file_path: str, func_name: str) -> str:
    """Extract the full source text for one function definition from a C file."""
    with open(file_path, "r", encoding="utf-8") as f:
        content = f.read()

    matches = re.finditer(rf"\b{re.escape(func_name)}\s*\(", content)
    for match in matches:
        depth = 0
        for ch in content[:match.start()]:
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
        if depth != 0:
            continue

        brace_start = content.find("{", match.end())
        if brace_start == -1:
            continue

        semicolon = content.find(";", match.end())
        if semicolon != -1 and semicolon < brace_start:
            continue

        start = content.rfind("\n", 0, match.start())
        start = 0 if start == -1 else start + 1
        break
    else:
        raise ValueError(f"Could not find function signature for '{func_name}' in {file_path}")

    depth = 0
    end = None
    for idx in range(brace_start, len(content)):
        ch = content[idx]
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                end = idx + 1
                break

    if end is None:
        raise ValueError(f"Could not find function body end for '{func_name}' in {file_path}")

    return content[start:end]


def collect_callee_functions(content: str, functions: List[Dict]) -> set[str]:
    """Collect functions that are called by another function or by themselves."""
    function_names = []
    seen = set()
    for func in functions:
        name = func.get('function')
        if name and name not in seen:
            seen.add(name)
            function_names.append(name)

    callees = set()
    for caller in function_names:
        body = _extract_function_body(content, caller)
        if body is None:
            continue
        stripped_body = _strip_c_comments(body)
        for callee in function_names:
            if re.search(rf'\b{re.escape(callee)}\s*\(', stripped_body):
                callees.add(callee)

    return callees


def _format_funcspec_comment(parts: List[str], header: Optional[str] = None) -> str:
    """Render one annotation comment from a header label and clause lines."""
    lines = []
    if header:
        lines.append(f"/*@ {header}")
    else:
        lines.append("/*@")

    if parts:
        lines.extend(f"    {part}" for part in parts)
    lines.append(" */")
    return "\n".join(lines)


def _build_funcspec_parts(processed: Dict) -> List[str]:
    """Convert a processed funcspec dict into formatted clause lines."""
    parts = []
    if 'with' in processed and processed['with']:
        parts.append(f"With {processed['with']['translated']}")
    if 'require' in processed and processed['require']:
        req = processed['require']
        parts.append(f"Require {req.get('with_safeexec', req.get('translated', ''))}")
    if 'ensure' in processed and processed['ensure']:
        ens = processed['ensure']
        parts.append(f"Ensure {ens.get('with_safeexec', ens.get('translated', ''))}")
    return parts


def _build_helper_aux_funcspec(
    processed: Dict,
    funcspec: Dict,
    program: str,
    return_type: str = "",
) -> str:
    """Build the derived continuation-passing helper specification.

    The aux spec is mechanically derived from the primary (`low_level_spec`):
      With:    prepend ``{B} (cont: <prog-return-type> -> program unit B)``
      Require: rewrap ``safeExec(ATrue, <prog>(args), X)`` as
               ``safeExec(ATrue, bind(<prog>(args), cont), X)``
      Ensure:  rewrap the exact ``safeExec(ATrue, return(<expr>), X)`` as
               ``safeExec(ATrue, bind(return(<expr>), cont), X)``

    The cont type must match the abstract program's return type — including
    any synthetic ``r`` witness AddAbstract introduced for non-void scalar
    returns.
    """
    ret_types, _ = _extract_funcspec_return_info(funcspec)
    # Replicate AddAbstract's synthetic-witness rule so the cont type and
    # the return-call form agree with what was actually emitted in the
    # Ensure clause.
    ensure_translated = (funcspec.get('ensure') or {}).get('translated', '') or ''
    need_witness = (
        return_type
        and not _is_void_return_type(return_type)
        and "__return" not in ensure_translated
    )
    if need_witness:
        ret_types = list(ret_types) + ["Z"]
    cont_arg_type = _return_type(ret_types, len(ret_types))
    base_with = processed.get('with', {}).get('translated', '').strip()
    with_prefix = f"{{B}} (cont: {cont_arg_type} -> program unit B)"
    with_clause = f"{with_prefix} {base_with}".strip()

    require_text = ""
    if processed.get('require'):
        require_text = processed['require'].get('with_safeexec', processed['require'].get('translated', ''))
        require_text = require_text.replace(
            f"safeExec(ATrue, {program}",
            f"safeExec(ATrue, bind({program}",
            1,
        )
        if "bind(" in require_text:
            require_text = require_text.replace(", X)", ", cont), X)", 1)

    ensure_text = ""
    if processed.get('ensure'):
        ensure_text = processed['ensure'].get('with_safeexec', processed['ensure'].get('translated', ''))
        # Extract the exact ``return(...)`` form that was actually emitted so
        # the substitution matches the synthesized witness layout (e.g.
        # ``return(maketuple(l2, r))`` rather than the translator's
        # variable-only ``return(l2)``).
        match = re.search(
            r"safeExec\(ATrue,\s*(return\([^X]*?\)),\s*X\)",
            ensure_text,
        )
        if match:
            return_expr = match.group(1)
            ensure_text = ensure_text.replace(
                f"safeExec(ATrue, {return_expr}, X)",
                f"safeExec(ATrue, bind({return_expr}, cont), X)",
                1,
            )

    return _format_funcspec_comment(
        [
            f"With {with_clause}",
            f"Require {require_text}",
            f"Ensure {ensure_text}",
        ],
        header="low_level_spec_aux <= low_level_spec",
    )


def _early_result_type(left_type: str, right_type: str) -> str:
    return f"early_result {left_type} {right_type}"


def _render_helper_funcspec_declarations(header_decl: str, primary_spec: str, aux_spec: str) -> str:
    """Repeat a helper declaration so each named spec gets its own prototype.

    The auxiliary (`low_level_spec_aux`) appears FIRST as a forward
    declaration; the primary (`low_level_spec`) appears on the actual
    definition.  Order is required by the proof framework — recursive
    callers need the cont-passing spec visible before the body is
    elaborated.
    """
    normalized_header = header_decl.rstrip()
    return (
        f"{normalized_header}\n"
        f"{aux_spec};\n"
        f"{normalized_header}\n"
        f"{primary_spec}"
    )


def generate_coq_blocks(basename: str, func_infos: List[Dict], needs_maketuple: bool = False) -> str:
    """Generate Import Coq and Extern Coq annotation blocks.

    Args:
        basename: Output file basename without _rel.c suffix (e.g. "sll_copy")
        func_infos: List of dicts from collect_func_extern_info (only non-None entries)
        needs_maketuple: Whether to declare maketuple in the Extern Coq block
    """
    if not func_infos:
        return ''

    lines = []

    # Import Coq
    lines.append(f'/*@ Import Coq Require Import {basename}_rel_lib */')

    # Functions that actually reference MretTy (i.e. have a loop program).
    # When there are 2+ such functions in one file the rel_lib uses per-
    # function `{fn}_MretTy` names to avoid result-type clashes after merge;
    # mirror that here so the _rel.c references the same symbols.
    mretty_users = [
        info for info in func_infos
        if info.get('has_loop_program', info['inv_var_count'] > 0)
    ]
    per_function_mretty = len(mretty_users) >= 2

    def _mretty_for(info):
        return f"{info['func_name']}_MretTy" if per_function_mretty else "MretTy"

    # Extern Coq type constructors.  Only emit MretTy when at least one
    # function in this file actually has a loop program that references it;
    # a no-loop / recursive-only file has no MretTy users and the shared
    # `MretTy :: *` would dangle (nothing else in the block uses it).
    if per_function_mretty:
        for info in mretty_users:
            lines.append(f'/*@ Extern Coq ({_mretty_for(info)} :: *) */')
    elif mretty_users:
        lines.append('/*@ Extern Coq (MretTy :: *) */')
    if any(
        info.get('needs_early_result', False)
        or info.get('has_pre_loop_early_return', False)
        or info.get('has_loop_body_early_return', False)
        for info in func_infos
    ):
        lines.append('/*@ Extern Coq (early_result :: * => * => *) */')

    # Extern Coq with program declarations
    decl_lines = []
    if needs_maketuple:
        decl_lines.append('(maketuple: {A} {B} -> A -> B -> (A * B))')

    for info in func_infos:
        fn = info['func_name']
        has_loop_program = info.get('has_loop_program', info['inv_var_count'] > 0)
        has_pre_loop_early_return = info.get('has_pre_loop_early_return', False)
        has_loop_body_early_return = info.get('has_loop_body_early_return', False)
        req_count = info['require_var_count']
        inv_count = info['inv_var_count']
        ens_count = info.get('ensure_var_count', 1)
        req_types = _normalize_var_types(info.get('require_var_types'), req_count)
        inv_types = _normalize_var_types(info.get('inv_var_types'), inv_count)
        ens_types = _normalize_var_types(info.get('ensure_var_types'), ens_count)
        ret_type = _return_type(ens_types, ens_count)
        state_type = _tuple_type(inv_types) if inv_types else "unit"
        mretty = _mretty_for(info)

        # {func}_M: t1 -> ... -> program unit (r1 [* r2 ...])
        req_args = _curried_type(req_types)
        decl_lines.append(f'({fn}_M: {req_args}program unit {ret_type})')

        if has_loop_program:
            loop_templates = info.get('loop_templates') or []
            if len(loop_templates) > 1:
                # Forest case: emit per-loop ``_M_loop{k}`` declarations and
                # one ``_M_loop{k}_end`` per top-level loop (the only ones
                # the forest scaffold concretely defines an ``end`` for).
                for t in loop_templates:
                    k = t['loop_index'] + 1
                    loop_inv_args = _curried_type(t['inv_var_types']) if t['inv_var_types'] else ""
                    decl_lines.append(
                        f'({fn}_M_loop{k}: {loop_inv_args}program unit {mretty})'
                    )
                for t in loop_templates:
                    if t.get('parent') is not None:
                        continue
                    k = t['loop_index'] + 1
                    # Expose ``_tail`` (the full residual from this loop
                    # to function return) — the Inv binding uses this.
                    # ``_end`` is still a Parameter in the lib (the LLM
                    # fills it) but is internal to the lib's M
                    # composition; the rel.c never references it.
                    decl_lines.append(
                        f'({fn}_M_loop{k}_tail: {mretty} -> program unit {ret_type})'
                    )
            else:
                # {func}_M_loop: t1 -> ... -> program unit {mretty}
                inv_args = _curried_type(inv_types)
                if has_loop_body_early_return:
                    loop_ret_type = _early_result_type(mretty, ret_type)
                    decl_lines.append(f'({fn}_M_loop: {inv_args}program unit ({loop_ret_type}))')
                else:
                    decl_lines.append(f'({fn}_M_loop: {inv_args}program unit {mretty})')

                # {func}_M_loop_end: {mretty} -> program unit (r1 [* r2 ...])
                decl_lines.append(f'({fn}_M_loop_end: {mretty} -> program unit {ret_type})')
                if has_loop_body_early_return:
                    decl_lines.append(
                        f'({fn}_M_after_loop: {_early_result_type(mretty, ret_type)} -> program unit {ret_type})'
                    )
                if has_pre_loop_early_return:
                    decl_lines.append(
                        f'({fn}_M_loop_before: {req_args}program unit ({_early_result_type(state_type, ret_type)}))'
                    )

    # Format multi-line Extern Coq block
    padding = '               '
    formatted = f'/*@ Extern Coq \n'
    formatted += '\n'.join(f'{padding}{d}' for d in decl_lines)
    formatted += f'\n{padding} */'

    lines.append(formatted)

    return '\n'.join(lines)


def insert_blocks_after_includes(content: str, blocks: str) -> str:
    """Insert generated blocks after the last #include line."""
    if not blocks:
        return content

    lines = content.split('\n')
    last_include_idx = -1
    for i, line in enumerate(lines):
        if re.match(r'\s*#include\s+[<"]', line):
            last_include_idx = i

    if last_include_idx >= 0:
        lines.insert(last_include_idx + 1, '')
        lines.insert(last_include_idx + 2, blocks)
    return '\n'.join(lines)


def translate_c_file(input_path: str, output_path: str, monad: str = "staterel") -> bool:
    """
    Translate a C file with shape assertions to use translated assertions.
    """
    # Read the original file
    try:
        with open(input_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        print(f"Error reading file {input_path}: {e}")
        return False

    # Process the file to get translations
    try:
        result = process_and_translate_file(input_path, generate_guards=False)
    except Exception as e:
        print(f"Error processing file {input_path}: {e}")
        return False

    if 'error' in result:
        print(f"Error in result: {result['error']}")
        return False

    # Collect extern info for Coq blocks
    func_infos = []

    # If we have multiple functions (new logic), process each
    if 'functions' in result and result['functions']:
        callee_functions = collect_callee_functions(content, result['functions'])
        for func_data in result['functions']:
            func_name = func_data['function']
            program = f"{func_name}_M"
            program_loop = f"{func_name}_M_loop"
            program_loop_end = f"{func_name}_M_loop_end"
            program_after_loop = f"{func_name}_M_after_loop"
            try:
                func_source = _extract_function_source(input_path, func_name)
            except Exception:
                func_source = None
            early_shape = detect_early_return_shape(func_source) if func_source else {
                'has_top_level_loop': False,
                'has_pre_loop_early_return': False,
                'has_loop_body_early_return': False,
                'needs_early_result': False,
            }

            # 1. Replace Specs
            content = replace_funcspec(
                content,
                func_name,
                func_data.get('funcspec'),
                program,
                is_callee_funcspec=func_name in callee_functions,
                return_type=func_data.get('return_type', ''),
            )

            # Per-Inv program names for the forest case — each Inv references
            # its own loop's ``_M_loop{k}`` / ``_M_loop{k}_end`` so the
            # generated ``_rel.c`` aligns with the forest scaffold.
            per_inv_programs = _build_per_inv_programs(
                func_name, func_data.get('inner_assertions', []), func_source,
            )

            # 2. Replace Inners
            content = replace_inner_assertions_for_func(
                content,
                func_name,
                func_data.get('inner_assertions', []),
                program_loop,
                program_after_loop if early_shape['has_loop_body_early_return'] else program_loop_end,
                per_inv_programs=per_inv_programs,
            )

            # 3. Collect extern info
            info = collect_func_extern_info(
                func_data,
                include_helpers=True,
                function_source=func_source,
            )
            if info:
                info['loop_templates'] = _loop_template_summary(
                    func_data.get('inner_assertions', []), func_source,
                )
                func_infos.append(info)
    else:
        # Fallback to single-function mode (original behavior)
        func_name = result['function']
        program = f"{func_name}_M"
        program_loop = f"{func_name}_M_loop"
        program_loop_end = f"{func_name}_M_loop_end"
        program_after_loop = f"{func_name}_M_after_loop"
        callee_functions = collect_callee_functions(content, [{'function': func_name}])
        try:
            func_source = _extract_function_source(input_path, func_name)
        except Exception:
            func_source = None
        early_shape = detect_early_return_shape(func_source) if func_source else {
            'has_top_level_loop': False,
            'has_pre_loop_early_return': False,
            'has_loop_body_early_return': False,
            'needs_early_result': False,
        }
        content = replace_funcspec(
            content,
            func_name,
            result.get('funcspec'),
            program,
            is_callee_funcspec=func_name in callee_functions,
            return_type=result.get('return_type', ''),
        )
        per_inv_programs = _build_per_inv_programs(
            func_name, result.get('inner_assertions', []), func_source,
        )
        content = replace_inner_assertions_original(
            content,
            func_name,
            result.get('inner_assertions', []),
            program_loop,
            program_after_loop if early_shape['has_loop_body_early_return'] else program_loop_end,
            per_inv_programs=per_inv_programs,
        )

        # Collect extern info for single-function mode
        info = collect_func_extern_info(
            result,
            include_helpers=True,
            function_source=func_source,
        )
        if info:
            info['loop_templates'] = _loop_template_summary(
                result.get('inner_assertions', []), func_source,
            )
            func_infos.append(info)

    # Translate header file includes
    content = translate_headers(content)

    # Insert safeexec_def.h include, unless a header already includes it
    # (directly or transitively).  Search:
    #   - the input directory (for unmapped headers shipped alongside the .c),
    #   - the output directory (for mapped data headers like
    #     `glibc_slist_clean_data.h` that live next to the generated _rel.c).
    header_search_dirs = [
        os.path.dirname(os.path.abspath(input_path)),
        os.path.dirname(os.path.abspath(output_path)),
    ]
    content = insert_safeexec_include(content, header_search_dirs=header_search_dirs, monad=monad)

    # Generate and insert Coq blocks
    basename = os.path.splitext(os.path.basename(output_path))[0]
    # Strip _rel suffix to get the base name for the lib import
    if basename.endswith('_rel'):
        lib_basename = basename[:-4]
    else:
        lib_basename = basename
    coq_blocks = generate_coq_blocks(lib_basename, func_infos, needs_maketuple='maketuple(' in content)
    content = insert_blocks_after_includes(content, coq_blocks)

    # Write the output file
    try:
        os.makedirs(os.path.dirname(output_path), exist_ok=True)
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(content)
        return True
    except Exception as e:
        print(f"Error writing file {output_path}: {e}")
        return False


def replace_funcspec(
    content: str,
    func_name: str,
    funcspec: Optional[Dict],
    program: str,
    is_callee_funcspec: bool = False,
    return_type: str = "",
) -> str:
    if not funcspec:
        return content

    processed = process_funcspec_with_safeexec(
        funcspec, program, return_type=return_type
    )

    spec_comments = [_format_funcspec_comment(_build_funcspec_parts(processed))]
    if is_callee_funcspec:
        spec_comments = [
            _format_funcspec_comment(_build_funcspec_parts(processed), header="low_level_spec"),
            _build_helper_aux_funcspec(processed, funcspec, program, return_type=return_type),
        ]
    rendered_spec = "\n".join(spec_comments)

    # Simplified but robust pattern: find function name, then the annotation block before or after it
    # The original tests expect the spec to be replaced correctly.
    
    # Original pattern from the codebase (re-implemented robustly)
    func_pattern = (
        rf'((?:[a-zA-Z_][a-zA-Z0-9_\s\*]*?)\b{re.escape(func_name)}\s*\([^)]*\)\s*)'
        rf'(/\*@.*?\*/)'
    )
    
    # If it matches func(...) /*@ ... */
    if re.search(func_pattern, content, re.DOTALL):
        def replace_spec(match):
            header_prefix = match.group(1)
            if is_callee_funcspec:
                return _render_helper_funcspec_declarations(
                    header_prefix,
                    spec_comments[0],
                    spec_comments[1],
                )
            return f"{header_prefix}{rendered_spec}"
        return re.sub(func_pattern, replace_spec, content, flags=re.DOTALL)
    
    # Try the case where /*@ ... */ is BEFORE func(...)
    # This is more complex because we don't want to match a different function's spec
    # We'll use a more specialized approach: look for /*@ ... */ then optional whitespace/return types then the func header
    before_pattern = rf'(/\*@\s*(?:(?!/\*@).)*?\*/)(\s*(?:[a-zA-Z_][a-zA-Z0-9_\s\*]*?)\b{re.escape(func_name)}\s*\([^)]*\)\s*[;{{])'

    
    match = re.search(before_pattern, content, re.DOTALL)
    if match:
        spec_comment = match.group(1)
        func_header = match.group(2)
        if is_callee_funcspec:
            stripped_header = func_header.strip()
            if stripped_header.endswith(';'):
                header_decl = stripped_header[:-1].rstrip()
                repeated = _render_helper_funcspec_declarations(
                    header_decl,
                    spec_comments[0],
                    spec_comments[1],
                )
                return content.replace(spec_comment + func_header, repeated + ";")
        return content.replace(spec_comment + func_header, rendered_spec + func_header)

    return content


def _loop_template_summary(
    inner_assertions: list, func_source: Optional[str],
) -> List[dict]:
    """Per-loop descriptor list — thin wrapper over the canonical
    :func:`loop_forest.build_loop_templates`.

    Used by ``generate_coq_blocks`` to emit per-loop Extern Coq declarations
    and by :func:`_build_per_inv_programs` to compute per-loop program names.
    """
    # Lazy import — loop_forest has no upward dependency on this module.
    from GenMonads.absprog.loop_forest import build_loop_templates
    return build_loop_templates("", func_source, inner_assertions)


def _build_per_inv_programs(
    func_name: str, inner_assertions: list, func_source: Optional[str],
) -> List[tuple]:
    """Compute the abstract-program name pair (``M_loop{k}``,
    ``M_loop{k}_end``) for each Inv annotation in source order, when the
    function has multiple loops.  Returns ``[]`` for single-loop / no-loop
    functions (callers fall back to the function-wide ``M_loop`` name).

    The k-th loop (1-based source order) drives the k-th Inv — and only
    top-level loops have a ``_M_loop{k}_end`` Definition in the forest
    scaffold, so nested loops' Inv annotations reuse their nearest top-level
    ancestor's ``_end`` to keep the residual program well-typed.
    """
    summary = _loop_template_summary(inner_assertions, func_source)
    if len(summary) <= 1:
        return []
    by_idx = {t['loop_index']: t for t in summary}

    def _root(loop_idx: int) -> int:
        cur = loop_idx
        while by_idx[cur]['parent'] is not None:
            cur = by_idx[cur]['parent']
        return cur

    invs = [a for a in inner_assertions if a.get('type') == 'Inv' and 'variables' in a]
    pairs: List[tuple] = []
    # The i-th Inv pairs with the i-th LOOP in source order (the summary is
    # already in source order and only contains loops with assigned Invs).
    summary_sorted = sorted(summary, key=lambda t: t['loop_index'])
    for i, t in enumerate(summary_sorted):
        if i >= len(invs):
            break
        k = t['loop_index'] + 1
        root_k = _root(t['loop_index']) + 1
        # Bind the loop's continuation with ``_M_loop{root_k}_tail`` —
        # the residual program from this loop's exit through to the
        # function's return.  For non-terminal top-level loops, the
        # bare ``_end`` Parameter is only the BRIDGE to the next loop;
        # using it would silently under-quantify the residual.  The
        # forest scaffold emits a ``Definition M_loop{k}_tail`` for
        # every top-level loop (the last one is just an alias of
        # ``_end``, so semantics are preserved everywhere).
        pairs.append((
            f"{func_name}_M_loop{k}",
            f"{func_name}_M_loop{root_k}_tail",
        ))
    return pairs


def _loop_program_names(
    i: int,
    program_loop: str,
    program_loop_end: str,
    per_inv_programs: Optional[List[tuple]] = None,
) -> tuple:
    """Pick the abstract-program names to wrap the *i*-th Inv with.

    When *per_inv_programs* is supplied (multi-loop / forest case) and indexes
    into the list, use its loop-indexed names — otherwise fall back to the
    function-wide single-loop names.
    """
    if per_inv_programs and i < len(per_inv_programs):
        return per_inv_programs[i]
    return program_loop, program_loop_end


def replace_inner_assertions_original(
    content: str,
    func_name: str,
    inner_assertions: list,
    program_loop: str,
    program_loop_end: str,
    per_inv_programs: Optional[List[tuple]] = None,
) -> str:
    """Original implementation of replace_inner_assertions."""
    if not inner_assertions:
        return content
    # Match both ``/*@ Inv ... */`` and bare ``/*@ Assert ... */``
    # proof-checkpoint annotations.  ``Inv`` is tried first in the
    # alternation so ``/*@ Inv Assert ... */`` matches as ``Inv`` (the
    # nested ``Assert`` keyword is stripped by the preprocessor and
    # tracked via ``assertion['inv_assert']``).
    annot_pattern = r'/\*@\s*(Inv|Assert)\s+(.*?)\s*\*/'
    matches = list(re.finditer(annot_pattern, content, flags=re.DOTALL))
    for i, match in enumerate(reversed(matches)):
        assertion_index = len(matches) - 1 - i
        if assertion_index < len(inner_assertions):
            assertion = inner_assertions[assertion_index]
            keyword = match.group(1)
            if (keyword == 'Inv'
                    and assertion['type'] == 'Inv'
                    and 'translated' in assertion):
                pl, ple = _loop_program_names(
                    assertion_index, program_loop, program_loop_end, per_inv_programs,
                )
                with_safeexec = add_safeexec_predicate(
                    assertion['translated'],
                    assertion['variables'],
                    pl,
                    ple,
                )
                kw = "Inv Assert" if assertion.get('inv_assert') else "Inv"
                new_comment = f"/*@ {kw} {with_safeexec} */"
                content = content[:match.start()] + new_comment + content[match.end():]
            elif (keyword == 'Assert'
                    and assertion['type'] == 'Assert'
                    and 'translated' in assertion):
                # Bare Assert blocks are intermediate proof checkpoints
                # — no safeExec wrapping (they don't bind a loop's
                # abstract state); just emit the shape→data rewritten
                # body.
                new_comment = f"/*@ Assert {assertion['translated']} */"
                content = content[:match.start()] + new_comment + content[match.end():]
    return content


def replace_inner_assertions_for_func(
    content: str,
    func_name: str,
    inner_assertions: list,
    program_loop: str,
    program_loop_end: str,
    per_inv_programs: Optional[List[tuple]] = None,
) -> str:
    """Targeted replacement for one function's body."""
    # Find the body
    pattern = (
        rf'\b{re.escape(func_name)}\s*\((?:[^)]*)\)\s*'
        rf'(?:/\*@.*?\*/\s*)?\{{'
    )
    match = re.search(pattern, content, re.DOTALL)
    if not match: return content

    start = match.end()
    brace_count, pos = 1, start
    while pos < len(content) and brace_count > 0:
        if content[pos] == '{': brace_count += 1
        elif content[pos] == '}': brace_count -= 1
        pos += 1
    if brace_count != 0: return content

    body = content[start:pos-1]

    # Same alternation as the file-wide variant — see comment above.
    annot_pattern = r'/\*@\s*(Inv|Assert)\s+(.*?)\s*\*/'
    matches = list(re.finditer(annot_pattern, body, flags=re.DOTALL))

    for i, match in enumerate(reversed(matches)):
        assertion_index = len(matches) - 1 - i
        if assertion_index < len(inner_assertions):
            assertion = inner_assertions[assertion_index]
            keyword = match.group(1)
            if (keyword == 'Inv'
                    and assertion['type'] == 'Inv'
                    and 'translated' in assertion):
                pl, ple = _loop_program_names(
                    assertion_index, program_loop, program_loop_end, per_inv_programs,
                )
                with_safeexec = add_safeexec_predicate(
                    assertion['translated'],
                    assertion['variables'],
                    pl,
                    ple,
                )
                kw = "Inv Assert" if assertion.get('inv_assert') else "Inv"
                new_text = f"/*@ {kw} {with_safeexec} */"
                body = body[:match.start()] + new_text + body[match.end():]
            elif (keyword == 'Assert'
                    and assertion['type'] == 'Assert'
                    and 'translated' in assertion):
                new_text = f"/*@ Assert {assertion['translated']} */"
                body = body[:match.start()] + new_text + body[match.end():]

    return content[:start] + body + content[pos-1:]

def translate_directory(input_dir: str, output_dir: str, monad: str = "staterel") -> Dict[str, bool]:
    results = {}
    if not os.path.exists(input_dir):
        print(f"Error: Input directory not found: {input_dir}")
        return results
    os.makedirs(output_dir, exist_ok=True)
    for filename in os.listdir(input_dir):
        if filename.endswith('.c'):
            input_path = os.path.join(input_dir, filename)
            base_name = os.path.splitext(filename)[0]
            output_filename = f"{base_name}_rel.c"
            output_path = os.path.join(output_dir, output_filename)
            print(f"Processing {filename}...", end=' ')
            success = translate_c_file(input_path, output_path, monad=monad)
            results[filename] = success
            if success: print(f"OK -> {output_filename}")
            else: print("FAILED")
    return results

def _build_main_parser():
    import argparse
    parser = argparse.ArgumentParser(
        description='Translate C files with shape assertions, generate the rel_lib.v template, and run synthesis'
    )
    add_input_path_arguments(parser, 'Input C file or directory')
    add_output_path_argument(parser, 'output', 'Output C file or directory')
    parser.add_argument(
        '--no-rel-lib', action='store_true',
        help='Skip stage 2 (rel_lib.v template generation). Incompatible with running synthesis.',
    )
    parser.add_argument(
        '--coq-lib-dir',
        help='Directory for the generated _rel_lib.v template (overrides COQ_LIB_DIR).',
    )
    parser.add_argument(
        '--no-synth', action='store_true',
        help='Skip stage 3 (LLM synthesis). Synthesis runs by default.',
    )
    parser.add_argument(
        '--synth-output-dir',
        help='Directory for synthesis artifacts. Required unless --no-synth is set.',
    )
    parser.add_argument(
        '--backend', choices=['gold-example', 'response-file', 'command'],
        default=LLM4PV_DEFAULT_BACKEND,
        help=f'Synthesis backend (default: {LLM4PV_DEFAULT_BACKEND}).',
    )
    parser.add_argument(
        '--command', default=LLM4PV_DEFAULT_COMMAND,
        help=f'Shell command for the command backend (default: {LLM4PV_DEFAULT_COMMAND!r}).',
    )
    parser.add_argument('--replay-from', help='Auto-example JSON for the gold-example backend.')
    parser.add_argument('--response-file', help='Raw LLM response file for the response-file backend.')
    parser.add_argument(
        '--few-shot', action='append', default=[],
        help='Few-shot example JSON to embed into the prompt (repeatable).',
    )
    parser.add_argument(
        '--max-retries', type=int, default=LLM4PV_DEFAULT_MAX_RETRIES,
        help=f'Number of repair attempts after the initial attempt (default: {LLM4PV_DEFAULT_MAX_RETRIES}).',
    )
    from GenMonads.absprog.synthesize import DEFAULT_COMMAND_TIMEOUT_SECONDS
    parser.add_argument(
        '--command-timeout', type=int, default=DEFAULT_COMMAND_TIMEOUT_SECONDS,
        help=(
            f'Timeout (seconds) for each command-backend call (default: '
            f'{DEFAULT_COMMAND_TIMEOUT_SECONDS}s).  Pass 0 to disable.'
        ),
    )
    parser.add_argument(
        '--no-check', action='store_true',
        help='Skip the Rocq syntax check step in synthesis.',
    )
    parser.add_argument(
        '--no-patch-rel-c', action='store_true',
        help='Do not patch the generated _rel.c after synthesis (patching is on by default).',
    )
    parser.add_argument(
        '--sibling-dir', action='append', default=[],
        help=(
            'Directory to search for sibling callee .c files (repeatable). '
            'Replaces the default of the input file\'s own directory.'
        ),
    )
    parser.add_argument(
        '--monad', choices=['staterel', 'staterr'], default='staterel',
        help=(
            "Monad backend for the generated rel_lib: 'staterel' (StateRelMonad, "
            "default) or 'staterr' (error-aware MonadErr)."
        ),
    )
    parser.add_argument(
        '--use-block-renderer', action='store_true', default=False,
        help=(
            "Phase 2 feature flag.  When set, callee-only straight-line "
            "(Shape 1) functions emit a fully concrete `Definition fn_M := …` "
            "instead of `Parameter fn_M`, eliminating the LLM hole for those "
            "functions.  Falls back to `Parameter` automatically for any "
            "function the renderer can't translate mechanically.  Default "
            "off: legacy behavior is preserved."
        ),
    )
    return parser


def _topo_sort_c_files(c_files):
    """Order ``c_files`` so callees come before callers.

    ``c_files`` is a list of ``(src, rel_c)`` tuples. Cross-file edges are
    detected by scanning each source for calls to *other* source basenames in
    the same list (matches what stage 2 / stage 3 import via
    ``Require Import {callee}_rel_lib``). If a cycle is detected, the original
    order is returned with a warning printed.
    """
    from GenMonads.absprog.gen_rel_lib import (
        _C_KEYWORDS_AND_BUILTINS,
        _collect_cross_file_callees,
    )

    basename_of = {src: os.path.splitext(os.path.basename(src))[0] for src, _ in c_files}
    pair_by_src = {src: (src, rel_c) for src, rel_c in c_files}
    basenames = set(basename_of.values())

    deps = {src: set() for src, _ in c_files}
    func_def_re = re.compile(
        r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\([^;{}]*\)\s*(?:/\*@[^*]*(?:\*(?!/)[^*]*)*\*/\s*)?\{",
        re.DOTALL,
    )
    for src, _ in c_files:
        try:
            with open(src, "r", encoding="utf-8") as f:
                content = f.read()
        except OSError:
            continue
        func_names = [
            m.group(1) for m in func_def_re.finditer(content)
            if m.group(1) not in _C_KEYWORDS_AND_BUILTINS
        ]
        if not func_names:
            continue
        callees = _collect_cross_file_callees(src, func_names, content)
        for callee in callees:
            if callee in basenames and callee != basename_of[src]:
                callee_src = next(s for s, b in basename_of.items() if b == callee)
                deps[src].add(callee_src)

    ordered = []
    visiting = set()
    visited = set()
    cycle_detected = [False]

    def visit(node):
        if node in visited:
            return
        if node in visiting:
            cycle_detected[0] = True
            return
        visiting.add(node)
        for dep in sorted(deps[node]):
            visit(dep)
        visiting.discard(node)
        visited.add(node)
        ordered.append(node)

    for src, _ in sorted(c_files):
        visit(src)

    if cycle_detected[0]:
        print(
            "Warning: cyclic cross-file callee dependency detected; "
            "falling back to alphabetical order.",
            file=sys.stderr,
        )
        return sorted(c_files)

    return [pair_by_src[src] for src in ordered]


def _run_stage2(
    input_c: str, lib_dir: str, sibling_dirs: Optional[List[str]] = None,
    monad: str = "staterel", use_block_renderer: bool = False,
) -> Optional[str]:
    """Generate the _rel_lib.v template. Returns the lib path or None on failure."""
    from GenMonads.absprog.gen_rel_lib import generate_rel_lib_for_file
    return generate_rel_lib_for_file(
        input_c, lib_dir, sibling_dirs=sibling_dirs, monad=monad,
        use_block_renderer=use_block_renderer,
    )


def _run_stage3(input_c: str, rel_c_path: str, args) -> int:
    """Run the synthesis pipeline. Returns 0 on success, nonzero otherwise."""
    from GenMonads.absprog.synth_cli import main as synth_main
    synth_argv = [
        'llm4pv-synth',
        f'--FILE={input_c}',
        f'--OUTPUT_PATH={args.synth_output_dir}',
        f'--backend={args.backend}',
        f'--max-retries={args.max_retries}',
        f'--command-timeout={args.command_timeout}',
        f'--monad={args.monad}',
    ]
    # Forward the per-invocation lib dir so the synth pre-spawn check looks
    # at the same place the rel_lib stage wrote to (instead of falling back
    # to CONFIGURE's default).  Without this, --coq-lib-dir was honored at
    # rel_lib time but ignored at synth time → callee-libs-missing errors.
    if args.coq_lib_dir:
        synth_argv += [f'--coq-lib-dir={args.coq_lib_dir}']
    if getattr(args, 'use_block_renderer', False):
        synth_argv += ['--use-block-renderer']
    if args.backend == 'command' and args.command:
        synth_argv += ['--command', args.command]
    if args.replay_from:
        synth_argv += [f'--replay-from={args.replay_from}']
    if args.response_file:
        synth_argv += [f'--response-file={args.response_file}']
    for fs in args.few_shot:
        synth_argv += ['--few-shot', fs]
    for sd in (args.sibling_dir or []):
        synth_argv += ['--sibling-dir', sd]
    if args.no_check:
        synth_argv.append('--no-check')
    if not args.no_patch_rel_c:
        synth_argv += ['--patch-rel-c', f'--rel-c-path={rel_c_path}']

    saved_argv = sys.argv
    sys.argv = synth_argv
    try:
        synth_main()
    except SystemExit as exc:
        return int(exc.code or 0)
    finally:
        sys.argv = saved_argv
    return 0


def _resolve_lib_dir(args, parser) -> str:
    if args.coq_lib_dir:
        return os.path.normpath(args.coq_lib_dir)
    configured = read_configure_value("COQ_LIB_DIR")
    if configured:
        return os.path.normpath(configured)
    parser.error(
        "No rel_lib output directory. Set COQ_LIB_DIR in CONFIGURE/env or pass --coq-lib-dir."
    )


def main():
    parser = _build_main_parser()
    args = parser.parse_args()

    input_path = resolve_cli_value(
        args, parser, 'input', ('file_path', 'c_dir'),
        'Provide an input path via positional input, --FILE, or --C_DIR.',
        is_path=True,
    )
    output_path = resolve_cli_value(
        args, parser, 'output', ('output_path',),
        'Provide an output path via positional output or --OUTPUT_PATH.',
        is_path=True,
    )

    run_synth = not args.no_synth
    run_lib = not args.no_rel_lib

    if run_synth and not run_lib:
        parser.error(
            "synth requires the rel_lib template; pass --no-synth or drop --no-rel-lib."
        )
    if run_synth and not args.synth_output_dir:
        parser.error("--synth-output-dir is required when synthesis is enabled (default).")

    lib_dir = _resolve_lib_dir(args, parser) if run_lib else None

    # ---- Stage 1 ----
    if os.path.isdir(input_path):
        results = translate_directory(input_path, output_path, monad=args.monad)
        total, success = len(results), sum(1 for v in results.values() if v)
        print(f"\nSummary: {success}/{total} files translated successfully")
        if success != total:
            sys.exit(1)
        c_files = sorted(
            (
                os.path.join(input_path, f),
                os.path.join(output_path, f"{os.path.splitext(f)[0]}_rel.c"),
            )
            for f in os.listdir(input_path) if f.endswith('.c')
        )
        if run_lib or run_synth:
            c_files = _topo_sort_c_files(c_files)
            order_names = [os.path.basename(src) for src, _ in c_files]
            print(f"Processing order (callees first): {', '.join(order_names)}")
        directory_mode = True
    else:
        ok = translate_c_file(input_path, output_path, monad=args.monad)
        if not ok:
            print("Translation failed", file=sys.stderr)
            sys.exit(1)
        print(f"Translation successful: {output_path}")
        c_files = [(input_path, output_path)]
        directory_mode = False

    # Pre-filter: a file is "synthesizable" only if it exposes at least one
    # context that needs scaffolding.  Callee-only declarations and files
    # without translated funcspecs return zero contexts and are silently
    # skipped in stages 2 and 3.  Only invoke the collector when a later
    # stage actually consumes the result.
    if run_lib or run_synth:
        from GenMonads.absprog.context import collect_all_synthesis_contexts
        synthesizable = []
        for src, rel_c in c_files:
            try:
                contexts = collect_all_synthesis_contexts(src)
            except Exception as exc:
                print(f"context collection failed for {src}: {exc}", file=sys.stderr)
                sys.exit(2)
            if contexts:
                synthesizable.append((src, rel_c))
            else:
                print(f"Skipped (no synthesis targets): {src}")
    else:
        synthesizable = list(c_files)

    # ---- Stage 2 ----
    if run_lib:
        lib_failures = []
        for src, _ in synthesizable:
            lib_path = _run_stage2(
                src, lib_dir, sibling_dirs=(args.sibling_dir or None),
                monad=args.monad,
                use_block_renderer=args.use_block_renderer,
            )
            if not lib_path:
                print(f"rel_lib generation failed: {src}", file=sys.stderr)
                lib_failures.append(src)
            else:
                print(f"rel_lib generated: {lib_path}")
        if lib_failures:
            sys.exit(2)

    # ---- Stage 3 ----
    if run_synth:
        synth_failures = []
        for src, rel_c in synthesizable:
            print(f"\n=== synth: {src} ===")
            code = _run_stage3(src, rel_c, args)
            if code != 0:
                synth_failures.append(src)
        if synth_failures:
            sys.exit(1)

    if directory_mode:
        print(
            f"\nAll done: {len(c_files)} rel.c"
            + (f", {len(c_files)} rel_lib.v" if run_lib else "")
            + (f", synth ran on {len(c_files)} files" if run_synth else "")
        )

if __name__ == "__main__":
    main()
