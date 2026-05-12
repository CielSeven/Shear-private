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
    resolve_cli_value,
)
from GenMonads.transshape.process_and_translate import process_and_translate_file
from GenMonads.addabstract import add_safeexec_predicate, process_funcspec_with_safeexec
from GenMonads.addabstract.addexec import (
    _is_void_return_type,
    extract_variables_from_assertion,
)
from GenMonads.header_mapping import translate_headers


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


def _quoted_includes(content: str) -> List[str]:
    """Return the list of ``#include "<name>"`` filenames in *content*."""
    return re.findall(r'^\s*#include\s+"([^"]+)"', content, flags=re.MULTILINE)


def _header_includes_safeexec(
    header_name: str,
    search_dirs: List[str],
    visited: Optional[Set[str]] = None,
) -> bool:
    """Return True if *header_name* (or any header it #includes, recursively)
    contains ``#include "safeexec_def.h"``.

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
        if _SAFEEXEC_HEADER_NAME in header_text:
            return True
        # Recurse into nested ``#include "..."`` directives.
        for nested in _quoted_includes(header_text):
            if nested == header_name:
                continue
            nested_dirs = [os.path.dirname(real)] + search_dirs
            if _header_includes_safeexec(nested, nested_dirs, visited):
                return True
        return False
    return False


def insert_safeexec_include(
    content: str,
    header_search_dirs: Optional[List[str]] = None,
) -> str:
    """Insert ``#include "safeexec_def.h"`` after the last ``#include`` line,
    unless it is already present in *content* or transitively reachable via
    one of the headers ``#include``d from *content*.

    *header_search_dirs* is the list of directories to look in when chasing
    quoted-form includes (usually the input C file's directory).  When
    omitted, only the literal text of *content* is checked.
    """
    if _SAFEEXEC_HEADER_NAME in content:
        return content

    if header_search_dirs:
        for header in _quoted_includes(content):
            if _header_includes_safeexec(header, header_search_dirs):
                return content

    lines = content.split('\n')
    last_include_idx = -1
    for i, line in enumerate(lines):
        if re.match(r'\s*#include\s+[<"]', line):
            last_include_idx = i

    if last_include_idx >= 0:
        lines.insert(last_include_idx + 1, f'#include "{_SAFEEXEC_HEADER_NAME}"')
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


def _build_helper_aux_funcspec(processed: Dict, funcspec: Dict, program: str) -> str:
    """Build the derived continuation-passing helper specification."""
    ret_types, ret_count = _extract_funcspec_return_info(funcspec)
    ret_type = _return_type(ret_types, ret_count)
    base_with = processed.get('with', {}).get('translated', '').strip()
    with_prefix = f"{{B}} (cont: {ret_type} -> program unit B)"
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
        ensure_vars = processed['ensure'].get('variables') or extract_variables_from_assertion(
            processed['ensure'].get('translated', '')
        )
        return_expr = _build_return_call([v.lstrip('?') for v in ensure_vars])
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
    """Repeat a helper declaration so each named spec gets its own prototype."""
    normalized_header = header_decl.rstrip()
    return (
        f"{normalized_header}\n"
        f"{primary_spec};\n"
        f"{normalized_header}\n"
        f"{aux_spec}"
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

    # Extern Coq type constructors
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

        # {func}_M: t1 -> ... -> program unit (r1 [* r2 ...])
        req_args = _curried_type(req_types)
        decl_lines.append(f'({fn}_M: {req_args}program unit {ret_type})')

        if has_loop_program:
            # {func}_M_loop: t1 -> ... -> program unit MretTy
            inv_args = _curried_type(inv_types)
            if has_loop_body_early_return:
                loop_ret_type = _early_result_type("MretTy", ret_type)
                decl_lines.append(f'({fn}_M_loop: {inv_args}program unit ({loop_ret_type}))')
            else:
                decl_lines.append(f'({fn}_M_loop: {inv_args}program unit MretTy)')

            # {func}_M_loop_end: MretTy -> program unit (r1 [* r2 ...])
            decl_lines.append(f'({fn}_M_loop_end: MretTy -> program unit {ret_type})')
            if has_loop_body_early_return:
                decl_lines.append(
                    f'({fn}_M_after_loop: {_early_result_type("MretTy", ret_type)} -> program unit {ret_type})'
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


def translate_c_file(input_path: str, output_path: str) -> bool:
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

            # 2. Replace Inners
            content = replace_inner_assertions_for_func(
                content,
                func_name,
                func_data.get('inner_assertions', []),
                program_loop,
                program_after_loop if early_shape['has_loop_body_early_return'] else program_loop_end
            )

            # 3. Collect extern info
            info = collect_func_extern_info(
                func_data,
                include_helpers=True,
                function_source=func_source,
            )
            if info:
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
        content = replace_inner_assertions_original(
            content,
            func_name,
            result.get('inner_assertions', []),
            program_loop,
            program_after_loop if early_shape['has_loop_body_early_return'] else program_loop_end
        )

        # Collect extern info for single-function mode
        info = collect_func_extern_info(
            result,
            include_helpers=True,
            function_source=func_source,
        )
        if info:
            func_infos.append(info)

    # Translate header file includes
    content = translate_headers(content)

    # Insert safeexec_def.h include, unless a header in the input directory
    # already includes it (directly or transitively).
    header_search_dirs = [os.path.dirname(os.path.abspath(input_path))]
    content = insert_safeexec_include(content, header_search_dirs=header_search_dirs)

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
            _build_helper_aux_funcspec(processed, funcspec, program),
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


def replace_inner_assertions_original(
    content: str,
    func_name: str,
    inner_assertions: list,
    program_loop: str,
    program_loop_end: str
) -> str:
    """Original implementation of replace_inner_assertions."""
    if not inner_assertions:
        return content
    inv_pattern = r'/\*@\s*Inv\s+(.*?)\s*\*/'
    matches = list(re.finditer(inv_pattern, content, flags=re.DOTALL))
    for i, match in enumerate(reversed(matches)):
        assertion_index = len(matches) - 1 - i
        if assertion_index < len(inner_assertions):
            assertion = inner_assertions[assertion_index]
            if assertion['type'] == 'Inv' and 'translated' in assertion:
                with_safeexec = add_safeexec_predicate(
                    assertion['translated'],
                    assertion['variables'],
                    program_loop,
                    program_loop_end
                )
                new_comment = f"/*@ Inv {with_safeexec} */"
                content = content[:match.start()] + new_comment + content[match.end():]
    return content


def replace_inner_assertions_for_func(
    content: str,
    func_name: str,
    inner_assertions: list,
    program_loop: str,
    program_loop_end: str
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
    
    inv_pattern = r'/\*@\s*Inv\s+(.*?)\s*\*/'
    matches = list(re.finditer(inv_pattern, body, flags=re.DOTALL))

    for i, match in enumerate(reversed(matches)):
        assertion_index = len(matches) - 1 - i
        if assertion_index < len(inner_assertions):
            assertion = inner_assertions[assertion_index]
            if assertion['type'] == 'Inv' and 'translated' in assertion:
                with_safeexec = add_safeexec_predicate(
                    assertion['translated'],
                    assertion['variables'],
                    program_loop,
                    program_loop_end
                )
                new_text = f"/*@ Inv {with_safeexec} */"
                body = body[:match.start()] + new_text + body[match.end():]
            
    return content[:start] + body + content[pos-1:]

def translate_directory(input_dir: str, output_dir: str) -> Dict[str, bool]:
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
            success = translate_c_file(input_path, output_path)
            results[filename] = success
            if success: print(f"OK -> {output_filename}")
            else: print("FAILED")
    return results

def main():
    import argparse
    parser = argparse.ArgumentParser(description='Translate C files with shape assertions')
    add_input_path_arguments(parser, 'Input C file or directory')
    add_output_path_argument(parser, 'output', 'Output C file or directory')
    args = parser.parse_args()
    input_path = resolve_cli_value(
        args,
        parser,
        'input',
        ('file_path', 'c_dir'),
        'Provide an input path via positional input, --FILE, or --C_DIR.',
        is_path=True,
    )
    output_path = resolve_cli_value(
        args,
        parser,
        'output',
        ('output_path',),
        'Provide an output path via positional output or --OUTPUT_PATH.',
        is_path=True,
    )
    if os.path.isdir(input_path):
        results = translate_directory(input_path, output_path)
        total, success = len(results), sum(1 for v in results.values() if v)
        print(f"\nSummary: {success}/{total} files translated successfully")
        if success != total:
            sys.exit(1)
    else:
        success = translate_c_file(input_path, output_path)
        if success:
            print(f"Translation successful: {output_path}")
        else:
            print("Translation failed", file=sys.stderr)
            sys.exit(1)

if __name__ == "__main__":
    main()
