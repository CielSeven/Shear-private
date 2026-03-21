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
from typing import Dict, Optional, List

from GenMonads.transshape.process_and_translate import process_and_translate_file
from GenMonads.addabstract import add_safeexec_predicate, process_funcspec_with_safeexec
from GenMonads.addabstract.addexec import extract_variables_from_assertion
from GenMonads.header_mapping import translate_headers


def collect_func_extern_info(func_data: Dict) -> Optional[Dict]:
    """Collect variable counts needed for Extern Coq declarations.

    Returns None if the function has no inner assertions (loop invariants),
    meaning it doesn't need Extern Coq entries (e.g. helper functions).
    """
    inner = func_data.get('inner_assertions', [])
    inv_assertions = [a for a in inner if a.get('type') == 'Inv' and 'variables' in a]
    if not inv_assertions:
        return None

    funcspec = func_data.get('funcspec')
    require_var_count = 0
    require_var_names = []
    if funcspec and funcspec.get('require') and funcspec['require'].get('translated'):
        require_vars = extract_variables_from_assertion(funcspec['require']['translated'])
        require_var_count = len(require_vars)
        require_var_names = [v.lstrip('?') for v in require_vars]

    ensure_var_count = 0
    if funcspec and funcspec.get('ensure') and funcspec['ensure'].get('translated'):
        ensure_vars = extract_variables_from_assertion(funcspec['ensure']['translated'])
        # Only count vars NOT already in Require (those are reused, not returned)
        ensure_only = [v for v in ensure_vars if v.lstrip('?') not in require_var_names]
        ensure_var_count = len(ensure_only)

    inv_var_count = max(len(a['variables']) for a in inv_assertions)

    return {
        'func_name': func_data['function'],
        'require_var_count': require_var_count,
        'inv_var_count': inv_var_count,
        'ensure_var_count': ensure_var_count,
    }


def _return_type(n: int) -> str:
    """Build return type from ensure var count: 1 -> (list Z), 2 -> (list Z * list Z), etc."""
    if n <= 1:
        return "(list Z)"
    return "(" + " * ".join(["list Z"] * n) + ")"


def insert_safeexec_include(content: str) -> str:
    """Insert #include "safeexec_def.h" after the last #include line, if not already present."""
    if 'safeexec_def.h' in content:
        return content

    lines = content.split('\n')
    last_include_idx = -1
    for i, line in enumerate(lines):
        if re.match(r'\s*#include\s+[<"]', line):
            last_include_idx = i

    if last_include_idx >= 0:
        lines.insert(last_include_idx + 1, '#include "safeexec_def.h"')
    return '\n'.join(lines)


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

    # Extern Coq (MretTy :: *)
    lines.append('/*@ Extern Coq (MretTy :: *) */')

    # Extern Coq with program declarations
    decl_lines = []
    if needs_maketuple:
        decl_lines.append('(maketuple: {A} {B} -> A -> B -> (A * B))')

    for info in func_infos:
        fn = info['func_name']
        req_count = info['require_var_count']
        inv_count = info['inv_var_count']
        ens_count = info.get('ensure_var_count', 1)
        ret_type = _return_type(ens_count)

        # {func}_M: list Z -> ... -> program unit (list Z [* list Z ...])
        req_args = ' '.join(['list Z ->'] * req_count) + ' ' if req_count else ''
        decl_lines.append(f'({fn}_M: {req_args}program unit {ret_type})')

        # {func}_M_loop: list Z -> ... -> program unit MretTy
        inv_args = ' '.join(['list Z ->'] * inv_count) + ' ' if inv_count else ''
        decl_lines.append(f'({fn}_M_loop: {inv_args}program unit MretTy)')

        # {func}_M_loop_end: MretTy -> program unit (list Z [* list Z ...])
        decl_lines.append(f'({fn}_M_loop_end: MretTy -> program unit {ret_type})')

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
        for func_data in result['functions']:
            func_name = func_data['function']
            program = f"{func_name}_M"
            program_loop = f"{func_name}_M_loop"
            program_loop_end = f"{func_name}_M_loop_end"

            # 1. Replace Specs
            content = replace_funcspec(content, func_name, func_data.get('funcspec'), program)

            # 2. Replace Inners
            content = replace_inner_assertions_for_func(
                content,
                func_name,
                func_data.get('inner_assertions', []),
                program_loop,
                program_loop_end
            )

            # 3. Collect extern info
            info = collect_func_extern_info(func_data)
            if info:
                func_infos.append(info)
    else:
        # Fallback to single-function mode (original behavior)
        func_name = result['function']
        program = f"{func_name}_M"
        program_loop = f"{func_name}_M_loop"
        program_loop_end = f"{func_name}_M_loop_end"
        content = replace_funcspec(content, func_name, result.get('funcspec'), program)
        content = replace_inner_assertions_original(
            content,
            func_name,
            result.get('inner_assertions', []),
            program_loop,
            program_loop_end
        )

        # Collect extern info for single-function mode
        info = collect_func_extern_info(result)
        if info:
            func_infos.append(info)

    # Translate header file includes
    content = translate_headers(content)

    # Insert safeexec_def.h include
    content = insert_safeexec_include(content)

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


def replace_funcspec(content: str, func_name: str, funcspec: Optional[Dict], program: str) -> str:
    if not funcspec:
        return content

    processed = process_funcspec_with_safeexec(funcspec, program)

    # Simplified but robust pattern: find function name, then the annotation block before or after it
    # The original tests expect the spec to be replaced correctly.
    
    # Original pattern from the codebase (re-implemented robustly)
    func_pattern = rf'(\b{re.escape(func_name)}\s*\([^)]*\)\s*/\*@)(.*?)(\*/)'
    
    # If it matches func(...) /*@ ... */
    if re.search(func_pattern, content, re.DOTALL):
        def replace_spec(match):
            prefix = match.group(1)
            suffix = match.group(3)
            new_parts = []
            if 'with' in processed and processed['with']:
                new_parts.append(f" With {processed['with']['translated']}")
            if 'require' in processed and processed['require']:
                req = processed['require']
                new_parts.append(f" Require {req.get('with_safeexec', req.get('translated', ''))}")
            if 'ensure' in processed and processed['ensure']:
                ens = processed['ensure']
                new_parts.append(f" Ensure {ens.get('with_safeexec', ens.get('translated', ''))}")
            new_spec = '\n   '.join(new_parts)
            return f"{prefix}\n   {new_spec}\n {suffix}"
        return re.sub(func_pattern, replace_spec, content, flags=re.DOTALL)
    
    # Try the case where /*@ ... */ is BEFORE func(...)
    # This is more complex because we don't want to match a different function's spec
    # We'll use a more specialized approach: look for /*@ ... */ then optional whitespace/return types then the func header
    before_pattern = rf'(/\*@\s*(?:(?!/\*@).)*?\*/)(\s*(?:[a-zA-Z_][a-zA-Z0-9_\s\*]*?)\b{re.escape(func_name)}\s*\([^)]*\)\s*[;{{])'

    
    match = re.search(before_pattern, content, re.DOTALL)
    if match:
        spec_comment = match.group(1)
        func_header = match.group(2)
        
        # Strip /*@ and */
        inner_content = spec_comment[3:-2].strip()
        
        new_parts = []
        if 'with' in processed and processed['with']:
            new_parts.append(f" With {processed['with']['translated']}")
        if 'require' in processed and processed['require']:
            req = processed['require']
            new_parts.append(f" Require {req.get('with_safeexec', req.get('translated', ''))}")
        if 'ensure' in processed and processed['ensure']:
            ens = processed['ensure']
            new_parts.append(f" Ensure {ens.get('with_safeexec', ens.get('translated', ''))}")
        
        new_spec = '/*@ ' + '\n   '.join(new_parts) + '\n */'
        return content.replace(spec_comment + func_header, new_spec + func_header)

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
            if success: print(f"✓ -> {output_filename}")
            else: print(f"✗ Failed")
    return results

def main():
    import argparse
    parser = argparse.ArgumentParser(description='Translate C files with shape assertions')
    parser.add_argument('input', help='Input C file or directory')
    parser.add_argument('output', help='Output C file or directory')
    args = parser.parse_args()
    if os.path.isdir(args.input):
        results = translate_directory(args.input, args.output)
        total, success = len(results), sum(1 for v in results.values() if v)
        print(f"\nSummary: {success}/{total} files translated successfully")
    else:
        success = translate_c_file(args.input, args.output)
        if success: print(f"✓ Translation successful: {args.output}")
        else: print(f"✗ Translation failed")

if __name__ == "__main__":
    main()
