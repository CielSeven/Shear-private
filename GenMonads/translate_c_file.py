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
from typing import Dict, Optional

from GenMonads.transshape.process_and_translate import process_and_translate_file
from GenMonads.addabstract import add_safeexec_predicate, process_funcspec_with_safeexec
from GenMonads.header_mapping import translate_headers


def translate_c_file(input_path: str, output_path: str) -> bool:
    """
    Translate a C file with shape assertions to use translated assertions.

    Args:
        input_path: Path to input C file (e.g., 'sll_copy.c')
        output_path: Path to output C file (e.g., 'sll_copy_rel.c')

    Returns:
        True if successful, False otherwise
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

    # Get function name for abstract programs
    func_name = result['function']
    program = f"{func_name}_M"
    program_loop = f"{func_name}_M_loop"
    program_loop_end = f"{func_name}_M_loop_end"

    # Replace function specification with safeExec
    content = replace_funcspec(content, func_name, result.get('funcspec'), program)

    # Replace inner assertions (loop invariants)
    content = replace_inner_assertions(
        content,
        func_name,
        result.get('inner_assertions', []),
        program_loop,
        program_loop_end
    )

    # Translate header file includes
    content = translate_headers(content)

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
    """
    Replace function specification with translated version including safeExec.

    Args:
        content: Original file content
        func_name: Function name
        funcspec: Translated function specification dictionary
        program: Abstract program name (e.g., 'sll_copy_M')

    Returns:
        Updated content with replaced function specification
    """
    if not funcspec:
        return content

    # Process funcspec to add safeExec predicates
    processed = process_funcspec_with_safeexec(funcspec, program)

    # Find the function specification comment
    # Pattern: function_name(...) /*@ ... */
    func_pattern = rf'({re.escape(func_name)}\s*\([^)]*\)\s*/\*@)(.*?)(\*/)'

    def replace_spec(match):
        prefix = match.group(1)  # function_name(...) /*@
        original_spec = match.group(2)  # original spec content
        suffix = match.group(3)  # */

        # Build the new specification
        new_spec_parts = []

        # With clause (translated version includes X parameter)
        if 'with' in processed and processed['with']:
            with_translated = processed['with']['translated']
            new_spec_parts.append(f" With {with_translated}")

        # Require clause with safeExec
        if 'require' in processed and processed['require']:
            require = processed['require']
            if 'with_safeexec' in require:
                new_spec_parts.append(f" Require {require['with_safeexec']}")
            elif 'translated' in require:
                new_spec_parts.append(f" Require {require['translated']}")

        # Ensure clause with safeExec
        if 'ensure' in processed and processed['ensure']:
            ensure = processed['ensure']
            if 'with_safeexec' in ensure:
                new_spec_parts.append(f" Ensure {ensure['with_safeexec']}")
            elif 'translated' in ensure:
                new_spec_parts.append(f" Ensure {ensure['translated']}")

        # Join with newlines
        new_spec = '\n   '.join(new_spec_parts)

        return f"{prefix}\n   {new_spec}\n {suffix}"

    content = re.sub(func_pattern, replace_spec, content, flags=re.DOTALL)

    return content


def replace_inner_assertions(
    content: str,
    func_name: str,
    inner_assertions: list,
    program_loop: str,
    program_loop_end: str
) -> str:
    """
    Replace inner assertions (loop invariants) with translated versions + safeExec.

    Args:
        content: Original file content
        func_name: Function name
        inner_assertions: List of translated inner assertions
        program_loop: Abstract program name for loop
        program_loop_end: Abstract program name for loop end

    Returns:
        Updated content with replaced inner assertions
    """
    if not inner_assertions:
        return content

    # Find all /*@ Inv ... */ comments
    inv_pattern = r'/\*@\s*Inv\s+(.*?)\s*\*/'

    matches = list(re.finditer(inv_pattern, content, flags=re.DOTALL))

    # Replace in reverse order to preserve positions
    for i, match in enumerate(reversed(matches)):
        assertion_index = len(matches) - 1 - i

        if assertion_index < len(inner_assertions):
            assertion = inner_assertions[assertion_index]

            if assertion['type'] == 'Inv' and 'translated' in assertion:
                # Add safeExec predicate
                with_safeexec = add_safeexec_predicate(
                    assertion['translated'],
                    assertion['variables'],
                    program_loop,
                    program_loop_end
                )

                # Replace the comment content
                start = match.start()
                end = match.end()

                new_comment = f"/*@ Inv {with_safeexec} */"
                content = content[:start] + new_comment + content[end:]

    return content


def translate_directory(input_dir: str, output_dir: str) -> Dict[str, bool]:
    """
    Translate all C files in a directory.

    Args:
        input_dir: Input directory containing C files
        output_dir: Output directory for translated files

    Returns:
        Dictionary mapping filenames to success status
    """
    results = {}

    if not os.path.exists(input_dir):
        print(f"Error: Input directory not found: {input_dir}")
        return results

    # Create output directory
    os.makedirs(output_dir, exist_ok=True)

    # Process each C file
    for filename in os.listdir(input_dir):
        if filename.endswith('.c'):
            input_path = os.path.join(input_dir, filename)

            # Generate output filename: xxx.c -> xxx_rel.c
            base_name = os.path.splitext(filename)[0]
            output_filename = f"{base_name}_rel.c"
            output_path = os.path.join(output_dir, output_filename)

            print(f"Processing {filename}...", end=' ')

            success = translate_c_file(input_path, output_path)
            results[filename] = success

            if success:
                print(f"✓ -> {output_filename}")
            else:
                print(f"✗ Failed")

    return results


def main():
    """Example usage."""
    import argparse

    parser = argparse.ArgumentParser(description='Translate C files with shape assertions')
    parser.add_argument('input', help='Input C file or directory')
    parser.add_argument('output', help='Output C file or directory')

    args = parser.parse_args()

    if os.path.isdir(args.input):
        # Process directory
        results = translate_directory(args.input, args.output)

        total = len(results)
        success = sum(1 for v in results.values() if v)

        print()
        print(f"Summary: {success}/{total} files translated successfully")
    else:
        # Process single file
        success = translate_c_file(args.input, args.output)

        if success:
            print(f"✓ Translation successful: {args.output}")
        else:
            print(f"✗ Translation failed")


if __name__ == "__main__":
    main()
