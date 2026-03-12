"""
Example demonstrating separate Coq guard generation.

This shows how translation and Coq guard generation are separate steps.
"""

import os
from process_and_translate import (
    AssertionProcessor,
    generate_coq_guards_for_assertions,
    process_and_translate_file
)


def example_two_step_process():
    """Example: Two-step process (translate, then generate guards)"""
    print("=" * 80)
    print("EXAMPLE 1: Two-Step Process")
    print("=" * 80)
    print()

    base_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    file_path = os.path.join(base_dir, '..', 'shape_invdataset', 'sll', 'sll_copy.c')

    if not os.path.exists(file_path):
        print(f"ERROR: File not found: {file_path}")
        return

    # Step 1: Extract and translate (no guard generation)
    print("Step 1: Extract and translate assertions")
    processor = AssertionProcessor()
    extraction = processor.extractor.process_file(file_path)
    translated = processor.translate_inner_assertions(extraction['inner_assertions'])

    print(f"  Translated {len(translated)} assertions")
    for i, assertion in enumerate(translated, 1):
        print(f"  {i}. Type: {assertion['type']}")
        if 'command_guard' in assertion:
            print(f"     CommandGuard: {assertion['command_guard']}")
        print(f"     Has coq_guard: {'coq_guard' in assertion}")
    print()

    # Step 2: Generate Coq guards separately
    print("Step 2: Generate Coq guards")
    with_guards = generate_coq_guards_for_assertions(translated)

    print(f"  Processed {len(with_guards)} assertions")
    for i, assertion in enumerate(with_guards, 1):
        print(f"  {i}. Type: {assertion['type']}")
        if 'coq_guard' in assertion:
            print(f"     ✓ CoqGuard generated")
        elif 'coq_guard_error' in assertion:
            print(f"     ✗ CoqGuard error: {assertion['coq_guard_error'][:50]}...")
        else:
            print(f"     - No CoqGuard (not INV or no command_guard)")
    print()


def example_automatic_process():
    """Example: Automatic process (guards generated automatically)"""
    print("=" * 80)
    print("EXAMPLE 2: Automatic Process (Default)")
    print("=" * 80)
    print()

    base_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    file_path = os.path.join(base_dir, '..', 'shape_invdataset', 'sll', 'sll_copy.c')

    if not os.path.exists(file_path):
        print(f"ERROR: File not found: {file_path}")
        return

    print("Processing with automatic guard generation...")
    result = process_and_translate_file(file_path)

    print(f"  Processed {len(result['inner_assertions'])} assertions")
    for i, assertion in enumerate(result['inner_assertions'], 1):
        print(f"  {i}. Type: {assertion['type']}")
        if 'coq_guard' in assertion:
            print(f"     ✓ CoqGuard: {assertion['coq_guard'][:50]}...")
        elif 'coq_guard_error' in assertion:
            print(f"     ✗ Error: {assertion['coq_guard_error'][:50]}...")
    print()


def example_disabled_guards():
    """Example: Disable guard generation"""
    print("=" * 80)
    print("EXAMPLE 3: Disabled Guard Generation")
    print("=" * 80)
    print()

    base_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    file_path = os.path.join(base_dir, '..', 'shape_invdataset', 'sll', 'sll_copy.c')

    if not os.path.exists(file_path):
        print(f"ERROR: File not found: {file_path}")
        return

    print("Processing with guard generation DISABLED...")
    result = process_and_translate_file(file_path, generate_guards=False)

    print(f"  Processed {len(result['inner_assertions'])} assertions")
    for i, assertion in enumerate(result['inner_assertions'], 1):
        print(f"  {i}. Type: {assertion['type']}")
        print(f"     Has coq_guard: {'coq_guard' in assertion}")
        print(f"     Has coq_guard_error: {'coq_guard_error' in assertion}")
    print()


def example_method_directly():
    """Example: Using the method directly"""
    print("=" * 80)
    print("EXAMPLE 4: Using Method Directly")
    print("=" * 80)
    print()

    base_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    file_path = os.path.join(base_dir, '..', 'shape_invdataset', 'sll', 'sll_copy.c')

    if not os.path.exists(file_path):
        print(f"ERROR: File not found: {file_path}")
        return

    processor = AssertionProcessor()

    # Extract
    print("Extracting...")
    extraction = processor.extractor.process_file(file_path)

    # Translate
    print("Translating...")
    translated = processor.translate_inner_assertions(extraction['inner_assertions'])

    # Generate guards using the method
    print("Generating guards using processor.generate_coq_guards()...")
    with_guards = processor.generate_coq_guards(translated)

    print(f"  Result: {len(with_guards)} assertions")
    for i, assertion in enumerate(with_guards, 1):
        if 'coq_guard' in assertion:
            print(f"  {i}. ✓ Guard generated")
    print()


def main():
    """Run all examples."""
    print("\n")
    print("*" * 80)
    print("*" + " " * 78 + "*")
    print("*" + "SEPARATE COQ GUARD GENERATION EXAMPLES".center(78) + "*")
    print("*" + " " * 78 + "*")
    print("*" * 80)
    print()

    example_two_step_process()
    example_automatic_process()
    example_disabled_guards()
    example_method_directly()

    print("=" * 80)
    print("ALL EXAMPLES COMPLETED")
    print("=" * 80)
    print()
    print("Key Points:")
    print("  1. Translation and guard generation are separate functions")
    print("  2. Can use automatically (default) or in two steps")
    print("  3. Can disable with generate_guards=False")
    print("  4. Standalone function: generate_coq_guards_for_assertions()")


if __name__ == "__main__":
    main()
