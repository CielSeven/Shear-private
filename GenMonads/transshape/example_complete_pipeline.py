"""
Example: Complete pipeline from C file to translated assertions.

This example demonstrates how to use the combined preprocessor and translator
to extract and translate shape assertions from C files.
"""

import os
from process_and_translate import (
    AssertionProcessor,
    format_translation_result,
    process_and_translate_file
)


def example_single_file():
    """Example: Process a single C file."""
    print("=" * 80)
    print("EXAMPLE 1: Processing a Single C File")
    print("=" * 80)
    print()

    # Get path to sll_copy.c
    base_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    file_path = os.path.join(base_dir, '..', 'shape_invdataset', 'sll', 'sll_copy.c')

    if not os.path.exists(file_path):
        print(f"ERROR: File not found: {file_path}")
        return

    print(f"Processing: {file_path}")
    print()

    # Process and translate the file
    result = process_and_translate_file(file_path)

    # Display results
    print(format_translation_result(result))


def example_directory():
    """Example: Process all files in a directory."""
    print("=" * 80)
    print("EXAMPLE 2: Processing All Files in SLL Directory")
    print("=" * 80)
    print()

    # Get path to sll directory
    base_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    sll_dir = os.path.join(base_dir, '..', 'shape_invdataset', 'sll')

    if not os.path.exists(sll_dir):
        print(f"ERROR: Directory not found: {sll_dir}")
        return

    # Create processor
    processor = AssertionProcessor()

    # Process all files in directory
    results = processor.process_directory(sll_dir)

    print(f"Processed {len(results)} files")
    print()

    # Display results for each file
    for file_name in sorted(results.keys()):
        print(format_translation_result(results[file_name]))


def example_custom_usage():
    """Example: Custom processing with manual control."""
    print("=" * 80)
    print("EXAMPLE 3: Custom Processing with Manual Control")
    print("=" * 80)
    print()

    base_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    file_path = os.path.join(base_dir, '..', 'shape_invdataset', 'dll', 'dll_copy.c')

    if not os.path.exists(file_path):
        print(f"ERROR: File not found: {file_path}")
        return

    # Create processor
    processor = AssertionProcessor()

    # Process file
    result = processor.process_file(file_path)

    # Extract specific information
    print(f"File: {os.path.basename(result['file'])}")
    print(f"Function: {result['function']}")
    print()

    # Show function specification translation
    if result['funcspec']:
        print("Function Specification Translations:")
        print("-" * 40)

        if 'require' in result['funcspec']:
            req = result['funcspec']['require']
            print(f"\nRequire:")
            print(f"  Original:    {req['original']}")
            if 'translated' in req:
                print(f"  Translated:  {req['translated']}")
                print(f"  Variables:   {', '.join(req['variables'])}")

        if 'ensure' in result['funcspec']:
            ens = result['funcspec']['ensure']
            print(f"\nEnsure:")
            print(f"  Original:    {ens['original']}")
            if 'translated' in ens:
                print(f"  Translated:  {ens['translated']}")
                print(f"  Variables:   {', '.join(ens['variables'])}")

    # Show inner assertions
    if result['inner_assertions']:
        print()
        print("Inner Assertion Translations:")
        print("-" * 40)

        for i, assertion in enumerate(result['inner_assertions'], 1):
            print(f"\n{i}. {assertion['type']}:")
            print(f"   Original (first 80 chars):")
            print(f"     {assertion['original'][:80]}...")
            if 'translated' in assertion:
                print(f"   Translated (first 80 chars):")
                print(f"     {assertion['translated'][:80]}...")
                print(f"   Variables: {', '.join(assertion['variables'])}")

    print()


def example_comparison():
    """Example: Compare original vs translated side-by-side."""
    print("=" * 80)
    print("EXAMPLE 4: Side-by-Side Comparison")
    print("=" * 80)
    print()

    base_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    file_path = os.path.join(base_dir, '..', 'shape_invdataset', 'sll', 'sll_reverse.c')

    if not os.path.exists(file_path):
        print(f"ERROR: File not found: {file_path}")
        return

    result = process_and_translate_file(file_path)

    print(f"File: {os.path.basename(result['file'])}")
    print(f"Function: {result['function']}")
    print()

    # Compare function spec
    if result['funcspec'] and 'require' in result['funcspec']:
        req = result['funcspec']['require']
        print("Require Clause Comparison:")
        print("-" * 80)
        print(f"BEFORE: {req['original']}")
        if 'translated' in req:
            print(f"AFTER:  {req['translated']}")
            print(f"ADDED:  {len(req['variables'])} existential list variables: {', '.join(req['variables'])}")
        print()

    if result['funcspec'] and 'ensure' in result['funcspec']:
        ens = result['funcspec']['ensure']
        print("Ensure Clause Comparison:")
        print("-" * 80)
        print(f"BEFORE: {ens['original']}")
        if 'translated' in ens:
            print(f"AFTER:  {ens['translated']}")
            print(f"ADDED:  {len(ens['variables'])} existential list variables: {', '.join(ens['variables'])}")
        print()

    # Compare inner assertions
    if result['inner_assertions']:
        for i, assertion in enumerate(result['inner_assertions'], 1):
            print(f"Inner Assertion {i} Comparison:")
            print("-" * 80)
            print(f"BEFORE: {assertion['original']}")
            if 'translated' in assertion:
                print(f"AFTER:  {assertion['translated']}")
                print(f"ADDED:  {len(assertion['variables'])} existential list variables: {', '.join(assertion['variables'])}")
            print()


def main():
    """Run all examples."""
    print()
    print("*" * 80)
    print("*" + " " * 78 + "*")
    print("*" + "COMPLETE PIPELINE EXAMPLES".center(78) + "*")
    print("*" + "Extract + Translate Shape Assertions from C Files".center(78) + "*")
    print("*" + " " * 78 + "*")
    print("*" * 80)
    print()

    example_single_file()
    print("\n\n")

    example_directory()
    print("\n\n")

    example_custom_usage()
    print("\n\n")

    example_comparison()

    print()
    print("=" * 80)
    print("ALL EXAMPLES COMPLETED")
    print("=" * 80)


if __name__ == "__main__":
    main()
