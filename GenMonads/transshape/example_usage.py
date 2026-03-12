"""
Example usage of the shape assertion parser and translator.

This script demonstrates how to parse, recover, and translate shape assertions.
"""

from parser import parse_assertion, recover_assertion
from translator import ShapeTranslator, translate


def example_1_basic_parsing():
    """Example 1: Basic parsing and recovery"""
    print("=" * 70)
    print("EXAMPLE 1: Basic Parsing and Recovery")
    print("=" * 70)

    assertion = "t != 0 && lseg(x, y) * listrep(z)"

    print(f"Original assertion: {assertion}")
    print()

    # Parse the assertion
    ast = parse_assertion(assertion)
    print(f"Parsed AST: {ast}")
    print()

    # Recover it back to string
    recovered = recover_assertion(ast)
    print(f"Recovered assertion: {recovered}")
    print()


def example_2_simple_translation():
    """Example 2: Simple translation without existentials"""
    print("=" * 70)
    print("EXAMPLE 2: Simple Translation")
    print("=" * 70)

    assertion = "t != 0 && t -> next == 0 && lseg(x@pre,p) * listrep(p) * lseg(y, t)"

    print(f"Original: {assertion}")
    print()

    # Translate
    translated, vars = translate(assertion)

    print(f"Translated: {translated}")
    print(f"Generated variables: {vars}")
    print()


def example_3_existential_translation():
    """Example 3: Translation with existential quantifiers"""
    print("=" * 70)
    print("EXAMPLE 3: Translation with Existential Quantifiers")
    print("=" * 70)

    assertion = "exists p_prev, t != 0 && dllseg_shape(x@pre,0, p_prev,p) * dlistrep_shape(p, p_prev)"

    print(f"Original:")
    print(f"  {assertion}")
    print()

    # Translate
    translated, vars = translate(assertion)

    print(f"Translated:")
    print(f"  {translated}")
    print()
    print(f"Generated variables: {vars}")
    print()


def example_4_custom_translator():
    """Example 4: Using a custom translator with modified mappings"""
    print("=" * 70)
    print("EXAMPLE 4: Custom Translator with Modified Mappings")
    print("=" * 70)

    # Create a custom translator
    translator = ShapeTranslator()

    # Add a custom predicate mapping
    translator.add_mapping('my_tree', 1)  # my_tree needs 1 list argument

    assertion = "my_tree(root) * listrep(x)"

    print(f"Original: {assertion}")
    print()

    # Translate using the custom translator
    translated, vars = translator.translate_assertion(assertion)

    print(f"Translated: {translated}")
    print(f"Generated variables: {vars}")
    print()

    # Show all mappings
    print(f"Current mappings:")
    for pred, num_args in translator.get_mapping().items():
        print(f"  {pred} -> adds {num_args} list argument(s)")
    print()


def example_5_complex_invariant():
    """Example 5: Complex loop invariant from real code"""
    print("=" * 70)
    print("EXAMPLE 5: Complex Loop Invariant (from dll_multi_merge.c)")
    print("=" * 70)

    assertion = """exists v, v == t -> data && u == t -> next && t != 0 && dlistrep_shape(y,0) * dlistrep_shape(z,0) * dlistrep_shape(u,t) * dllseg_shape(x@pre, 0, t->prev, t)"""

    print(f"Original:")
    print(f"  {assertion}")
    print()

    # Parse
    ast = parse_assertion(assertion)
    print(f"Parsed successfully: {type(ast).__name__}")
    print()

    # Translate
    translated, vars = translate(assertion)

    print(f"Translated:")
    print(f"  {translated}")
    print()
    print(f"Generated list variables: {vars}")
    print()


def example_6_batch_processing():
    """Example 6: Batch processing multiple assertions"""
    print("=" * 70)
    print("EXAMPLE 6: Batch Processing Multiple Assertions")
    print("=" * 70)

    assertions = [
        "listrep(x)",
        "lseg(x, y) * lseg(y, z)",
        "dlistrep_shape(x, 0) * dlistrep_shape(y, 0)",
        "exists p, lseg(x, p) * listrep(p)",
    ]

    translator = ShapeTranslator()

    print("Processing assertions:")
    print()

    for i, assertion in enumerate(assertions, 1):
        translator.reset_var_counter()  # Reset counter for each assertion
        translated, vars = translator.translate_assertion(assertion)

        print(f"{i}. {assertion}")
        print(f"   -> {translated}")
        if vars:
            print(f"   Variables: {', '.join(vars)}")
        print()


def main():
    """Run all examples"""
    print()
    print("*" * 70)
    print("*" + " " * 68 + "*")
    print("*" + " " * 15 + "SHAPE ASSERTION PARSER & TRANSLATOR" + " " * 19 + "*")
    print("*" + " " * 68 + "*")
    print("*" * 70)
    print()

    example_1_basic_parsing()
    example_2_simple_translation()
    example_3_existential_translation()
    example_4_custom_translator()
    example_5_complex_invariant()
    example_6_batch_processing()

    print("=" * 70)
    print("All examples completed successfully!")
    print("=" * 70)


if __name__ == "__main__":
    main()
