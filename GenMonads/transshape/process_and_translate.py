"""
Process and translate shape assertions from C files.

This module combines the preprocessor and translator to extract shape assertions
from C files and translate them to data assertions with existential list variables.
It also generates Coq guards using the guardgen module.
"""

import os
from typing import Dict, List, Tuple, Optional

from .preprocess import AnnotationExtractor
from .translator import ShapeTranslator
from .parser import parse_assertion, recover_assertion

# Import guardgen module
try:
    from GenMonads.guardgen import gen_coq_guard
    GUARDGEN_AVAILABLE = True
except ImportError:
    GUARDGEN_AVAILABLE = False
    gen_coq_guard = None


class AssertionProcessor:
    """Process and translate assertions from C files."""

    def __init__(self):
        self.extractor = AnnotationExtractor()
        self.translator = ShapeTranslator()

    def translate_funcspec(self, funcspec: Dict[str, str]) -> Dict[str, Dict]:
        """Translate function specification clauses as a single unit.

        The variable counter is shared across Require and Ensure clauses,
        so variables are numbered continuously (?l1, ?l2, ?l3, ...).

        Args:
            funcspec: Dictionary with 'with', 'require', 'ensure' keys

        Returns:
            Dictionary with translated clauses and all generated variables
        """
        if not funcspec:
            return None

        # Reset counter for the entire function specification
        self.translator.reset_var_counter()

        result = {}
        all_variables = []

        # Keep With clause as-is (no translation needed)
        if funcspec['with']:
            result['with'] = {
                'original': funcspec['with']
            }

        # Translate Require clause (starts from ?l1)
        if funcspec['require']:
            try:
                # First assertion: reset=True (default behavior)
                translated, vars = self.translator.translate_assertion(funcspec['require'], reset=True)
                result['require'] = {
                    'original': funcspec['require'],
                    'translated': translated,
                }
                all_variables.extend(vars)
            except Exception as e:
                result['require'] = {
                    'original': funcspec['require'],
                    'error': str(e)
                }

        # Translate Ensure clause (counter continues from where Require left off)
        if funcspec['ensure']:
            try:
                # Second assertion: reset=False to continue variable numbering
                translated, vars = self.translator.translate_assertion(funcspec['ensure'], reset=False)
                result['ensure'] = {
                    'original': funcspec['ensure'],
                    'translated': translated,
                }
                all_variables.extend(vars)
            except Exception as e:
                result['ensure'] = {
                    'original': funcspec['ensure'],
                    'error': str(e)
                }

        # Add all variables at the top level
        result['variables'] = all_variables

        return result

    def translate_inner_assertions(self, inner_assertions: List[Dict]) -> List[Dict]:
        """Translate inner assertions (loop invariants).

        For INV type assertions, uses translate_assertion_with_exists to:
        1. Translate shape predicates
        2. Replace ?l1, ?l2 with l1, l2
        3. Wrap with 'exists l1 l2 ...' (or merge with existing exists)
        4. Preserves the command_guard (while condition) if present

        Args:
            inner_assertions: List of assertion dictionaries

        Returns:
            List of dictionaries with translated assertions
        """
        if not inner_assertions:
            return []

        results = []

        for assertion in inner_assertions:
            self.translator.reset_var_counter()

            try:
                # For INV type, use the special translation with exists wrapper
                if assertion['type'] == 'Inv':
                    translated, vars = self.translator.translate_assertion_with_exists(assertion['content'])
                else:
                    # For other types, use regular translation
                    translated, vars = self.translator.translate_assertion(assertion['content'])

                result_dict = {
                    'type': assertion['type'],
                    'original': assertion['content'],
                    'translated': translated,
                    'variables': vars,
                    'position': assertion.get('position')
                }

                # Add command_guard for Inv assertions if present
                if assertion['type'] == 'Inv' and 'command_guard' in assertion:
                    result_dict['command_guard'] = assertion['command_guard']

                results.append(result_dict)
            except Exception as e:
                result_dict = {
                    'type': assertion['type'],
                    'original': assertion['content'],
                    'error': str(e),
                    'position': assertion.get('position')
                }

                # Add command_guard even in error case
                if assertion['type'] == 'Inv' and 'command_guard' in assertion:
                    result_dict['command_guard'] = assertion['command_guard']

                results.append(result_dict)

        return results

    def generate_coq_guards(self, translated_assertions: List[Dict]) -> List[Dict]:
        """Generate Coq guards for translated INV assertions.

        Takes the output from translate_inner_assertions and generates Coq guards
        for INV assertions that have command guards.

        Args:
            translated_assertions: List of translated assertion dictionaries

        Returns:
            List of dictionaries with Coq guards added (if generation succeeded)
        """
        if not translated_assertions:
            return []

        if not GUARDGEN_AVAILABLE:
            # guardgen not available, return as-is
            return translated_assertions

        results = []

        for assertion in translated_assertions:
            result_dict = assertion.copy()

            # Only generate Coq guard for INV assertions with command_guard
            if (assertion['type'] == 'Inv' and
                'command_guard' in assertion and
                'translated' in assertion and
                'error' not in assertion):

                try:
                    coq_guard = gen_coq_guard(assertion['translated'], assertion['command_guard'])
                    result_dict['coq_guard'] = coq_guard
                except Exception as guard_error:
                    # Guard generation failed, store the error
                    result_dict['coq_guard_error'] = str(guard_error)

            results.append(result_dict)

        return results

    def process_file(self, file_path: str, generate_guards: bool = True) -> Dict:
        """Process a C file: extract and translate all assertions.

        Args:
            file_path: Path to the C file
            generate_guards: If True, generate Coq guards for INV assertions (default: True)

        Returns:
            Dictionary with extracted and translated assertions
        """
        # Extract annotations using preprocessor
        extraction_result = self.extractor.process_file(file_path)

        if 'error' in extraction_result:
            return extraction_result

        # Translate function specification
        translated_funcspec = None
        if extraction_result['funcspec']:
            translated_funcspec = self.translate_funcspec(extraction_result['funcspec'])

        # Translate inner assertions
        translated_inner = self.translate_inner_assertions(extraction_result['inner_assertions'])

        # Generate Coq guards if requested
        if generate_guards:
            translated_inner = self.generate_coq_guards(translated_inner)

        return {
            'file': extraction_result['file'],
            'function': extraction_result['function'],
            'funcspec': translated_funcspec,
            'inner_assertions': translated_inner
        }

    def process_directory(self, directory: str) -> Dict[str, Dict]:
        """Process all C files in a directory.

        Args:
            directory: Path to directory containing C files

        Returns:
            Dictionary mapping file names to their processed results
        """
        import os

        results = {}

        for root, dirs, files in os.walk(directory):
            for file in files:
                if file.endswith('.c'):
                    file_path = os.path.join(root, file)
                    result = self.process_file(file_path)
                    results[file] = result

        return results


def format_translation_result(result: Dict) -> str:
    """Format a translation result for display.

    Args:
        result: Result dictionary from process_file

    Returns:
        Formatted string
    """
    lines = []
    lines.append("=" * 80)
    lines.append(f"File: {result['file']}")
    lines.append(f"Function: {result['function']}")
    lines.append("=" * 80)

    if 'error' in result:
        lines.append(f"ERROR: {result['error']}")
        return '\n'.join(lines)

    # Function specification
    if result['funcspec']:
        lines.append("\n" + "─" * 80)
        lines.append("FUNCTION SPECIFICATION")
        lines.append("─" * 80)

        spec = result['funcspec']

        # Original specification
        lines.append("\nOriginal:")
        if 'with' in spec:
            lines.append(f"  With: {spec['with']['original']}")
        if 'require' in spec:
            lines.append(f"  Require: {spec['require']['original']}")
        if 'ensure' in spec:
            lines.append(f"  Ensure: {spec['ensure']['original']}")

        # Translated specification
        has_error = False
        if 'require' in spec and 'error' in spec['require']:
            has_error = True
            lines.append(f"\n  Require ERROR: {spec['require']['error']}")
        if 'ensure' in spec and 'error' in spec['ensure']:
            has_error = True
            lines.append(f"\n  Ensure ERROR: {spec['ensure']['error']}")

        if not has_error:
            lines.append("\nTranslated:")
            if 'with' in spec:
                lines.append(f"  With: {spec['with']['original']}")
            if 'require' in spec:
                lines.append(f"  Require: {spec['require']['translated']}")
            if 'ensure' in spec:
                lines.append(f"  Ensure: {spec['ensure']['translated']}")

            # Show all generated variables for the entire function spec
            if 'variables' in spec and spec['variables']:
                lines.append(f"  Generated variables: {', '.join(spec['variables'])}")
    else:
        lines.append("\nFunction Specification: Not found")

    # Inner assertions
    lines.append("\n" + "─" * 80)
    lines.append("INNER ASSERTIONS")
    lines.append("─" * 80)

    if result['inner_assertions']:
        for i, assertion in enumerate(result['inner_assertions'], 1):
            lines.append(f"\n{i}. Type: {assertion['type']}")
            lines.append(f"   Original:")
            lines.append(f"     {assertion['original']}")

            # Show command guard for Inv assertions
            if assertion['type'] == 'Inv' and 'command_guard' in assertion:
                lines.append(f"   CommandGuard: {assertion['command_guard']}")

            if 'error' in assertion:
                lines.append(f"   ERROR: {assertion['error']}")
            else:
                lines.append(f"   Translated:")
                lines.append(f"     {assertion['translated']}")
                if assertion['variables']:
                    lines.append(f"   Generated variables: {', '.join(assertion['variables'])}")

                # Show Coq guard if available
                if 'coq_guard' in assertion:
                    lines.append(f"   CoqGuard:")
                    lines.append(f"     {assertion['coq_guard']}")
                elif 'coq_guard_error' in assertion:
                    lines.append(f"   CoqGuard: ERROR - {assertion['coq_guard_error']}")
    else:
        lines.append("\nNo inner assertions found")

    lines.append("")
    return '\n'.join(lines)


def generate_coq_guards_for_assertions(translated_assertions: List[Dict]) -> List[Dict]:
    """Generate Coq guards for a list of translated assertions.

    This is a standalone function that takes translated assertions and adds Coq guards.
    Useful when you want to generate guards separately from the translation process.

    Args:
        translated_assertions: List of dictionaries with translated assertions
                              (output from translate_inner_assertions)

    Returns:
        List of dictionaries with coq_guard added (if generation succeeded)

    Example:
        >>> processor = AssertionProcessor()
        >>> extraction = processor.extractor.process_file('sll_copy.c')
        >>> translated = processor.translate_inner_assertions(extraction['inner_assertions'])
        >>> with_guards = generate_coq_guards_for_assertions(translated)
    """
    processor = AssertionProcessor()
    return processor.generate_coq_guards(translated_assertions)


def process_and_translate_file(file_path: str, generate_guards: bool = True) -> Dict:
    """Convenience function to process and translate a single file.

    Args:
        file_path: Path to the C file
        generate_guards: If True, generate Coq guards for INV assertions (default: True)

    Returns:
        Dictionary with processed and translated results
    """
    processor = AssertionProcessor()
    return processor.process_file(file_path, generate_guards=generate_guards)


def process_and_translate_directory(directory: str, generate_guards: bool = True) -> Dict[str, Dict]:
    """Convenience function to process and translate all files in a directory.

    Args:
        directory: Path to directory containing C files
        generate_guards: If True, generate Coq guards for INV assertions (default: True)

    Returns:
        Dictionary mapping file names to their results
    """
    processor = AssertionProcessor()
    return processor.process_directory(directory)
