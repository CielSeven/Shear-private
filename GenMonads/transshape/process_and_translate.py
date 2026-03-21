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
        """Translate function specification clauses as a single unit."""
        if not funcspec:
            return None

        # Reset counter for the entire function specification
        self.translator.reset_var_counter()

        result = {}
        all_variables = []

        # Keep With clause as-is
        if funcspec['with']:
            result['with'] = {'original': funcspec['with']}

        # Translate Require clause
        if funcspec['require']:
            try:
                translated, vars = self.translator.translate_assertion(funcspec['require'], reset=True)
                result['require'] = {
                    'original': funcspec['require'],
                    'translated': translated,
                }
                all_variables.extend(vars)
            except Exception as e:
                result['require'] = {'original': funcspec['require'], 'error': str(e)}

        # Translate Ensure clause
        if funcspec['ensure']:
            try:
                translated, vars = self.translator.translate_assertion(funcspec['ensure'], reset=False)
                result['ensure'] = {
                    'original': funcspec['ensure'],
                    'translated': translated,
                }
                all_variables.extend(vars)
            except Exception as e:
                result['ensure'] = {'original': funcspec['ensure'], 'error': str(e)}

        result['variables'] = all_variables
        return result

    def translate_inner_assertions(self, inner_assertions: List[Dict]) -> List[Dict]:
        """Translate inner assertions (loop invariants and control flow).
        """
        if not inner_assertions:
            return []

        results = []
        
        # If there's only one loop, don't use a prefix to maintain backward compatibility (l1, l2...)
        # If there are multiple, use a prefix to ensure uniqueness.
        use_prefix = len([a for a in inner_assertions if a['type'] == 'Inv']) > 1

        for i, assertion in enumerate(inner_assertions):
            prefix = str(i + 1) if use_prefix else ""
            self.translator.reset_var_counter(prefix=prefix)

            try:
                if assertion['type'] == 'Inv':
                    translated, vars = self.translator.translate_assertion_with_exists(
                        assertion['content'], prefix=prefix
                    )
                else:
                    translated, vars = self.translator.translate_assertion(
                        assertion['content'], prefix=prefix
                    )

                result_dict = {
                    'type': assertion['type'],
                    'original': assertion['content'],
                    'translated': translated,
                    'variables': vars,
                    'position': assertion.get('position')
                }

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
                if assertion['type'] == 'Inv' and 'command_guard' in assertion:
                    result_dict['command_guard'] = assertion['command_guard']
                results.append(result_dict)

        return results

    def process_file(self, file_path: str, generate_guards: bool = True) -> Dict:
        """Process a C file: extract and translate all assertions."""
        extraction_result = self.extractor.process_file(file_path)

        if 'error' in extraction_result:
            return extraction_result

        # 2. Process the single-function (backward compatibility)
        translated_funcspec = self.translate_funcspec(extraction_result['funcspec'])
        translated_inner = self.translate_inner_assertions(extraction_result['inner_assertions'])
        if generate_guards:
            translated_inner = self.generate_coq_guards(translated_inner)

        # 3. Process all functions (new functionality)
        processed_functions = []
        for func_data in extraction_result.get('functions', []):
            f_spec = self.translate_funcspec(func_data['funcspec'])
            f_inner = self.translate_inner_assertions(func_data['inner_assertions'])
            if generate_guards:
                f_inner = self.generate_coq_guards(f_inner)
            
            processed_functions.append({
                'function': func_data['function'],
                'funcspec': f_spec,
                'inner_assertions': f_inner
            })

        return {
            'file': extraction_result['file'],
            'function': extraction_result['function'],
            'funcspec': translated_funcspec,
            'inner_assertions': translated_inner,
            'functions': processed_functions
        }

    def generate_coq_guards(self, translated_assertions: List[Dict]) -> List[Dict]:
        if not translated_assertions or not GUARDGEN_AVAILABLE:
            return translated_assertions

        results = []
        for assertion in translated_assertions:
            result_dict = assertion.copy()
            if (assertion['type'] == 'Inv' and
                'command_guard' in assertion and
                'translated' in assertion and
                'error' not in assertion):
                try:
                    coq_guard = gen_coq_guard(assertion['translated'], assertion['command_guard'])
                    result_dict['coq_guard'] = coq_guard
                except Exception as guard_error:
                    result_dict['coq_guard_error'] = str(guard_error)
            results.append(result_dict)
        return results

    def process_directory(self, directory: str) -> Dict[str, Dict]:
        results = {}
        for root, dirs, files in os.walk(directory):
            for file in files:
                if file.endswith('.c'):
                    file_path = os.path.join(root, file)
                    result = self.process_file(file_path)
                    results[file] = result
        return results

def format_translation_result(result: Dict) -> str:
    lines = []
    lines.append("=" * 80)
    lines.append(f"File: {result['file']}")
    if 'error' in result:
        lines.append(f"ERROR: {result['error']}")
        return '\n'.join(lines)
    for func in result.get('functions', []):
        lines.append(f"\nFunction: {func['function']}")
        if func['funcspec']:
            spec = func['funcspec']
            lines.append("FuncSpec:")
            if 'require' in spec: lines.append(f"  Require: {spec['require'].get('translated', 'ERROR')}")
            if 'ensure' in spec: lines.append(f"  Ensure: {spec['ensure'].get('translated', 'ERROR')}")
        if func['inner_assertions']:
            lines.append("Inner Assertions:")
            for i, assertion in enumerate(func['inner_assertions'], 1):
                lines.append(f"  {i}. {assertion['type']}: {assertion['translated']}")
    return '\n'.join(lines)

def process_and_translate_file(file_path: str, generate_guards: bool = True) -> Dict:
    processor = AssertionProcessor()
    return processor.process_file(file_path, generate_guards=generate_guards)

def process_and_translate_directory(directory: str, generate_guards: bool = True) -> Dict[str, Dict]:
    processor = AssertionProcessor()
    return processor.process_directory(directory)
