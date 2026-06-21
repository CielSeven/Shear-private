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
from .data_witness import extract_data_witnesses, extract_pre_existing_vars
from .c_types import build_type_env, collect_struct_decls

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
        self._struct_decls: Dict[str, Dict[str, str]] = {}
        self._c_source: str = ""
        self._type_env: Dict[str, str] = {}

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
                translated, vars = self.translator.translate_assertion(
                    funcspec['require'], reset=True,
                    type_env=self._type_env, struct_decls=self._struct_decls,
                )
                var_types = self.translator.last_generated_var_types[:]
                result['require'] = {
                    'original': funcspec['require'],
                    'translated': translated,
                    'variables': vars,
                    'variable_types': var_types,
                }
                all_variables.extend(vars)
                all_variable_types = result.get('variable_types', [])
                all_variable_types.extend(var_types)
                result['variable_types'] = all_variable_types
            except Exception as e:
                result['require'] = {'original': funcspec['require'], 'error': str(e)}

        # Translate Ensure clause
        if funcspec['ensure']:
            try:
                translated, vars = self.translator.translate_assertion(
                    funcspec['ensure'], reset=False,
                    type_env=self._type_env, struct_decls=self._struct_decls,
                )
                var_types = self.translator.last_generated_var_types[:]

                # Detect data-field witnesses bound by the original Ensure's
                # ``exists`` clause (e.g. ``__return -> data == d``).  These
                # become abstract-state-visible variables, the same way they
                # are for loop invariants.
                pre_existing = extract_pre_existing_vars(funcspec['ensure'])
                data_witnesses = extract_data_witnesses(translated, pre_existing)

                result['ensure'] = {
                    'original': funcspec['ensure'],
                    'translated': translated,
                    'variables': vars,
                    'variable_types': var_types,
                    'data_witnesses': data_witnesses,
                }
                all_variables.extend(vars)
                all_variable_types = result.get('variable_types', [])
                all_variable_types.extend(var_types)
                result['variable_types'] = all_variable_types
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
                # ``Inv`` and bare ``Assert`` proof-checkpoints both
                # wrap their bodies in ``exists`` and use the same
                # shape→data rewriter; the difference is downstream
                # (data-witness propagation into the abstract loop
                # state, only meaningful for ``Inv``).
                if assertion['type'] in ('Inv', 'Assert'):
                    translated, vars = self.translator.translate_assertion_with_exists(
                        assertion['content'], prefix=prefix,
                        type_env=self._type_env, struct_decls=self._struct_decls,
                    )
                else:
                    translated, vars = self.translator.translate_assertion(
                        assertion['content'], prefix=prefix,
                        type_env=self._type_env, struct_decls=self._struct_decls,
                    )

                var_types = self.translator.last_generated_var_types[:]

                # For Inv assertions, detect data witness variables from
                # pre-existing existentials (e.g. 'w' in 't -> data == w').
                # Assert blocks have no loop state to lift witnesses
                # into, so we skip the extraction for them.
                data_witnesses = []
                if assertion['type'] == 'Inv':
                    pre_existing = extract_pre_existing_vars(assertion['content'])
                    data_witnesses = extract_data_witnesses(translated, pre_existing)
                    if data_witnesses:
                        vars = list(vars) + data_witnesses
                        var_types = var_types + ['Z'] * len(data_witnesses)

                result_dict = {
                    'type': assertion['type'],
                    'original': assertion['content'],
                    'translated': translated,
                    'variables': vars,
                    'variable_types': var_types,
                    'data_witnesses': data_witnesses,
                    'position': assertion.get('position')
                }
                # Preserve the ``Inv Assert`` qualifier when the source
                # had it so the substitution layer can emit it back.
                if assertion.get('inv_assert'):
                    result_dict['inv_assert'] = True

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
                if assertion.get('inv_assert'):
                    result_dict['inv_assert'] = True
                if assertion['type'] == 'Inv' and 'command_guard' in assertion:
                    result_dict['command_guard'] = assertion['command_guard']
                results.append(result_dict)

        return results

    def process_file(self, file_path: str, generate_guards: bool = True) -> Dict:
        """Process a C file: extract and translate all assertions."""
        extraction_result = self.extractor.process_file(file_path)

        if 'error' in extraction_result:
            return extraction_result

        # Pre-load C struct definitions + raw C source so the translator can
        # resolve ``EXPR -> FIELD`` types and desugar field-equalities into
        # typed ``store(...)`` predicates.
        self._struct_decls = collect_struct_decls(file_path)
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                self._c_source = f.read()
        except OSError:
            self._c_source = ""
        primary_func = extraction_result.get('function', '')
        self._type_env = (
            build_type_env(self._c_source, primary_func) if primary_func else {}
        )

        # 2. Process the single-function (backward compatibility)
        translated_funcspec = self.translate_funcspec(extraction_result['funcspec'])
        translated_inner = self.translate_inner_assertions(extraction_result['inner_assertions'])
        if generate_guards:
            translated_inner = self.generate_coq_guards(translated_inner)

        # 3. Process all functions (new functionality)
        processed_functions = []
        for func_data in extraction_result.get('functions', []):
            func_name = func_data.get('function', '')
            self._type_env = (
                build_type_env(self._c_source, func_name) if func_name else {}
            )
            f_spec = self.translate_funcspec(func_data['funcspec'])
            f_inner = self.translate_inner_assertions(func_data['inner_assertions'])
            if generate_guards:
                f_inner = self.generate_coq_guards(f_inner)
            
            processed_functions.append({
                'function': func_data['function'],
                'return_type': func_data.get('return_type', ''),
                'funcspec': f_spec,
                'inner_assertions': f_inner
            })

        # Mirror return_type at top level for the single-function fallback.
        top_level_return_type = ''
        for func in processed_functions:
            if func['function'] == extraction_result['function']:
                top_level_return_type = func.get('return_type', '')
                break

        return {
            'file': extraction_result['file'],
            'function': extraction_result['function'],
            'return_type': top_level_return_type,
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
                    extra_vars = assertion.get('data_witnesses', [])
                    coq_guard = gen_coq_guard(
                        assertion['translated'], assertion['command_guard'],
                        extra_vars=extra_vars or None,
                    )
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
