"""
Shape Assertion Parser and Translator

This package provides tools for parsing and translating shape assertions
used in separation logic verification of C programs.
"""

from .parser import (
    parse_assertion,
    recover_assertion,
    Var,
    BinOp,
    FieldAccess,
    Predicate,
    SepConj,
    AndConj,
    Exists,
)

from .translator import (
    ShapeTranslator,
    translate,
    translate_file,
)

from .preprocess import (
    AnnotationExtractor,
    format_result,
)

from .process_and_translate import (
    AssertionProcessor,
    format_translation_result,
    process_and_translate_file,
    process_and_translate_directory,
)

__all__ = [
    # Parser
    'parse_assertion',
    'recover_assertion',
    'Var',
    'BinOp',
    'FieldAccess',
    'Predicate',
    'SepConj',
    'AndConj',
    'Exists',
    # Translator
    'ShapeTranslator',
    'translate',
    'translate_file',
    # Preprocessor
    'AnnotationExtractor',
    'format_result',
    # Combined Processing
    'AssertionProcessor',
    'format_translation_result',
    'process_and_translate_file',
    'process_and_translate_directory',
]

__version__ = '1.0.0'
