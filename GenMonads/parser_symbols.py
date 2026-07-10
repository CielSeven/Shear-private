"""
Parser symbol registry for transshape assertions.

This registry classifies call syntax that is not about translation.  Predicate
mappings still define shape-to-data rewrites; this file only tells the parser
which ``name(...)`` forms are formula-level spatial predicates and which are
expression-level pure calls.
"""

import json
import os
from functools import lru_cache
from typing import Any, Dict, List


_CONFIG_DIR = os.path.join(os.path.dirname(__file__), 'data')
_CONFIG_FILE = os.path.join(_CONFIG_DIR, 'parser_symbols.json')

_DEFAULT_SYMBOLS: Dict[str, List[str]] = {
    'spatial_predicates': [
        'emp',
        'CharArray::full',
        'CharArray::seg',
        'CharArray::undef_full',
        'CharArray::undef_seg',
        'IntArray::full',
        'IntArray::seg',
        'IntArray::undef_full',
        'IntArray::undef_seg',
        'IntArray::missing_i',
    ],
    'pure_call_exprs': [
        'Zlength',
        'app',
        'cons',
        'string_length',
    ],
}


def _normalize_symbol_list(data: Dict[str, Any], key: str) -> List[str]:
    values = data.get(key, [])
    if not isinstance(values, list) or any(not isinstance(v, str) or not v for v in values):
        raise ValueError(f"Invalid parser symbol list for {key!r}")
    return values[:]


@lru_cache(maxsize=1)
def _load_symbols() -> Dict[str, List[str]]:
    """Load parser symbols from JSON, or return defaults if unavailable."""
    if os.path.exists(_CONFIG_FILE):
        try:
            with open(_CONFIG_FILE, 'r', encoding='utf-8') as f:
                data = json.load(f)
            if not isinstance(data, dict):
                raise ValueError("Parser symbol registry must be a JSON object")
            return {
                'spatial_predicates': _normalize_symbol_list(data, 'spatial_predicates'),
                'pure_call_exprs': _normalize_symbol_list(data, 'pure_call_exprs'),
            }
        except (json.JSONDecodeError, IOError, ValueError):
            return {key: values[:] for key, values in _DEFAULT_SYMBOLS.items()}
    return {key: values[:] for key, values in _DEFAULT_SYMBOLS.items()}


def get_parser_symbols() -> Dict[str, List[str]]:
    """Return parser symbol lists loaded from ``data/parser_symbols.json``."""
    return _load_symbols()


def clear_parser_symbols_cache() -> None:
    """Clear the parser symbol registry cache, mainly for tests."""
    _load_symbols.cache_clear()
